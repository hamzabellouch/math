import Mathlib
import OAI.Analysis.Conductivity.Variational.CompactFiberPrimitive

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology

variable {ι P : Type*}
  [TopologicalSpace P] [FirstCountableTopology P] [LocallyCompactSpace P]

def compactCrossMoment (χ : ℝ → ℝ) (w v : ℝ → ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => ∫ s, χ s*w s j*v s i

lemma compactCrossMoment_restrict (χ : ℝ → ℝ) (w v : ℝ → ι → ℝ) (i j : ι) :
    compactCrossMoment χ w v i j=∫ s in tsupport χ, χ s*w s j*v s i := by
  dsimp only [compactCrossMoment]
  nth_rw 1 [←setIntegral_univ]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ (subset_univ _)
  intro s hs
  simp only [image_eq_zero_of_notMem_tsupport hs.2,zero_mul]

lemma compactCrossMoment_continuous {χ : ℝ → ℝ} {w : ℝ → ι → ℝ}
    {v : P → ℝ → ι → ℝ} (hc : Continuous χ) (hs : HasCompactSupport χ)
    (hw : ∀ j,Continuous (fun s => w s j))
    (hv : ∀ i,Continuous (fun ps : P × ℝ => v ps.1 ps.2 i)) :
    Continuous (fun p => compactCrossMoment χ w (v p)) := by
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  simp only [compactCrossMoment_restrict]
  apply continuous_parametric_integral_of_continuous (μ := volume) _ hs
  exact ((hc.comp continuous_snd).mul ((hw j).comp continuous_snd)).mul (hv i)

lemma compactCrossMoment_self (χ : ℝ → ℝ) (w : ℝ → ι → ℝ) :
    compactCrossMoment χ w w=compactMomentGram χ w := by
  ext i j
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun s => by dsimp; ring)

variable [Fintype ι] [DecidableEq ι]

lemma compactCrossMoment_solve {χ : ℝ → ℝ} {w v : ℝ → ι → ℝ}
    (hc : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hs : HasCompactSupport χ)
    (hw : ∀ j,ContDiff ℝ (↑(⊤ : ℕ∞)) (fun s => w s j))
    (hv : ∀ i,Continuous (fun s => v s i))
    (hM : IsUnit (compactCrossMoment χ w v)) (b : ι → ℝ) :
    ∃ a : ι → ℝ, compactCrossMoment χ w v*ᵥa=b ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) (fun s => χ s*(a ⬝ᵥ w s)) ∧
      HasCompactSupport (fun s => χ s*(a ⬝ᵥ w s)) ∧
      tsupport (fun s => χ s*(a ⬝ᵥ w s))⊆tsupport χ ∧
      (∀ i,(∫ s,χ s*(a ⬝ᵥ w s)*v s i)=b i) := by
  obtain ⟨a,ha⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hM b
  refine ⟨a,ha,hc.mul (ContDiff.sum fun j _ => contDiff_const.mul (hw j)),
    hs.mul_right,tsupport_mul_subset_left,?_⟩
  intro i
  rw [←congrFun ha i]
  change (∫ s,χ s*(a ⬝ᵥ w s)*v s i)=∑ j,compactCrossMoment χ w v i j*a j
  calc
    _ = ∫ s,∑ j,(χ s*w s j*v s i)*a j := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun s => by
        simp only [dotProduct,Finset.mul_sum,Finset.sum_mul]
        apply Finset.sum_congr rfl; intro j _; ring
    _ = _ := by
      have hi (j : ι) : Integrable (fun s => (χ s*w s j*v s i)*a j) := by
        exact (((hc.continuous.mul (hw j).continuous).mul (hv i)).integrable_of_hasCompactSupport
          (hs.mul_right.mul_right)).mul_const _
      rw [integral_finsetSum _ (fun j _ => hi j)]
      simp only [integral_mul_const,compactCrossMoment]

theorem compactMoment_perturbed_surjective {χ : ℝ → ℝ} {w : ℝ → ι → ℝ}
    {v : P → ℝ → ι → ℝ} {p₀ : P}
    (hc : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hs : HasCompactSupport χ)
    (hw : ∀ j,ContDiff ℝ (↑(⊤ : ℕ∞)) (fun s => w s j))
    (hv : ∀ i,Continuous (fun ps : P × ℝ => v ps.1 ps.2 i))
    (hlim : v p₀=w) (hG : (compactMomentGram χ w).PosDef) :
    ∀ᶠ p in 𝓝 p₀,∀ b : ι → ℝ,
      ∃ f : ℝ → ℝ,ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ HasCompactSupport f ∧
        tsupport f⊆tsupport χ ∧ (∀ i,(∫ s,f s*v p s i)=b i) := by
  have hM := compactCrossMoment_continuous hc.continuous hs (fun j => (hw j).continuous) hv
  have hM₀ : IsUnit (compactCrossMoment χ w (v p₀)) := by
    rw [hlim,compactCrossMoment_self]
    exact hG.isUnit
  have hd₀ : (compactCrossMoment χ w (v p₀)).det≠0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hM₀)
  have hed : ∀ᶠ p in 𝓝 p₀,(compactCrossMoment χ w (v p)).det≠0 :=
    (isOpen_ne_fun hM.matrix_det continuous_const).mem_nhds hd₀
  have he : ∀ᶠ p in 𝓝 p₀,IsUnit (compactCrossMoment χ w (v p)) :=
    hed.mono (fun p hp => (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hp))
  filter_upwards [he] with p hp
  intro b
  obtain ⟨a,ha,hf,hfs,hsub,hb⟩ := compactCrossMoment_solve hc hs hw
    (fun i => (hv i).comp (continuous_const.prodMk continuous_id)) hp b
  exact ⟨_,hf,hfs,hsub,hb⟩

end ScalarConductivity

end

end OAI
