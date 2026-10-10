import Mathlib
import OAI.Analysis.Conductivity.Variational.WeakHarmonicClassical
import OAI.Analysis.Conductivity.Geometry.BoxMomentRightInverse

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology

variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P] [LocallyCompactSpace P]

def wallProjectedMoment (η : ℝ → ℝ) (w : P → (ℝ×ℝ) → Fin 3 → ℝ)
    (p : P) (s : ℝ) (i : Fin 3) : ℝ := ∫ y,η y*w p (s,y) i

lemma wallProjectedMoment_continuous {η : ℝ → ℝ} {w : P → (ℝ×ℝ) → Fin 3 → ℝ}
    (hη : Continuous η) (hs : HasCompactSupport η)
    (hw : ∀ i,Continuous (fun pq : P × (ℝ×ℝ) => w pq.1 pq.2 i)) (i : Fin 3) :
    Continuous (fun ps : P × ℝ => wallProjectedMoment η w ps.1 ps.2 i) := by
  have he (p : P) (s : ℝ) : wallProjectedMoment η w p s i=
      ∫ y in tsupport η,η y*w p (s,y) i := by
    dsimp [wallProjectedMoment]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    simp only [image_eq_zero_of_notMem_tsupport hy,zero_mul]
  simp_rw [he]
  apply continuous_parametric_integral_of_continuous (μ := volume) _ hs
  exact (hη.comp continuous_snd).mul ((hw i).comp
    ((continuous_fst.fst).prodMk (continuous_fst.snd.prodMk continuous_snd)))

lemma surface_product_compact {f η : ℝ → ℝ} (hf : HasCompactSupport f)
    (hη : HasCompactSupport η) :
    HasCompactSupport (fun q : ℝ×ℝ => f q.1*η q.2) ∧
      tsupport (fun q : ℝ×ℝ => f q.1*η q.2)⊆tsupport f ×ˢ tsupport η := by
  have hv : Function.support (fun q : ℝ×ℝ => f q.1*η q.2)⊆tsupport f ×ˢ tsupport η := by
    intro q hq
    exact ⟨subset_tsupport f (mul_ne_zero_iff.mp hq).1,
      subset_tsupport η (mul_ne_zero_iff.mp hq).2⟩
  exact ⟨HasCompactSupport.of_support_subset_isCompact (hf.prod hη) hv,
    closure_minimal hv (hf.isClosed.prod hη.isClosed)⟩

lemma wallProjectedMoment_fubini {f η : ℝ → ℝ} {w : (ℝ×ℝ) → ℝ}
    (hf : Continuous f) (hsf : HasCompactSupport f)
    (hη : Continuous η) (hsη : HasCompactSupport η) (hw : Continuous w) :
    (∫ q : ℝ×ℝ,(f q.1*η q.2)*w q)=∫ s,f s*(∫ y,η y*w (s,y)) := by
  have hi : Integrable (fun q : ℝ×ℝ => (f q.1*η q.2)*w q) :=
    (((hf.comp continuous_fst).mul (hη.comp continuous_snd)).mul hw).integrable_of_hasCompactSupport
      (surface_product_compact hsf hsη).1.mul_right
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [integral_prod _ hi]
  congr 1
  ext s
  simp_rw [mul_assoc]
  exact integral_const_mul _ _

theorem wall_surface_moment_uniform_inverse {l r a b σ lam : ℝ}
    (hlr : l<r) (hab : a<b) (hσ : σ≠0) (hlam : lam≠0)
    {w : P → (ℝ×ℝ) → Fin 3 → ℝ} {p₀ : P}
    (hw : ∀ i,Continuous (fun pq : P × (ℝ×ℝ) => w pq.1 pq.2 i))
    (hlim : ∀ q,w p₀ q=wallMomentBasis σ lam q.1) :
    ∃ χ η : ℝ → ℝ,
      ContDiff ℝ (↑(⊤ : ℕ∞)) χ ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) η ∧
      HasCompactSupport χ ∧ HasCompactSupport η ∧
      tsupport χ⊆Icc l r ∧ tsupport η⊆Ioo a b ∧
      ∃ C : ℝ,0<C ∧ ∀ᶠ p in 𝓝 p₀,∀ m : Fin 3 → ℝ,
        ∃ c : Fin 3 → ℝ,(∀ i,‖c i‖≤C*‖m‖) ∧
          let f := fun q : ℝ×ℝ => (χ q.1*(c ⬝ᵥ wallMomentBasis σ lam q.1))*η q.2
          ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ HasCompactSupport f ∧
          tsupport f⊆Icc l r ×ˢ Ioo a b ∧
          (∀ i,(∫ q,f q*w p q i)=m i) := by
  obtain ⟨η,hη,hsη,hvη,hiη⟩ := exists_unit_global_interval_bump hab
  have hc := wallProjectedMoment_continuous hη.continuous hsη hw
  have he : wallProjectedMoment η w p₀=wallMomentBasis σ lam := by
    ext s i
    dsimp [wallProjectedMoment]
    simp_rw [hlim]
    rw [integral_mul_const,hiη,one_mul]
  obtain ⟨χ,hχ,hsχ,hvχ,C,hC,hne⟩ := wall_moment_uniform_inverse hlr hσ hlam hc he
  refine ⟨χ,η,hχ,hη,hsχ,hsη,hvχ,hvη,C,hC,?_⟩
  filter_upwards [hne] with p hp
  intro m
  obtain ⟨c,hc,hf,hsf,hvf,hif⟩ := hp m
  refine ⟨c,hc,((hf.comp contDiff_fst).mul (hη.comp contDiff_snd)),
    (surface_product_compact hsf hsη).1,
    (surface_product_compact hsf hsη).2.trans (prod_mono hvf hvη),?_⟩
  intro i
  rw [wallProjectedMoment_fubini (w := fun q => w p q i) hf.continuous hsf hη.continuous hsη
    ((hw i).comp (continuous_const.prodMk continuous_id))]
  exact hif i

end ScalarConductivity

end

end OAI
