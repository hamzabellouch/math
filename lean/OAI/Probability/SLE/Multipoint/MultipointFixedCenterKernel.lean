import OAI.Probability.SLE.Multipoint.MultipointKernelExpansion
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI

/-! The fixed-center form of the capped kernel estimate. The constant
is independent of the location of the fixed center. -/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace SLEExactGauge.Multipoint

def fixedKernelBound (ι : Type*) [Fintype ι] [DecidableEq ι] (α b : ℝ) (C : ℝ≥0∞) : ℝ≥0∞ :=
  ∑ _f : ι → Option ι, capCoefficient α b ^ Fintype.card ι * C^(Fintype.card ι-1)

lemma fixedKernelBound_lt_top (ι : Type*) [Fintype ι] [DecidableEq ι] (α b : ℝ)
    (C : ℝ≥0∞) (hC : C < ⊤) : fixedKernelBound ι α b C < ⊤ := by
  apply ENNReal.sum_lt_top.mpr
  intro f _
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top (capCoefficient_finite α b))
    (ENNReal.pow_lt_top hC)

lemma cappedDistanceKernel_marginal_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α b : ℝ) (K : Set ℂ) (C : ℝ≥0∞) (hC : C < ⊤)
    (hC0 : volume K ≤ C)
    (hC1 : ∀ y, (∫⁻ x in K, distanceKernel α x y) ≤ C)
    (hC2 : ∀ y z, (∫⁻ x in K, distanceKernel α x y * distanceKernel α x z) ≤ C)
    (root : ι) (x : ι → ℂ) :
    lmarginal (fun _ : ι => volume.restrict K) (Finset.univ.erase root)
      (cappedDistanceKernel α b) x ≤ fixedKernelBound ι α b C := by
  let S : Finset ι := Finset.univ.erase root
  have hg (f : ι → Option ι) :
      lmarginal (fun _ : ι => volume.restrict K) S (graphKernel α (selectedEdges f)) x ≤ C^S.card := by
    apply graphKernel_marginal_le_with_root α K C hC hC0 hC1 hC2 root S (selectedEdges f)
    · exact Finset.notMem_erase _ _
    · intro e _
      constructor <;> simp only [S,Finset.insert_erase (Finset.mem_univ root),Finset.mem_univ]
    · exact selectedEdges_outgoing f
    · exact selectedEdges_loopfree f
  change lmarginal (fun _ : ι => volume.restrict K) S (cappedDistanceKernel α b) x ≤ _
  calc
    _ ≤ lmarginal (fun _ : ι => volume.restrict K) S
        (fun y => ∑ f : ι → Option ι,
          capCoefficient α b ^ Fintype.card ι * graphKernel α (selectedEdges f) y) x :=
      lmarginal_mono (cappedDistanceKernel_le_graph_sum α b) x
    _ = ∑ f : ι → Option ι, capCoefficient α b ^ Fintype.card ι *
        lmarginal (fun _ : ι => volume.restrict K) S (graphKernel α (selectedEdges f)) x := by
      unfold lmarginal
      rw [lintegral_finsetSum]
      · apply Finset.sum_congr rfl
        intro f _
        exact lintegral_const_mul' _ _ (ENNReal.pow_ne_top (capCoefficient_finite α b).ne)
      · intro f _
        exact measurable_const.mul ((measurable_graphKernel α (selectedEdges f)).comp
          measurable_updateFinset)
    _ ≤ ∑ _f : ι → Option ι, capCoefficient α b ^ Fintype.card ι * C^S.card := by
      apply Finset.sum_le_sum
      intro f _
      have hh := hg f
      gcongr
    _ = fixedKernelBound ι α b C := by
      simp only [S,Finset.card_erase_of_mem (Finset.mem_univ root),Finset.card_univ,fixedKernelBound]

lemma lintegral_fin_cons_eq_marginal (m : ℕ) (K : Set ℂ)
    (f : (Fin (m+1) → ℂ) → ℝ≥0∞) (hf : Measurable f) (z : ℂ) :
    (∫⁻ x, f (Fin.cons z x) ∂Measure.pi (fun _ : Fin m => volume.restrict K)) =
      lmarginal (fun _ : Fin (m+1) => volume.restrict K) (Finset.univ.erase 0)
        f (Fin.cons z (fun _ => 0)) := by
  let g : (Fin m → ℂ) → ℝ≥0∞ := fun x => f (Fin.cons z x)
  have hg : Measurable g := by
    apply hf.comp
    apply measurable_pi_iff.mpr
    intro i
    cases i using Fin.cases <;> simp only [Fin.cons_zero,Fin.cons_succ]
    · exact measurable_const
    · exact measurable_pi_apply _
  have hcomp : (fun y : Fin (m+1) → ℂ => f (Function.update y 0 z)) =
      g ∘ (fun y : Fin (m+1) → ℂ => y ∘ Fin.succ) := by
    funext y
    apply congrArg f
    ext i
    cases i using Fin.cases <;> simp [Function.comp_def]
  have hset : (Finset.univ : Finset (Fin m)).image Fin.succ = Finset.univ.erase 0 := by
    rw [Fin.image_succ_univ]
    ext i
    simp
  calc
    _ = lmarginal (fun _ : Fin m => volume.restrict K) Finset.univ g (fun _ => 0) := by
      simp only [lmarginal_univ,g]
    _ = lmarginal (fun _ : Fin (m+1) => volume.restrict K) (Finset.univ.image Fin.succ)
        (g ∘ (fun y => y ∘ Fin.succ)) (Fin.cons z (fun _ => 0)) := by
      exact (lmarginal_image (μ := fun _ : Fin (m+1) => volume.restrict K)
        (Fin.succ_injective m) Finset.univ hg (Fin.cons z (fun _ => 0))).symm
    _ = lmarginal (fun _ : Fin (m+1) => volume.restrict K) (Finset.univ.erase 0)
        (fun y => f (Function.update y 0 z)) (Fin.cons z (fun _ => 0)) := by rw [hset,hcomp]
    _ = _ := by
      simpa only [Fin.update_cons_zero,Function.comp_def] using
        (lmarginal_update_of_notMem (μ := fun _ : Fin (m+1) => volume.restrict K) hf
          (Finset.notMem_erase 0 Finset.univ) (Fin.cons z (fun _ => 0)) z).symm

/-- Uniform fixed-center kernel bound, with the center in coordinate zero
and the free variables in the successor coordinates. -/
theorem cappedDistanceKernel_fixed_center_bound (m : ℕ)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (b : ℝ)
    (K : Set ℂ) (hK : Bornology.IsBounded K) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z : ℂ,
      (∫⁻ x, cappedDistanceKernel α b (Fin.cons z x)
        ∂Measure.pi (fun _ : Fin m => volume.restrict K)) ≤ C := by
  obtain ⟨C,hC,_,hC0,hC1,hC2⟩ := distanceKernel_uniform_local_bounds hα hα1 K hK
  refine ⟨fixedKernelBound (Fin (m+1)) α b C,
    fixedKernelBound_lt_top _ α b C hC,fun z => ?_⟩
  rw [lintegral_fin_cons_eq_marginal m K _ (measurable_cappedDistanceKernel α b)]
  exact cappedDistanceKernel_marginal_le α b K C hC hC0 hC1 hC2 0 _

lemma ae_fin_cons_injective (m : ℕ) (K : Set ℂ) (z : ℂ) :
    ∀ᵐ x : Fin m → ℂ ∂Measure.pi (fun _ : Fin m => volume.restrict K),
      Function.Injective (Fin.cons z x) := by
  filter_upwards [ae_tuple_injective K,ae_tuple_avoids K z] with x hx hz
  apply Fin.cons_injective_of_injective _ hx
  rintro ⟨i,hi⟩
  exact hz i hi

end SLEExactGauge.Multipoint

end

end OAI
