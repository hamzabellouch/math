import OAI.Analysis.CircleDomains.Topology.BoundedCompactCutoff
import OAI.Analysis.CircleDomains.Sobolev.BoundedSobolevChain

namespace OAI

/-! Smooth value cutoffs and spatial cutoffs of an actual compact
Sobolev function, retaining the exact product/chain-rule gradient. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

def smoothScalarCutoffWitness {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (hsu : HasCompactSupport u)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hFu : ∀ t, F t ∈ Icc 0 1)
    {C : ℝ} (hC : ∀ t, ‖deriv F t‖ ≤ C)
    {η : EuclideanPlane → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hsη : HasCompactSupport η) :
    DeGiorgi.MemW1pWitness 2 (fun x => η x * F (u x)) univ := by
  let B := Classical.choose (hu.bounded_above_of_compact_support hsu)
  have hB := Classical.choose_spec (hu.bounded_above_of_compact_support hsu)
  have hub (x : EuclideanPlane) : u x ∈ Icc (-B) B := by
    exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hB x)
  let G : EuclideanPlane → EuclideanPlane := fun x =>
    WithLp.toLp 2 (fun i => deriv F (u x) * W.weakGrad x i)
  have hG (i : Fin 2) : MemLp (fun x => G x i) 2 volume := by
    change MemLp (fun x => deriv F (u x) * W.weakGrad x i) 2 volume
    apply (show MemLp (fun x => W.weakGrad x i) 2 volume by
      simpa only [Measure.restrict_univ] using W.weakGrad_component_memLp i).of_le_mul
      (c := C)
      (((hF.continuous_deriv le_rfl).comp hu).aestronglyMeasurable.mul
        (by simpa only [Measure.restrict_univ] using
          (W.weakGrad_component_memLp i).aestronglyMeasurable))
    exact Eventually.of_forall fun x => by
      simp only [Pi.mul_apply, Function.comp_apply]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC (u x)) (norm_nonneg _)
  have hwG : DeGiorgi.HasWeakGrad G (F ∘ u) univ := by
    intro i
    exact bounded_sobolev_chain_rule_Icc W hsu hub hF i
  exact boundedCompactCutoffWitness (hF.continuous.comp hu).aestronglyMeasurable
    (fun x => hFu (u x)) hG hwG hη hsη

lemma smoothScalarCutoffWitness_gradient {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (hsu : HasCompactSupport u)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hFu : ∀ t, F t ∈ Icc 0 1)
    {C : ℝ} (hC : ∀ t, ‖deriv F t‖ ≤ C)
    {η : EuclideanPlane → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hsη : HasCompactSupport η) (x : EuclideanPlane) (i : Fin 2) :
    (smoothScalarCutoffWitness hu W hsu hF hFu hC hη hsη).weakGrad x i =
      η x * (deriv F (u x) * W.weakGrad x i) +
        fderiv ℝ η x (EuclideanSpace.single i 1) * F (u x) := rfl

end CircleDomainRigidity

end

end OAI
