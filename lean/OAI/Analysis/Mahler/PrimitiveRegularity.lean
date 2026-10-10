import OAI.Analysis.Mahler.HomogeneousSmoothForms
import OAI.Analysis.Mahler.WedgeDecomposition

namespace OAI

open Complex ContinuousAlternatingMap
open scoped TensorProduct

noncomputable section
namespace Mahler
variable {E X J ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [Fintype J] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Continuous form for a fixed basis covector determinant. -/
def basisVolumeContinuous (b : Module.Basis J ℝ E) (q : ι → J) :
    E [⋀^ι]→L[ℝ] ℂ :=
  ((ContinuousMultilinearMap.mkPiAlgebra ℝ ι ℂ).compContinuousLinearMap
    (fun i => { complexCoord b (q i) with
      cont := (complexCoord b (q i)).continuous_of_finiteDimensional })).alternatization

omit [Fintype J] in
lemma basisVolumeContinuous_eq [Fintype J] (b : Module.Basis J ℝ E) (q : ι → J) :
    (basisVolumeContinuous b q).toAlternatingMap = covectorVolume (complexCoord b ∘ q) := by
  ext v
  simp [basisVolumeContinuous, covectorVolume,
    MultilinearMap.alternatization_apply]

/-- Bundle an actual finite-dimensional form using its exact normalized basis
expansion. Forgetting continuity returns the original form. -/
def bundleFiniteForm (b : Module.Basis J ℝ E) (a : E [⋀^ι]→ₗ[ℝ] ℂ) :
    E [⋀^ι]→L[ℝ] ℂ :=
  ∑ q : ι → J, (a (b ∘ q) / (Fintype.card ι).factorial) • basisVolumeContinuous b q

lemma bundleFiniteForm_eq (b : Module.Basis J ℝ E) (a : E [⋀^ι]→ₗ[ℝ] ℂ) :
    (bundleFiniteForm b a).toAlternatingMap = a := by
  classical
  conv_rhs => rw [alternating_basis_expansion_normalized b a]
  ext v
  simp only [bundleFiniteForm, ContinuousAlternatingMap.coe_toAlternatingMap,
    ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
    alternatingMap_sum_apply, AlternatingMap.smul_apply]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← basisVolumeContinuous_eq b q]
  rfl

lemma contDiffAt_bundleFiniteForm (b : Module.Basis J ℝ E)
    {a : X → E [⋀^ι]→ₗ[ℝ] ℂ} {x : X} (s : ℕ)
    (ha : ∀ v, ContDiffAt ℝ s (fun y => a y v) x) :
    ContDiffAt ℝ s (fun y => bundleFiniteForm b (a y)) x := by
  apply ContDiffAt.sum
  intro q hq
  exact ((ha _).div_const _).smul contDiffAt_const

omit [FiniteDimensional ℝ E] in
lemma contDiffAt_wedge_eval [FiniteDimensional ℝ E] {a : X → E [⋀^ι]→ₗ[ℝ] ℂ}
    {b : X → E [⋀^κ]→ₗ[ℝ] ℂ} {x : X} (s : ℕ)
    (ha : ∀ v, ContDiffAt ℝ s (fun y => a y v) x)
    (hb : ∀ v, ContDiffAt ℝ s (fun y => b y v) x) (v : ι ⊕ κ → E) :
    ContDiffAt ℝ s (fun y => wedge (a y) (b y) v) x := by
  have ht (σ : Equiv.Perm.ModSumCongr ι κ) :
      ContDiffAt ℝ s (fun y => (LinearMap.mul' ℝ ℂ)
        (AlternatingMap.domCoprod.summand (a y) (b y) σ v)) x := by
    induction σ using Quotient.inductionOn' with
    | h σ =>
      simp only [wedge_summand_eval]
      exact contDiffAt_const.mul ((ha _).mul (hb _))
  simpa only [wedge, LinearMap.compAlternatingMap_apply, AlternatingMap.domCoprod_apply,
    _root_.sum_apply, _root_.map_sum] using
    (ContDiffAt.sum (s := Finset.univ) (fun σ _ => ht σ))

lemma contDiffAt_wedgePower_eval {a : X → E [⋀^Fin 2]→ₗ[ℝ] ℂ}
    {x : X} (s : ℕ) (ha : ∀ v, ContDiffAt ℝ s (fun y => a y v) x)
    (k : ℕ) (v : WedgePowerSlots k → E) :
    ContDiffAt ℝ s (fun y => wedgePower (a y) k v) x := by
  induction k with
  | zero => exact contDiffAt_const
  | succ k ih => exact contDiffAt_wedge_eval s ha ih v

end Mahler

end

end OAI
