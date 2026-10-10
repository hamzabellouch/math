import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialProduct
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ContinuousOneParameter
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LocalParameterSmoothness

namespace OAI

/-! # Automatic smoothness of continuous homomorphisms into algebra units

Products of one-parameter subgroups supply coordinates of the second kind.
The integral argument for continuous algebra-valued one-parameter groups
then proves smoothness in those coordinates.
-/

noncomputable section
namespace PolycyclicRecognition

open Function
open scoped Manifold ContDiff

variable {E G A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem contDiff_comp_exponentialProduct
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (ρ : G →* Aˣ) (hρ : Continuous (fun g => (ρ g : A)))
    {n : ℕ} (v : Fin n → E) :
    ContDiff ℝ ∞ (fun x => (ρ (exponentialProduct Exp v x) : A)) := by
  induction n with
  | zero =>
    simpa only [exponentialProduct, map_one, Units.val_one] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : Fin 0 → ℝ => (1 : A)))
  | succ n ih =>
    have hc : ContDiff ℝ ∞ (fun t : ℝ => (ρ (Exp (t • v 0)) : A)) := by
      apply contDiff_continuous_oneParameter
      · exact hρ.comp (hExp.contMDiff_curve (v 0)).continuous
      · rw [zero_smul]
        have hz : Exp (0 : E) = 1 := hExp.map_zero
        rw [hz, map_one, Units.val_one]
      · intro s t
        have heq : Exp ((s + t) • v 0) = Exp (s • v 0) * Exp (t • v 0) :=
          hExp.map_add_smul (v 0) s t
        rw [heq, map_mul, Units.val_mul]
    have hh := hc.comp (ContinuousLinearMap.proj (0 : Fin (n + 1)) :
      (Fin (n + 1) → ℝ) →L[ℝ] ℝ).contDiff
    have ht := (ih (v ∘ Fin.succ)).comp (coordinateTail n).contDiff
    have hp := hh.mul ht
    change ContDiff ℝ ∞ (fun x : Fin (n + 1) → ℝ =>
      (ρ (Exp (x 0 • v 0)) : A) *
        (ρ (exponentialProduct Exp (v ∘ Fin.succ) (x ∘ Fin.succ)) : A)) at hp
    simpa only [exponentialProduct, map_mul, Units.val_mul] using hp

theorem contMDiffAt_one_of_continuous_unitsHom [FiniteDimensional ℝ E]
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (ρ : G →* Aˣ) (hρ : Continuous (fun g => (ρ g : A))) :
    ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, A)) ∞ (fun g => (ρ g : A)) 1 := by
  let b := Module.finBasis ℝ E
  let d := b.equivFun.toContinuousLinearEquiv.symm
  have hcomb : tangentCombination b = d.toContinuousLinearMap := by
    ext x
    simp only [tangentCombination_apply]
    exact (b.equivFun_symm_apply x).symm
  have hd : HasMFDerivAt (𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ)) (𝓘(ℝ, E))
      (exponentialProduct Exp b) 0 d.toContinuousLinearMap := by
    apply (hExp.hasMFDerivAt_exponentialProduct_zero b).congr_mfderiv
    exact hcomb
  have hh := contMDiffAt_of_local_parameterization (f := fun g => (ρ g : A))
    (hExp.contMDiff_exponentialProduct b).contMDiffAt hd
    (contDiff_comp_exponentialProduct hExp ρ hρ b).contDiffAt
  simpa only [hExp.exponentialProduct_zero] using hh

theorem contMDiff_of_continuous_unitsHom [FiniteDimensional ℝ E]
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (ρ : G →* Aˣ) (hρ : Continuous (fun g => (ρ g : A))) :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, A)) ∞ (fun g => (ρ g : A)) := by
  have hbase := contMDiffAt_one_of_continuous_unitsHom hExp ρ hρ
  intro g
  have hl : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (fun x : G => g⁻¹ * x) g :=
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (a := g⁻¹) :
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (fun x : G => g⁻¹ * x)).contMDiffAt
  have hm := hbase.comp_of_eq hl (inv_mul_cancel g)
  have hh := (ContinuousLinearMap.mul ℝ A (ρ g : A)).contDiff.contMDiff.contMDiffAt.comp g hm
  have heq : (fun x => (ρ g : A) * (ρ (g⁻¹ * x) : A)) = fun x => (ρ x : A) := by
    funext x
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]
  change ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, A)) ∞
    (fun x => (ρ g : A) * (ρ (g⁻¹ * x) : A)) g at hh
  rwa [heq] at hh

end PolycyclicRecognition

end

end OAI
