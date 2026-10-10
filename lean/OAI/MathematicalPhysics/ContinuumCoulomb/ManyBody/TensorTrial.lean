import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockEnergyError
import OAI.Analysis.Laughlin.Tensor.Antisymmetry

namespace OAI

/-! Antisymmetric coefficient arrays synthesize actual admissible continuum
trial states. Their positive occupation mass is preserved exactly. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb
open Laughlin.Fock

theorem finiteTensorState_antisymmetric {n Q : ℕ}
    (v : Fin (Q+1) → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (c : Laughlin.State n Q) (hc : Laughlin.Antisymmetric c) :
    Coulomb.Antisymmetric (finiteTensorState v hv hL2 hpartial c) := by
  intro p s
  filter_upwards [] with x
  change (∑ b, c b*Coulomb.tensorOrbital v b (s ∘ p) (Coulomb.permute p x)) =
    (((p.sign : ℤ):ℂ))*(∑ b, c b*Coulomb.tensorOrbital v b s x)
  let e : (Fin n → Fin (Q+1)) ≃ (Fin n → Fin (Q+1)) :=
    Equiv.arrowCongr p (Equiv.refl _)
  have he (b : Fin n → Fin (Q+1)) : e.symm b=b ∘ p := rfl
  have hperm (b : Fin n → Fin (Q+1)) : c (b ∘ p)=(((p.sign:ℤ):ℂ))*c b := by
    simpa only [Units.smul_def,zsmul_eq_mul] using Laughlin.antisymmetric_perm hc p b
  rw [← e.symm.sum_comp]
  simp only [he,hperm,Coulomb.tensorOrbital_permute,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem finiteTensorState_mass_eq_fockMass {n Q : ℕ}
    (v : Fin (Q+1) → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x, star (v a x s)*v b x s) = if a=b then (1:ℂ) else 0)
    (c : Laughlin.State n Q) (hc : Laughlin.Antisymmetric c) :
    Coulomb.mass (finiteTensorState v hv hL2 hpartial c) =
      HubbardGlobal.fockMass (normalizedTensorExterior n Q c) := by
  rw [finiteTensorState_occupationMass v hv hL2 hpartial ho c hc,
    occupationNormSq_fockCoordinates,HubbardGlobal.fockCoordinates_norm_sq]

end ContinuumCoulomb

end

end OAI
