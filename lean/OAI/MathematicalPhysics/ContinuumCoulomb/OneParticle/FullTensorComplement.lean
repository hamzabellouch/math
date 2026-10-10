import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.FullSpinTensorCoefficients
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteOrbitalComplement

namespace OAI

/-! The actual antisymmetric H1 remainder has a missing orbital occupation
on the full spin-space product measure. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical ENNReal
namespace ContinuumCoulomb

theorem finiteTensorRemainder_flat_occupation {m n : ℕ}
    (v : Fin m → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (ho : ∀ a b, (∑ t : Fin 2, ∫ y, star (v a y t)*v b y t) =
      if a=b then (1:ℂ) else 0) (u : Coulomb.H1Vector (n+1)) (hu : Coulomb.Antisymmetric u) :
    let q := finiteTensorRemainder v hv hL2 hpartial u
    (n+1:ℕ)*(∑ a, ∫ y, ‖Coulomb.fiberContract (μ := Coulomb.spinSpaceMeasure)
      (Coulomb.flatSpinOrbital (v a)) (Coulomb.firstFiber (Coulomb.cubeState q)) y‖^2
      ∂(Measure.pi fun _ : Fin n => Coulomb.spinSpaceMeasure)) ≤ (n:ℝ)*Coulomb.mass q := by
  let : Fact ((2:ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let q := finiteTensorRemainder v hv hL2 hpartial u
  have hflat (a b : Fin m) :
      (∫ x, star (Coulomb.flatSpinOrbital (v a) x)*Coulomb.flatSpinOrbital (v b) x
        ∂Coulomb.spinSpaceMeasure) = if a=b then (1:ℂ) else 0 := by
    rw [Coulomb.flatSpinOrbital_inner _ _ (hL2 a) (hL2 b)]
    exact ho a b
  have hz (b : Fin (n+1) → Fin m) :
      Coulomb.scalarCoefficient (μ := Coulomb.spinSpaceMeasure) (Coulomb.cubeState q)
        (fun a => Coulomb.flatSpinOrbital (v a)) b = 0 := by
    rw [fullSpin_scalarCoefficient q v hL2 b,Coulomb.orbitalCoefficient_eq_inner q v hL2 b]
    exact finiteTensorRemainder_orthogonal v hv hL2 hpartial (by
      intro i j
      by_cases hij : i=j <;> simpa only [hij,ite_true,ite_false] using ho i j) u b
  have h := finite_orbital_complement_bound (fun a => Coulomb.flatSpinOrbital (v a))
    (fun a => Coulomb.flatSpinOrbital_memLp (v a) (hL2 a)) hflat (Coulomb.cubeState q)
    q.cubeState_full_memLp (fullSpin_antisymmetric q (finiteTensorRemainder_antisymmetric v hv hL2 hpartial u hu)) hz
  simpa only [Coulomb.cubeState_full_mass] using h

end ContinuumCoulomb

end

end OAI
