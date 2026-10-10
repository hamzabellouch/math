import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteTensorDiagonal
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedSpinOperator
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedCoercivity

namespace OAI

/-! Bounds on the actual finite tensor projection for the manufactured
potential, including its full weak-H1 orthogonal remainder. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem finiteTensorProjection_inner_remainder {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (ho : ∀ a b, (∑ t : Fin 2, ∫ y, star (v a y t)*v b y t) =
      if a=b then (1:ℂ) else 0) (u : Coulomb.H1Vector n) :
    inner ℂ (finiteTensorProjection v hv hL2 hpartial u).toHilbert
      (finiteTensorRemainder v hv hL2 hpartial u).toHilbert = 0 := by
  rw [finiteTensorProjection_toHilbert,sum_inner]
  simp only [inner_smul_left,finiteTensorRemainder_orthogonal v hv hL2 hpartial ho u,
    mul_zero,Finset.sum_const_zero]

theorem localizedSpinResidual_sum_bound {rho H S freq η D R : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hfreq : 0 < freq)
    (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S)
    (scale : ℝ) {m : ℕ} (u : Fin (m+1) → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : (m+1:ℕ)*localizedOverlapBound D ≤ 1/2) (hη : 0 ≤ η)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ η) :
    (∑ j, ∫ x, ‖Coulomb.flatSpinOrbital (localizedSpinResidual rho H S freq scale u j) x‖^2
      ∂Coulomb.spinSpaceMeasure) ≤
      8*(m+1:ℕ)^2*∑ j, manufacturedOrbitalSquaredError rho H S freq η D R u j := by
  rw [localizedSpinResidual_sum_norm hrho hH.le hS.le hfreq scale u hη hcoeff]
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    correctedManufacturedResidual_square_bound hrho hH hS hfreq hR hRH hRS
      scale u hsep hs hη hcoeff i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at he
  nlinarith only [he]

theorem manufacturedTensorProjection_mixed_square_bound
    (hdensity : PublishedSobolevSmoothDensity) {rho H S freq η D R : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hfreq : 0 < freq)
    (hrelation : freq^2 = 4*Real.pi*rho) (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S)
    (scale : ℝ) {m n : ℕ} (u : Fin (m+1) → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : (m+1:ℕ)*localizedOverlapBound D ≤ 1/2) (hη : 0 ≤ η)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ η)
    (B : ℝ) (hB : ∀ x : Configuration (n+1),
      |∑ i, manufacturedSlabPotential rho H S freq scale u (Coulomb.position x i)| ≤ B)
    (w : Coulomb.H1Vector (n+1)) :
    let p : Coulomb.H1Vector (n+1) := finiteTensorProjection (localizedSpinMode freq u) (localizedSpinMode_C1 freq u)
      (localizedSpinMode_memLp hfreq u) (localizedSpinMode_partial_memLp hfreq u) w
    let q : Coulomb.H1Vector (n+1) := w.add (Coulomb.H1Vector.scale (-1) p)
    let V : Configuration (n+1) → ℝ := fun x => ∑ i,
      manufacturedSlabPotential rho H S freq scale u (Coulomb.position x i)
    let hV : Continuous V := continuous_finsetSum _ (fun i _ =>
      (manufacturedSlabPotential_continuous hrho hH.le hS.le freq scale u).comp
        (Coulomb.positionCLM i).continuous)
    (graphBoundedCross (BoundedPotential.operator V hV B hB) (h1Coordinates p) (h1Coordinates q))^2 ≤
      (n+1:ℝ)^2*(8*(m+1:ℕ)^2*∑ j, manufacturedOrbitalSquaredError rho H S freq η D R u j)*
        Coulomb.mass p*Coulomb.mass q := by
  let v := localizedSpinMode freq u
  have hi := finiteTensorProjection_inner_remainder v (localizedSpinMode_C1 freq u)
    (localizedSpinMode_memLp hfreq u) (localizedSpinMode_partial_memLp hfreq u)
    (fun a b => by
      have h := localizedSpinMode_inner hfreq u hsep hs a b
      by_cases hab : a=b <;> simpa only [hab,ite_true,ite_false] using h) w
  have hc := finiteTensorState_mixed_square_bound hdensity v
    (localizedSpinResidual rho H S freq scale u) (localizedSpinMode_C1 freq u)
    (localizedSpinMode_C2 freq u) (localizedSpinMode_memLp hfreq u)
    (localizedSpinMode_partial_memLp hfreq u)
    (localizedSpinResidual_memLp hrho hH.le hS.le hfreq scale u hη hcoeff)
    (fun a b => by
      have h := localizedSpinMode_inner hfreq u hsep hs a b
      by_cases hab : a=b <;> simpa only [hab,ite_true,ite_false] using h)
    (manufacturedSlabPotential rho H S freq scale u)
    (manufacturedSlabPotential_continuous hrho hH.le hS.le freq scale u)
    ((-1/2:ℝ)+freq/2) B hB (fun a s x => by
      simpa only [Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_neg,
        Complex.ofReal_one,Complex.ofReal_ofNat] using
        localizedSpinResidual_operator hrelation H S scale u a s x)
    (Coulomb.orbitalCoefficient w v)
    (finiteTensorRemainder v (localizedSpinMode_C1 freq u)
      (localizedSpinMode_memLp hfreq u) (localizedSpinMode_partial_memLp hfreq u) w) hi
  apply hc.trans
  apply mul_le_mul_of_nonneg_right _ (Coulomb.mass_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (Coulomb.mass_nonneg _)
  exact mul_le_mul_of_nonneg_left
    (localizedSpinResidual_sum_bound hrho hH hS hfreq hR hRH hRS scale u hsep hs hη hcoeff)
    (sq_nonneg _)

end ContinuumCoulomb

end

end OAI
