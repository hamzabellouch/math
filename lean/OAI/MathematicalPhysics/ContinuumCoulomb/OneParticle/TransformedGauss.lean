import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.MoserCoordinateProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.GaussNodeProgram

namespace OAI

/-! Actual rational transport of Gauss nodes. A common polynomial precision
absorbs both the initial square-root error and the numerical flow error. -/

noncomputable section
open scoped NNReal
namespace ContinuumCoulomb.TransformedGauss
open CappedKernelProgram (Triple position)
open EulerRegisters (Registers)
open RationalGaussNodes (Signs)

def precision (K P : ℕ) : ℕ := 2*(K+1)*(P+1)

def value (rho U C K P N : ℕ) (scale S : ℚ) (sites : List (ℚ×ℚ))
    (k : Registers) (b : Signs) : Triple :=
  let T := precision K P
  ManufacturedEuler.approximate rho U C T scale S sites (RationalGaussNodes.value T N k b)

theorem error_budget (K P : ℕ) :
    (1+(K:ℝ))*((precision K P:ℝ)+1)⁻¹ ≤ ((P:ℝ)+1)⁻¹ := by
  have hP : 0 < (P:ℝ)+1 := by positivity
  have hK : 0 < (K:ℝ)+1 := by positivity
  have hT : (precision K P:ℝ) = 2*((K:ℝ)+1)*((P:ℝ)+1) := by
    simp only [precision,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
  apply (mul_inv_le_iff₀ (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one)).mpr
  rw [hT]
  have he : ((P:ℝ)+1)⁻¹*(2*((K:ℝ)+1)*((P:ℝ)+1)+1) =
      2*((K:ℝ)+1)+((P:ℝ)+1)⁻¹ := by field_simp
  rw [he]
  linarith [inv_nonneg.mpr hP.le]

/-- This is an error-composition lemma. Its numerical-flow premise is
supplied below by the proved actual manufactured Euler construction. -/
theorem error_of_endpoint_error (rho U C K P : ℕ) {N : ℕ} (hN : 0 < N)
    (scale S : ℚ) (sites : List (ℚ×ℚ)) (k : Registers) (b : Signs)
    (G : Position → Position) {L : ℝ≥0} (hG : LipschitzWith L G) (hL : (L:ℝ) ≤ K)
    (hendpoint : ∀ q : Triple,
      ‖position (ManufacturedEuler.approximate rho U C (precision K P) scale S sites q)-G (position q)‖ ≤
        ((precision K P:ℝ)+1)⁻¹) :
    ‖position (value rho U C K P N scale S sites k b)-
      G (gaussLatticePoint (N:ℝ)⁻¹ (RationalGaussNodes.index k b))‖ ≤ ((P:ℝ)+1)⁻¹ := by
  have he := RationalGaussNodes.transported_error G hG (precision K P) hN k b
    (ManufacturedEuler.approximate rho U C (precision K P) scale S sites
      (RationalGaussNodes.value (precision K P) N k b))
    (hendpoint (RationalGaussNodes.value (precision K P) N k b))
  apply he.trans
  have hm := mul_le_mul_of_nonneg_right hL
    (inv_nonneg.mpr (add_nonneg (Nat.cast_nonneg (precision K P)) zero_le_one))
  calc
    _ ≤ ((precision K P:ℝ)+1)⁻¹+(K:ℝ)*((precision K P:ℝ)+1)⁻¹ := add_le_add le_rfl hm
    _ = (1+(K:ℝ))*((precision K P:ℝ)+1)⁻¹ := by ring
    _ ≤ _ := error_budget K P

/-- The transformed-node approximation is uniform over all manufactured
fields and all their actual time-one maps. U and C are fixed beforehand. -/
theorem exists_uniform_constants (rho : ℕ) (hrho : 0 < rho) :
    ∃ U C : ℕ, 0 < U ∧ 0 < C ∧ ∀ (K P N : ℕ), 0 < N → ∀ (scale S : ℚ),
      (1:ℝ) ≤ scale → (1:ℝ) ≤ S → ∀ (m : ℕ) (u : Fin m → ℚ×ℚ),
      Function.Injective u →
      (∀ i j, i ≠ j → 3 ≤ ‖PlanarForcingProgram.position (u i)-PlanarForcingProgram.position (u j)‖) →
      (∀ i, localizedCounterterm (GaussianFrequency.frequency rho)
        (fun j => PlanarForcingProgram.position (u j)) i ≤ scale) →
      (∀ x, |manufacturedCharge (manufacturedWellField (GaussianFrequency.frequency rho)
        scale S (fun i => PlanarForcingProgram.position (u i))) x| ≤ (rho:ℝ)/2) →
      ∀ G : Position → ℝ → Position,
      IsUnitTimeFlow (moserVelocity (rho:ℝ) (manufacturedWellField (GaussianFrequency.frequency rho)
        scale S (fun i => PlanarForcingProgram.position (u i)))) G →
      ∀ L : ℝ≥0, LipschitzWith L (fun x => G x 1) → (L:ℝ) ≤ K →
      ∀ (k : Registers) (b : Signs),
        ‖position (value rho U C K P N scale S (List.ofFn u) k b)-
          G (gaussLatticePoint (N:ℝ)⁻¹ (RationalGaussNodes.index k b)) 1‖ ≤ ((P:ℝ)+1)⁻¹ := by
  obtain ⟨U,C,hU,hC,herror⟩ := ManufacturedEuler.exists_uniform_constants rho hrho
  refine ⟨U,C,hU,hC,?_⟩
  intro K P N hN scale S hs hS m u hu hsep hc hcharge G hG L hLip hL k b
  exact error_of_endpoint_error rho U C K P hN scale S (List.ofFn u) k b
    (fun x => G x 1) hLip hL
    (herror (precision K P) scale S hs hS m u hu hsep hc hcharge G hG)

end ContinuumCoulomb.TransformedGauss

end

end OAI
