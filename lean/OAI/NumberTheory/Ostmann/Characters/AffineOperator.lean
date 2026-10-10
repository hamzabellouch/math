import OAI.NumberTheory.Ostmann.Characters.AffineAction

namespace OAI

/-!
# The weighted affine averaging operator

This is the operator in equation `tree-affine-coefficient`, together with
its adjoint. Its adjoint square is the affine action whose coefficient
energy is bounded in `AffineCoefficients`.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

def affineGenerator {p : ℕ} (r : (ZMod p)ˣ) (t : ZMod p) : ZMod p :=
  (r : ZMod p) - (r : ZMod p) ^ 2 * t

def affineGeneratorInv {p : ℕ} [Fact p.Prime] (r : (ZMod p)ˣ) (t : ZMod p) : ZMod p :=
  ((r : ZMod p) - t) / (r : ZMod p) ^ 2

noncomputable def affineGeneratorEquiv {p : ℕ} [Fact p.Prime]
    (r : (ZMod p)ˣ) : ZMod p ≃ ZMod p where
  toFun := affineGenerator r
  invFun := affineGeneratorInv r
  left_inv t := by
    dsimp [affineGenerator, affineGeneratorInv]
    field_simp
    ring
  right_inv t := by
    dsimp [affineGenerator, affineGeneratorInv]
    field_simp
    ring

theorem affineGenerator_comp_inv {p : ℕ} [Fact p.Prime]
    (r s : (ZMod p)ˣ) (t : ZMod p) :
    affineGenerator s (affineGeneratorInv r t) =
      ((affineParameters r s).1 : ZMod p) * t + (affineParameters r s).2 := by
  rw [affineParameters_translation]
  simp only [affineGenerator, affineGeneratorInv, affineParameters,
    Units.val_pow_eq_pow_val, Units.val_div_eq_div_val]
  field_simp
  ring

/-- The paper uses this with weights `W r = conj (G r)`. -/
noncomputable def affineAverage {p : ℕ} [Fact p.Prime]
    (W : (ZMod p)ˣ → ℂ) (F : ZMod p → ℂ) (t : ZMod p) : ℂ :=
  (p : ℂ)⁻¹ * ∑ r : (ZMod p)ˣ, W r * F (affineGenerator r t)

noncomputable def affineAverageAdjoint {p : ℕ} [Fact p.Prime]
    (W : (ZMod p)ˣ → ℂ) (F : ZMod p → ℂ) (t : ZMod p) : ℂ :=
  (p : ℂ)⁻¹ * ∑ r : (ZMod p)ˣ, conj (W r) * F (affineGeneratorInv r t)

theorem affineGenerator_inner_reindex {p : ℕ} [Fact p.Prime]
    (r : (ZMod p)ˣ) (F H : ZMod p → ℂ) :
    (∑ t : ZMod p, conj (F (affineGenerator r t)) * H t) =
      ∑ t : ZMod p, conj (F t) * H (affineGeneratorInv r t) := by
  have h := ((affineGeneratorEquiv r).symm.bijective.sum_comp
    (fun t : ZMod p => conj (F (affineGenerator r t)) * H t)).symm
  have hinv (t : ZMod p) : affineGenerator r (affineGeneratorInv r t) = t :=
    (affineGeneratorEquiv r).apply_symm_apply t
  change (∑ t : ZMod p, conj (F (affineGenerator r t)) * H t) =
    ∑ t : ZMod p, conj (F (affineGenerator r (affineGeneratorInv r t))) *
      H (affineGeneratorInv r t) at h
  simpa only [hinv] using h

theorem affineAverage_adjoint_identity {p : ℕ} [Fact p.Prime]
    (W : (ZMod p)ˣ → ℂ) (F H : ZMod p → ℂ) :
    (∑ t : ZMod p, conj (affineAverage W F t) * H t) =
      ∑ t : ZMod p, conj (F t) * affineAverageAdjoint W H t := by
  simp only [affineAverage, affineAverageAdjoint, map_mul, map_inv₀, map_natCast,
    map_sum, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  calc
    _ = ∑ r : (ZMod p)ˣ, (p : ℂ)⁻¹ * conj (W r) *
        ∑ t : ZMod p, conj (F (affineGenerator r t)) * H t := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ r : (ZMod p)ˣ, (p : ℂ)⁻¹ * conj (W r) *
        ∑ t : ZMod p, conj (F t) * H (affineGeneratorInv r t) := by
      simp_rw [affineGenerator_inner_reindex]
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro r _
      ring

theorem affineCoefficientSum_action {p : ℕ} [Fact p.Prime]
    (W : (ZMod p)ˣ → ℂ) (F : ZMod p → ℂ) (t : ZMod p) :
    (∑ ab : (ZMod p)ˣ × ZMod p,
      affineCoefficientSum W ab * F ((ab.1 : ZMod p) * t + ab.2)) =
      ∑ r : (ZMod p)ˣ, ∑ s : (ZMod p)ˣ,
        conj (W r) * W s * F (affineGenerator s (affineGeneratorInv r t)) := by
  classical
  simp only [affineCoefficientSum, Finset.sum_mul, Finset.sum_filter, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Fintype.sum_prod_type]
  simp_rw [← affineGenerator_comp_inv]

/-- The adjoint square is the affine action with the collected coefficient array. -/
theorem affineAverage_adjoint_square {p : ℕ} [Fact p.Prime]
    (W : (ZMod p)ˣ → ℂ) (F : ZMod p → ℂ) :
    affineAverageAdjoint W (affineAverage W F) = affineAction (affineCoefficient W) F := by
  classical
  funext t
  calc
    _ = (p : ℂ)⁻¹ ^ 2 * ∑ r : (ZMod p)ˣ, ∑ s : (ZMod p)ˣ,
        conj (W r) * W s * F (affineGenerator s (affineGeneratorInv r t)) := by
      simp only [affineAverageAdjoint, affineAverage, Finset.mul_sum, pow_two]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = (p : ℂ)⁻¹ ^ 2 * ∑ ab : (ZMod p)ˣ × ZMod p,
        affineCoefficientSum W ab * F ((ab.1 : ZMod p) * t + ab.2) := by
      rw [affineCoefficientSum_action]
    _ = _ := by
      simp only [affineAction, affineCoefficient,
        Complex.ofReal_pow, Complex.ofReal_natCast, div_eq_mul_inv, inv_pow,
        Finset.mul_sum]
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring

/-- Squared form of the mean-zero operator bound from Section 6. -/
theorem affineAverage_energy_sq_bound {p : ℕ} [Fact p.Prime]
    (W : (ZMod p)ˣ → ℂ) (hW : (∑ r : (ZMod p)ˣ, ‖W r‖ ^ 2) ≤ (p : ℝ))
    (F : ZMod p → ℂ) (hF : additiveFourier F 0 = 0) :
    (∑ t : ZMod p, ‖affineAverage W F t‖ ^ 2) ^ 2 ≤
      (3 / (p : ℝ)) * (∑ t : ZMod p, ‖F t‖ ^ 2) ^ 2 := by
  have hid : (∑ t : ZMod p, conj (affineAverage W F t) * affineAverage W F t) =
      ∑ t : ZMod p, conj (F t) * affineAction (affineCoefficient W) F t := by
    simpa only [affineAverage_adjoint_square] using
      affineAverage_adjoint_identity W F (affineAverage W F)
  have hcs := complex_sum_mul_sq Finset.univ (fun t : ZMod p => conj (F t))
    (affineAction (affineCoefficient W) F)
  rw [← hid] at hcs
  simp only [Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_sum,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.norm_conj] at hcs
  have hnonneg : 0 ≤ ∑ t : ZMod p, ‖F t‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc
    _ ≤ (∑ t : ZMod p, ‖F t‖ ^ 2) *
        ∑ t : ZMod p, ‖affineAction (affineCoefficient W) F t‖ ^ 2 := hcs
    _ ≤ (∑ t : ZMod p, ‖F t‖ ^ 2) *
        ((3 / (p : ℝ)) * ∑ t : ZMod p, ‖F t‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (affineAction_collected_energy_bound W hW F hF) hnonneg
    _ = _ := by ring

theorem affineAverage_energy_bound {p : ℕ} [Fact p.Prime]
    (W : (ZMod p)ˣ → ℂ) (hW : (∑ r : (ZMod p)ˣ, ‖W r‖ ^ 2) ≤ (p : ℝ))
    (F : ZMod p → ℂ) (hF : additiveFourier F 0 = 0) :
    (∑ t : ZMod p, ‖affineAverage W F t‖ ^ 2) ≤
      Real.sqrt (3 / (p : ℝ)) * ∑ t : ZMod p, ‖F t‖ ^ 2 := by
  have hR : 0 ≤ 3 / (p : ℝ) := div_nonneg (by norm_num) (Nat.cast_nonneg p)
  have hE : 0 ≤ ∑ t : ZMod p, ‖F t‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) hE)).mp
  rw [mul_pow, Real.sq_sqrt hR]
  exact affineAverage_energy_sq_bound W hW F hF

end Ostmann

end OAI
