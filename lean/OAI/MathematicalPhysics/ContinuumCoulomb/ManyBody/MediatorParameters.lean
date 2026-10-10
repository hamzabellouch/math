import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorRounding
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.DyadicRootProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.ChargePrograms

namespace OAI

/-! Explicit polynomial scales and rational positive spokes for one actual
simultaneous singlet-mediator stage. The norm hypothesis concerns the
unchanged low-block terms; no spectral conclusion is assumed. -/

namespace ContinuumCoulomb.MediatorParameters
open scoped BigOperators Kronecker InnerProductSpace

def scale (r W G : ℕ) : ℕ := 1048576 * (r + 1) ^ 3 * W ^ 3 * G
def delta (r W G : ℕ) : ℕ := scale r W G ^ 2
def precision (r G : ℕ) : ℕ := r + G + 20

noncomputable def epsilon (r W G : ℕ) : ℝ := 4 * (r + 1) * W / scale r W G

theorem scale_pos (r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G) : 0 < scale r W G := by
  unfold scale
  positivity

theorem scale_lower (r : ℕ) {W G : ℕ} (_hW : 0 < W) (hG : 0 < G) :
    16 * (r + 1) * W ≤ scale r W G := by
  have hrpow := Nat.le_self_pow (by decide : 3 ≠ 0) (r + 1)
  have hWpow := Nat.le_self_pow (by decide : 3 ≠ 0) W
  calc
    _ ≤ 1048576 * (r + 1) * W := by gcongr; norm_num
    _ ≤ 1048576 * (r + 1) ^ 3 * W ^ 3 * G := by
      calc
        _ ≤ 1048576 * (r + 1) ^ 3 * W ^ 3 := by gcongr
        _ ≤ _ := Nat.le_mul_of_pos_right _ hG
    _ = scale r W G := rfl

theorem epsilon_nonneg (r W G : ℕ) : 0 ≤ epsilon r W G := by unfold epsilon; positivity

theorem epsilon_small (r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G) :
    epsilon r W G ≤ 1 / 4 := by
  have hS : (0 : ℝ) < scale r W G := by exact_mod_cast scale_pos r hW hG
  have hl : 16 * ((r : ℝ) + 1) * W ≤ scale r W G := by exact_mod_cast scale_lower r hW hG
  unfold epsilon
  apply (div_le_iff₀ hS).mpr
  nlinarith

theorem second_order_error (r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G) :
    16 * (delta r W G : ℝ) * epsilon r W G ^ 3 = 1 / (1024 * (G : ℝ)) := by
  have hr : (r : ℝ) + 1 ≠ 0 := by positivity
  have hWr : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  have hGr : (G : ℝ) ≠ 0 := by exact_mod_cast hG.ne'
  unfold delta epsilon scale
  push_cast
  field_simp [hr, hWr, hGr]
  ring

theorem canonical_amplitude_upper (r : ℕ) {W G : ℕ} (hW : 0 < W) (_hG : 0 < G)
    {J : ℝ} (hJ : |J| ≤ W) :
    signedMediatorAmplitude (delta r W G : ℝ) J ≤ 2 * (scale r W G : ℝ) * W := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW2 : (W : ℝ) ≤ 2 * (W : ℝ) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left (hJ.trans hW2)
    (show 0 ≤ 2 * (scale r W G : ℝ) ^ 2 by positivity)
  unfold signedMediatorAmplitude
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  unfold delta
  push_cast
  nlinarith only [hmul]

theorem canonical_amplitude_lower (r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G)
    {J : ℝ} (hJ : 1 / (W : ℝ) ≤ |J|) :
    1 ≤ signedMediatorAmplitude (delta r W G : ℝ) J := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hSl : (W : ℝ) ≤ scale r W G := by
    have h := scale_lower r hW hG
    have : W ≤ scale r W G := by nlinarith
    exact_mod_cast this
  have hS1 : (1 : ℝ) ≤ scale r W G := by exact_mod_cast scale_pos r hW hG
  have hmul : 1 ≤ (W : ℝ) * |J| := by
    simpa only [mul_comm] using (div_le_iff₀ hWr).mp hJ
  have hSW : (W : ℝ) ≤ (scale r W G : ℝ) ^ 2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hSW (abs_nonneg J)
  unfold signedMediatorAmplitude
  apply Real.le_sqrt_of_sq_le
  unfold delta
  push_cast
  nlinarith

def radicand (r W G : ℕ) (J : ℚ) : ℚ := 2 * (delta r W G : ℚ) * |J|

def spoke (r W G : ℕ) (J : ℚ) : ℚ :=
  let q := radicand r W G J
  DyadicRootProgram.value (precision r G) q.num.toNat q.den

theorem rational_sqrt_error (b : ℕ) {q : ℚ} (hq : 0 ≤ q) :
    0 ≤ Real.sqrt (q : ℝ) - (DyadicRootProgram.value b q.num.toNat q.den : ℝ) ∧
      Real.sqrt (q : ℝ) - (DyadicRootProgram.value b q.num.toNat q.den : ℝ) < 1 / (2 : ℝ) ^ b := by
  have hnum : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)
  have hnumq : (q.num.toNat : ℚ) = (q.num : ℚ) := by exact_mod_cast hnum
  have hrepr : (q.num.toNat : ℚ) / q.den = q := by rw [hnumq, Rat.num_div_den]
  have hre : (q.num.toNat : ℝ) / q.den = (q : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_natCast] using congrArg (fun x : ℚ => (x : ℝ)) hrepr
  simpa only [hre] using DyadicRootProgram.value_error b q.num.toNat q.den q.pos

theorem spoke_error (r W G : ℕ) (J : ℚ) :
    0 ≤ signedMediatorAmplitude (delta r W G : ℝ) (J : ℝ) - (spoke r W G J : ℝ) ∧
      signedMediatorAmplitude (delta r W G : ℝ) (J : ℝ) - (spoke r W G J : ℝ) <
        1 / (2 : ℝ) ^ precision r G := by
  have h := rational_sqrt_error (precision r G)
    (show 0 ≤ radicand r W G J by unfold radicand; positivity)
  simpa only [spoke, radicand, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast,
    Rat.cast_abs, signedMediatorAmplitude] using h

theorem spoke_pos (r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G)
    {J : ℚ} (hJ : 1 / (W : ℝ) ≤ |(J : ℝ)|) : 0 < spoke r W G J := by
  have ha := canonical_amplitude_lower r hW hG hJ
  have he := (spoke_error r W G J).2
  have hp : 1 / (2 : ℝ) ^ precision r G ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact one_le_pow₀ (by norm_num)
  have : (0 : ℝ) < spoke r W G J := by linarith
  exact_mod_cast this

theorem precision_power (r G : ℕ) :
    1048576 * (r + 1) * (G + 1) ≤ 2 ^ precision r G := by
  have hlinear (n : ℕ) : n + 1 ≤ 2 ^ n := by
    induction n with
    | zero => norm_num
    | succ n ih => rw [pow_succ]; omega
  have hr : r + 1 ≤ 2 ^ r := hlinear r
  have hG : G + 1 ≤ 2 ^ G := hlinear G
  unfold precision
  rw [pow_add, pow_add]
  norm_num
  nlinarith [Nat.mul_le_mul hr hG]

theorem rounding_error (r : ℕ) {G : ℕ} (hG : 0 < G) :
    6 * r * (1 / (2 : ℝ) ^ precision r G) ≤ 1 / (1024 * (G : ℝ)) := by
  have hp : 1048576 * ((r : ℝ) + 1) * ((G : ℝ) + 1) ≤ (2 : ℝ) ^ precision r G := by
    exact_mod_cast precision_power r G
  have hGr : (0 : ℝ) < G := by exact_mod_cast hG
  rw [mul_one_div]
  apply (le_div_iff₀ (by positivity : 0 < 1024 * (G : ℝ))).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ precision r G)).mpr
  have hrG : 0 ≤ (r : ℝ) * G := by positivity
  nlinarith [show 0 ≤ (r : ℝ) by positivity]

noncomputable section

/-- Explicit parameters discharge the small-perturbation hypotheses of the
actual simultaneous-mediator theorem, retaining arbitrary unchanged C. -/
theorem canonical_bottom (n r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (left right : Fin r → Fin n) (hneq : ∀ e, left e ≠ right e)
    (J : Fin r → ℚ) (hJ : ∀ e, |(J e : ℝ)| ≤ W)
    (hNorm : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤ W) :
    |mediatorFullBottom n r (physicalRawMediatorHamiltonian n r (delta r W G) C left right
        (fun e => signedMediatorMember (J e))
        (fun e => signedMediatorAmplitude (delta r W G) (J e))) +
      3 * r * delta r W G + 3 * ∑ e, |(J e : ℝ)| -
        sourceMatrixBottom n (C + ∑ e, (J e : ℂ) • sourceHeisenbergMatrix n (left e) (right e))| ≤
          1 / (1024 * (G : ℝ)) := by
  have hS : (1 : ℝ) ≤ scale r W G := by exact_mod_cast scale_pos r hW hG
  have hSp : (0 : ℝ) < scale r W G := by exact_mod_cast scale_pos r hW hG
  have hDelta : (0 : ℝ) < delta r W G := by
    unfold delta
    rw [Nat.cast_pow]
    exact pow_pos hSp 2
  have hamp : (∑ e : Fin r, signedMediatorAmplitude (delta r W G) (J e)) ≤
      r * (2 * (scale r W G : ℝ) * W) := by
    calc
      _ ≤ ∑ _e : Fin r, 2 * (scale r W G : ℝ) * W :=
        Finset.sum_le_sum (fun e _ => canonical_amplitude_upper r hW hG (hJ e))
      _ = _ := by simp
  have heq : epsilon r W G * (4 * (delta r W G : ℝ)) =
      16 * ((r : ℝ) + 1) * scale r W G * W := by
    unfold epsilon delta
    push_cast
    field_simp [hSp.ne']
    ring
  have hbound : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      6 * ∑ e, signedMediatorAmplitude (delta r W G) (J e) ≤
        epsilon r W G * (4 * (delta r W G : ℝ)) := by
    rw [heq]
    have hSW : (W : ℝ) ≤ (scale r W G : ℝ) * W := by
      nlinarith [show 0 ≤ (W : ℝ) by positivity]
    have hExtra : 0 ≤ 4 * (r : ℝ) * scale r W G * W := by positivity
    nlinarith only [hNorm, hamp, hSW, hExtra]
  have h := physicalCanonicalMediator_bottom n r hDelta C hC left right hneq
    (fun e => (J e : ℝ)) (epsilon_nonneg r W G) (epsilon_small r hW hG) hbound
  exact h.trans_eq (second_order_error r hW hG)

/-- A concrete positive rational-spoke stage, with a full-spin spectral
error bound including the arithmetic approximation of every spoke. -/
theorem rational_bottom (n r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (left right : Fin r → Fin n) (hneq : ∀ e, left e ≠ right e)
    (J : Fin r → ℚ) (hJ : ∀ e, |(J e : ℝ)| ≤ W)
    (hJlower : ∀ e, 1 / (W : ℝ) ≤ |(J e : ℝ)|)
    (hNorm : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤ W) :
    (∀ e, 0 < spoke r W G (J e)) ∧
    |mediatorFullBottom n r (physicalRawMediatorHamiltonian n r (delta r W G) C left right
        (fun e => signedMediatorMember (J e)) (fun e => (spoke r W G (J e) : ℝ))) +
      3 * r * delta r W G + 3 * ∑ e, |(J e : ℝ)| -
        sourceMatrixBottom n (C + ∑ e, (J e : ℂ) • sourceHeisenbergMatrix n (left e) (right e))| ≤
          1 / (512 * (G : ℝ)) := by
  refine ⟨fun e => spoke_pos r hW hG (hJlower e), ?_⟩
  have hcanonical := canonical_bottom n r hW hG C hC left right hneq J hJ hNorm
  have hsum : (∑ e, |(spoke r W G (J e) : ℝ) -
      signedMediatorAmplitude (delta r W G) (J e)|) ≤ r * (1 / (2 : ℝ) ^ precision r G) := by
    calc
      _ ≤ ∑ _e : Fin r, 1 / (2 : ℝ) ^ precision r G := by
        apply Finset.sum_le_sum
        intro e _
        rw [abs_sub_comm, abs_of_nonneg (spoke_error r W G (J e)).1]
        exact (spoke_error r W G (J e)).2.le
      _ = _ := by simp
  have hround := (physicalRawMediator_bottom_rounding n r (delta r W G) C left right
    (fun e => signedMediatorMember (J e)) (fun e => (spoke r W G (J e) : ℝ))
    (fun e => signedMediatorAmplitude (delta r W G) (J e))).trans
      (mul_le_mul_of_nonneg_left hsum (by norm_num))
  have hround' : _ ≤ 1 / (1024 * (G : ℝ)) := hround.trans (by
    convert rounding_error r hG using 1
    ring)
  have htriangle := abs_add_le
    (mediatorFullBottom n r (physicalRawMediatorHamiltonian n r (delta r W G) C left right
      (fun e => signedMediatorMember (J e)) (fun e => (spoke r W G (J e) : ℝ))) -
      mediatorFullBottom n r (physicalRawMediatorHamiltonian n r (delta r W G) C left right
        (fun e => signedMediatorMember (J e))
        (fun e => signedMediatorAmplitude (delta r W G) (J e))))
    (mediatorFullBottom n r (physicalRawMediatorHamiltonian n r (delta r W G) C left right
      (fun e => signedMediatorMember (J e))
      (fun e => signedMediatorAmplitude (delta r W G) (J e))) +
      3 * r * delta r W G + 3 * ∑ e, |(J e : ℝ)| -
      sourceMatrixBottom n (C + ∑ e, (J e : ℂ) • sourceHeisenbergMatrix n (left e) (right e)))
  have hnormalize : (1 / (1024 * (G : ℝ))) + 1 / (1024 * (G : ℝ)) = 1 / (512 * (G : ℝ)) := by ring
  convert htriangle.trans (add_le_add hround' hcanonical) using 1
  · congr 1
    ring
  · exact hnormalize.symm

end
end ContinuumCoulomb.MediatorParameters

end OAI
