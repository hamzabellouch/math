import OAI.Analysis.Cotype.FiniteL2Dual
import OAI.Analysis.Cotype.Damping

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem average_const_smul {α : Type*} [Fintype α] (c : ℝ) (f : α → X) :
    average (fun a => c • f a) = c • average f := by
  simp only [average, Finset.smul_sum, smul_smul]
  simp only [mul_comm]

def cubeTranslate {n : ℕ} (a : Cube n) : Cube n ≃ Cube n where
  toFun u := xorCube a u
  invFun u := xorCube a u
  left_inv u := by ext i; simp [xorCube]
  right_inv u := by ext i; simp [xorCube]

theorem average_translate {n : ℕ} (a : Cube n) (f : Cube n → X) :
    average (fun u => f (xorCube a u)) = average f := average_equiv (cubeTranslate a) f

omit [NormedSpace ℝ X] in
theorem cubeL2_translate {n : ℕ} (a : Cube n) (f : Cube n → X) :
    cubeL2 X (fun u => f (xorCube a u)) = cubeL2 X f := by
  exact congrArg Real.sqrt (average_translate a (fun u => ‖f u‖ ^ 2))

theorem character_xor_left {n : ℕ} (a b c : Cube n) :
    character (xorCube a b) c = character a c * character b c := by
  rw [character_symm, character_xor]
  rw [character_symm c a, character_symm c b]

theorem character_pairing_twist {n : ℕ} (u v a b : Cube n) :
    character u b * character a b * character a v =
      character v u * character (xorCube v b) (xorCube u a) := by
  rw [character_xor_left, character_xor, character_xor]
  rw [character_symm v a, character_symm b u, character_symm b a]
  calc
    _ = (character v u * character v u) *
        (character u b * character a b * character a v) := by rw [character_sq, one_mul]
    _ = _ := by ring

def twistedPrimal {n : ℕ} (p : Cube n → X) (u : Cube n) (z : Cube (n+n)) : X :=
  let ab := (cubeJoin n n).symm z
  (character u ab.2 * character ab.1 ab.2) • p (xorCube u ab.1)

def twistedDual {n : ℕ} (q : Cube n → (Y →L[ℝ] ℝ)) (v : Cube n)
    (z : Cube (n+n)) : Y →L[ℝ] ℝ :=
  let ab := (cubeJoin n n).symm z
  character ab.1 v • q (xorCube v ab.2)

@[simp] theorem twistedPrimal_join {n : ℕ} (p : Cube n → X) (u a b : Cube n) :
    twistedPrimal p u (cubeJoin n n (a,b)) =
      (character u b * character a b) • p (xorCube u a) := by
  simp only [twistedPrimal, Equiv.symm_apply_apply]

@[simp] theorem twistedDual_join {n : ℕ} (q : Cube n → (Y →L[ℝ] ℝ)) (v a b : Cube n) :
    twistedDual q v (cubeJoin n n (a,b)) = character a v • q (xorCube v b) := by
  simp only [twistedDual, Equiv.symm_apply_apply]

theorem twistedPrimal_L2 {n : ℕ} (p : Cube n → X) (u : Cube n) :
    cubeL2 X (twistedPrimal p u) = cubeL2 X p := by
  rw [cubeL2_join]
  have hn (a b : Cube n) : ‖twistedPrimal p u (cubeJoin n n (a,b))‖ = ‖p (xorCube u a)‖ := by
    simp only [twistedPrimal_join, norm_smul, Real.norm_eq_abs, abs_mul, abs_character, one_mul]
  simp only [cubeL2, hn]
  change cubeL2 ℝ (fun a : Cube n => cubeL2 X (fun _ : Cube n => p (xorCube u a))) = _
  simp_rw [cubeL2_const]
  rw [cubeL2_norms, cubeL2_translate]
  rfl

theorem twistedDual_L2 {n : ℕ} (q : Cube n → (Y →L[ℝ] ℝ)) (v : Cube n) :
    cubeL2 (Y →L[ℝ] ℝ) (twistedDual q v) = cubeL2 (Y →L[ℝ] ℝ) q := by
  rw [cubeL2_join]
  have hn (a b : Cube n) : ‖twistedDual q v (cubeJoin n n (a,b))‖ = ‖q (xorCube v b)‖ := by
    simp only [twistedDual_join, norm_smul, Real.norm_eq_abs, abs_character, one_mul]
  simp only [cubeL2, hn]
  change cubeL2 ℝ (fun _ : Cube n => cubeL2 (Y →L[ℝ] ℝ) (fun b : Cube n => q (xorCube v b))) = _
  rw [cubeL2_translate, cubeL2_const, Real.norm_eq_abs, abs_of_nonneg (cubeL2_nonneg _)]
  rfl

theorem twistedPairing {n : ℕ} (T : X →L[ℝ] Y) (p : Cube n → X)
    (q : Cube n → (Y →L[ℝ] ℝ)) (u v : Cube n) :
    dualPairing (fun z => T (twistedPrimal p u z)) (twistedDual q v) =
      walshBilinear T p q * character v u := by
  unfold dualPairing
  rw [average_join]
  simp only [twistedPrimal_join, twistedDual_join, map_smul, smul_apply, smul_eq_mul]
  have he (a b : Cube n) :
      (character u b * character a b) * (character a v * q (xorCube v b) (T (p (xorCube u a)))) =
      character v u * (character (xorCube v b) (xorCube u a) *
        q (xorCube v b) (T (p (xorCube u a)))) := by
    calc
      _ = (character u b * character a b * character a v) *
        q (xorCube v b) (T (p (xorCube u a))) := by ring
      _ = _ := by rw [character_pairing_twist]; ring
  simp_rw [he]
  simp only [← smul_eq_mul, average_const_smul]
  have hv (a : Cube n) :
      average (fun b => character (xorCube v b) (xorCube u a) •
        q (xorCube v b) (T (p (xorCube u a)))) =
      average (fun b => character b (xorCube u a) • q b (T (p (xorCube u a)))) :=
    average_translate v (fun b => character b (xorCube u a) • q b (T (p (xorCube u a))))
  simp_rw [hv]
  have hu :
      average (fun a => average (fun b => character b (xorCube u a) • q b (T (p (xorCube u a))))) =
      average (fun a => average (fun b => character b a • q b (T (p a)))) :=
    average_translate u (fun a => average (fun b => character b a • q b (T (p a))))
  rw [hu]
  simp only [smul_eq_mul, walshBilinear, mul_comm]

theorem exists_exact_amplified_pairing (n : ℕ) {T : X →L[ℝ] Y} (hT : T ≠ 0) :
    ∃ (γ : ℝ)
      (x : Cube n → PiLp 2 (fun _ : Cube (n+n) => X))
      (y : Cube n → (PiLp 2 (fun _ : Cube (n+n) => Y) →L[ℝ] ℝ)),
      walshNorm n T / 2 < γ ∧ 0 < γ ∧
      (∀ u, ‖x u‖ ≤ 1) ∧ (∀ v, ‖y v‖ ≤ 1) ∧
      (∀ u v, y v (l2Amplification T (x u)) = γ * character v u) ∧
      (∀ k, walshNorm k (l2Amplification (Ω := Cube (n+n)) T) = walshNorm k T) := by
  obtain ⟨p, q, hp, hq, hh, hpos⟩ := exists_walshBilinear_half n hT
  refine ⟨walshBilinear T p q, fun u => probabilityL2Vector (twistedPrimal p u),
    fun v => probabilityL2Dual (twistedDual q v), hh, hpos, ?_, ?_, ?_, ?_⟩
  · intro u
    simpa only [probabilityL2Vector_norm, twistedPrimal_L2] using hp
  · intro v
    exact (probabilityL2Dual_norm_le _).trans ((twistedDual_L2 q v).le.trans hq)
  · intro u v
    rw [probabilityL2Dual_amplification, twistedPairing]
  · intro k
    exact walshNorm_amplification k T

end Cotype

end

end OAI
