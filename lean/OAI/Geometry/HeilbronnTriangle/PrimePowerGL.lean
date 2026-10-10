import Mathlib

namespace OAI


namespace Problem355.PrimePowerGL

open Matrix

theorem map_GL_surjective {R S n : Type*} [CommRing R] [CommRing S]
    [Fintype n] [DecidableEq n] (f : R →+* S)
    (hf : Function.Surjective f) (hu : ∀ x, IsUnit (f x) → IsUnit x) :
    Function.Surjective (Matrix.GeneralLinearGroup.map (n := n) f) := by
  classical
  intro A
  choose B hB using fun i j => hf (A i j)
  have hmap : Matrix.map (Matrix.of B) f = (A : Matrix n n S) := by
    ext i j
    exact hB i j
  have hdet : IsUnit (Matrix.det (Matrix.of B)) := hu _ (by
    rw [RingHom.map_det]
    change IsUnit (Matrix.det (Matrix.map (Matrix.of B) f))
    rw [hmap]
    exact A.det.isUnit)
  let U : GL n R := Matrix.GeneralLinearGroup.mk'' (Matrix.of B) hdet
  refine ⟨U, ?_⟩
  apply Units.ext
  exact hmap

theorem prime_power_reflects_units (p k : ℕ) (hp : p.Prime) (hk : 0 < k)
    (x : ZMod (p ^ k)) :
    IsUnit (ZMod.castHom (dvd_pow_self p (Nat.ne_zero_of_lt hk)) (ZMod p) x) ↔
      IsUnit x := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp0⟩
  conv_rhs => rw [← ZMod.natCast_zmod_val x]
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  simp only [map_natCast]
  rw [ZMod.isUnit_iff_coprime, ZMod.isUnit_iff_coprime,
    Nat.coprime_pow_right_iff hk]

theorem prime_power_GL_surjective (p k : ℕ) (hp : p.Prime) (hk : 0 < k)
    (n : Type*) [Fintype n] [DecidableEq n] :
    Function.Surjective (Matrix.GeneralLinearGroup.map (n := n)
      (ZMod.castHom (dvd_pow_self p (Nat.ne_zero_of_lt hk)) (ZMod p))) := by
  apply map_GL_surjective
  · exact ZMod.castHom_surjective _
  · intro x hx
    exact (prime_power_reflects_units p k hp hk x).mp hx

noncomputable def fiberEquivKer {R S : Type*} [AddGroup R] [AddGroup S]
    (f : R →+ S) (hf : Function.Surjective f) (y : S) :
    {x : R // f x = y} ≃ f.ker := by
  classical
  let r := Classical.choose (hf y)
  have hr : f r = y := Classical.choose_spec (hf y)
  refine
    { toFun := fun x => ⟨x.1 - r, ?_⟩
      invFun := fun x => ⟨x.1 + r, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · change f (x.1 - r) = 0
    simp [map_sub, x.2, hr]
  · have hx : f x.1 = 0 := x.2
    simp [map_add, hx, hr]
  · intro x
    apply Subtype.ext
    simp
  · intro x
    apply Subtype.ext
    simp

noncomputable def unitsEquivSigmaFiber {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (hu : ∀ x, IsUnit (f x) → IsUnit x) :
    Rˣ ≃ Σ y : Sˣ, {x : R // f x = (y : S)} where
  toFun x := ⟨Units.map f.toMonoidHom x, ⟨x, rfl⟩⟩
  invFun x := (hu x.2.1 (by rw [x.2.2]; exact x.1.isUnit)).unit
  left_inv x := by apply Units.ext; simp
  right_inv x := by
    rcases x with ⟨y, x, hx⟩
    apply Sigma.ext
    · apply Units.ext
      simp [hx]
    · apply (Subtype.heq_iff_coe_eq (fun z => by simp [hx])).mpr
      simp

theorem card_units_of_surjective {R S : Type*} [Ring R] [Ring S]
    [Fintype R] [Fintype S] (f : R →+* S)
    (hf : Function.Surjective f) (hu : ∀ x, IsUnit (f x) → IsUnit x) :
    Nat.card Rˣ = Nat.card Sˣ * Nat.card f.toAddMonoidHom.ker := by
  classical
  let : Fintype Sˣ := Fintype.ofFinite _
  calc
    Nat.card Rˣ = ∑ y : Sˣ, Nat.card {x : R // f x = (y : S)} := by
      rw [Nat.card_congr (unitsEquivSigmaFiber f hu), Nat.card_sigma]
    _ = ∑ _ : Sˣ, Nat.card f.toAddMonoidHom.ker := by
      apply Finset.sum_congr rfl
      intro y hy
      exact Nat.card_congr (fiberEquivKer f.toAddMonoidHom hf y)
    _ = Nat.card Sˣ * Nat.card f.toAddMonoidHom.ker := by
      simp [Nat.card_eq_fintype_card]

noncomputable def matrixKernelEquiv {R S n : Type*} [Ring R] [Ring S]
    [Fintype n] [DecidableEq n] (f : R →+* S) :
    (f.mapMatrix (m := n)).toAddMonoidHom.ker ≃
      (n → n → f.toAddMonoidHom.ker) where
  toFun A i j := ⟨A.1 i j, by
    have hA : f.mapMatrix A.1 = 0 := A.2
    exact congrFun (congrFun hA i) j⟩
  invFun A := ⟨fun i j => (A i j).1, by
    ext i j
    exact (A i j).2⟩
  left_inv A := by rfl
  right_inv A := by rfl

theorem card_matrix_kernel {R S n : Type*} [Ring R] [Ring S]
    [Fintype n] [DecidableEq n] (f : R →+* S) :
    Nat.card (f.mapMatrix (m := n)).toAddMonoidHom.ker =
      Nat.card f.toAddMonoidHom.ker ^ (Fintype.card n * Fintype.card n) := by
  rw [Nat.card_congr (matrixKernelEquiv f), Nat.card_fun, Nat.card_fun,
    ← pow_mul, Nat.card_eq_fintype_card (α := n)]

theorem card_GL_of_surjective {R S n : Type*} [CommRing R] [CommRing S]
    [Fintype R] [Fintype S] [Fintype n] [DecidableEq n] (f : R →+* S)
    (hf : Function.Surjective f) (hu : ∀ x, IsUnit (f x) → IsUnit x) :
    Nat.card (GL n R) = Nat.card (GL n S) *
      Nat.card f.toAddMonoidHom.ker ^ (Fintype.card n * Fintype.card n) := by
  have hfM : Function.Surjective (f.mapMatrix (m := n)) := by
    intro A
    choose B hB using fun i j => hf (A i j)
    exact ⟨B, by ext i j; exact hB i j⟩
  have huM : ∀ A : Matrix n n R, IsUnit (f.mapMatrix A) → IsUnit A := by
    intro A hA
    rw [Matrix.isUnit_iff_isUnit_det] at hA ⊢
    apply hu
    rwa [RingHom.map_det]
  change Nat.card (Matrix n n R)ˣ = _
  rw [card_units_of_surjective (f.mapMatrix) hfM huM, card_matrix_kernel]

theorem card_prime_power_kernel (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    Nat.card (ZMod.castHom (dvd_pow_self p (Nat.ne_zero_of_lt hk))
      (ZMod p)).toAddMonoidHom.ker = p ^ (k - 1) := by
  let f := ZMod.castHom (dvd_pow_self p (Nat.ne_zero_of_lt hk)) (ZMod p)
  have hf : Function.Surjective f := ZMod.castHom_surjective _
  have hrange : f.toAddMonoidHom.range = ⊤ := AddMonoidHom.range_eq_top.mpr hf
  have h := f.toAddMonoidHom.ker.card_mul_index
  rw [AddSubgroup.index_ker, hrange] at h
  rw [Nat.card_congr AddSubgroup.topEquiv.toEquiv] at h
  simp only [Nat.card_zmod] at h
  apply Nat.eq_of_mul_eq_mul_right hp.pos
  calc
    Nat.card f.toAddMonoidHom.ker * p = p ^ k := h
    _ = p ^ (k - 1) * p := by
      rw [← pow_succ]
      congr 1
      omega

theorem card_GL_prime_power (p k : ℕ) (hp : p.Prime) (hk : 0 < k)
    (n : Type*) [Fintype n] [DecidableEq n] :
    Nat.card (GL n (ZMod (p ^ k))) =
      Nat.card (GL n (ZMod p)) * p ^ ((k - 1) * (Fintype.card n * Fintype.card n)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let f := ZMod.castHom (dvd_pow_self p (Nat.ne_zero_of_lt hk)) (ZMod p)
  rw [card_GL_of_surjective f (ZMod.castHom_surjective _) (fun x hx =>
    (prime_power_reflects_units p k hp hk x).mp hx)]
  rw [card_prime_power_kernel p k hp hk, ← pow_mul]

theorem card_GL_three_field (F : Type*) [Field F] [Fintype F] :
    Nat.card (GL (Fin 3) F) =
      (Fintype.card F ^ 3 - 1) * (Fintype.card F ^ 3 - Fintype.card F) *
        (Fintype.card F ^ 3 - Fintype.card F ^ 2) := by
  simp [Matrix.card_GL_field, Fin.prod_univ_succ, mul_assoc]

theorem card_GL_three_field_lower (F : Type*) [Field F] [Fintype F] :
    (21 / 64 : ℝ) * (Fintype.card F : ℝ) ^ 9 ≤
      (Nat.card (GL (Fin 3) F) : ℝ) := by
  let q := Fintype.card F
  have hq : 2 ≤ q := Fintype.one_lt_card
  have hq0 : 0 < q := by omega
  have h1 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq0
  have hq3 : q ≤ q ^ 3 := Nat.le_pow (by norm_num)
  have hq23 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right hq0 (by norm_num)
  rw [card_GL_three_field]
  change (21 / 64 : ℝ) * (q : ℝ) ^ 9 ≤
    (((q ^ 3 - 1) * (q ^ 3 - q) * (q ^ 3 - q ^ 2) : ℕ) : ℝ)
  push_cast [Nat.cast_sub h1, Nat.cast_sub hq3, Nat.cast_sub hq23]
  have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqnonneg : (0 : ℝ) ≤ q := by positivity
  have hpow2 : (4 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  have hpow3 : (8 : ℝ) ≤ (q : ℝ) ^ 3 := by
    nlinarith [mul_le_mul hpow2 hqr (by norm_num : (0 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ (q : ℝ) ^ 2)]
  have ha : (7 / 8 : ℝ) * (q : ℝ) ^ 3 ≤ (q : ℝ) ^ 3 - 1 := by nlinarith
  have hb : (3 / 4 : ℝ) * (q : ℝ) ^ 3 ≤ (q : ℝ) ^ 3 - q := by
    nlinarith [mul_le_mul_of_nonneg_right hpow2 hqnonneg]
  have hc : (1 / 2 : ℝ) * (q : ℝ) ^ 3 ≤ (q : ℝ) ^ 3 - (q : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hqr (sq_nonneg (q : ℝ))]
  calc
    (21 / 64 : ℝ) * (q : ℝ) ^ 9 =
      ((7 / 8 : ℝ) * (q : ℝ) ^ 3) * ((3 / 4 : ℝ) * (q : ℝ) ^ 3) *
        ((1 / 2 : ℝ) * (q : ℝ) ^ 3) := by ring
    _ ≤ ((q : ℝ) ^ 3 - 1) * ((q : ℝ) ^ 3 - q) *
        ((q : ℝ) ^ 3 - (q : ℝ) ^ 2) := by
      apply mul_le_mul
      · exact mul_le_mul ha hb (by positivity) (by linarith [ha])
      · exact hc
      · positivity
      · exact mul_nonneg (by linarith [ha]) (by linarith [hb])

theorem card_GL_three_prime_power_lower (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (21 / 64 : ℝ) * ((p ^ k : ℕ) : ℝ) ^ 9 ≤
      (Nat.card (GL (Fin 3) (ZMod (p ^ k))) : ℝ) := by
  have : Fact p.Prime := ⟨hp⟩
  have hfield := card_GL_three_field_lower (ZMod p)
  simp only [ZMod.card] at hfield
  rw [card_GL_prime_power p k hp hk (Fin 3)]
  simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
  norm_num only [show 3 * 3 = 9 by norm_num]
  have hpow : ((p : ℝ) ^ k) ^ 9 =
      (p : ℝ) ^ 9 * (p : ℝ) ^ ((k - 1) * 9) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [hpow, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hfield (by positivity)

end Problem355.PrimePowerGL

end OAI
