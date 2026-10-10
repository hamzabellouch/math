import OAI.Geometry.PeriodicTiling.WordAffine
import OAI.Geometry.PeriodicTiling.WordAffineAlgebra
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section

namespace PeriodicTilingThree

private theorem word_one_ne_two {p : ℕ} (hlarge : 200 < p) :
    (1 : ZMod p) ≠ 2 := by
  intro h
  have hv := congrArg (fun x : ZMod p => x.val) h
  rw [ZMod.val_one_eq_one_mod, ZMod.val_two_eq_two_mod,
    Nat.mod_eq_of_lt (by omega : 1 < p),
    Nat.mod_eq_of_lt (by omega : 2 < p)] at hv
  omega

private theorem word_two_ne_zero {p : ℕ} (hlarge : 200 < p) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < p) hd

private def smallColumn {p : ℕ} (hlarge : 200 < p) (n : Fin p) : Column p :=
  ⟨n.val, by have := n.isLt; nlinarith⟩

private def fourColumn {p : ℕ} (hlarge : 200 < p) (i : Fin 4) : Column p :=
  smallColumn hlarge ⟨i.val, by have := i.isLt; omega⟩

private theorem small_affine_nonzero {p : ℕ} (hp : p.Prime)
    (A C : ZMod p) (hAC : A ≠ 0 ∨ C ≠ 0) :
    ∃ n : Fin p, A * (n.val : ZMod p) + C ≠ 0 := by
  by_cases hC : C = 0
  · have hA : A ≠ 0 := hAC.resolve_right (fun h => h hC)
    refine ⟨⟨1, hp.one_lt⟩, ?_⟩
    simpa only [Nat.cast_one, mul_one, hC, add_zero] using hA
  · refine ⟨⟨0, hp.pos⟩, ?_⟩
    simpa only [Nat.cast_zero, mul_zero, zero_add] using hC

private theorem exists_vertical_value {p : ℕ} (hp : p.Prime)
    (A B C : ZMod p) (hB : B ≠ 0) (n : Column p) (t : ZMod p) :
    ∃ m : ℤ, affineValue A B C n m = t := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective
    (B⁻¹ * (t - A * (n.val : ZMod p) - C))
  refine ⟨m, ?_⟩
  have hBm : B * (m : ZMod p) = t - A * (n.val : ZMod p) - C := by
    rw [hm, ← mul_assoc, mul_inv_cancel₀ hB, one_mul]
  unfold affineValue
  rw [hBm]
  ring

theorem nonconstantColumns_iff_vertical_coefficient {p : ℕ} (hp : p.Prime)
    (hlarge : 200 < p) {W : WordArray p} {A B C : ZMod p}
    (hH : AffineApproximation W A B C) : NonconstantColumns W ↔ B ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  constructor
  · intro hcolumns hB
    have hAC : A ≠ 0 ∨ C ≠ 0 := by
      rcases hH.1 with hA | hB' | hC
      · exact Or.inl hA
      · exact (hB' hB).elim
      · exact Or.inr hC
    obtain ⟨n₀, hn₀⟩ := small_affine_nonzero hp A C hAC
    let n := smallColumn hlarge n₀
    obtain ⟨m, m', hmm'⟩ := hcolumns n
    apply hmm'
    apply Units.ext
    have hval (z : ℤ) : (W n z : ZMod p) = A * (n₀.val : ZMod p) + C := by
      have hn : affineValue A B C n z ≠ 0 := by
        simpa only [affineValue, n, smallColumn, hB, zero_mul, add_zero] using hn₀
      simpa only [affineValue, n, smallColumn, hB, zero_mul, add_zero] using hH.2 n z hn
    exact (hval m).trans (hval m').symm
  · intro hB n
    obtain ⟨m, hm⟩ := exists_vertical_value hp A B C hB n 1
    obtain ⟨m', hm'⟩ := exists_vertical_value hp A B C hB n 2
    refine ⟨m, m', ?_⟩
    intro heq
    have hwm : (W n m : ZMod p) = 1 :=
      (hH.2 n m (by rw [hm]; exact one_ne_zero)).trans hm
    have hwm' : (W n m' : ZMod p) = 2 :=
      (hH.2 n m' (by rw [hm']; exact word_two_ne_zero hlarge)).trans hm'
    exact word_one_ne_two hlarge
      (hwm.symm.trans ((congrArg (fun u : Symbol p => (u : ZMod p)) heq).trans hwm'))

theorem prime_dvd_vertical_period {p : ℕ} (hp : p.Prime)
    (hlarge : 200 < p) {W : WordArray p} {A B C : ZMod p}
    (hH : AffineApproximation W A B C) (hB : B ≠ 0) {M : ℤ}
    (hperiod : VerticalPeriod W M) : (p : ℤ) ∣ M := by
  let : Fact p.Prime := ⟨hp⟩
  let n : Column p := ⟨0, pow_pos hp.pos 2⟩
  let x : Fin 4 → ZMod p := fun i => (i.val : ZMod p)
  have hx : Function.Injective x := by
    simpa only [zero_add, Int.cast_natCast] using
      (four_residues_injective (p := p) (by omega : 4 ≤ p) 0)
  obtain ⟨i, j, hij, hi, hiM, hj, hjM⟩ := two_common_nonzero_of_four x hx
    B (A * (n.val : ZMod p) + C)
    B (B * (M : ZMod p) + A * (n.val : ZMod p) + C)
    (Or.inl hB) (Or.inl hB)
  let m : ℤ := i.val
  have hm : affineValue A B C n m ≠ 0 := by
    have heq : affineValue A B C n m = B * x i + (A * (n.val : ZMod p) + C) := by
      simp only [affineValue, m, x, Int.cast_natCast]
      ring
    rw [heq]
    exact hi
  have hmM : affineValue A B C n (m + M) ≠ 0 := by
    have heq : affineValue A B C n (m + M) =
        B * x i + (B * (M : ZMod p) + A * (n.val : ZMod p) + C) := by
      simp only [affineValue, m, x, Int.cast_add, Int.cast_natCast]
      ring
    rw [heq]
    exact hiM
  have heq : affineValue A B C n (m + M) = affineValue A B C n m :=
    (hH.2 n (m + M) hmM).symm.trans
      ((congrArg (fun u : Symbol p => (u : ZMod p)) (hperiod n m)).trans (hH.2 n m hm))
  have hBM : B * (M : ZMod p) = 0 := by
    simp only [affineValue, Int.cast_add] at heq
    linear_combination heq
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd M p).mp
    ((mul_eq_zero.mp hBM).resolve_left hB)

def straighten {p : ℕ} (W : WordArray p) (u v : ℤ) : WordArray p :=
  fun n m => W n (m + u * (n.val : ℤ) + v)

theorem straighten_lineRule {p : ℕ} {W : WordArray p}
    (hW : LineRule p W) (u v : ℤ) : LineRule p (straighten W u v) := by
  intro d e
  have heq : (fun n => straighten W u v n (d * (n.val : ℤ) + e)) =
      (fun n => W n ((d + u) * (n.val : ℤ) + (e + v))) := by
    funext n
    unfold straighten
    congr 1
    ring
  rw [heq]
  exact hW (d + u) (e + v)

theorem straighten_nonconstantColumns_iff {p : ℕ} (W : WordArray p) (u v : ℤ) :
    NonconstantColumns (straighten W u v) ↔ NonconstantColumns W := by
  constructor
  · intro h n
    obtain ⟨m, m', hmm'⟩ := h n
    exact ⟨m + u * (n.val : ℤ) + v, m' + u * (n.val : ℤ) + v, hmm'⟩
  · intro h n
    obtain ⟨m, m', hmm'⟩ := h n
    refine ⟨m - u * (n.val : ℤ) - v, m' - u * (n.val : ℤ) - v, ?_⟩
    have hm : m - u * (n.val : ℤ) - v + u * (n.val : ℤ) + v = m := by ring
    have hm' : m' - u * (n.val : ℤ) - v + u * (n.val : ℤ) + v = m' := by ring
    simpa only [straighten, hm, hm'] using hmm'

theorem straighten_verticalPeriod_iff {p : ℕ} (W : WordArray p)
    (u v M : ℤ) : VerticalPeriod (straighten W u v) M ↔ VerticalPeriod W M := by
  constructor
  · intro h n m
    have hh := h n (m - u * (n.val : ℤ) - v)
    change W n ((m - u * (n.val : ℤ) - v + M) + u * (n.val : ℤ) + v) =
      W n ((m - u * (n.val : ℤ) - v) + u * (n.val : ℤ) + v) at hh
    convert hh using 1 <;> congr 1 <;> ring
  · intro h n m
    change W n ((m + M) + u * (n.val : ℤ) + v) = W n (m + u * (n.val : ℤ) + v)
    convert h n (m + u * (n.val : ℤ) + v) using 1 ; congr 1 ; ring

theorem exists_straighten_affine {p : ℕ} (hp : p.Prime)
    {W : WordArray p} {A B C : ZMod p} (hH : AffineApproximation W A B C)
    (hB : B ≠ 0) : ∃ u v : ℤ, AffineApproximation (straighten W u v) 0 B 0 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, hu⟩ := ZMod.intCast_surjective (-(B⁻¹ * A))
  obtain ⟨v, hv⟩ := ZMod.intCast_surjective (-(B⁻¹ * C))
  have hbu : A + B * (u : ZMod p) = 0 := by
    rw [hu, mul_neg, ← mul_assoc, mul_inv_cancel₀ hB, one_mul, add_neg_cancel]
  have hbv : C + B * (v : ZMod p) = 0 := by
    rw [hv, mul_neg, ← mul_assoc, mul_inv_cancel₀ hB, one_mul, add_neg_cancel]
  refine ⟨u, v, Or.inr (Or.inl hB), ?_⟩
  intro n m hm
  have hnorm : affineValue A B C n (m + u * (n.val : ℤ) + v) =
      affineValue 0 B 0 n m := by
    simp only [affineValue, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    linear_combination (n.val : ZMod p) * hbu + hbv
  exact (hH.2 n _ (by rw [hnorm]; exact hm)).trans hnorm

def rescale {p : ℕ} (W : WordArray p) : WordArray p :=
  fun n m => W n ((p : ℤ) * m)

theorem rescale_lineRule {p : ℕ} {W : WordArray p} (hW : LineRule p W) :
    LineRule p (rescale W) := by
  intro d e
  have heq : (fun n => rescale W n (d * (n.val : ℤ) + e)) =
      (fun n => W n (((p : ℤ) * d) * (n.val : ℤ) + (p : ℤ) * e)) := by
    funext n
    unfold rescale
    congr 1
    ring
  rw [heq]
  exact hW ((p : ℤ) * d) ((p : ℤ) * e)

private theorem exists_nonzero_affine_ne {p : ℕ} (hp : p.Prime)
    (hlarge : 200 < p) (a z c : ZMod p) (ha : a ≠ 0) :
    ∃ k : Fin p, z + a * (k.val : ZMod p) ≠ 0 ∧
      z + a * (k.val : ZMod p) ≠ c := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  have ht : ∃ t : ZMod p, t ≠ 0 ∧ t ≠ c := by
    by_cases hc : c = 1
    · exact ⟨2, word_two_ne_zero hlarge, by
        rw [hc]
        exact Ne.symm (word_one_ne_two hlarge)⟩
    · exact ⟨1, one_ne_zero, Ne.symm hc⟩
  obtain ⟨t, ht0, htc⟩ := ht
  let x : ZMod p := a⁻¹ * (t - z)
  let k : Fin p := ⟨x.val, ZMod.val_lt x⟩
  have hk : (k.val : ZMod p) = x := ZMod.natCast_zmod_val x
  have heq : z + a * (k.val : ZMod p) = t := by
    rw [hk]
    dsimp only [x]
    rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
    ring
  exact ⟨k, by rw [heq]; exact ht0, by rw [heq]; exact htc⟩

private def fiberColumn {p : ℕ} (n₀ k : Fin p) : Column p :=
  ⟨n₀.val + p * k.val, by
    calc
      n₀.val + p * k.val < p + p * k.val := Nat.add_lt_add_right n₀.isLt _
      _ = p * (k.val + 1) := by ring
      _ ≤ p * p := Nat.mul_le_mul_left p (Nat.succ_le_of_lt k.isLt)
      _ = p ^ 2 := by ring⟩

theorem rescale_vertical_coefficient_ne_zero {p : ℕ} (hp : p.Prime)
    (hlarge : 200 < p) {W : WordArray p} (hW : LineRule p W)
    {B : ZMod p} (hB : B ≠ 0) (hH : AffineApproximation W 0 B 0)
    {A₁ B₁ C₁ : ZMod p} (hH₁ : AffineApproximation (rescale W) A₁ B₁ C₁) :
    B₁ ≠ 0 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  intro hB₁
  have hAC : A₁ ≠ 0 ∨ C₁ ≠ 0 := by
    rcases hH₁.1 with hA | hB' | hC
    · exact Or.inl hA
    · exact (hB' hB₁).elim
    · exact Or.inr hC
  obtain ⟨n₀, hc⟩ := small_affine_nonzero hp A₁ C₁ hAC
  let c : ZMod p := A₁ * (n₀.val : ZMod p) + C₁
  obtain ⟨a, b, hab, hw⟩ := hW 1 (-(n₀.val : ℤ))
  have hab' : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0 := by
    rcases hab with ha | hb
    · exact Or.inl (fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h))
    · exact Or.inr (fun h => hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp h))
  let x : Fin 4 → ZMod p := fun i => (i.val : ZMod p)
  have hx : Function.Injective x := by
    simpa only [zero_add, Int.cast_natCast] using
      (four_residues_injective (p := p) (by omega : 4 ≤ p) 0)
  obtain ⟨i, j, hij, hai, hbi, haj, hbj⟩ := two_common_nonzero_of_four x hx
    (a : ZMod p) (b : ZMod p) B (-B * (n₀.val : ZMod p)) hab' (Or.inl hB)
  have hmatch (s : Fin 4)
      (has : (a : ZMod p) * x s + (b : ZMod p) ≠ 0)
      (hbs : B * x s + -B * (n₀.val : ZMod p) ≠ 0) :
      (a : ZMod p) * x s + (b : ZMod p) =
        B * x s + -B * (n₀.val : ZMod p) := by
    let n := fourColumn hlarge s
    have hnot : ¬ (p : ℤ) ∣ a * (n.val : ℤ) + b := by
      intro hd
      apply has
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, n, fourColumn, smallColumn, x] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd (a * (n.val : ℤ) + b) p).mpr hd
    have harg : affineValue 0 B 0 n (1 * (n.val : ℤ) + -(n₀.val : ℤ)) =
        B * x s + -B * (n₀.val : ZMod p) := by
      simp only [affineValue, zero_mul, zero_add, add_zero, one_mul,
        Int.cast_add, Int.cast_neg, Int.cast_natCast]
      change B * ((s.val : ZMod p) + -(n₀.val : ZMod p)) =
        B * (s.val : ZMod p) + -B * (n₀.val : ZMod p)
      ring
    have hw' := (hw n).1 hnot
    dsimp only at hw'
    have hH' := hH.2 n (1 * (n.val : ℤ) + -(n₀.val : ℤ))
      (by rw [harg]; exact hbs)
    calc
      (a : ZMod p) * x s + (b : ZMod p) =
          (W n (1 * (n.val : ℤ) + -(n₀.val : ℤ)) : ZMod p) := by
        simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, n, fourColumn, smallColumn, x] using hw'.symm
      _ = B * x s + -B * (n₀.val : ZMod p) := hH'.trans harg
  obtain ⟨haB, hbB⟩ := affine_coefficients_eq_of_two (fun h => hij (hx h))
    (hmatch i hai hbi) (hmatch j haj hbj)
  have ha0 : (a : ZMod p) ≠ 0 := by rw [haB]; exact hB
  have hdiv : (p : ℤ) ∣ a * (n₀.val : ℤ) + b := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
    rw [haB, hbB]
    ring
  obtain ⟨z, hz⟩ := hdiv
  obtain ⟨k, hk0, hkc⟩ := exists_nonzero_affine_ne hp hlarge (a : ZMod p) (z : ZMod p) c ha0
  let n := fiberColumn n₀ k
  have hnv : (n.val : ℤ) = (n₀.val : ℤ) + (p : ℤ) * (k.val : ℤ) := by
    simp only [n, fiberColumn, Nat.cast_add, Nat.cast_mul]
  have hnvmod : (n.val : ZMod p) = (n₀.val : ZMod p) := by
    simp only [n, fiberColumn, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self,
      zero_mul, add_zero]
  have hnew : affineValue A₁ B₁ C₁ n (k.val : ℤ) = c := by
    simp only [affineValue, hB₁, zero_mul, add_zero, hnvmod, c]
  have hvalue : (W n ((p : ℤ) * (k.val : ℤ)) : ZMod p) = c :=
    (hH₁.2 n (k.val : ℤ) (by rw [hnew]; exact hc)).trans hnew
  have hfactor : a * (n.val : ℤ) + b = (p : ℤ) * (z + a * (k.val : ℤ)) := by
    rw [hnv]
    linear_combination hz
  have hnot : ¬ (p : ℤ) ∣ z + a * (k.val : ℤ) := by
    intro hd
    apply hk0
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd (z + a * (k.val : ℤ)) p).mpr hd
  have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  have hnotSq : ¬ (p : ℤ) ^ 2 ∣ a * (n.val : ℤ) + b := by
    intro hd
    apply hnot
    apply (Int.mul_dvd_mul_iff_left hp0).mp
    simpa only [pow_two, hfactor] using hd
  have hdivn : (p : ℤ) ∣ a * (n.val : ℤ) + b := ⟨z + a * (k.val : ℤ), hfactor⟩
  have hsecond := (hw n).2 hdivn hnotSq
  dsimp only at hsecond
  have hline : 1 * (n.val : ℤ) + -(n₀.val : ℤ) = (p : ℤ) * (k.val : ℤ) := by
    rw [hnv]
    ring
  rw [hline, hvalue, hfactor, Int.mul_ediv_cancel_left _ hp0] at hsecond
  apply hkc
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using hsecond.symm

theorem no_positive_nat_vertical_period {p : ℕ} (hp : p.Prime)
    (hlarge : 200 < p) :
    ∀ M : ℕ, ∀ W : WordArray p, LineRule p W → NonconstantColumns W →
      0 < M → VerticalPeriod W (M : ℤ) → False := by
  intro M
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro W hW hcolumns hM hperiod
    obtain ⟨A, B, C, hH⟩ := global_affine_approximation hp hlarge hW
    have hB := (nonconstantColumns_iff_vertical_coefficient hp hlarge hH).mp hcolumns
    have hdivZ := prime_dvd_vertical_period hp hlarge hH hB hperiod
    have hdiv : p ∣ M := Int.natCast_dvd_natCast.mp hdivZ
    obtain ⟨u, v, hnorm⟩ := exists_straighten_affine hp hH hB
    let W₀ := straighten W u v
    have hW₀ : LineRule p W₀ := straighten_lineRule hW u v
    have hperiod₀ : VerticalPeriod W₀ (M : ℤ) :=
      (straighten_verticalPeriod_iff W u v (M : ℤ)).mpr hperiod
    have hW₁ : LineRule p (rescale W₀) := rescale_lineRule hW₀
    obtain ⟨A₁, B₁, C₁, hH₁⟩ := global_affine_approximation hp hlarge hW₁
    have hB₁ := rescale_vertical_coefficient_ne_zero hp hlarge hW₀ hB hnorm hH₁
    have hcolumns₁ := (nonconstantColumns_iff_vertical_coefficient hp hlarge hH₁).mpr hB₁
    have hsmall : M / p < M := Nat.div_lt_self hM hp.one_lt
    have hpos : 0 < M / p := Nat.div_pos (Nat.le_of_dvd hM hdiv) hp.pos
    have hquot : (p : ℤ) * ((M / p : ℕ) : ℤ) = (M : ℤ) := by
      exact_mod_cast Nat.mul_div_cancel' hdiv
    have hperiod₁ : VerticalPeriod (rescale W₀) ((M / p : ℕ) : ℤ) := by
      intro n m
      change W₀ n ((p : ℤ) * (m + ((M / p : ℕ) : ℤ))) = W₀ n ((p : ℤ) * m)
      rw [mul_add, hquot]
      exact hperiod₀ n ((p : ℤ) * m)
    exact ih (M / p) hsmall (rescale W₀) hW₁ hcolumns₁ hpos hperiod₁

theorem no_positive_vertical_period {p : ℕ} (hp : p.Prime)
    (hlarge : 200 < p) {W : WordArray p} (hW : LineRule p W)
    (hcolumns : NonconstantColumns W) {M : ℤ} (hM : 0 < M)
    (hperiod : VerticalPeriod W M) : False := by
  have hpos : 0 < M.toNat := Int.pos_iff_toNat_pos.mp hM
  have hcast : (M.toNat : ℤ) = M := Int.toNat_of_nonneg hM.le
  exact no_positive_nat_vertical_period hp hlarge M.toNat W hW hcolumns hpos
    (by simpa only [hcast] using hperiod)

end PeriodicTilingThree

end

end OAI
