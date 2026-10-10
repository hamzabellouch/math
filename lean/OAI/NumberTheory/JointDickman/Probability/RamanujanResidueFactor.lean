import OAI.NumberTheory.JointDickman.Amplification.RamanujanVanishing

namespace OAI

/-! # The exact residue factor in the small-major-arc kernel -/

namespace JointDickman
open Finset
open scoped ArithmeticFunction.Moebius

theorem ramanujanSum_crt {a b : ℕ} [NeZero a] [NeZero b] [NeZero (a*b)]
    (hab : a.Coprime b) (h : ZMod (a*b)) :
    ramanujanSum (a*b) h =
      ramanujanSum a ((ZMod.chineseRemainder hab) h).1 *
      ramanujanSum b ((ZMod.chineseRemainder hab) h).2 := by
  have he : (ZMod.chineseRemainder hab) h =
      ((h.val : ZMod a), (h.val : ZMod b)) := by
    calc
      _ = (ZMod.chineseRemainder hab) (h.val : ZMod (a*b)) := by
        rw [ZMod.natCast_zmod_val]
      _ = _ := by rw [map_natCast]; rfl
  rw [he]
  simpa only [ZMod.natCast_zmod_val] using ramanujanSum_multiplicative hab h.val

theorem ramanujanSum_parseval (q : ℕ) [NeZero q] :
    (∑ h : ZMod q, ‖ramanujanSum q h‖^2) = (q : ℝ)*q.totient := by
  simpa [ramanujanSum,unitResidueFourier,ZMod.card_units_eq_totient] using
    unitResidue_fourier_parseval (q := q) (fun _ => (1 : ℂ))

theorem ramanujanSum_coprime_norm {q : ℕ} [NeZero q] (hq : Squarefree q)
    {h : ZMod q} (hh : h.val.Coprime q) : ‖ramanujanSum q h‖ = 1 := by
  rw [← ZMod.natCast_zmod_val h,ramanujanSum_coprime hh,Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree hq

theorem coprime_residue_count (q : ℕ) [NeZero q] :
    (∑ h : ZMod q, if h.val.Coprime q then (1 : ℝ) else 0) = q.totient := by
  classical
  have hc := Fintype.card_congr (ZMod.unitsEquivCoprime (n := q))
  rw [ZMod.card_units_eq_totient] at hc
  simp only [Fintype.card_subtype] at hc
  calc
    _ = ((univ.filter (fun h : ZMod q => h.val.Coprime q)).card : ℝ) := by
      rw [← sum_filter]
      simp
    _ = q.totient := by exact_mod_cast hc.symm

theorem crt_coprime_frequency {a b : ℕ} [NeZero a] [NeZero b] [NeZero (a*b)]
    (hab : a.Coprime b) (h : ZMod (a*b)) :
    ((ZMod.chineseRemainder hab h).2).val.Coprime b ↔ h.val.Coprime b := by
  have he : (ZMod.chineseRemainder hab h).2 = (h.val : ZMod b) := by
    have ht : ZMod.chineseRemainder hab h = ((h.val : ZMod a),(h.val : ZMod b)) := by
      calc
        _ = (ZMod.chineseRemainder hab) (h.val : ZMod (a*b)) := by
          rw [ZMod.natCast_zmod_val]
        _ = _ := by rw [map_natCast]; rfl
    exact congrArg Prod.snd ht
  rw [he,ZMod.val_natCast,ZMod.coprime_mod_iff_coprime]

/-- Unnormalized version of manuscript (40). -/
theorem ramanujan_restricted_parseval {j q : ℕ} [NeZero j] [NeZero q]
    [NeZero (j*q)] (hcop : j.Coprime q) (hq : Squarefree q) :
    (∑ h : ZMod (j*q), if h.val.Coprime q then ‖ramanujanSum (j*q) h‖^2 else 0) =
      (j : ℝ)*j.totient*q.totient := by
  classical
  let f : ZMod j × ZMod q → ℝ := fun h =>
    ‖ramanujanSum j h.1‖^2 * (if h.2.val.Coprime q then 1 else 0)
  calc
    _ = ∑ h : ZMod j × ZMod q, f h := by
      apply Fintype.sum_equiv (ZMod.chineseRemainder hcop).toEquiv
      intro h
      change (if h.val.Coprime q then ‖ramanujanSum (j*q) h‖^2 else 0) =
        ‖ramanujanSum j (ZMod.chineseRemainder hcop h).1‖^2 *
          (if (ZMod.chineseRemainder hcop h).2.val.Coprime q then 1 else 0)
      simp only [← crt_coprime_frequency hcop h]
      split_ifs with hh
      · rw [ramanujanSum_crt hcop,norm_mul,ramanujanSum_coprime_norm hq hh]
        simp
      · simp
    _ = (j : ℝ)*j.totient*q.totient := by
      simp only [f,Fintype.sum_prod_type,← mul_sum,coprime_residue_count,← sum_mul,
        ramanujanSum_parseval]

/-- The exact normalized frequency factor, including the vanishing non-coprime case. -/
theorem ramanujan_residue_factor {j q : ℕ} [NeZero j] [NeZero q] [NeZero (j*q)]
    (hq : Squarefree q) :
    (∑ h : ZMod (j*q), if h.val.Coprime q then
      ‖ramanujanSum (j*q) h‖^2 / ((j*q).totient : ℝ)^2 else 0) =
      if j.Coprime q then (j : ℝ)/(j.totient*q.totient) else 0 := by
  classical
  by_cases hcop : j.Coprime q
  · rw [ite_eq_left hcop]
    have hj : (j.totient : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos j)).ne'
    have hq' : (q.totient : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
    have he (h : ZMod (j*q)) :
        (if h.val.Coprime q then ‖ramanujanSum (j*q) h‖^2 / ((j*q).totient : ℝ)^2 else 0) =
        (if h.val.Coprime q then ‖ramanujanSum (j*q) h‖^2 else 0) /
          ((j*q).totient : ℝ)^2 := by split_ifs <;> simp
    simp_rw [he]
    rw [← sum_div,ramanujan_restricted_parseval hcop hq,Nat.totient_mul hcop,Nat.cast_mul]
    field_simp
  · rw [ite_eq_right hcop]
    apply sum_eq_zero
    intro h _
    split_ifs with hh
    · have hz : ramanujanSum (j*q) h = 0 := by
        simpa only [ZMod.natCast_zmod_val] using ramanujanSum_zero_of_not_coprime hcop hh
      simp [hz]
    · rfl

end JointDickman

end OAI
