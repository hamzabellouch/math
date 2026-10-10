import Mathlib
import OAI.Analysis.BoxTransport.Definitions

namespace OAI

/-! Computable rational arithmetic and exponential/flat-function approximation. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

open scoped BigOperators ContDiff

namespace BoxTransport.Routing.Computation

abbrev QCode := ℕ × ℕ × ℕ

def Qval (q : QCode) : ℚ := ((q.1 : ℚ) - q.2.1) / (q.2.2 + 1)

def qZero : QCode := (0, 0, 0)
def qOne : QCode := (1, 0, 0)
def qNat (n : ℕ) : QCode := (n, 0, 0)
def qNeg (q : QCode) : QCode := (q.2.1, q.1, q.2.2)
def qAdd (q r : QCode) : QCode :=
  (q.1 * (r.2.2 + 1) + r.1 * (q.2.2 + 1),
   q.2.1 * (r.2.2 + 1) + r.2.1 * (q.2.2 + 1),
   (q.2.2 + 1) * (r.2.2 + 1) - 1)
def qMul (q r : QCode) : QCode :=
  (q.1 * r.1 + q.2.1 * r.2.1, q.1 * r.2.1 + q.2.1 * r.1,
   (q.2.2 + 1) * (r.2.2 + 1) - 1)
def qInv (q : QCode) : QCode :=
  if q.2.1 < q.1 then (q.2.2 + 1, 0, q.1 - q.2.1 - 1)
  else if q.1 < q.2.1 then (0, q.2.2 + 1, q.2.1 - q.1 - 1)
  else qZero

def qSub (q r : QCode) : QCode := qAdd q (qNeg r)
def qDiv (q r : QCode) : QCode := qMul q (qInv r)
def qPow (q : QCode) (n : ℕ) : QCode := (qMul q)^[n] qOne

def qLe (q r : QCode) : Prop :=
  q.1 * (r.2.2 + 1) + r.2.1 * (q.2.2 + 1) ≤
    r.1 * (q.2.2 + 1) + q.2.1 * (r.2.2 + 1)
instance : DecidableRel qLe := fun _ _ => Nat.decLe _ _

@[simp] theorem Qval_zero : Qval qZero = 0 := by norm_num [Qval, qZero]
@[simp] theorem Qval_one : Qval qOne = 1 := by norm_num [Qval, qOne]
@[simp] theorem Qval_nat (n : ℕ) : Qval (qNat n) = n := by simp [Qval, qNat]
@[simp] theorem Qval_neg (q : QCode) : Qval (qNeg q) = -Qval q := by
  dsimp [Qval, qNeg]
  ring

theorem denominator_product (d e : ℕ) :
    (((d + 1) * (e + 1) - 1 : ℕ) : ℚ) + 1 = (d + 1) * (e + 1) := by
  have h : 1 ≤ (d + 1) * (e + 1) := by nlinarith
  rw [Nat.cast_sub h]
  push_cast
  ring

@[simp] theorem Qval_add (q r : QCode) : Qval (qAdd q r) = Qval q + Qval r := by
  simp only [Qval, qAdd, Nat.cast_add, Nat.cast_mul, Nat.cast_one, denominator_product]
  field_simp
  ring

@[simp] theorem Qval_mul (q r : QCode) : Qval (qMul q r) = Qval q * Qval r := by
  simp only [Qval, qMul, Nat.cast_add, Nat.cast_mul, denominator_product]
  rw [div_mul_div_comm]
  congr 1
  ring

@[simp] theorem Qval_inv (q : QCode) : Qval (qInv q) = (Qval q)⁻¹ := by
  unfold qInv
  split_ifs with h h'
  · have hd : 1 ≤ q.1 - q.2.1 := by omega
    have he : ((((q.1 - q.2.1) - 1 : ℕ) : ℚ) + 1) = (q.1 : ℚ) - q.2.1 := by
      rw [Nat.cast_sub hd, Nat.cast_sub (by omega : q.2.1 ≤ q.1)]
      norm_num
    simp only [Qval, Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero, he, inv_div]
  · have hd : 1 ≤ q.2.1 - q.1 := by omega
    have he : ((((q.2.1 - q.1) - 1 : ℕ) : ℚ) + 1) = (q.2.1 : ℚ) - q.1 := by
      rw [Nat.cast_sub hd, Nat.cast_sub (by omega : q.1 ≤ q.2.1)]
      norm_num
    simp only [Qval, Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_sub, he, inv_div]
    rw [← neg_sub (q.1 : ℚ) q.2.1, div_neg, neg_div, neg_neg]
  · have he : q.1 = q.2.1 := by omega
    simp [Qval, qZero, he]

@[simp] theorem Qval_sub (q r : QCode) : Qval (qSub q r) = Qval q - Qval r := by
  simp [qSub, sub_eq_add_neg]
@[simp] theorem Qval_div (q r : QCode) : Qval (qDiv q r) = Qval q / Qval r := by
  simp [qDiv, div_eq_mul_inv]
@[simp] theorem Qval_pow (q : QCode) (n : ℕ) : Qval (qPow q n) = Qval q ^ n := by
  induction n with
  | zero => simp [qPow]
  | succ n ih =>
    simp only [qPow, Function.iterate_succ_apply', Qval_mul]
    rw [← qPow, ih, pow_succ']

theorem qLe_iff (q r : QCode) : qLe q r ↔ Qval q ≤ Qval r := by
  rw [Qval, Qval, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [qLe]
  have :
      q.1 * (r.2.2 + 1) + r.2.1 * (q.2.2 + 1) ≤
        r.1 * (q.2.2 + 1) + q.2.1 * (r.2.2 + 1) ↔
      (q.1 : ℚ) * (r.2.2 + 1) + r.2.1 * (q.2.2 + 1) ≤
        r.1 * (q.2.2 + 1) + q.2.1 * (r.2.2 + 1) := by norm_cast
  rw [this]
  constructor <;> intro h <;> nlinarith

theorem Qval_surjective : Function.Surjective Qval := by
  intro q
  let p := q.num.toNat
  let n := (-q.num).toNat
  have hpn : q.num = (p : ℤ) - n := (Int.toNat_sub_toNat_neg q.num).symm
  refine ⟨(p, n, q.den - 1), ?_⟩
  have hd : 1 ≤ q.den := q.pos
  have he : ((q.den - 1 : ℕ) : ℚ) + 1 = q.den := by
    rw [Nat.cast_sub hd]
    norm_num
  rw [Qval, he, ← Int.cast_natCast p, ← Int.cast_natCast n, ← Int.cast_sub, ← hpn]
  exact Rat.num_div_den q

private theorem pr_plus {α} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f a + g a :=
  Primrec.nat_add.comp hf hg
private theorem pr_times {α} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f a * g a :=
  Primrec.nat_mul.comp hf hg

 theorem primrec_qNat : Primrec qNat := (Primrec.id.pair ((Primrec.const 0).pair (.const 0)))
 theorem primrec_qNeg : Primrec qNeg :=
  (Primrec.fst.comp Primrec.snd).pair (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))
 theorem primrec_qAdd : Primrec₂ qAdd := by
  unfold qAdd
  apply Primrec.pair
  · exact pr_plus
      (pr_times (Primrec.fst.comp Primrec.fst)
        (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
      (pr_times (Primrec.fst.comp Primrec.snd)
        (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  apply Primrec.pair
  · exact pr_plus
      (pr_times (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
      (pr_times (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  exact Primrec.nat_sub.comp
    (pr_times (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))) (Primrec.const 1)

 theorem primrec_qMul : Primrec₂ qMul := by
  unfold qMul
  apply Primrec.pair
  · exact pr_plus (pr_times (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (pr_times (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  apply Primrec.pair
  · exact pr_plus
      (pr_times (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
      (pr_times (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd))
  exact Primrec.nat_sub.comp
    (pr_times (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))) (Primrec.const 1)

 theorem primrec_qInv : Primrec qInv := by
  unfold qInv
  apply Primrec.ite (Primrec.nat_lt.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
  · apply Primrec.pair
    · exact Primrec.succ.comp (Primrec.snd.comp Primrec.snd)
    apply Primrec.pair (Primrec.const 0)
    exact Primrec.nat_sub.comp
      (Primrec.nat_sub.comp Primrec.fst (Primrec.fst.comp Primrec.snd)) (Primrec.const 1)
  apply Primrec.ite (Primrec.nat_lt.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
  · apply Primrec.pair (Primrec.const 0)
    apply Primrec.pair (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
    exact Primrec.nat_sub.comp
      (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd) Primrec.fst) (Primrec.const 1)
  exact Primrec.const qZero

 theorem primrec_qSub : Primrec₂ qSub :=
  primrec_qAdd.comp Primrec.fst (primrec_qNeg.comp Primrec.snd)
 theorem primrec_qDiv : Primrec₂ qDiv :=
  primrec_qMul.comp Primrec.fst (primrec_qInv.comp Primrec.snd)
 theorem primrec_qPow : Primrec₂ qPow := by
  exact Primrec.nat_iterate Primrec.snd (Primrec.const qOne)
    (primrec_qMul.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)

 theorem primrec_qLe : PrimrecRel qLe := by
  exact Primrec.nat_le.comp
    (pr_plus
      (pr_times (Primrec.fst.comp Primrec.fst)
        (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
      (pr_times (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
    (pr_plus
      (pr_times (Primrec.fst.comp Primrec.snd)
        (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
      (pr_times (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))

def qAbs (q : QCode) : QCode := if qLe qZero q then q else qNeg q

@[simp] theorem Qval_abs (q : QCode) : Qval (qAbs q) = |Qval q| := by
  unfold qAbs
  split_ifs with h
  · rw [abs_of_nonneg (by simpa only [qLe_iff, Qval_zero] using h)]
  · rw [Qval_neg, abs_of_neg (lt_of_not_ge (by simpa only [qLe_iff, Qval_zero] using h))]

theorem primrec_qAbs : Primrec qAbs :=
  Primrec.ite (primrec_qLe.comp (.const qZero) .id) .id primrec_qNeg

theorem primrec_factorial : Primrec Nat.factorial := by
  have hp : Primrec (Nat.rec 1 (fun n s => (n + 1) * s)) :=
    Primrec.nat_rec₁ 1 (Primrec.nat_mul.comp (Primrec.succ.comp Primrec.fst) Primrec.snd)
  apply hp.of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih => dsimp; rw [ih, Nat.factorial_succ]

def qTaylor (q : QCode) (n : ℕ) : QCode :=
  ((List.range n).map fun m => qDiv (qPow q m) (qNat m.factorial)).foldr qAdd qZero

@[simp] theorem Qval_taylor (q : QCode) (n : ℕ) :
    Qval (qTaylor q n) = ∑ m ∈ Finset.range n, Qval q ^ m / m.factorial := by
  have hsum (l : List QCode) : Qval (l.foldr qAdd qZero) = (l.map Qval).sum := by
    induction l with
    | nil => simp
    | cons q l ih => simp [ih]
  rw [qTaylor, hsum, List.map_map]
  simp only [Function.comp_def, Qval_div, Qval_pow, Qval_nat]
  simpa only [List.toFinset_range] using (List.sum_toFinset (fun m => Qval q ^ m / m.factorial) (List.nodup_range (n := n))).symm

theorem primrec_qTaylor : Primrec₂ qTaylor := by
  unfold Primrec₂ qTaylor
  apply Primrec.list_foldr (h := fun _ p => qAdd p.1 p.2)
  · exact Primrec.list_map (Primrec.list_range.comp Primrec.snd)
      (primrec_qDiv.comp (primrec_qPow.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
        (primrec_qNat.comp (primrec_factorial.comp Primrec.snd)))
  · exact Primrec.const qZero
  exact primrec_qAdd.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)

def expStop (r : QCode × ℕ) (m : ℕ) : Prop :=
  qLe (qDiv (qAbs r.1) (qNat (m + 1))) (qInv (qNat 2)) ∧
    qLe (qMul (qDiv (qPow (qAbs r.1) m) (qNat m.factorial)) (qNat 2))
      (qInv (qNat (r.2 + 1)))

instance : DecidableRel expStop := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

theorem primrec_expStop : PrimrecRel expStop := by
  apply PrimrecPred.and
  · exact primrec_qLe.comp
      (primrec_qDiv.comp (primrec_qAbs.comp (Primrec.fst.comp Primrec.fst))
        (primrec_qNat.comp (Primrec.succ.comp Primrec.snd))) (Primrec.const _)
  exact primrec_qLe.comp
    (primrec_qMul.comp
      (primrec_qDiv.comp
        (primrec_qPow.comp (primrec_qAbs.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
        (primrec_qNat.comp (primrec_factorial.comp Primrec.snd))) (Primrec.const _))
    (primrec_qInv.comp (primrec_qNat.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))))

theorem expStop_iff (q : QCode) (N m : ℕ) : expStop (q, N) m ↔
    |(Qval q : ℝ)| / (m + 1) ≤ 1 / 2 ∧
    |(Qval q : ℝ)| ^ m / m.factorial * 2 ≤ ((N : ℝ) + 1)⁻¹ := by
  simp only [expStop, qLe_iff, Qval_div, Qval_abs, Qval_nat, Qval_inv,
    Qval_mul, Qval_pow]
  rw [← Rat.cast_le (K := ℝ), ← Rat.cast_le (K := ℝ)]
  push_cast
  norm_num

theorem exists_expStop (r : QCode × ℕ) : ∃ m, expStop r m := by
  let x : ℝ := Qval r.1
  have htail : Filter.Tendsto (fun m : ℕ => |x| ^ m / m.factorial * 2)
      Filter.atTop (nhds 0) := by
    simpa using (Real.summable_pow_div_factorial |x|).tendsto_atTop_zero.mul_const 2
  have hp : (0 : ℝ) < ((r.2 : ℝ) + 1)⁻¹ := by positivity
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 (htail.eventually_lt_const hp)
  obtain ⟨M : ℕ, hM⟩ := exists_nat_gt (2 * |x|)
  refine ⟨max K M, (expStop_iff r.1 r.2 _).2 ⟨?_, (hK _ (le_max_left ..)).le⟩⟩
  rw [div_le_iff₀ (by positivity)]
  have hm : (M : ℝ) ≤ (max K M : ℕ) := by exact_mod_cast le_max_right K M
  dsimp [x] at hM
  linarith

noncomputable def qExp (r : QCode × ℕ) : QCode := qTaylor r.1 (Nat.find (exists_expStop r))

theorem computable_qExp : Computable qExp :=
  primrec_qTaylor.to_comp.comp Computable.fst (Computable.find primrec_expStop.computablePred exists_expStop)

theorem real_exp_taylor_bound (x : ℝ) (n : ℕ) (h : |x| / (n + 1) ≤ 1 / 2) :
    |Real.exp x - ∑ m ∈ Finset.range n, x ^ m / m.factorial| ≤
      |x| ^ n / n.factorial * 2 := by
  have hc := Complex.exp_bound' (x := (x : ℂ)) (n := n) (by simpa [Real.norm_eq_abs] using h)
  rw [← Complex.ofReal_exp] at hc
  have he : (∑ m ∈ Finset.range n, (x : ℂ) ^ m / (m.factorial : ℂ)) =
      ((∑ m ∈ Finset.range n, x ^ m / m.factorial : ℝ) : ℂ) := by push_cast; rfl
  rw [he, ← Complex.ofReal_sub, Complex.norm_real] at hc
  simpa [Real.norm_eq_abs] using hc

theorem qExp_error (q : QCode) (N : ℕ) :
    |Real.exp (Qval q) - (Qval (qExp (q, N)) : ℝ)| ≤ ((N : ℝ) + 1)⁻¹ := by
  have h := (expStop_iff q N (Nat.find (exists_expStop (q, N)))).1
    (Nat.find_spec (exists_expStop (q, N)))
  rw [qExp, Qval_taylor]
  push_cast
  exact (real_exp_taylor_bound _ _ h.1).trans h.2

end BoxTransport.Routing.Computation

open scoped BigOperators ContDiff
namespace BoxTransport.Routing.Computation

noncomputable def flatTerm (m : ℕ) (x : ℝ) : ℝ := x⁻¹ ^ m * expNegInvGlue x

@[simp] theorem flatTerm_zero_index : flatTerm 0 = expNegInvGlue := by
  funext x
  simp [flatTerm]

theorem flatTerm_zero {m : ℕ} {x : ℝ} (hx : x ≤ 0) : flatTerm m x = 0 := by
  simp [flatTerm, expNegInvGlue.zero_of_nonpos hx]

theorem contDiff_flatTerm (m : ℕ) : ContDiff ℝ ∞ (flatTerm m) := by
  convert! (expNegInvGlue.contDiff_polynomial_eval_inv_mul (n := ⊤) (Polynomial.X ^ m)) using 1
  ext x
  simp only [flatTerm, Polynomial.eval_pow, Polynomial.eval_X]

theorem hasDerivAt_flatTerm (m : ℕ) (x : ℝ) :
    HasDerivAt (flatTerm m) (flatTerm (m + 2) x - m * flatTerm (m + 1) x) x := by
  convert expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (Polynomial.X ^ m) x using 1
  · ext y
    simp [flatTerm]
  · cases m with
    | zero => simp [flatTerm]
    | succ m =>
      rw [Polynomial.derivative_X_pow]
      simp only [flatTerm, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_sub, Polynomial.eval_C, Nat.succ_sub_one, Nat.cast_succ]
      simp only [pow_succ]
      ring

theorem flatTerm_nonneg (m : ℕ) (x : ℝ) : 0 ≤ flatTerm m x := by
  by_cases hx : x ≤ 0
  · rw [flatTerm_zero hx]
  · unfold flatTerm
    have : 0 ≤ x⁻¹ := inv_nonneg.mpr (le_of_not_ge hx)
    exact mul_nonneg (pow_nonneg this _) (expNegInvGlue.nonneg x)

theorem flatTerm_bound (m : ℕ) (x : ℝ) : |flatTerm m x| ≤ (m.factorial : ℝ) := by
  rw [abs_of_nonneg (flatTerm_nonneg m x)]
  by_cases hx : x ≤ 0
  · rw [flatTerm_zero hx]
    positivity
  have hv : 0 ≤ x⁻¹ := le_of_lt (inv_pos.mpr (lt_of_not_ge hx))
  have hterm : x⁻¹ ^ m / (m.factorial : ℝ) ≤ Real.exp x⁻¹ := by
    apply le_trans _ (Real.sum_le_exp_of_nonneg hv (m + 1))
    exact Finset.single_le_sum (f := fun i : ℕ => x⁻¹ ^ i / (i.factorial : ℝ))
      (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self m))
  have hm : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hmul := mul_le_mul_of_nonneg_right ((div_le_iff₀ hm).mp hterm)
    (Real.exp_pos (-x⁻¹)).le
  have he : Real.exp x⁻¹ * Real.exp (-x⁻¹) = 1 := by rw [← Real.exp_add]; simp
  unfold flatTerm expNegInvGlue
  rw [ite_eq_right hx]
  nlinarith [he]

def flatLipschitzBound (m : ℕ) : ℕ := (m + 2).factorial + m * (m + 1).factorial

theorem flatTerm_lipschitz (m : ℕ) : LipschitzWith (flatLipschitzBound m) (flatTerm m) := by
  apply lipschitzWith_of_nnnorm_deriv_le ((contDiff_flatTerm m).differentiable (by simp))
  intro x
  rw [(hasDerivAt_flatTerm m x).deriv]
  apply NNReal.coe_le_coe.mp
  simp only [coe_nnnorm, Real.norm_eq_abs, flatLipschitzBound,
    Nat.cast_add, Nat.cast_mul]
  calc
    |flatTerm (m + 2) x - (m : ℝ) * flatTerm (m + 1) x| ≤
        |flatTerm (m + 2) x| + |(m : ℝ) * flatTerm (m + 1) x| := abs_sub _ _
    _ ≤ (m + 2).factorial + (m : ℝ) * (m + 1).factorial := by
      simp only [abs_mul, Nat.abs_cast]
      
      gcongr <;> exact flatTerm_bound _ _

end BoxTransport.Routing.Computation

open scoped BigOperators ContDiff
namespace BoxTransport.Routing.Computation

theorem computable_ite {α β} [Primcodable α] [Primcodable β]
    {p : α → Prop} [DecidablePred p] {f g : α → β}
    (hp : ComputablePred p) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => if p a then f a else g a) := by
  simpa only [Bool.cond_decide] using Computable.cond hp.decide hf hg

def qBound (q : QCode) : ℕ := q.1 + q.2.1

theorem Qval_bound (q : QCode) : |Qval q| ≤ qBound q := by
  rw [Qval, abs_div, abs_of_pos (by positivity : (0 : ℚ) < q.2.2 + 1)]
  have h : |(q.1 : ℚ) - q.2.1| ≤ (q.1 : ℚ) + q.2.1 := by
    simpa only [Nat.abs_cast] using abs_sub (q.1 : ℚ) q.2.1
  apply le_trans (div_le_self (abs_nonneg _) (by norm_cast; omega))
  simpa [qBound] using h

theorem primrec_qBound : Primrec qBound :=
  Primrec.nat_add.comp Primrec.fst (Primrec.fst.comp Primrec.snd)

noncomputable def qFlat (r : ℕ × QCode × ℕ) : QCode :=
  if qLe r.2.1 qZero then qZero else
    let w := qPow (qInv r.2.1) r.1
    qMul w (qExp (qNeg (qInv r.2.1), (r.2.2 + 1) * (qBound w + 1)))

theorem computable_qFlat : Computable qFlat := by
  unfold qFlat
  apply computable_ite (primrec_qLe.comp (Primrec.fst.comp Primrec.snd) (.const qZero)).computablePred
  · exact .const qZero
  have hw : Primrec fun r : ℕ × QCode × ℕ => qPow (qInv r.2.1) r.1 :=
    primrec_qPow.comp (primrec_qInv.comp (Primrec.fst.comp Primrec.snd)) Primrec.fst
  exact primrec_qMul.to_comp.comp hw.to_comp (computable_qExp.comp
    ((primrec_qNeg.comp (primrec_qInv.comp (Primrec.fst.comp Primrec.snd))).pair
      (Primrec.nat_mul.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.succ.comp (primrec_qBound.comp hw)))).to_comp)

theorem qFlat_error (m : ℕ) (q : QCode) (N : ℕ) :
    |flatTerm m (Qval q) - (Qval (qFlat (m, q, N)) : ℝ)| ≤ ((N : ℝ) + 1)⁻¹ := by
  by_cases hq : qLe q qZero
  · rw [qFlat, ite_eq_left hq, Qval_zero, Rat.cast_zero, sub_zero,
      flatTerm_zero (by exact_mod_cast (show Qval q ≤ 0 from by simpa using (qLe_iff q qZero).1 hq)), abs_zero]
    positivity
  have hp : (0 : ℝ) < Qval q := by
    exact_mod_cast lt_of_not_ge (by simpa only [qLe_iff, Qval_zero] using hq)
  let w := qPow (qInv q) m
  let B := qBound w
  have hB : |(Qval w : ℝ)| ≤ (B : ℝ) := by exact_mod_cast Qval_bound w
  have hw : (Qval w : ℝ) = (Qval q : ℝ)⁻¹ ^ m := by simp [w]
  have hx : (Qval (qNeg (qInv q)) : ℝ) = -(Qval q : ℝ)⁻¹ := by simp
  have he := qExp_error (qNeg (qInv q)) ((N + 1) * (B + 1))
  rw [hx] at he
  rw [qFlat, ite_eq_right hq]
  change |flatTerm m (Qval q) - (Qval (qMul w
    (qExp (qNeg (qInv q), (N + 1) * (B + 1)))) : ℝ)| ≤ _
  rw [Qval_mul, Rat.cast_mul]
  have ht : flatTerm m (Qval q) = (Qval w : ℝ) * Real.exp (-(Qval q : ℝ)⁻¹) := by
    simp only [flatTerm, expNegInvGlue, not_le.mpr hp, ↓reduceIte, hw]
  rw [ht, ← mul_sub, abs_mul]
  apply le_trans (mul_le_mul hB he (abs_nonneg _) (Nat.cast_nonneg B))
  push_cast
  rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  have hn : (0 : ℝ) < N + 1 := by positivity
  apply (mul_le_mul_iff_right₀ hn).mp
  field_simp
  nlinarith

end BoxTransport.Routing.Computation

end

end OAI
