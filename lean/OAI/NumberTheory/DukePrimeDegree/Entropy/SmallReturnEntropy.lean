import OAI.NumberTheory.DukePrimeDegree.Entropy.ReturnPartitionEntropy

namespace OAI

/-! # Small sections have small return-partition entropy

The adjustable geometric reference distribution controls the entropy by
the section mass and the return-time first moment. This quantitative form
allows the transverse-return refinement to have an arbitrarily small
entropy cost.
-/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

lemma return_information_geometric_bound (p : ℕ → ℝ)
    (hp : ∀ n, 0 ≤ p n) (hp1 : ∀ n, p n ≤ 1)
    (hmean : Summable (fun n : ℕ => (n+1:ℝ)*p n))
    {m : ℝ} (hmass : ∑' n, p n ≤ m)
    (hmeanBound : ∑' n : ℕ, (n+1:ℝ)*p n ≤ 1)
    {c r : ℝ} (hc : 0 < c) (hr : 0 < r) (hr1 : r < 1) :
    (∑' n, Real.negMulLog (p n)) ≤ |Real.log c| * m-Real.log r+c*r/(1-r) := by
  have hsum : Summable p := Summable.of_nonneg_of_le hp
    (fun n => by nlinarith [hp n,Nat.cast_nonneg (α := ℝ) n]) hmean
  have hgeom : Summable (fun n : ℕ => c*r^(n+1)) := by
    simpa only [pow_succ',←mul_assoc] using
      (summable_geometric_of_lt_one hr.le hr1).mul_left (c*r)
  have hs := (hsum.mul_left |Real.log c|).add
    ((hmean.mul_left (-Real.log r)).add hgeom)
  have hbound (n : ℕ) : Real.negMulLog (p n) ≤
      |Real.log c| * p n+((-Real.log r)*((n+1:ℝ)*p n)+c*r^(n+1)) := by
    have hq : 0 < c*r^(n+1) := mul_pos hc (pow_pos hr _)
    have H := negMulLog_le_cross (hp n) hq.le (fun h => (hq.ne' h).elim)
    rw [Real.log_mul hc.ne' (pow_pos hr _).ne',Real.log_pow] at H
    have hl : -Real.log c ≤ |Real.log c| := neg_le_abs _
    have hh := mul_le_mul_of_nonneg_right hl (hp n)
    push_cast at H
    nlinarith [hp n]
  have H := (summable_information_of_first_moment p hp hp1 hmean).tsum_le_tsum hbound hs
  have hgeo : (∑' n : ℕ, c*r^(n+1))=c*r/(1-r) := by
    simp only [pow_succ',←mul_assoc,tsum_mul_left,
      tsum_geometric_of_lt_one hr.le hr1,div_eq_mul_inv]
  rw [Summable.tsum_add (hsum.mul_left |Real.log c|)
    ((hmean.mul_left (-Real.log r)).add hgeom),
    Summable.tsum_add (hmean.mul_left (-Real.log r)) hgeom,
    tsum_mul_left,tsum_mul_left,hgeo] at H
  have hm := mul_le_mul_of_nonneg_left hmass (abs_nonneg (Real.log c))
  have ht := mul_le_mul_of_nonneg_left hmeanBound
    (neg_nonneg.mpr (Real.log_nonpos hr.le hr1.le))
  nlinarith

/-- With return-time mean at most one, small section mass makes the whole
return partition, including its complement atom, arbitrarily low entropy. -/
theorem exists_small_mass_return_information_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : ℕ → ℝ,
      (∀ n, 0 ≤ p n) → (∀ n, p n ≤ 1) →
      Summable (fun n : ℕ => (n+1:ℝ)*p n) →
      (∑' n : ℕ, (n+1:ℝ)*p n) ≤ 1 →
      ∀ m : ℝ, 0 ≤ m → m ≤ 1 → m ≤ δ → (∑' n, p n) ≤ m →
        Real.negMulLog (1-m)+(∑' n, Real.negMulLog (p n)) < ε := by
  let r := Real.exp (-ε/4)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  let c := (ε/4)*(1-r)/r
  have hc : 0 < c := div_pos (mul_pos (by linarith) (by linarith)) hr
  let δ := ε/(4*(|Real.log c|+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  refine ⟨δ,hδ,?_⟩
  intro p hp hp1 hmean hmeanBound m hm0 hm1 hmδ hmass
  have H := return_information_geometric_bound p hp hp1 hmean hmass hmeanBound hc hr hr1
  have hcomp : Real.negMulLog (1-m) ≤ m := by
    have h := Real.negMulLog_le_one_sub_self (by linarith : 0 ≤ 1-m)
    linarith
  have hlog : Real.log r = -ε/4 := Real.log_exp _
  have hgeo : c*r/(1-r)=ε/4 := by
    dsimp only [c]
    field_simp [hr.ne',sub_ne_zero.mpr (ne_of_gt hr1)]
  have hδeq : (|Real.log c|+1)*δ=ε/4 := by
    dsimp only [δ]
    field_simp
  have hsmall := mul_le_mul_of_nonneg_left hmδ (by positivity : 0 ≤ |Real.log c|+1)
  rw [hδeq] at hsmall
  rw [hlog,hgeo] at H
  linarith

end DukePrimeDegree

end

end OAI
