import OAI.NumberTheory.DukePrimeDegree.Entropy.ReturnPartitionEntropy

namespace OAI

/-! # Exponential refinements of the first-return partition

A return level may be subdivided into exponentially many transverse cells.
The logarithmic cell count is paid for by the return-time first moment.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma finiteShannon_le_mass_log_card {α : Type*} [Fintype α]
    (p : α → ℝ) (hp : ∀ i, 0 ≤ p i) :
    finiteShannon p ≤ Real.negMulLog (∑ i, p i) +
      (∑ i, p i)*Real.log (Fintype.card α) := by
  classical
  let s := ∑ i, p i
  have hs : 0 ≤ s := Finset.sum_nonneg (fun i _ => hp i)
  by_cases hz : s=0
  · have hzero (i : α) : p i=0 := by
      apply le_antisymm _ (hp i)
      have hi := Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
      exact hi.trans_eq hz
    simp only [finiteShannon,hzero,Real.negMulLog_zero,Finset.sum_const_zero,
      zero_mul,add_zero,le_refl]
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hz)
  have hn : 0 < Fintype.card α := by
    by_contra hn
    have : IsEmpty α := Fintype.card_eq_zero_iff.mp (by omega)
    exact hz (by simp [s])
  have hnr : (0:ℝ) < Fintype.card α := by exact_mod_cast hn
  let q := s/(Fintype.card α:ℝ)
  have hq : 0 < q := div_pos hspos hnr
  have H : finiteShannon p ≤ ∑ i : α, (-p i*Real.log q+q-p i) :=
    Finset.sum_le_sum fun i _ => negMulLog_le_cross (hp i) hq.le
      (fun h => (hq.ne' h).elim)
  apply H.trans_eq
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,
    ←Finset.sum_mul,Finset.sum_neg_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  change -s*Real.log q+(Fintype.card α:ℝ)*q-s=Real.negMulLog s+s*Real.log (Fintype.card α)
  rw [show (Fintype.card α:ℝ)*q=s by dsimp [q]; field_simp]
  rw [show Real.log q=Real.log s-Real.log (Fintype.card α) by
    exact Real.log_div hz hnr.ne']
  unfold Real.negMulLog
  ring

/-- The exact entropy budget used by exponentially refined return cells. -/
theorem refined_return_information_summable
    (K : ℕ → ℕ) (p : ∀ n, Fin (K n) → ℝ) (mass : ℕ → ℝ)
    (hp : ∀ n i, 0 ≤ p n i) (hm : ∀ n, ∑ i, p n i=mass n)
    (hm1 : ∀ n, mass n ≤ 1)
    (hmean : Summable (fun n : ℕ => (n+1:ℝ)*mass n))
    (C : ℝ) (hcard : ∀ n, Real.log (K n) ≤ C*(n+1)) :
    Summable (fun z : Σ n : ℕ, Fin (K n) => Real.negMulLog (p z.1 z.2)) := by
  have hm0 (n : ℕ) : 0 ≤ mass n := by rw [←hm n]; exact Finset.sum_nonneg (fun i _ => hp n i)
  have hp1 (n : ℕ) (i : Fin (K n)) : p n i ≤ 1 := by
    apply le_trans _ (hm1 n)
    rw [←hm n]
    exact Finset.single_le_sum (fun j _ => hp n j) (Finset.mem_univ i)
  have hs := (summable_information_of_first_moment mass hm0 hm1 hmean).add
    (hmean.mul_right C)
  have hb : Summable (fun n => finiteShannon (p n)) := by
    apply Summable.of_nonneg_of_le
      (fun n => Finset.sum_nonneg (fun i _ => Real.negMulLog_nonneg (hp n i) (hp1 n i))) _ hs
    intro n
    have H := finiteShannon_le_mass_log_card (p n) (hp n)
    rw [hm n,Fintype.card_fin] at H
    calc
      _ ≤ Real.negMulLog (mass n)+mass n*Real.log (K n) := H
      _ ≤ Real.negMulLog (mass n)+((n+1:ℝ)*mass n)*C := by
        have hh := mul_le_mul_of_nonneg_left (hcard n) (hm0 n)
        nlinarith
  apply (summable_sigma_of_nonneg
    (fun z : Σ n : ℕ, Fin (K n) => Real.negMulLog_nonneg (hp z.1 z.2) (hp1 z.1 z.2))).mpr
  refine ⟨fun n => hasSum_fintype (fun i => Real.negMulLog (p n i)) |>.summable,?_⟩
  simpa only [tsum_fintype,finiteShannon] using hb

end DukePrimeDegree

end

end OAI
