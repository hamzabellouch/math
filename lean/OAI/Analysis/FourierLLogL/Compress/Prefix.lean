import OAI.Analysis.FourierLLogL.Compress.Blocks
/-! # Entropy increments along a prefix -/

open Function Set Filter
open scoped BigOperators
noncomputable section
namespace OAI

namespace FourierLLogL.Compress
open Law Real
variable {n m : ℕ} {α Ω G : Type} [Fintype α] [Fintype Ω] [Fintype G]

def rateH (P : Law Ω) (X : Ω → Letters n α) (j : ℕ) :=
  if h : j < n then P.Hcond (readLetter X j h) (prefixB X j h.le) else 0

lemma rate_lt (P : Law Ω) (X : Ω → Letters n α) {j : ℕ} (h : j < n) :
    rateH P X j = P.Hcond (readLetter X j h) (prefixB X j h.le) :=
  dite_eq_left h

lemma H_prefix (P : Law Ω) (X : Ω → Letters n α) (l : ℕ) (h : l ≤ n) :
    P.H (prefixB X l h) = ∑ j ∈ Finset.range l, rateH P X j := by
  induction l with
  | zero =>
    rw [prefix_zero, H_constant]; simp
  | succ l ih =>
    have hh := P.H_partition (X:=prefixB X (l+1) h)
      (Y:=fun x => (readLetter X l h x, prefixB X l (by omega) x))
      (by intro x y; simp only [Prod.mk.injEq]; exact prefix_last_partition X l h x y)
    rw [hh,H_pair_chain, ih, Finset.sum_range_succ, rate_lt _ _ h]

lemma H_post_prefix (P : Law Ω) (X : Ω → Letters n α) (j l : ℕ) (h : j+l ≤ n) :
    let W := prefixB X j (by omega)
    (P.send W).Ex (fun w => (P.after W w).H (readBlock X j l h)) =
      ∑ i ∈ Finset.range l, rateH P X (j+i) := by
  intro W
  rw [← Hcond_after,Hcond]
  have H : P.H (prefixB X (j+l) h) = P.H (fun x => (readBlock X j l h x, W x)) := by
    refine P.H_partition fun x y => ?_
    rw [prefix_partition, Prod.mk.injEq]
    exact and_comm
  rw [← H,H_prefix]
  dsimp only [W]
  rw [H_prefix, Finset.sum_range_add]
  ring


private abbrev S := WordSample

lemma conditional_block_exch {P : Law (S n α G)} (hp : exch P)
    {j m} (hh : j+m ≤ n) (w : Letters j α) :
    exch ((P.after (prefixB Prod.fst j (by omega)) w).send (fun p =>
      (readBlock Prod.fst j m hh p,p.2))) := by
  apply exch_subSample_cond hp (offset j m hh) (offset_injective _ _ _)
    (offset 0 j (by omega))
  rintro i ⟨b,hb⟩
  have H := congrArg Fin.val hb
  simp only [offset] at H
  omega

lemma conditional_block_marg {P : Law (S n α G)} (hp : exch P)
    {j m} (hh : j+m ≤ n) (w : Letters j α) (i : Fin m) :
    let R := P.after (prefixB Prod.fst j (by omega)) w
    R.send (fun x => readBlock Prod.fst j m hh x i) =
      R.send (readLetter Prod.fst j (by have := i.isLt; omega)) := by
  intro R
  let i₀ : Fin m := ⟨0,by have := i.isLt; omega⟩
  have he := same_marginal (conditional_block_exch hp hh w) i i₀
  simp only [send_send] at he
  exact he

lemma rate_antitone_succ {P : Law (S n α G)} (hp : exch P)
    {j} (h : j+1 < n) : rateH P Prod.fst (j+1) ≤ rateH P Prod.fst j := by
  let X : S n α G → Letters n α := Prod.fst
  let W := prefixB X j (by omega)
  let V := prefixB X (j+1) h.le
  have H : P.Hcond (readLetter X (j+1) h) W = P.Hcond (readLetter X j (by omega)) W := by
    rw [Hcond_after,Hcond_after]
    have HH (w) := conditional_block_marg hp (j:=j) (m:=2) (by omega) w (1:Fin 2)
    have hEq (w : Letters j α) :
        (P.after W w).send (readLetter X (j+1) h) =
          (P.after W w).send (readLetter X j (by omega)) := HH w
    simp_rw [Law.H,hEq]
  rw [rate_lt _ _ h, rate_lt _ _ (by omega : j < n)]
  change P.Hcond _ V ≤ P.Hcond (readLetter X j _) W
  rw [← H]
  apply Hcond_antitone
  exact fun a b hh => ((prefix_last_partition X j (by omega) a b).mp hh).2

lemma rate_antitone {P : Law (S n α G)} (hp : exch P) :
    Antitone (rateH P Prod.fst) := by
  refine antitone_nat_of_succ_le fun k => ?_
  by_cases h : k+1<n
  · exact rate_antitone_succ hp h
  rw [rateH,dite_eq_right h]
  unfold rateH
  split
  · exact Hcond_nonneg _ _ _
  · exact le_rfl

lemma rate_bdd (P : Law Ω) (X : Ω → Letters n α) (j : ℕ) :
    rateH P X j ≤ log (Fintype.card α) := by
  rw [rateH]
  split
  · exact (Hcond_le_H P _ _).trans (H_card _ _)
  · cases Fintype.card α with
    | zero => simp
    | succ k => apply log_nonneg; simp

/-- The joint divergence of the conditional block from the product of its row marginals. -/
lemma avg_block_kl {P : Law (S n α G)} (hp : exch P)
    {j m} (hh : j+m ≤ n) (hj : j<n) :
    let X : S n α G → Letters n α := Prod.fst
    let W := prefixB X j hj.le
    let V := readBlock X j m hh
    (P.send W).Ex (fun w =>
      let R := P.after W w
      kl (R.send V) (pack (fun _ : Fin m => R.send (readLetter X j hj)))) =
      ∑ i ∈ Finset.range m, (rateH P X j - rateH P X (j+i)) := by
  intro X W V
  let f := readLetter X j hj
  let A (w : Letters j α) := P.after W w
  have hk (w : Letters j α) :
      kl ((A w).send V) (pack (fun _ : Fin m => (A w).send f)) =
        (m:ℝ) * (A w).H f - (A w).H V := by
    have hm (i : Fin m) := conditional_block_marg hp hh w i
    have hm' (i : Fin m) :
        ((A w).send V).send (fun x => x i) = (A w).send f := by rw [send_send]; exact hm i
    have he : dominated ((A w).send V) (pack (fun _ : Fin m => (A w).send f)) := by
      intro x hx
      rw [pack_pos]
      intro i
      rw [← hm' i]; exact send_pos _ _ hx
    rw [kl,crossE_pack he]
    simp_rw [hm']
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rfl
  change (P.send W).Ex (fun w => kl ((A w).send V) (pack (fun _ : Fin m => (A w).send f))) = _
  have h1 : (P.send W).Ex (fun w => (A w).H f) = rateH P X j :=
    (rate_lt P X hj ▸ Hcond_after P f W).symm
  have h2 : (P.send W).Ex (fun w => (A w).H V) = _ := H_post_prefix P X j m hh
  simp_rw [hk,Ex_sub,Ex_lmul,h1,h2,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,
    nsmul_eq_mul]

lemma kl_uniform {α : Type} [Fintype α] [Nonempty α]
    (P : Law (Letters n α)) :
    P.kl (pack (fun _ : Fin n => uniform α)) =
      n*log (Fintype.card α) - P.entropy := by
  have h : P.dominated (pack (fun _ => uniform α)) := by
    intro x _
    rw [pack_pos]
    intro i
    rw [uniform_apply]
    positivity
  unfold kl
  rw [crossE_pack h]
  simp_rw [crossE, uniform_apply, log_inv,neg_neg,Ex_const,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]

lemma sum_deficit (P : Law Ω) [Nonempty α] (X : Ω → Letters n α) :
    ∑ j ∈ Finset.range n, (log (Fintype.card α)-rateH P X j) =
      (P.send X).kl (pack (fun _ => uniform α)) := by
  have h := H_prefix P X n le_rfl
  rw [prefix_all] at h
  rw [Finset.sum_sub_distrib,kl_uniform,← h]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; rfl

end FourierLLogL.Compress

end OAI
