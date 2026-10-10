import OAI.Analysis.FourierLLogL.Finite.Mixture
/-! # Product laws -/
open Set Function Filter
open scoped BigOperators
noncomputable section

namespace OAI

namespace FourierLLogL.Law
open Real
universe u u' v v' w w'
variable {ι : Type u} {τ : Type u'} {α : Type v} {β : Type v'} {γ : Type w} {η : Type w'}
  [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ]
  [Fintype α] [Fintype β] [Fintype γ] [Fintype η]

def pack (P : ι → Law α) : Law (ι → α) :=
  ⟨fun x => ∏ i, P i (x i), fun x => Finset.prod_nonneg (fun i _ => (P i).nonneg _), by
    rw [← Fintype.prod_sum (fun i x => P i x)]
    simp [Law.total]⟩

lemma pack_apply (P : ι → Law α) (x : ι → α) :
    pack P x = ∏ i, P i (x i) := rfl

lemma pack_pos (P : ι → Law α) (x : ι → α) :
    0 < pack P x ↔ ∀ i, 0 < P i (x i) := by
  rw [pack_apply]
  constructor
  · intro h i
    obtain hx|hx := eq_or_lt_of_le ((P i).nonneg (x i))
    · rw [Finset.prod_eq_zero (Finset.mem_univ i) hx.symm] at h
      exact (lt_irrefl _ h).elim
    · exact hx
  · exact fun h => Finset.prod_pos fun i _ => h i

lemma pack_Ex_prod (P : ι → Law α) (f : ι → α → ℝ) :
    (pack P).Ex (fun x => ∏ i, f i (x i)) = ∏ i, (P i).Ex (f i) := by
  simp_rw [Ex, pack_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => P i x * f i x)).symm

lemma ext_by_products {P Q : Law (ι → α)}
    (h : ∀ f : ι → α → ℝ, P.Ex (fun x => ∏ i, f i (x i)) = Q.Ex fun x => ∏ i, f i (x i)) :
    P = Q := by
  classical
  apply Law.ext
  intro x
  let f i (a : α) : ℝ := if a = x i then 1 else 0
  have heq (y : ι → α) : (∏ i, f i (y i)) = if y = x then 1 else 0 := by
    split_ifs with H
    · subst y; simp [f]
    · have : ∃ i, y i ≠ x i := by contrapose! H; exact funext H
      obtain ⟨i,hi⟩ := this
      exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
  have HH := h f
  simp_rw [heq] at HH
  simpa [Ex, mul_ite] using HH

lemma sendPack (P : ι → Law α) (X : ι → α → β) :
    (pack P).send (fun x i => X i (x i)) = pack (fun i => (P i).send (X i)) := by
  apply ext_by_products; intro f
  rw [Ex_send,pack_Ex_prod]
  have h := pack_Ex_prod P (fun i a => f i (X i a))
  simp_rw [Ex_send]
  exact h

lemma marginalPack (P : ι → Law α) (i : ι) :
    (pack P).send (fun x => x i) = P i := by
  apply ext_of_Ex; intro f
  let F (j : ι) := if j=i then f else fun _ : α => (1:ℝ)
  have h := pack_Ex_prod P F
  have h1 (x : ι → α) : (∏ j, F j (x j)) = f (x i) := by
    rw [Finset.prod_eq_single i] <;> intros <;> simp_all [F]
  have h2 : (∏ j, (P j).Ex (F j)) = (P i).Ex f := by
    rw [Finset.prod_eq_single i] <;> intros <;> simp_all [F, Ex_const]
  rw [Ex_send]; simp_rw [h1,h2] at h; exact h

lemma Ex_pack_proj (P : ι → Law α) (i : ι) (f : α → ℝ) :
    (pack P).Ex (fun x => f (x i)) = (P i).Ex f := by
  rw [← Ex_send (pack P) (fun x => x i), marginalPack]

lemma sendPack_embedding (P : ι → Law α) (s : τ → ι) (hs : Injective s) :
    (pack P).send (fun x i => x (s i)) = pack (fun i => P (s i)) := by
  classical
  apply ext_by_products; intro f
  let F := extend s f (fun _ _ => 1)
  have h1 (i : τ) : F (s i) = f i := hs.extend_apply _ _ _
  have h2 (i : ι) (hi : i ∉ range s) : F i = fun _ => 1 :=
    extend_apply' _ _ _ hi
  have H (a : ι → ℝ) (h : ∀ i, i ∉ range s → a i = 1) :
      ∏ i, a i = ∏ i, a (s i) := by
    rw [← Finset.prod_image hs.injOn]
    apply (Finset.prod_subset (Finset.subset_univ _) ?_).symm
    intro i _ hi; apply h; simpa using hi
  have h3 (x : ι → α) :
      (∏ i, F i (x i)) = ∏ i, f i (x (s i)) := by
    rw [H]; simp_rw [h1]; intro i hi; rw [h2 i hi]
  have h4 :
      (∏ i, (P i).Ex (F i)) = ∏ i, (P (s i)).Ex (f i) := by
    rw [H]; simp_rw [h1]; intro i hi; rw [h2 i hi, Ex_const]
  have h := pack_Ex_prod P F
  rw [Ex_send,pack_Ex_prod]; simp_rw [h3,h4] at h; exact h

lemma crossE_pack {P : Law (ι → α)} {Q : ι → Law α}
    (h : P.dominated (pack Q)) :
    P.crossE (pack Q) = ∑ i, (P.send (fun x => x i)).crossE (Q i) := by
  have hh (x) (hx : 0 < P x) : -log (pack Q x) = ∑ i, -log (Q i (x i)) := by
    rw [pack_apply, log_prod, Finset.sum_neg_distrib]
    intro i _
    exact ((pack_pos Q x).mp (h x hx) i).ne'
  unfold crossE
  have hi : P.Ex (fun x => -log (pack Q x)) =
      P.Ex fun x => ∑ i, -log (Q i (x i)) := P.Ex_congr_mem hh
  rw [hi, Ex_finset_sum]
  simp_rw [Ex_send]

lemma pack_kl {P Q : ι → Law α} (h : ∀ i, (P i).dominated (Q i)) :
    (pack P).kl (pack Q) = ∑ i, (P i).kl (Q i) := by
  have h1 : (pack P).dominated (pack Q) := fun x hx =>
    (pack_pos Q _).mpr fun i => h i _ ((pack_pos _ _).mp hx i)
  simp only [kl,entropy,crossE_pack h1,crossE_pack (dominated_refl (pack P)),marginalPack]
  rw [Finset.sum_sub_distrib]

lemma entropy_pack (P : ι → Law α) : (pack P).entropy = ∑ i, (P i).entropy := by
  rw [entropy,crossE_pack (dominated_refl (pack P))]
  simp only [marginalPack, entropy]

lemma entropy_coord_bound (P : Law (ι → α)) :
    P.entropy ≤ ∑ i, P.H (fun x => x i) := by
  let Q i := P.send (fun x => x i)
  have hh : P.dominated (pack Q) := fun x hx => (pack_pos Q _).mpr fun i => P.send_pos _ hx
  refine le_trans (b:=P.crossE (pack Q)) (sub_nonneg.mp (kl_nonneg hh)) ?_
  rw [crossE_pack hh]
  exact le_refl _

lemma H_vec_le (P : Law α) (X : α → ι → β) :
    P.H X ≤ ∑ i, P.H (fun x => X x i) := by
  have h := entropy_coord_bound (P.send X)
  simp only [H_send] at h; exact h

lemma Hcond_vec_le (P : Law α) (X : α → ι → β) (W : α → γ) :
    P.Hcond X W ≤ ∑ i, P.Hcond (fun x => X x i) W := by
  simp_rw [Hcond_after, ← Ex_finset_sum]
  exact Ex_mono _ fun _ => H_vec_le _ _

lemma H_vec_pack (P : ι → Law α) (X : ι → α → β) :
    (pack P).H (fun x i => X i (x i)) = ∑ i, (P i).H (X i) := by
  unfold H
  rw [sendPack P X, entropy_pack]

lemma Hcond_vec_pack (P : ι → Law α) (X : ι → α → β) (W : ι → α → γ) :
    (pack P).Hcond (fun x i => X i (x i)) (fun x i => W i (x i)) =
      ∑ i, (P i).Hcond (X i) (W i) := by
  unfold Hcond
  let Y i x := (X i x,W i x)
  have Heq :
      (pack P).H (fun x => ((fun i => X i (x i)),(fun i => W i (x i)))) =
      (pack P).H (fun x i => Y i (x i)) := by
    refine H_partition _ fun x y => ?_
    simp only [Y, Prod.mk.injEq, funext_iff, forall_and]
  rw [Heq,H_vec_pack P Y,H_vec_pack P W,Finset.sum_sub_distrib]

/-- Attach an independent new observation per row. When the rows of
the initial law are independent, the refined rows remain independent. -/
lemma pack_withNext (P : ι → Law α) (Q : ι → α → Law β) :
    ((pack P).withNext (fun v => pack (fun i => Q i (v i)))).send
      (fun (z : (ι→α)×(ι→β)) i => (z.1 i,z.2 i)) =
      pack (fun i => (P i).withNext (Q i)) := by
  apply ext_by_products; intro f
  rw [Ex_send, Ex_withNext]
  have H (x : ι → α) := pack_Ex_prod (fun i => Q i (x i)) (fun i y => f i (x i,y))
  simp_rw [H]
  rw [pack_Ex_prod P (fun i a => (Q i a).Ex (fun y => f i (a,y))), pack_Ex_prod]
  simp_rw [Ex_withNext]

end FourierLLogL.Law

end OAI
