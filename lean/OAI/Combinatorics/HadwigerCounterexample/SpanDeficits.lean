import OAI.Combinatorics.HadwigerCounterexample.CoverSpaces

namespace OAI

/-! # Span Deficits -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset
open scoped BigOperators
variable {p : Shape} {N : ℕ} {I J K : Type} [Fintype I] [Fintype J] [Fintype K]

/-- Loss of rank from overlapping mode spans. -/
private theorem colsum_bound (A B : Mat I J) :
    A.rank+B.rank ≤ (A+B).rank+dim (colSp A⊓colSp B : Submodule _ _)+
      dim (colSp Aᵀ ⊓ colSp Bᵀ : Submodule _ _) := by
  classical
  obtain ⟨X,Y,hX,hY,hA⟩ := rank_product A
  obtain ⟨S,T,hS,hT,hB⟩ := rank_product B
  have h := rank_ge_mul (fromCols X S) (fromRows Y T)
  have he {I J U : Type} [Fintype I] [Fintype U] [Fintype J] (A : Mat I U) {B : Mat U J}
      (h : Function.Surjective B.mulVec) :
      colSp (A*B) = colSp A := by
    rw [colSp,mulVecLin_mul,LinearMap.range_comp,
      LinearMap.range_eq_top.mpr (show Function.Surjective B.mulVecLin from h),Submodule.map_top]
  have hc := colSp_join X S
  have hr := colSp_join Yᵀ Tᵀ
  rw [← he X hY,← he S hT,hA,hB] at hc
  rw [← he Yᵀ (transpose_surj_iff.mpr hX),←he Tᵀ (transpose_surj_iff.mpr hS),←transpose_mul,
    ←transpose_mul,hA,hB] at hr
  have h1 := finrank_sup_add_finrank_inf_eq (colSp A) (colSp B)
  rw [←hc] at h1
  have h2 := finrank_sup_add_finrank_inf_eq (colSp Aᵀ) (colSp Bᵀ)
  rw [←hr] at h2
  rw [fromCols_mul_fromRows,hA,hB,Fintype.card_sum,Fintype.card_fin,Fintype.card_fin,
    ← Matrix.rank_transpose (fromRows _ _), transpose_fromRows] at h
  change (fromCols X S).rank+dim (_ : Submodule _ _) = A.rank+B.rank at h1
  change (fromCols Yᵀ Tᵀ).rank+dim (_ : Submodule _ _)=Aᵀ.rank+Bᵀ.rank at h2
  rw [Matrix.rank_transpose,Matrix.rank_transpose] at h2
  omega

theorem cdim_mono {a b : Cov p N} (h : a≤b) : cdim p a ≤ cdim p b :=
  Finset.sum_le_sum fun i _ => Submodule.finrank_mono (h i)
@[simp] theorem cdim_bot {p N} : cdim p (N:=N) ⊥=0 := by
  unfold cdim
  refine Finset.sum_eq_zero fun i _ => ?_
  exact finrank_bot _ _

theorem cdim_sup_inf (a b : Cov p N) : cdim p (a⊔b)+cdim p (a⊓b)=cdim p a+cdim p b := by
  unfold cdim
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => finrank_sup_add_finrank_inf_eq (a i) (b i)

def tax (p : Shape) {N} (a b : Cov p N) := cdim p (a⊔b)-cdim p a

theorem tax_before (a b : Cov p N) : cdim p a+tax p a b=cdim p (a⊔b) :=
  Nat.add_sub_of_le (cdim_mono (p:=p) le_sup_left)

theorem tax_lost (a b : Cov p N) : tax p a b+cdim p (a⊓b)=cdim p b := by
  have h := cdim_sup_inf (p:=p) a b; rw [←tax_before (p:=p)] at h
  omega

theorem tax_antitone (p : Shape) {N} (a b c : Cov p N) (h : a≤b) :
    tax p b c≤ tax p a c := by
  have he := cdim_mono (p:=p) (inf_le_inf h (show c≤c from le_rfl))
  have hg := tax_lost (p:=p) a c
  have hh := tax_lost (p:=p) b c
  omega

theorem matter_pair {x y : Ambient p N} {a b : Cov p N}
    (hx : matter p x ≤ a) (hy : matter p y ≤ b) :
    matter p (x+y) ≤ a⊔b ∧
      epoch p x+ epoch p y+cdim p (a⊔b) ≤ epoch p (x+y)+cdim p a+cdim p b := by
  classical
  have h (i) : x i∈box (a (i,true)) (a (i,false)) :=
    (box_mem ..).mpr ⟨hx (i,true),hx (i,false)⟩
  have h' i : y i ∈box (b (i,true)) (b (i,false)) :=
    (box_mem ..).mpr ⟨hy (i,true),hy (i,false)⟩
  constructor
  · intro i
    let C := a⊔b
    have he : x i.1 + y i.1∈box (C (i.1,true)) (C (i.1,false)) :=
      Submodule.add_mem _ ((box_le le_sup_left le_sup_left) (h _))
        ((box_le le_sup_right le_sup_right) (h' _))
    have hg := (box_mem ..).mp he
    cases i with | mk i j => cases j; exact hg.2; exact hg.1
  · have hg (i) : (x i).rank+(y i).rank ≤ (x i+y i).rank+dim ((a⊓b) (i,true))+
        dim ((a⊓b) (i,false)) := by
      refine (colsum_bound (x i) (y i)).trans ?_
      have he c := Submodule.finrank_mono (inf_le_inf (hx (i,c)) (hy (i,c)))
      exact Nat.add_le_add (Nat.add_le_add_left (he true) _) (he false)
    have he := cdim_sup_inf (p:=p) a b
    have hh := (Finset.sum_le_sum (s:=Finset.univ) fun i _ => hg i)
    simp only [Finset.sum_add_distrib] at hh
    change epoch _ x+epoch _ y≤ epoch p (x+y)+cdSign p _ true+cdSign p _ false at hh
    rw [Nat.add_assoc,← cdim_sign] at hh
    omega

def chopped (p : Shape) {N} (a b : Cov p N) : Cov p N :=
  fun z => chopSpace (a z) (b z)

theorem matter_erased {a : Cov p N} (x : Ambient p N) :
    matter p (erased p a x) ≤ chopped p a (matter p x) := by
  intro z
  let D := matter p x
  have h : x z.1∈box (D (z.1,true)) (D (z.1,false)) :=
    (box_mem ..).mpr ⟨le_rfl,le_rfl⟩
  have he := (box_mem ..).mp (lift_mem_box (chop (a (z.1,true))) (chop (a (z.1,false))) h)
  cases z with | mk e c => cases c; exact he.2; exact he.1

theorem cdim_chopped (p : Shape) {N} (a b : Cov p N) :
    cdim p (chopped p a b)=tax p a b := by
  have h := tax_before (p:=p) a b
  have he : cdim p a+cdim p (chopped p a b)=cdim p (a⊔b) := by
    unfold cdim
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => chopSpace_rank ..
  exact Nat.add_left_cancel (he.trans h.symm)

def arrange (p : Shape) {N J} (f : J→ Ambient p N) (r : Finset J) := r.sup (matter p ∘ f)

theorem epoch_charge {J} (f : J→Ambient p N) (s : Cov p N) (r : Finset J) :
    (matter p (∑ i∈r, erased p s (f i))) ≤ chopped p s (arrange p f r) ∧
      ((∑ i∈r,epoch p (erased p s (f i)))+tax p s (arrange p f r) ≤
        epoch p (∑ i∈r, erased p s (f i)) + ∑ i∈r,tax p s (matter p (f i))) := by
  classical
  induction r using Finset.induction with
  | empty =>
    have he : matter p (N:=N) (0:Ambient p N)=⊥ := by funext i; simp [matter,colSp,Pi.bot_apply]
    simp only [Finset.sum_empty,he,bot_le,true_and,zero_add,add_zero]
    have hi : arrange p f ∅ = ⊥ := Finset.sup_empty
    rw [hi,tax,sup_bot_eq,Nat.sub_self]; exact Nat.zero_le _
  | insert i r hr ih =>
    obtain ⟨hx,hh⟩ := matter_pair (matter_erased (a:=s) (f i)) ih.1
    simp only [Finset.sum_insert hr]
    have he : arrange p f (insert i r)= matter p (f i)⊔arrange p f r :=
      Finset.sup_insert
    have ht : chopped p s (arrange p f (insert i r)) =
        chopped p s (matter p (f i))⊔chopped p s (arrange p f r) := by
      rw [he]
      funext z; exact Submodule.map_sup _ _ _
    rw [ht]
    refine ⟨hx,?_⟩
    rw [← ht, cdim_chopped,cdim_chopped,cdim_chopped] at hh
    have hi := ih.2
    omega

theorem epoch_erased (s : Cov p N) (x : Ambient p N) : epoch p (erased p s x) ≤ epoch p x :=
  Finset.sum_le_sum fun i _ => rank_lift_le _ _ (x i)

theorem epoch_eq_zero (x : Ambient p N) : epoch p x=0 ↔ x=0 := by
  classical
  constructor
  · intro h
    funext i
    have he := Finset.single_le_sum (fun i _ => Nat.zero_le (x i).rank)
      (Finset.mem_univ i)
    have ht : (x i).rank=0 := Nat.eq_zero_of_le_zero (by simpa only [epoch] using h ▸ he)
    obtain ⟨A,B,hA,hB,hZ⟩ := rank_product (x i)
    have : IsEmpty (Fin (x i).rank) := ht ▸ Fin.isEmpty'
    apply hZ.symm.trans
    ext; simp [Matrix.mul_apply]
  intro h
  rw [h,epoch]; simp

end HadwigerCounterexample

end

end OAI
