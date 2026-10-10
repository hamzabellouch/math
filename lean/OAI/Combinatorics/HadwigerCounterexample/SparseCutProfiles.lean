import OAI.Combinatorics.HadwigerCounterexample.RawFrameLaws

namespace OAI

/-! # Sparse Cut Profiles -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators

variable {p : Shape} {n : ℕ}

theorem Wtag_disabled {l d : Tag p.g} (h : ¬allowed d l) (t : Tag p.g) (i : Fin n)
    {m : Moment p n} (hm : m ∈ Wtag p n l) (s : SelIdx p.b p.j) (r : Row p n) :
    m (s,some (Block.O d t,i)) r = 0 := by
  unfold Wtag at hm
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨s,z,hz,rfl⟩ := hm
    change (selV _ _ _ * z _) * _ = 0
    rw [hz d t h,mul_zero,zero_mul]
  | zero => rfl
  | add x y _ _ hx hy => simp only [Matrix.add_apply,hx,hy,add_zero]
  | smul a x _ h => simp only [Matrix.smul_apply,h,smul_zero]

/-- Intersect W_l over a strict majority. Every O coordinate is forced
to zero and projecting onto the shared variables fixes the matrix. -/
theorem Wtag_majority_star {I : Finset (Tag p.g)}
    (hI : p.g < 2 * I.card) {m : Moment p n} (h : ∀ l ∈ I, m ∈ Wtag p n l) :
    m ∈ Wstar p n := by
  classical
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0 < I.card by omega)
  have hm : m ∈ Wspace p n := Wtag_le a (h a ha)
  have hz (s : SelIdx p.b p.j) (i : Fin n) (d t : Tag p.g) (r : Row p n) :
      m (s,some (Block.O d t,i)) r = 0 := by
    obtain ⟨l,hl,hg⟩ : ∃ l ∈ I, ¬allowed d l := by
      by_contra! he
      have hi := @Finset.card_le_card _ I (Finset.univ.filter (allowed d)) (by
        intro l hl; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he _ hl⟩)
      have hh := card_allowed d
      rw [Fintype.card_subtype] at hh
      have hi' := hi.trans_eq hh
      omega
    exact Wtag_disabled hg _ _ (h _ hl) _ _
  let kB : BaseIdx p.g n → F := fun i => i.1.elim (fun _ => 0) (fun _ => 1)
  let k : Row p n → F := fun i => Option.elim' 1 kB i.2
  let D := Matrix.diagonal k
  let L (z : Base p.g n) := fun i => kB i * z i
  have hL (s z) : D *ᵥ point p s z = point p s (L z) := by
    funext i
    simp only [D,Matrix.mulVec_diagonal]
    rcases i with ⟨s,i⟩
    rcases i with _|i
    · change (1:F)*_ = _
      rw [one_mul]; rfl
    change kB i * (selV _ _ _ * z i) = _ * (kB i * _); rw [mul_left_comm]
  have hx : liftM D D m ∈ Wstar p n := by
    clear h hz
    unfold Wspace at hm
    induction hm using Submodule.span_induction with
    | mem m he =>
      obtain ⟨s,z,rfl⟩ := he
      rw [mom,liftM_outer,hL]
      exact Submodule.subset_span ⟨s,L z,fun d t i => by
        change (0:F)*_=0
        rw [zero_mul],rfl⟩
    | zero => simp only [map_zero,Submodule.zero_mem]
    | add i j _ _ h g => rw [map_add]; exact Submodule.add_mem _ h g
    | smul _ _ _ h => rw [map_smul]; exact Submodule.smul_mem _ _ h
  have hrow (i j) : k i*m i j = m i j := by
    rcases i with ⟨s,_|⟨⟨d,t⟩|a,i⟩⟩
    · exact one_mul _
    · rw [hz]
      simp
    · exact one_mul _
  have hj : liftM D D m = m := by
    ext i j
    simp only [liftM_def,D,Matrix.diagonal_transpose,Matrix.mul_diagonal,Matrix.diagonal_mul,hrow]
    rw [mul_comm]
    have heq : m i j=m j i := congr_fun (congr_fun (Wspace_sym hm) j) i
    rw [heq,hrow]
  rwa [hj] at hx

def totalRank (x : Profile p n) : ℕ := ∑ i, (x i).rank
def nonzeroTags (w : Tag p.g → Moment p n) : Finset (Tag p.g) :=
  by classical exact Finset.univ.filter (fun i => w i ≠ 0)

theorem mem_nonzeroTags (i) (w : Tag p.g → Moment p n) :
    i ∈ nonzeroTags w ↔ w i ≠ 0 := by classical simp [nonzeroTags]

theorem cut_const (w : Tag p.g → Moment p n) (m : Moment p n) :
    cut p n (fun i => w i+m) = cut p n w := by
  funext i
  change w _ + m + (w _ + m) = w _ + w _
  rw [add_add_add_comm, char_two,add_zero]

theorem common_zero {w v : Tag p.g → Moment p n}
    (h : 2*(nonzeroTags w).card < p.g) (g : 2*(nonzeroTags v).card < p.g) :
    ∃ l, w l=0 ∧ v l=0 := by
  classical
  by_contra! hn
  have hu : Finset.univ ⊆ nonzeroTags w ∪ nonzeroTags v := by
    intro i hi
    by_cases h : w i=0
    · exact Finset.mem_union_right _ ((mem_nonzeroTags _ _).mpr (hn i h))
    · exact Finset.mem_union_left _ ((mem_nonzeroTags _ _).mpr h)
  have hx := (Finset.card_le_card hu).trans (Finset.card_union_le _ _)
  simp only [Finset.card_univ, Tag, Fintype.card_fin] at hx
  omega

theorem small_cut_unique {w v : Tag p.g → Moment p n}
    (h : 2*(nonzeroTags w).card < p.g) (g : 2*(nonzeroTags v).card < p.g)
    (he : cut p n w = cut p n v) : w=v := by
  obtain ⟨l,hl,hL⟩ := common_zero h g
  funext i
  have ha := getPair_cut w i l
  rw [he, getPair_cut,hl,hL,add_zero,add_zero] at ha
  exact ha.symm

private theorem nz_rank {I J : Type} [Fintype I] [Fintype J] {M : Mat I J}
    (h : M ≠ 0) : 1 ≤ M.rank := by
  by_contra hg
  have he : colSp M = ⊥ := Submodule.finrank_eq_zero.mp (by
    rw [show Module.finrank F (colSp M)=M.rank from rfl]; omega)
  have hm : M.mulVecLin = 0 := LinearMap.range_eq_bot.mp he
  apply h
  exact coe_mv_inj (J:=J) (show M.mulVecLin=Matrix.mulVecLin 0 by rw [hm,mulVecLin_zero])

theorem few_unequal {w : Tag p.g → Moment p n} :
    ∑ l : Tag p.g, (nonzeroTags (fun d => w d+w l)).card ≤ 2*totalRank (cut p n w) := by
  classical
  let r := fun i => ((cut p n w) i).rank
  have he (l) :
      (nonzeroTags (fun d => w d+w l)).card ≤
        ∑ i : Comp p.g, if inc i l then r i else 0 := by

    let f (i : Tag p.g) := if w i+w l ≠ 0 then (1:ℕ) else 0
    have h :
        (nonzeroTags (fun d => w d+w l)).card = ∑ i : {i : Tag p.g // l ≠ i}, f i := by
      have hh : (nonzeroTags (fun d => w d+w l)).card = ∑ i, f i := by
        unfold nonzeroTags f
        rw [Finset.card_eq_sum_ones,Finset.sum_filter]
      rw [hh,Fintype.sum_eq_add_sum_subtype_ne _ l]
      have hz : f l=0 := by simp [f,char_two]
      rw [hz,zero_add]
      exact (Equiv.subtypeEquivRight (show ∀ x, (x ≠ l) ↔ (l ≠ x) from fun _ => ne_comm)).sum_comp
        (fun x : {i : Tag p.g // l ≠ i} => f x)
    rw [h]
    have h' :
        (∑ i : Comp p.g, if inc i l then r i else 0) = ∑ i : TagStar l, r i.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _
    rw [h',← (starEquiv l).sum_comp]
    refine Finset.sum_le_sum fun i _ => ?_
    unfold f
    split
    · rename_i hx
      change 1 ≤ r (edge l i i.property)
      apply nz_rank
      have h0 := getPair_edge l i i.property (cut p n w)
      rw [getPair_cut, add_comm] at h0
      rw [← h0]
      exact hx
    · exact Nat.zero_le _
  refine (Finset.sum_le_sum (fun i _ => he i)).trans_eq ?_
  unfold totalRank
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : Finset.univ.filter (fun l => inc i l) = {i.val.1,i.val.2} := by
    ext; simp [inc,eq_comm]
  rw [← Finset.sum_filter,hi]
  simp [i.property.ne, two_mul,r]

/-- Sparse representatives: the bound here is g*(number of supported tags)
≤ 2*total rank (apply with total rank ≤ 2D). -/
theorem sparse_rep {x : Profile p n} (h : x ∈ Xspace p n)
    (hg : 4*totalRank x < p.g*p.g) :
    ∃ w : Tag p.g → Moment p n, cut p n w=x ∧
      (∀ l,w l∈Wtag p n l) ∧
      p.g*(nonzeroTags w).card ≤ 2*totalRank x ∧ 2*(nonzeroTags w).card < p.g := by
  classical
  obtain ⟨w,hw,rfl⟩ := mem_X.mp h
  let B := fun l => nonzeroTags (p:=p) (fun i => w i+w l)
  let t := totalRank (cut p n w)
  have hn : 0 < p.g := Nat.pos_of_ne_zero (fun he => by
    have hi : p.g*p.g=0 := by rw [he]
    omega)
  have : NeZero p.g := ⟨hn.ne'⟩
  obtain ⟨l,hl⟩ : ∃ l : Tag p.g, p.g*(B l).card ≤ 2*t := by
    by_contra! he
    have he1 :
        ∑ _l : Tag p.g, 2*t < ∑ l : Tag p.g, p.g*(B l).card :=
      Finset.sum_lt_sum (fun l _ => (he l).le) ⟨0,Finset.mem_univ _,he 0⟩
    simp only [Finset.sum_const,Finset.card_univ,Tag,Fintype.card_fin,nsmul_eq_mul] at he1
    rw [← Finset.mul_sum] at he1
    have hh : p.g*(∑ l, (B l).card) ≤ p.g*(2*t) := Nat.mul_le_mul_left _ few_unequal
    exact Nat.not_lt_of_le hh he1
  let v := fun i => w i+w l
  have hi : 2*(nonzeroTags v).card < p.g := by
    change p.g*(nonzeroTags v).card ≤ _ at hl
    by_contra h1
    have hh : p.g*p.g ≤ p.g*(2*(nonzeroTags v).card) :=
      Nat.mul_le_mul_left _ (Nat.le_of_not_lt h1)
    change 4*t< p.g*p.g at hg
    nlinarith
  refine ⟨v,cut_const w _,fun i => ?_,hl,hi⟩
  refine Submodule.add_mem _ (hw i) ((Wstar_le_tag i) ?_)
  apply Wtag_majority_star (I := (nonzeroTags v)ᶜ)
  · rw [Finset.card_compl,show Fintype.card (Tag p.g)=p.g from Fintype.card_fin _]
    omega
  · intro j hj
    have hh : w j+w l=0 := by
      change v j=0
      have h := Finset.mem_compl.mp hj
      rwa [mem_nonzeroTags, not_not] at h
    have he : w j = w l := add_right_cancel (hh.trans (char_two _).symm)
    rw [← he]; exact hw j

end HadwigerCounterexample

end

end OAI
