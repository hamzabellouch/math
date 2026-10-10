import OAI.Combinatorics.HadwigerCounterexample.RealizationConditions
import OAI.Combinatorics.HadwigerCounterexample.MomentLabelSupport

namespace OAI

/-! # Gradient Rank Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n : ℕ}

private theorem part_formula_single (i j : Tag p.g) (e : Comp p.g) (M : Moment p n) :
    getPair p n i j (Pi.single e M) =
      (if i=e.val.1 ∧ j=e.val.2 then M else 0) +
      (if i=e.val.2 ∧ j=e.val.1 then M else 0) := by
  classical
  rcases e with ⟨⟨u,v⟩,hu⟩
  by_cases h : i=j
  · subst j
    have hv : u≠v := hu.ne
    have hu : ¬ (i=u ∧ i=v) := fun ⟨e,g⟩ => hv (e.symm.trans g)
    have hw : ¬ (i=v ∧ i=u) := by tauto
    simp [getPair,hu,hw]
  rw [getPair_edge i j h]
  change (Pi.single (⟨(u,v),hu⟩:Comp p.g) M : Profile p n) (edge i j h) = (if i=u ∧ j=v then M else 0)+
    (if i=v ∧ j=u then M else 0)
  rcases lt_or_gt_of_ne h with ht|ht
  · have ha : ¬ (i=v∧j=u) := by
      rintro ⟨rfl,rfl⟩; exact hu.asymm ht
    simp [edge,ht,Pi.single_apply,ha]
  · have ha : ¬ (i=u∧j=v) := by
      rintro ⟨rfl,rfl⟩; exact hu.asymm ht
    simp [edge,not_lt.mpr ht.le,Pi.single_apply,ha,and_comm]

private theorem shared_at (t : Tag p.g) (e : Comp p.g) (M : Moment p n) :
    ∃ s : F,
      s = sharedT p n t (Pi.single e M) ∧
      s = (if t=e.val.2 then etab p n Block.S M else 0) +
        if t=e.val.1 then etab p n Block.S M else 0 := by
  refine ⟨_,rfl,?_⟩
  simp only [sharedT,LinearMap.sum_apply,LinearMap.comp_apply,part_formula_single,
    map_add,Finset.sum_add_distrib]
  let u := fun i => etab p n Block.S i
  have hi (a b : Tag p.g) :
      ∑ l, u (if l=a ∧ t=b then M else 0) =
        if t=b then u M else 0 := by
    rw [Finset.sum_eq_single a]
    · split <;> simp_all [u]
    · intro b _ hb; simp [hb,u]
    simp
  exact congrArg₂ (·+·) (hi _ _) (hi _ _)

private def routed (p : Shape) (n : ℕ) (t a d : Tag p.g) :=
  if allowed d a then testM p n (Block.O d t) else 0

private theorem role_at (t : Tag p.g) (e : Comp p.g) (M : Moment p n) :
    roleT p n t (Pi.single e M) =
      mpair (routed p n t e.val.1 e.val.2 + routed p n t e.val.2 e.val.1) M := by
  classical
  simp only [roleT,LinearMap.sum_apply,LinearMap.comp_apply,part_formula_single,map_add,
    Finset.sum_add_distrib,mpair_add]
  let u := fun d => etab p n (Block.O d t)
  have hh (i j : Tag p.g) :
      ∑ (l : Tag p.g), ∑ d ∈ Finset.univ.filter (fun d => allowed d l),
        u d (if l=i ∧ d=j then M else 0) = mpair (routed p n t i j) M := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · by_cases h : allowed j i
        · simp [h,u,routed,etab]
        simp [h,routed]; rw [mpair_comm,map_zero]
      · intro d _ hd
        simp [u,hd]
      simp
    · intro l _ hl
      simp [u,hl]
    simp
  exact congrArg₂ (·+·) (hh _ _) (hh _ _)

private theorem test_rank (d : Block p.g) : (testM p n d).rank ≤ p.r := by
  apply le_trans (mrk_sum_le ..)
  refine (Finset.sum_le_sum (g:=fun _ => 1) (fun i _ => Matrix.rank_vecMulVec_le ..)).trans_eq ?_
  simp

def Represents (m : Profile p n →ₗ[F] F) (A : Profile p n) :=
  ∀ x, m x=∑ i,mpair (A i) (x i)

theorem rep_single {m : Profile p n →ₗ[F] F} {A : Profile p n}
    (h : ∀ (e : Comp p.g) (M : Moment p n), m (Pi.single e M)=mpair (A e) M) :
    Represents m A := by
  intro x
  have heq : m x=m (∑ e, Pi.single e (x e)) := by rw [Finset.univ_sum_single]
  rw [heq,map_sum]
  exact Finset.sum_congr rfl fun i _ => h _ _

theorem tmix_small (m : Mixer p n) (x : Profile p n) (K : ℕ) (hK : ∀ e,(x e).rank≤K) :
    ∃ A, Represents (Tmix m x) A ∧ ∀ e,(A e).rank≤2*p.J*Fintype.card (Comp p.g)*K := by
  let f (e) := ∑ (j : Fin p.J), ∑ i : Comp p.g,
    (liftM (m.mixL j i e)ᵀ (m.mixR j i e)ᵀ (x i) +
     liftM (m.mixL j e i) (m.mixR j e i) (x i))
  refine ⟨f,fun y => ?_,fun e => ?_⟩
  · let F j i e := mpair (liftM (m.mixL j i e)ᵀ (m.mixR j i e)ᵀ (x i)) (y e)
    let G j i e := mpair (liftM (m.mixL j e i) (m.mixR j e i) (x i)) (y e)
    have he : Tmix m x y =
        (∑ j,∑ i, ∑ e,F j i e) + ∑ j,∑ e,∑ i,G j i e := by
      change (∑ j,∑ i,∑ e, mpair (x i) (liftM (m.mixL j i e) (m.mixR j i e) (y e)))+
        (∑ j,∑ e,∑ i, mpair (y e) (liftM (m.mixL j e i) (m.mixR j e i) (x i)))=_
      refine congrArg₂ _ ?_ ?_
      · simp_rw [mpair_liftM]; rfl
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => mpair_comm _ _
    rw [he]
    simp only [f,mpair_sum,mpair_add,Finset.sum_add_distrib]
    change _ = (∑ e,∑ j,∑ i,F j i e) + ∑ e,∑ j,∑ i,G j i e
    refine congrArg₂ _ ?_ (Finset.sum_comm)
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  · apply le_trans (mrk_sum_le ..)
    let E := Fintype.card (Comp p.g)
    refine (Finset.sum_le_sum (g:=fun _ => E*(2*K)) (fun j _ => ?_)).trans_eq ?_
    · apply le_trans (mrk_sum_le ..)
      refine (Finset.sum_le_sum (g:=fun _ => 2*K) (fun i _ => ?_)).trans_eq (by simp [E])
      exact (mrk_add_le ..).trans ((Nat.add_le_add ((rank_lift_le ..).trans (hK i))
        ((rank_lift_le ..).trans (hK i))).trans_eq (two_mul _).symm)
    simp [E]; ring

private def Xrep (p : Shape) (n : ℕ) (w : Tag p.g → Moment p n) :=
  ∀ l,w l∈ Wtag p n l

set_option maxHeartbeats 800000 in
theorem grad_small {m : Mixer p n} {v : Tag p.g → Moment p n}
    (hg : Odd p.g) (hv : ∀ l,v l∈ Wtag p n l) (hs : parityW v=1)
    (hz : (nonzeroTags v).card ≤ 7) (hr : ∀ e,(cut p n v e).rank ≤ 7) :
    ∃ A, Represents (grad m (cut p n v)) A ∧
      ∀ e,(A e).rank ≤ 15*p.r + 14*p.J * Fintype.card (Comp p.g) := by
  let x := cut p n v
  let d t := etab p n Block.S (v t)
  obtain ⟨A,hA,hR⟩ := tmix_small m x 7 hr
  let h : Profile p n →ₗ[F] F := role p n + T0 p n x
  have hf : h = (∑ t,d t • roleT p n t)+ ∑ t, roleT p n t x • sharedT p n t := by
    have hc : role p n x + ∑ t,d t=1 := by
      simp only [parityW,eta,LinearMap.add_apply,Finset.sum_add_distrib] at hs
      rw [show x=cut p n v from rfl,role_cut _ v hv]
      exact hs
    have hcoef (t : Tag p.g) : 1+role p n x + sharedT p n t x = d t := by
      unfold x
      rw [sharedT_cut p hg]
      change 1+role p n x + ((∑ i,d i)+d t) = _
      rw [←add_assoc,add_assoc 1,hc,char_two,zero_add]
    refine LinearMap.ext fun y => ?_
    change role p n y+T0 p n x y = _
    simp only [T0_val,LinearMap.add_apply,LinearMap.sum_apply,
      Finset.sum_add_distrib,LinearMap.smul_apply,smul_eq_mul]
    calc role p n y +
          (role p n x * role p n y +
          ((∑ x_1 : Tag p.g,roleT p n x_1 x*sharedT p n x_1 y)+
          ∑ x_1 : Tag p.g,sharedT p n x_1 x*roleT p n x_1 y))
      _ = (∑ t : Tag p.g,(1+role p n x+sharedT p n t x)* roleT p n t y)+
        ∑ x_1 : Tag p.g,roleT p n x_1 x*sharedT p n x_1 y := by
          simp only [add_mul,one_mul,Finset.sum_add_distrib,
            ← Finset.mul_sum]; simp only [role,LinearMap.sum_apply]; ring
      _ = _ := by simp_rw [hcoef]
  let Y (e : Comp p.g) (i : Tag p.g) :=
    routed p n i e.val.1 e.val.2 + routed p n i e.val.2 e.val.1
  let P (e : Comp p.g) :=
    ∑ i∈nonzeroTags v,d i • Y e i
  let a (e : Comp p.g) := roleT p n e.val.1 x + roleT p n e.val.2 x
  let Q (e : Comp p.g) := a e • testM p n Block.S
  have he : Represents h (fun e => P e+Q e) := by
    apply rep_single
    intro e M
    rw [hf,mpair_add]
    simp only [LinearMap.add_apply,LinearMap.sum_apply,LinearMap.smul_apply,
      smul_eq_mul]
    refine congrArg₂ _ ?_ ?_
    · simp only [P,Y,role_at,mpair_sum,mpair_smul]
      refine (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => ?_)).symm
      have hg : v i=0 := by rwa [mem_nonzeroTags,not_not] at hi
      rw [show d i=0 from (by unfold d; rw [hg,map_zero]),zero_mul]
    · have hh (i : Tag p.g) :
          sharedT p n i (Pi.single e M) =
            (if i=e.val.2 then etab p n Block.S M else 0)+(if i=e.val.1 then
              etab p n Block.S M else 0) := by
        obtain ⟨s,h1,h2⟩ := shared_at i e M; rw [← h1,h2]
      simp_rw [hh,mul_add,Finset.sum_add_distrib,Q,mpair_smul,a,add_mul]
      simp only [mul_ite,mul_zero,Finset.sum_ite_eq',
        Finset.mem_univ,ite_true,etab]
      exact add_comm _ _
  refine ⟨fun e => P e+Q e+A e,fun y => ?_, fun e => ?_⟩
  · simp only [mpair_add,Finset.sum_add_distrib]
    have hx : grad m x y=h y+Tmix m x y := (add_assoc (role p n y) (T0 p n x y) (Tmix m x y)).symm
    rw [show grad m (cut p n v) y=_ from hx,he y,hA y]
    simp only [mpair_add,Finset.sum_add_distrib]
  · have hi : (P e).rank ≤ 14*p.r := by
      have hr (i a b : Tag p.g) : (routed p n i a b).rank ≤ p.r := by
        unfold routed
        split
        · exact test_rank _
        simp
      have hy (i) : (d i • Y e i).rank ≤ 2*p.r := by
        rcases bit_cases (d i) with h|h
        · simp [h]
        rw [h,one_smul,two_mul]
        exact (mrk_add_le ..).trans (Nat.add_le_add (hr ..) (hr ..))
      refine (mrk_sum_le ..).trans ((Finset.sum_le_sum (fun i _ => hy i)).trans ?_)
      simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id]; nlinarith
    have hj : (Q e).rank ≤ p.r := by
      rcases bit_cases (a e) with h|h
      · simp [Q,h]
      unfold Q; rw [h,one_smul]; exact test_rank _
    refine le_trans (mrk_add_le ..) ((Nat.add_le_add ((mrk_add_le (P e) _).trans
      (Nat.add_le_add hi hj)) (hR e)).trans ?_)
    apply le_of_eq; ring

namespace Volley
variable {I : Type} [Fintype I] [DecidableEq I] (v : Volley p n I)

omit [DecidableEq I] in
theorem gradient_rep (m : Mixer p n) {t : Tagging p I} {w : I → Bool} {i j : Bool}
    (hg : Odd p.g) (h : v.legal t) (hb : (v.shoots w i j).card ≤ 7)
    (hd : ∑ a∈v.shoots w i j,v.diagonalAt a=1) :
    ∃ A, Represents (grad m (v.sumAt t w i j)) A ∧
      ∀ e,(A e).rank ≤ 15*p.r+14*p.J*Fintype.card (Comp p.g) := by
  classical
  let S := v.shoots w i j
  let w' (a : I) : Tag p.g → Moment p n :=
    Pi.single (t a) (mom p (v.sel a) (v.par a))
  let C := ∑ i∈S,w' i
  have h1 (a) : atomAt v t a=cut p n (w' a) := rfl
  have he : sumAt v t w i j=cut p n C := by
    change (∑ i∈S,_) = cut p n (∑ i∈S,_)
    simp_rw [h1,map_sum]
  rw [he]
  apply grad_small hg
  · intro l
    change (∑ i∈S, w' i) l ∈ _
    rw [Finset.sum_apply]
    apply Submodule.sum_mem
    intro a _
    by_cases e : l=t a
    · subst l
      simp only [w',Pi.single_eq_same]
      exact Submodule.subset_span ⟨_,_,h a,rfl⟩
    simp [w',Pi.single_eq_of_ne e]
  · unfold parityW
    simp only [C,Finset.sum_apply,map_sum]
    rw [Finset.sum_comm]
    refine (Finset.sum_congr (g:=fun a => v.diagonalAt a) rfl fun a _ => ?_).trans hd
    rw [Finset.sum_eq_single (t a)]
    · rw [show w' a (t a)=_ from Pi.single_eq_same _ _]
      rfl
    · intro l _ hl; simp [w',Pi.single_eq_of_ne hl]
    simp
  · have hC : nonzeroTags C ⊆ S.image t := by
      intro l hl
      by_contra hn
      apply mem_nonzeroTags l C |>.mp hl
      simp only [C,Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro a ha
      simp [w',Pi.single_eq_of_ne (show l≠t a from fun h0 => hn
        (Finset.mem_image.mpr ⟨a,ha,h0.symm⟩))]
    exact (Finset.card_le_card hC).trans (Finset.card_image_le.trans hb)
  intro e
  rw [← he,Volley.sumAt, Finset.sum_apply]
  apply le_trans (mrk_sum_le ..)
  refine le_trans ((Finset.sum_le_sum (g:=fun _ => 1) fun _ _ => ?_).trans_eq ?_) hb
  · rw [atomAt,atom_def]
    split
    · apply Matrix.rank_vecMulVec_le
    · simp
  · simp

theorem here_card {w : I → Bool} (h : v.bounded w) (i : Bool) : (v.here i).card≤14 := by
  have he : v.here i ⊆ v.shoots w i true ∪ v.shoots w i false :=
    fun j hj => by
      have hi : v.obj j=i := (Finset.mem_filter.mp hj).2
      cases h : w j <;> simp [shoots,hi,h]
  exact le_trans ((Finset.card_le_card he).trans (Finset.card_union_le _ _))
    (Nat.add_le_add (h _ _).2 (h _ _).2)

theorem call_count {w : I→Bool} (h : v.bounded w) : Fintype.card I ≤ 28 := by
  have he : Finset.univ ⊆ v.here true ∪ v.here false :=
    fun j _ => by cases h : v.obj j <;> simp [here,h]
  have hh := (Finset.card_le_card he).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add (here_card _ h true) (here_card _ h false)))
  exact (Finset.card_univ.symm.le.trans hh)

end Volley
end HadwigerCounterexample

end

end OAI
