import OAI.Combinatorics.HadwigerCounterexample.ProbePointMasses

namespace OAI

/-! # Frame Intersection Costs -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I J K : Type} [Fintype I] [Fintype J] [Fintype K]

private theorem prod_one {A I : Type} [Fintype I] [DecidableEq I] [Fintype A]
    (f : I → Wgt A) (hf : ∀ i,IsLaw (f i)) (i : I) :
    mapW (prodW f) (fun g => g i)=f i := by
  classical
  funext x
  let q (j : I) (y : A) := if j=i then y=x else True
  have hh : (fun f : I→A => f i=x)=fun f : I→A => ∀ j,q j (f j) := by
    funext g
    apply propext; constructor
    · intro h j; unfold q; split_ifs with he
      · rwa [he]
    intro h; simpa only [q,ite_eq_left rfl] using h i
  unfold mapW
  rw [hh,prodW_pr f q,Finset.prod_eq_single i]
  · simp [q]
  · intro j _ hj
    simp [q,hj,(hf j).total]
  simp

/-- Raw law of a single-sign observation of primary/channel columns. -/
theorem raw_part (m : Mixer p n) (z : Place p) [DecidableEq I]
    (hN : 2*num (Full p n)-N≤ -1)
    {A : Mat (Full p n) I} (hA : Injective A.mulVec) :
    mapW (raw m N) (fun x => takeSign (p:=p) (x z.1) z.2 * A)=
      unifOn (fun x => Injective x.mulVec) := by
  classical
  let w := unifOn (FramesAt (U:=Fin N) (gramCond m))
  have he : 2*num (Full p n)-num (Fin N) ≤ -1 := by simpa only [num,Fintype.card_fin] using hN
  have h : ∃ x : Oframe p n N, FramesAt (gramCond m) x := framesAt_exists
    (gramCond_exists m) (by linarith only [he])
  have hF := prod_one (fun (_ : Comp p.g) => w) (fun _ => unifOn_law h) z.1
  let g := fun o : Oframe p n N => takeSign o z.2 * A
  change mapW (raw m N) (g ∘ (fun x => x z.1))=_
  rw [← mapW_nested]
  rw [show mapW (raw m N) (fun x => x z.1)=w from hF]
  cases z with
  | mk e c =>
    cases c; exact framesAt_observe_minus h hA; exact framesAt_observe_plus h hA

private def ipPart (p : Shape) (n : ℕ) : Mat (Full p n) (Row p n) :=
  embedMat (.inl ·)

theorem frameP_cap {w : Wgt (UnitType p n N)} (m : Mixer p n) {H : ℝ} (hH : 0≤H)
    (h : bySide p w m H) (i : Bool) (z : Place p) (hN : 2*num (Full p n)-N≤ -1) :
    ∀ y,mapW w (fun x => fpAt p (onSide x i) z) y≤H*(2 * unif y) := by
  classical
  intro y
  let g := fun x : UnitType p n N => onSide x i
  let f := fun x : Orient p n N => fpAt p x z
  have hg : num (Row p n)-num (Fin N)≤ -1 := by
    have hi : num (Row p n) ≤ num (Full p n) := by
      have h := Fintype.card_le_of_injective _ (Sum.inl_injective (β:=Fin p.h)
        (α:=Row p n))
      exact_mod_cast h
    have hh : 0≤num (Full p n) := Nat.cast_nonneg _
    simp only [num,Fintype.card_fin] at hN hi hh ⊢; linarith
  change mapW w (f ∘ g) _ ≤ _
  rw [← mapW_nested]
  apply (mapW_cap (h i) f y).trans
  have hf (x : Orient p n N) :
      f x=takeSign (p:=p) (x z.1) z.2 * ipPart p n := by
    rw [ipPart,mul_embedMat]; rfl
  rw [show f=(fun x : Orient p n N => takeSign (p:=p) (x z.1) z.2 * ipPart p n) from funext hf]
  rw [raw_part m z hN (A:=ipPart p n) (embedMat_inj Sum.inl_injective)]
  exact mul_le_mul_of_nonneg_left (plus_le_unif hg y) hH

theorem frameY_cap {w : Wgt (UnitType p n N)} (m : Mixer p n) {H : ℝ} (hH : 0≤H)
    (h : bySide p w m H) (i : Bool) (z : Place p) (hN : 2*num (Full p n)-N≤ -1) :
    ∀ y,mapW w (fun x => fyAt p (onSide x i) z) y≤H*(2 * unif y) := by
  classical
  intro y
  let g := fun x : UnitType p n N => onSide x i
  let f := fun x : Orient p n N => fyAt p x z
  have hg : num (Fin p.h)-num (Fin N)≤ -1 := by
    have hi : num (Fin p.h) ≤ num (Full p n) := by
      have h := Fintype.card_le_of_injective _ (Sum.inr_injective (β:=Fin p.h)
        (α:=Row p n)); exact_mod_cast h
    have hh : 0≤num (Full p n) := Nat.cast_nonneg _
    simp only [num,Fintype.card_fin] at hN hi hh ⊢; linarith
  change mapW w (f ∘ g) _ ≤ _
  rw [← mapW_nested]
  apply (mapW_cap (h i) f y).trans
  have hf (x : Orient p n N) :
      f x=takeSign (p:=p) (x z.1) z.2 * intoChan p n := (intoChan_val ..).symm
  rw [show f=(fun x : Orient p n N => takeSign (p:=p) (x z.1) z.2 * intoChan p n) from funext hf]
  rw [raw_part m z hN (A:=intoChan p n) intoChan_inj]
  exact mul_le_mul_of_nonneg_left (plus_le_unif hg y) hH

variable [DecidableEq I] [DecidableEq J] [DecidableEq K]

theorem any_span_hit (S : Space (Vec I)) :
    pr unif (fun M : Mat I J => ¬ Disjoint (colSp M) S) ≤ bp (num J+dim S-num I) := by
  classical
  let P := fun (z : Vec J × S) (M : Mat I J) => z.1≠0 ∧ M *ᵥ z.1=z.2.val
  have h (M : Mat I J) : ¬ Disjoint (colSp M) S → ∃ z,P z M := by
    intro h
    rw [Submodule.disjoint_def] at h
    push Not at h
    obtain ⟨x,⟨y,rfl⟩,hy,hx⟩ := h
    have hh : y≠0 := fun h => hx (by rw [h,map_zero])
    exact ⟨(y,⟨_,hy⟩),hh,rfl⟩
  have he (z : Vec J × S) : pr unif (P z) ≤ bp (-num I) := by
    by_cases hh : z.1=0
    · simp only [P,hh,ne_eq,not_true_eq_false,false_and,pr_false]
      exact (bp_pos _).le
    have h' := shift_pmax (@unif_subLaw (Mat I J) _) ⊤ (fun _ _ _ => rfl) hh z.2.val
    rw [show dim (⊤ : Space (Vec I))=_ from (finrank_top ..).trans (dim_vec _)] at h'
    simpa only [P,hh,ne_eq,not_false_eq_true,true_and] using h'
  refine ((pr_mono unif_subLaw.nz h).trans (pr_exists_le unif_subLaw.nz P)).trans ?_
  refine (Finset.sum_le_sum fun i _ => he i).trans_eq ?_
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_prod,
    Nat.cast_mul,card_space,dim_vec,bp_sub,bp_add,bp_neg,num,div_eq_mul_inv]

def expand (P : Mat I J) (K : Type) : Mat I K →ₗ[F] Mat K J where
  toFun X := Xᵀ*P
  map_add' a b := by rw [Matrix.transpose_add,Matrix.add_mul]
  map_smul' a b := by rw [Matrix.transpose_smul,Matrix.smul_mul]; rfl

theorem transposed_uniform {P : Mat I J} (hp : Injective P.mulVec) :
    mapW (unif : Wgt (Mat I K)) (fun x => xᵀ*P)=unif := by
  obtain ⟨L,hL⟩ := mat_left_inv hp
  apply map_unif_surjective (expand P K)
  intro v
  exact ⟨(v*L)ᵀ,by change ((v*L)ᵀ)ᵀ*P=v; rw [transpose_transpose,Matrix.mul_assoc,hL,Matrix.mul_one]⟩

/-- per fixed nominal offsets in one component/side -/
theorem test_transpose {w : Wgt (UnitType p n N)} (m : Mixer p n) {H : ℝ} (hH : 0≤H)
    (h : bySide p w m H) (i : Bool) (z : Place p) (hN : 2*num (Full p n)-N≤ -1)
    (M : Mat (Fin N) I) (hM : Injective M.mulVec) :
    ∀ x,mapW w (fun y => (fyAt p (onSide y i) z)ᵀ * M) x≤H*2 * unif x := by
  intro x
  let f (y : HMat p N) := yᵀ * M
  let g (x : UnitType p n N) := fyAt p (onSide x i) z
  change mapW w (f ∘ g) _ ≤ _
  rw [←mapW_nested]
  have he := frameY_cap m hH h i z hN
  simp_rw [← mul_assoc] at he
  refine (mapW_cap he f x).trans_eq ?_
  rw [show mapW unif f=unif from transposed_uniform hM]

def glimpsesBill (p : Shape) (k : ℕ) (H : ℝ) :=
  num (Place p)*(H*2*bp ((k:ℝ)-p.h))

theorem glimpse_failure {w : Wgt (UnitType p n N)} (m : Mixer p n) {H : ℝ} (hH : 0≤H)
    (h : bySide p w m H) (hw : SubLaw w) (i : Bool) (hN : 2*num (Full p n)-N≤ -1)
    {q : Place p→ℕ} (M : DTuple (p:=p) q N) (k : ℕ) (hm : ∀ z,Injective (M z).mulVec)
    (hk : ∀ z,q z≤k) :
    pr w (fun x => ¬ glimpse p x i M) ≤ glimpsesBill p k H := by
  classical
  let P (A : Place p) :=
    fun x => ¬Injective ((fyAt p (onSide (x : UnitType p n N) i) (flipZ p A))ᵀ * M A).mulVec
  have he x : ¬ glimpse p x i M → ∃ z,P z x := by
    intro h
    unfold glimpse at h
    push Not at h
    exact h
  have hi z : pr w (P z) ≤ H*2*bp ((k:ℝ)-p.h) := by
    let f (x : UnitType p n N) := (fyAt p (onSide x i) (flipZ p z))ᵀ*M z
    let Q := fun x : Mat (Chan p) (Fin (q z)) => ¬ Injective x.mulVec
    change pr w (Q ∘ f) ≤ _
    rw [show pr w (Q ∘ f)=pr (mapW w f) Q from (mapW_pr w f Q).symm]
    refine (pr_cap (test_transpose m hH h i (flipZ p z) hN _ (hm z)) Q).trans
      (mul_le_mul_of_nonneg_left (unif_fail.trans ?_) (by positivity))
    apply bp_le
    have hh : (q z:ℝ)≤k := by exact_mod_cast hk z
    simpa [Chan,num] using sub_le_sub_right hh (p.h:ℝ)
  refine ((pr_mono hw.nz he).trans (pr_exists_le hw.nz P)).trans ?_
  refine (Finset.sum_le_sum fun i _ => hi i).trans_eq ?_
  simp only [Finset.sum_const,Finset.card_univ, nsmul_eq_mul,glimpsesBill,num]

/-- span of entire individual primary image in a fixed cover mode. -/
theorem any_frame_hit {w : Wgt (UnitType p n N)} (m : Mixer p n) {H : ℝ} (hH : 0≤H)
    (h : bySide p w m H) (i : Bool) (z : Place p) (hN : 2*num (Full p n)-N≤ -1)
    (S : Space (Vec (Fin N))) :
    pr w (fun x => ¬ Disjoint (imageP p x i z) S) ≤
      H*2*bp (num (Row p n)+dim S-N) := by
  let P (M : Mat (Fin N) (Row p n)) := ¬ Disjoint (colSp M) S
  let f (x : UnitType p n N) := fpAt p (onSide x i) z
  change pr w (fun x => P (f x)) ≤ _
  rw [← mapW_pr w f P]
  have he := frameP_cap m hH h i z hN
  simp_rw [← mul_assoc] at he
  refine (pr_cap he P).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  simpa only [num,Fintype.card_fin] using any_span_hit (J:=Row p n) S

end HadwigerCounterexample

end

end OAI
