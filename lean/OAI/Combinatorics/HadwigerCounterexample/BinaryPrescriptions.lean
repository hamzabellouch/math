import OAI.Combinatorics.HadwigerCounterexample.RealizationConditions
import OAI.Combinatorics.HadwigerCounterexample.MixerConditions

namespace OAI

/-! # Binary Prescriptions -/

noncomputable section
namespace HadwigerCounterexample

open scoped BigOperators
open Matrix Finset
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I]

/-- list for a cross edge -/
def aiming (a b : I → Bool) (i j : Bool) :=
  Finset.univ.filter (fun x => a x=i ∧ b x=j)

/-- within-endpoint L/R bit tests. Read only a x=a y, x≠y.
(tests between ordered points; no double counting since L,R and
both orientations are in the mixer hypothesis). -/
abbrev Script (p : Shape) (I : Type) := I → I → Vec (MOne p)

namespace Volley
variable (v : Volley p n I)
def reads (s : Script p I) (m : Mixer p n) :=
  ∀ x y : I,x≠y → v.obj x=v.obj y →
    ∀ i : MOne p, s x y i = evmat (orderedM m i) (v.rayAt x) (v.rayAt y)
end Volley

def prescribedB (p : Shape) (t : Tagging p I) (s : Script p I) (x y : I) :=
  ∑ i : Fin p.J,∑ e : Comp p.g, ∑ f : Comp p.g, if inc e (t x) ∧ inc f (t y) then
    s x y ((i,e,f),true)*s x y ((i,e,f),false) else 0

noncomputable def prescribedT (p : Shape) (t : Tagging p I) (d : Vec I)
    (h : Mat I I) (s : Script p I) (x y : I) : F :=
  @ite _ (x=y) (Classical.propDecidable _) (d x)
    (h x y+(prescribedB p t s x y+prescribedB p t s y x))

def fulfills (p : Shape) (t : Tagging p I) (d f : Vec I) (u : Mat I I)
    (s : Script p I) (a b : I → Bool) :=
  ∀ (x : I) (j : Bool),
    d x+ (∑ i∈aiming a b (a x) j, prescribedT p t d u s i x) =
      if j=b x then 0 else f x

namespace Volley
variable {v : Volley p n I}

omit [Fintype I] in
private theorem B1_eval {s : Script p I} (t : Tagging p I) (m : Mixer p n)
    (ha : v.reads s m) {x y : I} (hg : x ≠ y) (hh : v.obj x=v.obj y) :
    B1 m (v.atomAt t x) (v.atomAt t y)=prescribedB p t s x y := by
  classical
  change ∑ i : Fin p.J, _ = _
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun e _ =>
    Finset.sum_congr rfl fun f _ => ?_
  by_cases he : inc e (t x)
  · by_cases hf : inc f (t y)
    · rw [ite_eq_left ⟨he,hf⟩,ha x y hg hh,ha x y hg hh]
      simp only [atomAt,atom_def,he,hf,ite_true,mom,liftM_outer,pair_outers]
      rfl
    rw [ite_eq_right (show ¬ (_ ∧ _) from fun h => hf h.2)]
    simp only [atomAt,atom_def,hf,ite_false,map_zero]
  rw [ite_eq_right (show ¬ (_ ∧ _) from fun h => he h.1)]
  simp only [atomAt,atom_def,he,ite_false]
  rw [mpair_comm,map_zero]

theorem grads_by_script (t : Tagging p I) (m : Mixer p n) (w : Volley p n I)
    (y : UnitType p n N) {d f : Vec I} {u : Mat I I} {s : Script p I}
    (h : fulfills p t d f u s v.obj w.obj) (hs : v.reads s m)
    (hd : ∀ x,role p n (v.atomAt t x)=d x)
    (hf : ∀ x,innerP p y (w.obj x) (w.atomAt t x)=f x)
    (hu : ∀ x y : I,T0 p n (v.atomAt t x) (v.atomAt t y)=u x y) :
    v.attackGrad w t m y := by
  classical
  intro x j
  rw [grad_val,hd,hf,sumAt,map_sum,LinearMap.sum_apply]
  rw [← h x j]; congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  unfold prescribedT
  split
  · rename_i he
    subst x
    rw [T_diag,hd]
  rename_i he
  have hx := (Finset.mem_filter.mp hi).2.1
  rw [Tsym_val,hu, B1_eval t m hs he hx,B1_eval t m hs (Ne.symm he) hx.symm]
end Volley

/-- Solve symmetric row sums at one endpoint. Couple via opposite
same-target pmiss/role sum equality. Only the resulting necessary
(common d+f sum) is used as input here. -/
private theorem binary_plan (a b : I→Bool) (i : Bool) (d f : Vec I)
    (h : (∑ j∈aiming a b i true,(d j+f j))=∑ j∈aiming a b i false,(d j+f j))
    (h' : ∀ j,(aiming a b i j).Nonempty) :
    ∃ M : Mat I I, Mᵀ=M ∧ (∀ x,M x x=d x) ∧ ∀ j : Bool,∀ x∈Finset.univ.filter (fun l => a l=i),
      (∑ l∈aiming a b i j,M l x) = d x+(if j=b x then 0 else f x) := by
  classical
  let S := aiming a b i
  let X : Mat I Bool := Matrix.of (fun i j => if i∈S j then 1 else 0)
  let V : Mat I Bool := Matrix.of (fun x j => d x + (if j=b x then 0 else f x))
  let D := Matrix.diagonal d
  let Y := V+D*X
  obtain ⟨L,hL⟩ := mat_left_inv (P:=X) (by
    intro x y he
    funext j
    obtain ⟨v,hv⟩ := h' j
    have ha := (Finset.mem_filter.mp hv).2
    have heq (x) : (X *ᵥ x) v=x j := by
      unfold X Matrix.mulVec dotProduct
      rw [Finset.sum_eq_single j]
      · simp [hv,S]
      · intro k _ hk; simp [S,aiming,ha,hk.symm]
      simp
    rw [← heq x,← heq y,he])
  let B := Xᵀ*Y
  have hg (j k : Bool) : B j k=if j=k then 0 else (∑ l∈S j,(d l+f l)) := by
    have hi {l : I} (hh : l∈S j) : a l=i ∧ b l=j := (Finset.mem_filter.mp hh).2
    have hy {l : I} (hL : l∈S j) :
        Y l k= (if j=k then 0 else d l+f l) := by
      unfold Y V X; rw [Matrix.add_apply,Matrix.of_apply,Matrix.diagonal_mul,Matrix.of_apply]
      by_cases h : j=k
      · subst k
        simp only [(hi hL).2,hL,ite_true,add_zero,mul_one,char_two]
      have hv : l∉S k := fun hw => h ((hi hL).2.symm.trans (Finset.mem_filter.mp hw).2.2)
      simp [h,Ne.symm h,(hi hL).2,hv]
    have ht (l : I) : X l j*Y l k= if l∈S j then Y l k else 0 := by
      by_cases hv : l∈S j <;> simp [X,hv]
    unfold B; rw [Matrix.mul_apply]
    simp_rw [Matrix.transpose_apply,ht,← Finset.sum_filter]
    rw [show Finset.univ.filter (fun x => x∈S j)=S j from (by simp)]
    by_cases g : j=k
    · rw [ite_eq_left g]
      exact Finset.sum_eq_zero fun l hl => (hy hl).trans (ite_eq_left g)
    rw [ite_eq_right g]
    exact Finset.sum_congr rfl fun l hl => (hy hl).trans (ite_eq_right g)
  have ha (j : Bool) : B j j=0 := by rw [hg,ite_eq_left rfl]
  have hB : Bᵀ=B := by
    ext j k
    rw [Matrix.transpose_apply,hg,hg]
    cases j <;> cases k
    all_goals simp
    · exact h
    exact h.symm
  let W := Lᵀ*B*L
  have hW : Wᵀ=W := by unfold W; simp only [transpose_mul,transpose_transpose,hB,Matrix.mul_assoc]
  have hw (x : I) : W x x=0 := by
    unfold W
    have hf : B false true=B true false := congr_fun (congr_fun hB true) false
    simp only [Matrix.mul_apply,Fintype.sum_bool,Matrix.transpose_apply,ha,mul_zero,zero_add,
      add_zero,hf]
    rw [mul_right_comm (L false x), show L true x * B true false * L false x=
        L false x * L true x * B true false from (by ring),char_two]
  let Z := Y*L+(Y*L)ᵀ + W
  have he : (D+Z)*X=V := by
    have he : (Y*L)ᵀ*X=W*X := by
      unfold W
      have hh : Yᵀ * X=B := by
        have ht : Bᵀ=Yᵀ*X := by unfold B; rw [Matrix.transpose_mul,transpose_transpose]
        rw [← ht,hB]
      rw [Matrix.transpose_mul,Matrix.mul_assoc Lᵀ Yᵀ X,hh,Matrix.mul_assoc _ L X,hL,
        Matrix.mul_one]
    unfold Z
    rw [Matrix.add_mul,Matrix.add_mul,Matrix.add_mul,Matrix.mul_assoc Y L X,hL,
      Matrix.mul_one,he,add_assoc Y,char_two,add_zero]
    unfold Y
    rw [add_left_comm,char_two,add_zero]
  refine ⟨D+Z,?_,?_,fun j x hx => ?_⟩
  · unfold Z D
    simp only [transpose_add,Matrix.diagonal_transpose,transpose_transpose,hW]
    ac_rfl
  · intro x
    unfold D Z
    simp only [Matrix.add_apply,Matrix.diagonal_apply_eq,Matrix.transpose_apply,hw,
      char_two,add_zero]
  let Q := D+Z
  have hq : Qᵀ=Q := by
    unfold Q Z D
    simp only [transpose_add,Matrix.diagonal_transpose,transpose_transpose,hW]
    ac_rfl
  have h1 : (Q * X) x j= _ := congr_fun (congr_fun he x) j
  rw [Matrix.mul_apply] at h1
  have hy : ∑ l∈S j, Q l x =∑ l, Q x l * X l j := by
    conv_rhs => unfold X
    simp only [Matrix.of_apply,mul_ite,mul_one,mul_zero, ←Finset.sum_filter]
    rw [show Finset.univ.filter (fun x => x∈ S j)=S j from (by simp)]
    exact Finset.sum_congr rfl fun l _ => congr_fun (congr_fun hq x) l
  exact hy.trans h1

omit [Fintype I] in
private theorem scripted (p : Shape) (t : Tagging p I) (g : I→I→F)
    (h : 2≤p.g) (hJ : 1 ≤ p.J) :
    ∃ s : Script p I,∀ x y,prescribedB p t s x y=g x y := by
  classical
  have hh (x : I) : ∃ i : Comp p.g,inc i (t x) := by
    have he := card_star (t x)
    have hi : Nonempty (TagStar (t x)) := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨⟨i,h⟩⟩ := hi
    exact ⟨i,h⟩
  choose q hq using hh
  let i0 : Fin p.J := ⟨0,hJ⟩
  let s : Script p I := fun x y i =>
    if i.1=(i0,q x,q y) then if i.2 then g x y else 1 else 0
  refine ⟨s,fun x y => ?_⟩
  unfold prescribedB
  rw [Finset.sum_eq_single i0]
  · rw [Finset.sum_eq_single (q x)]
    · rw [Finset.sum_eq_single (q y)]
      · simp [s,hq]
      · intro i _ hi; simp [s,hi]
      simp
    · intro i _ hi; simp [s,hi]
    simp
  · intro i _ hi; simp [s,hi]
  simp

set_option maxHeartbeats 600000 in
theorem choose_script (p : Shape) (t : Tagging p I) (a b : I→Bool)
    (d : Vec I)
    (f : Vec I)
    (d' : Vec I)
    (h : ∀ i : Bool,(∑ x∈aiming a b i true,(d' x+f x)) =
      ∑ x∈aiming a b i false,(d' x+f x))
    (ha : ∀ i j : Bool, ∑ x∈aiming a b i j,(d x+d' x)=1)
    (hc : ∀ i j : Bool,(aiming a b i j).Nonempty)
    (u : Mat I I) (hu : uᵀ=u)
    (hg : 2≤p.g) (hi : 1≤p.J) :
    ∃ s : Script p I, fulfills p t d f u s a b := by
  classical
  have hh (i j : Bool) :
      (∑ x∈aiming a b i j,(d x+f x))=1+ ∑ x∈aiming a b i j,(d' x+f x) := by
    rw [←ha,← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [add_assoc,←add_assoc (d' x),char_two,zero_add]
  choose M hM hD hA using fun i : Bool => binary_plan a b i d f (by rw [hh,hh,h]) (hc i)
  let F' := Fintype.equivFin I
  let g (x y : I) := if F' x < F' y then M (a x) x y+u x y else 0
  obtain ⟨s,hs⟩ := scripted p t g hg hi
  have hf (x y : I) (h : a x=a y) : prescribedT p t d u s x y=M (a x) x y := by
    unfold prescribedT
    split
    · rename_i he
      subst y
      exact (hD _ _).symm
    rename_i he
    rw [hs x y, hs y x]
    rcases lt_or_gt_of_ne (show F' x ≠ F' y from fun h => he (F'.injective h)) with e|e
    · simp only [g, ite_eq_left e,ite_eq_right (not_lt.mpr e.le),add_zero]
      rw [add_left_comm,char_two,add_zero]
    simp only [g,ite_eq_left e,ite_eq_right (not_lt.mpr e.le),zero_add]
    rw [←h,show u y x=u x y from congr_fun (congr_fun hu x) y,
      show M (a x) y x=M (a x) x y from congr_fun (congr_fun (hM (a x)) x) y]
    rw [add_left_comm,char_two,add_zero]
  refine ⟨s,fun x j => ?_⟩
  let S := aiming a b (a x) j
  have he : ∑ i∈S,prescribedT p t d u s i x=∑ i∈S,M (a x) i x :=
    Finset.sum_congr rfl fun i hi => by
      have hm : a i=a x := (Finset.mem_filter.mp hi).2.1
      rw [hf i x hm,hm]
  rw [he,hA (a x) j x (by simp), ← add_assoc, char_two,zero_add]
end HadwigerCounterexample

end

end OAI
