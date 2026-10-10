import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.DiscreteLadderSteps

namespace OAI

namespace MatchingFPRAS.NumberedHierarchy

open Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (B : V → V → ℚ)

def related (t : ℚ) (x y : V) : Prop := x=y ∨ t≤B x y

instance relatedDec (t : ℚ) (x y : V) : Decidable (related B t x y) :=
  inferInstanceAs (Decidable (x=y ∨ t≤B x y))

def component (t : ℚ) (x : V) : Finset V := univ.filter (related B t x)

lemma component_self (t : ℚ) (x : V) : x∈component B t x := by simp [component,related]

def root (t : ℚ) (x : V) : V := (component B t x).min' ⟨x,component_self B t x⟩

lemma root_mem (t : ℚ) (x : V) : root B t x ∈ component B t x := min'_mem _ _

lemma related_root (t : ℚ) (x : V) : related B t x (root B t x) := by
  simpa [component] using root_mem B t x

omit [Fintype V] [LinearOrder V] in
lemma cast_related [Fintype V] [LinearOrder V] (t : ℚ) (x y : V) :
    related B t x y ↔ Hierarchy.Related (fun x y=>(B x y:ℝ)) (t:ℝ) x y := by
  simp only [related,Hierarchy.Related,Rat.cast_le]

variable (hsym : ∀ x y,B x y=B y x)

variable (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)

include hsym in
omit [Fintype V] [LinearOrder V] in
lemma symmetric [Fintype V] [LinearOrder V] : ∀ x y,(B x y:ℝ)=(B y x:ℝ) := by intro x y; rw [hsym]

include htri in
omit [Fintype V] [LinearOrder V] in
lemma triangular [Fintype V] [LinearOrder V] : ∀ x y z,x≠y → x≠z → y≠z →
    min (B x z:ℝ) (B z y:ℝ)≤(B x y:ℝ) := by
  intro x y z hxy hxz hyz
  exact_mod_cast htri x y z hxy hxz hyz

lemma related_trans (_hsym : ∀ x y,B x y=B y x)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (t : ℚ) {x y z : V} (hxy : related B t x y) (hyz : related B t y z) :
    related B t x z := by
  rw [cast_related] at *
  exact Hierarchy.related_trans _ (triangular B htri) _ hxy hyz

include hsym in
omit [Fintype V] [LinearOrder V] in
lemma related_symm [Fintype V] [LinearOrder V] (t : ℚ) {x y : V}
    (hxy : related B t x y) : related B t y x := by
  rcases hxy with rfl|h
  · exact Or.inl rfl
  · exact Or.inr (by rwa [hsym])

include hsym htri in
lemma component_eq_iff (t : ℚ) (x y : V) : component B t x=component B t y ↔ related B t x y := by
  constructor
  · intro h
    have := component_self B t y
    rw [←h] at this
    simpa [component] using this
  · intro h
    ext z
    simp only [component,mem_filter,mem_univ,true_and]
    exact ⟨fun hx=>related_trans B hsym htri t (related_symm B hsym t h) hx,
      fun hy=>related_trans B hsym htri t h hy⟩

include hsym htri in
lemma root_eq_iff (t : ℚ) (x y : V) : root B t x=root B t y ↔ related B t x y := by
  constructor
  · intro h
    have hx := related_root B t x
    rw [h] at hx
    exact related_trans B hsym htri t hx (related_symm B hsym t (related_root B t y))
  · intro h
    unfold root
    congr 1
    exact (component_eq_iff B hsym htri t x y).mpr h

include hsym htri in
lemma root_idem (t : ℚ) (x : V) : root B t (root B t x)=root B t x :=
  (root_eq_iff B hsym htri t _ _).mpr (related_symm B hsym t (related_root B t x))

abbrev NumberedComponent (t : ℚ) := {x : V // root B t x=x}

def classOf (t : ℚ) (x : V) : NumberedComponent B t := ⟨root B t x,root_idem B hsym htri t x⟩

def quotientEquiv (t : ℚ) :
    Hierarchy.Component (fun x y=>(B x y:ℝ)) (symmetric B hsym) (triangular B htri) (t:ℝ) ≃
      NumberedComponent B t where
  toFun := Quotient.lift (classOf B hsym htri t) (by
    intro x y h
    apply Subtype.ext
    exact (root_eq_iff B hsym htri t x y).mpr ((cast_related B t x y).mpr h))
  invFun x := Quotient.mk _ x.val
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with | h x =>
      apply Quotient.sound
      exact (cast_related B t _ _).mp (related_symm B hsym t (related_root B t x))
  right_inv := by intro x; apply Subtype.ext; exact x.property

def level (H : ℕ) (x : ℚ) : Fin (H+1) :=
  ⟨Nat.findGreatest (fun k => (2:ℚ)^k≤x) H,Nat.lt_succ_of_le (Nat.findGreatest_le H)⟩

lemma level_cast (H : ℕ) (x : ℚ) : level H x=Hierarchy.dyadicLevel H (x:ℝ) := by
  apply Fin.ext
  change Nat.findGreatest (fun k => (2:ℚ)^k≤x) H = Nat.findGreatest (fun k => (2:ℝ)^k≤(x:ℝ)) H
  have h : (fun k => (2:ℚ)^k≤x) = (fun k => (2:ℝ)^k≤(x:ℝ)) := by
    funext k
    apply propext
    norm_cast
  simp only [h]

abbrev Label (H : ℕ) := (k : Fin (H+1)) × NumberedComponent B ((2:ℚ)^k.val)

def labelAt {H : ℕ} (k : Fin (H+1)) (x : V) : Label B H :=
  ⟨k,classOf B hsym htri _ x⟩

def member {H : ℕ} (l : Label B H) (x : V) : Prop := root B ((2:ℚ)^l.1.val) x=l.2.val

instance memberDec {H : ℕ} (l : Label B H) (x : V) : Decidable (member B l x) :=
  inferInstanceAs (Decidable (root B _ x=l.2.val))

lemma member_self {H : ℕ} (l : Label B H) : member B l l.2.val := l.2.property

def parent {H : ℕ} (l : Label B H) : Option (Label B H) :=
  if h : 0<l.1.val then some (labelAt B hsym htri ⟨l.1.val-1,by omega⟩ l.2.val) else none

lemma parent_rank {H : ℕ} {l p : Label B H} (h : parent B hsym htri l=some p) : p.1.val<l.1.val := by
  unfold parent at h
  split_ifs at h with hl
  · cases h
    simp only [labelAt]
    omega

lemma label_card_bound (H : ℕ) : Fintype.card (Label B H)≤(H+1)*Fintype.card V := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ k : Fin (H+1),Fintype.card V := sum_le_sum (fun k _=>Fintype.card_subtype_le _)
    _ = _ := by simp

def componentEquiv (k : ℕ) :
    Hierarchy.Component (fun x y=>(B x y:ℝ)) (symmetric B hsym) (triangular B htri) ((2:ℝ)^k) ≃
      NumberedComponent B ((2:ℚ)^k) where
  toFun := Quotient.lift (classOf B hsym htri ((2:ℚ)^k)) (by
    intro x y h
    apply Subtype.ext
    apply (root_eq_iff B hsym htri _ x y).mpr
    apply (cast_related B ((2:ℚ)^k) x y).mpr
    change Hierarchy.Related (fun x y=>(B x y:ℝ)) ((2:ℝ)^k) x y at h
    simpa only [Rat.cast_pow,Rat.cast_ofNat] using h)
  invFun x := Quotient.mk _ x.val
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with | h x =>
      apply Quotient.sound
      change Hierarchy.Related (fun x y=>(B x y:ℝ)) ((2:ℝ)^k) (root B ((2:ℚ)^k) x) x
      have h := (cast_related B ((2:ℚ)^k) _ _).mp
        (related_symm B hsym ((2:ℚ)^k) (related_root B ((2:ℚ)^k) x))
      simpa only [Rat.cast_pow,Rat.cast_ofNat] using h
  right_inv := by intro x; apply Subtype.ext; exact x.property

def labelEquiv (H : ℕ) :
    Hierarchy.Label (fun x y=>(B x y:ℝ)) (symmetric B hsym) (triangular B htri) H ≃ Label B H :=
  Equiv.sigmaCongrRight (fun k=>componentEquiv B hsym htri k.val)

lemma componentEquiv_mk (k : ℕ) (x : V) :
    componentEquiv B hsym htri k (Quotient.mk _ x)=classOf B hsym htri ((2:ℚ)^k) x := by
  rfl

lemma labelEquiv_at {H : ℕ} (k : Fin (H+1)) (x : V) :
    labelEquiv B hsym htri H (Hierarchy.labelAt _ _ _ k x)=labelAt B hsym htri k x := by
  simp [labelEquiv,Hierarchy.labelAt,labelAt,componentEquiv_mk]

lemma labelEquiv_level {H : ℕ} (l : Hierarchy.Label (fun x y=>(B x y:ℝ))
    (symmetric B hsym) (triangular B htri) H) :
    (labelEquiv B hsym htri H l).1=l.1 := rfl

lemma member_labelAt {H : ℕ} (k : Fin (H+1)) (x y : V) :
    member B (labelAt B hsym htri k x) y ↔ related B ((2:ℚ)^k.val) y x := by
  exact root_eq_iff B hsym htri _ y x

lemma member_equiv {H : ℕ} (l : Hierarchy.Label (fun x y=>(B x y:ℝ))
    (symmetric B hsym) (triangular B htri) H) (x : V) :
    member B (labelEquiv B hsym htri H l) x ↔
      Hierarchy.Mem (fun x y=>(B x y:ℝ)) (symmetric B hsym) (triangular B htri) l x := by
  obtain ⟨k,l⟩:=l
  induction l using Quotient.inductionOn with | h y =>
    change member B (labelEquiv B hsym htri H (Hierarchy.labelAt _ _ _ k y)) x ↔ _
    rw [labelEquiv_at,member_labelAt]
    change related B ((2:ℚ)^k.val) x y ↔ Hierarchy.Mem _ _ _ (Hierarchy.labelAt _ _ _ k y) x
    rw [Hierarchy.mem_class_iff]
    simpa only [Rat.cast_pow,Rat.cast_ofNat] using cast_related B ((2:ℚ)^k.val) x y

lemma parent_iff {H : ℕ} (l p : Label B H) : parent B hsym htri l=some p ↔
    p.1.val+1=l.1.val ∧ member B p l.2.val := by
  obtain ⟨k,l⟩:=l
  obtain ⟨j,p⟩:=p
  unfold parent
  split_ifs with hl
  · change 0<k.val at hl
    constructor
    · intro h
      have he := Option.some.inj h
      have hk := congrArg (fun l : Label B H => l.1.val) he
      constructor
      · change j.val+1=k.val
        change k.val-1=j.val at hk
        omega
      · rw [←he]
        rfl
    · rintro ⟨hp,hm⟩
      change j.val+1=k.val at hp
      have hj : j=(⟨k.val-1,Nat.lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩ : Fin (H+1)) := by
        apply Fin.ext
        change j.val=k.val-1
        omega
      cases hj
      congr 1
      apply congrArg (Sigma.mk _)
      exact Subtype.ext hm
  · constructor
    · intro h; cases h
    · rintro ⟨hp,_⟩
      change j.val+1=k.val at hp
      change ¬0<k.val at hl
      omega

lemma parent_equiv_iff {H : ℕ}
    (l p : Hierarchy.Label (fun x y=>(B x y:ℝ)) (symmetric B hsym) (triangular B htri) H) :
    parent B hsym htri (labelEquiv B hsym htri H l)=some (labelEquiv B hsym htri H p) ↔
      Hierarchy.Parent (fun x y=>(B x y:ℝ)) (symmetric B hsym) (triangular B htri) p l := by
  rw [parent_iff]
  change (p.1.val+1=l.1.val ∧ _) ↔ _
  let v := (labelEquiv B hsym htri H l).2.val
  have hl : Hierarchy.Mem _ (symmetric B hsym) (triangular B htri) l v :=
    (member_equiv B hsym htri l v).mp (member_self B _)
  constructor
  · rintro ⟨hp,hm⟩
    exact ⟨hp,v,(member_equiv B hsym htri p v).mp hm,hl⟩
  · intro h
    exact ⟨h.1,(member_equiv B hsym htri p v).mpr (Hierarchy.parent_mem _ _ _ h hl)⟩

variable {E : Type*} [Fintype E] [DecidableEq E] (left right : E → V)

def edgeLabel (H : ℕ) (e : E) : Label B H :=
  labelAt B hsym htri (level H (B (left e) (right e))) (left e)

def bags (H : ℕ) (x : V) : Finset (Label B H) :=
  (univ.filter (fun e=>x=left e ∨ x=right e)).image (edgeLabel B hsym htri left right H)

omit [Fintype E] [DecidableEq E] in
lemma edgeLabel_equiv [Fintype E] [DecidableEq E] (H : ℕ) (e : E) :
    labelEquiv B hsym htri H (Hierarchy.edgeLabel (fun x y=>(B x y:ℝ))
      (symmetric B hsym) (triangular B htri) left right H e)=edgeLabel B hsym htri left right H e := by
  unfold Hierarchy.edgeLabel edgeLabel
  rw [←level_cast]
  exact labelEquiv_at B hsym htri _ _

omit [DecidableEq E] in
lemma mem_bags [DecidableEq E] (H : ℕ) (x : V) (l : Label B H) :
    l∈bags B hsym htri left right H x ↔
      ∃ e,(x=left e ∨ x=right e) ∧ edgeLabel B hsym htri left right H e=l := by
  simp [bags]

lemma bags_equiv (H : ℕ) (x : V) :
    (Hierarchy.memberships (fun x y=>(B x y:ℝ)) (symmetric B hsym) (triangular B htri)
      left right H x).image (labelEquiv B hsym htri H)=bags B hsym htri left right H x := by
  classical
  ext l
  simp only [mem_image,mem_bags,Hierarchy.mem_memberships,Hierarchy.Incident]
  constructor
  · rintro ⟨a,⟨e,he,hea⟩,hal⟩
    refine ⟨e,he,?_⟩
    rw [←edgeLabel_equiv,hea,hal]
  · rintro ⟨e,he,hel⟩
    refine ⟨_,⟨e,he,rfl⟩,?_⟩
    rwa [edgeLabel_equiv]

omit [DecidableEq E] in
lemma bags_card_edges [DecidableEq E] (H : ℕ) (x : V) :
    (bags B hsym htri left right H x).card≤Fintype.card E := by
  exact card_image_le.trans ((card_filter_le _ _).trans_eq (card_univ))

end MatchingFPRAS.NumberedHierarchy

namespace MatchingFPRAS.RationalSource

open MatchingFPRAS Switching Subdivision RealGeometry Enlargement Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

def logicalB (w : V → V → ℚ) : V → V → ℚ :=
  BottleneckAlgorithm.close w (Fintype.card V)

omit [Nontrivial V] in
lemma logicalB_cast [Nontrivial V] (w : V → V → ℚ) (x y : V) :
    (logicalB w x y:ℝ)=bottleneck (fun x y=>(w x y:ℝ)) x y :=
  BottleneckAlgorithm.rational_close_eq w x y

def height (w : V → V → ℚ) (x : V) : ℚ :=
  (univ.erase x).sup' (row_nonempty x) (logicalB w x)

lemma height_cast (w : V → V → ℚ) (x : V) :
    (height w x:ℝ)=sourceHeight (fun x y=>(w x y:ℝ)) x := by
  unfold height sourceHeight
  rw [Finset.apply_sup'_eq_sup'_comp _ (fun x:ℚ=>(x:ℝ)) (by intro x y; exact Rat.cast_max x y)]
  apply Finset.sup'_congr _ rfl
  intro y _
  exact logicalB_cast w x y

def maxHeight (w : V → V → ℚ) : ℚ := univ.sup' univ_nonempty (height w)

lemma maxHeight_cast (w : V → V → ℚ) :
    (maxHeight w:ℝ)=maxSourceHeight (fun x y=>(w x y:ℝ)) := by
  unfold maxHeight maxSourceHeight
  rw [Finset.apply_sup'_eq_sup'_comp _ (fun x:ℚ=>(x:ℝ)) (by intro x y; exact Rat.cast_max x y)]
  apply Finset.sup'_congr _ rfl
  intro x _
  exact height_cast w x

def levels (w : V → V → ℚ) (K : ℕ) : ℕ :=
  (NumberedHierarchy.level (2*K) (maxHeight w)).val

lemma levels_eq (w : V → V → ℚ) (K : ℕ) :
    levels w K=sourceLevels (fun x y=>(w x y:ℝ)) K := by
  simp only [levels,NumberedHierarchy.level_cast,maxHeight_cast,sourceLevels]

def profile (p : ℕ) (B Hu Hv lam : ℚ) (i : Fin (4*p+1)) : ℚ :=
  if i.val<2*p then max B (Hu/2^(i.val/2))
  else if i.val=2*p then lam else max B (Hv/2^((4*p-i.val)/2))

lemma profile_cast (p : ℕ) (B Hu Hv lam : ℚ) (i : Fin (4*p+1)) :
    (profile p B Hu Hv lam i:ℝ)=profileActivity p B Hu Hv lam i := by
  rcases lt_trichotomy i.val (2*p) with h|h|h
  · rw [profile,ite_eq_left h,profile_left _ _ _ _ _ _ h]
    norm_cast
  · have he : i=⟨2*p,by omega⟩:=Fin.ext h
    rw [he]
    simp [profile]
  · rw [profile,ite_eq_right (by omega),ite_eq_right (by omega),profile_right _ _ _ _ _ _ h]
    norm_cast

def pathActivity (w : V → V → ℚ) (K : ℕ) (e : LogicalEdge V) : Fin (4*(2*K+2)+1) → ℚ :=
  profile (2*K+2) (logicalB w (source e) (target e)) (height w (source e))
    (height w (target e)) (BottleneckAlgorithm.edge w (source e) (target e))

lemma pathActivity_cast (w : V → V → ℚ) (K : ℕ) (e : LogicalEdge V) (i : Fin (4*(2*K+2)+1)) :
    (pathActivity w K e i:ℝ) = Enlargement.pathActivity (2*K+2)
      (fun e=>bottleneck (fun x y=>(w x y:ℝ)) (source e) (target e))
      (fun e=>sourceHeight (fun x y=>(w x y:ℝ)) (source e))
      (fun e=>sourceHeight (fun x y=>(w x y:ℝ)) (target e))
      (logicalActivity (fun x y=>(w x y:ℝ))) e i := by
  rw [pathActivity,profile_cast,logicalB_cast,height_cast,height_cast]
  congr 1
  have he : source e<target e:=e.property
  simp [BottleneckAlgorithm.edge,logicalActivity,edgeActivity,he]

def activity (w : V → V → ℚ) (K : ℕ) (x y : SourceVertex V K) : ℚ :=
  ∑ q : SourceRealEdge V K,
    if RealGeometry.edge source target (4*(2*K+2)) q.1 q.2=s(x,y)
      then pathActivity w K q.1 q.2 else 0

lemma activity_cast (w : V → V → ℚ) (K : ℕ) (x y : SourceVertex V K) :
    (activity w K x y:ℝ)=RealGeometry.activity source target (4*(2*K+2))
      (Enlargement.pathActivity (2*K+2)
        (fun e=>bottleneck (fun x y=>(w x y:ℝ)) (source e) (target e))
        (fun e=>sourceHeight (fun x y=>(w x y:ℝ)) (source e))
        (fun e=>sourceHeight (fun x y=>(w x y:ℝ)) (target e))
        (logicalActivity (fun x y=>(w x y:ℝ)))) x y := by
  unfold activity RealGeometry.activity
  push_cast
  apply sum_congr rfl
  intro q _
  split_ifs
  · exact pathActivity_cast w K q.1 q.2
  · norm_cast

def realB (w : V → V → ℚ) (K : ℕ) : SourceVertex V K → SourceVertex V K → ℚ :=
  BottleneckAlgorithm.close (activity w K) (Fintype.card (SourceVertex V K))

lemma realB_cast (w : V → V → ℚ) (K : ℕ) (x y : SourceVertex V K) :
    (realB w K x y:ℝ)=sourceRealB (fun x y=>(w x y:ℝ)) K x y := by
  rw [realB,BottleneckAlgorithm.rational_close_eq]
  unfold sourceRealB realBottleneck
  congr 2
  funext a b
  exact activity_cast w K a b

lemma realB_symm (w : V → V → ℚ) (K : ℕ) (x y : SourceVertex V K) :
    realB w K x y=realB w K y x := by
  apply Rat.cast_injective (α:=ℝ)
  simp only [realB_cast,sourceRealB_comm]

lemma realB_tri (w : V → V → ℚ) (K : ℕ) (x y z : SourceVertex V K)
    (hxy : x≠y) (hxz : x≠z) (hyz : y≠z) :
    min (realB w K x z) (realB w K z y)≤realB w K x y := by
  apply (Rat.cast_le (K:=ℝ)).mp
  simp only [Rat.cast_min,realB_cast]
  exact sourceRealB_tri _ _ _ _ _ hxy hxz hyz

abbrev Label (w : V → V → ℚ) (K : ℕ) := NumberedHierarchy.Label (realB w K) (levels w K)

def bags (w : V → V → ℚ) (K : ℕ) : SourceVertex V K → Finset (Label w K) :=
  NumberedHierarchy.bags (realB w K) (realB_symm w K) (realB_tri w K)
    (realLeft K) (realRight K) (levels w K)

theorem label_card (w : V → V → ℚ) (K : ℕ) :
    Fintype.card (Label w K)≤(2*K+1)*Fintype.card (SourceVertex V K) := by
  calc
    _ ≤ (levels w K+1)*Fintype.card (SourceVertex V K) := by
      rw [Fintype.card_sigma]
      calc
        _ ≤ ∑ k : Fin (levels w K+1),Fintype.card (SourceVertex V K) :=
          sum_le_sum (fun k _=>Fintype.card_subtype_le _)
        _ = _ := by simp
    _ ≤ _ := by
      apply Nat.mul_le_mul_right
      rw [levels_eq]
      exact Nat.add_le_add_right (sourceLevels_le _ _) 1

noncomputable def sourceLabelsEquiv (w : V → V → ℚ) (K : ℕ) :
    SourceLabel (fun x y=>(w x y:ℝ)) K ≃ Label w K := by
  simpa only [SourceLabel,Label,realB_cast,levels_eq] using
    (NumberedHierarchy.labelEquiv (realB w K) (realB_symm w K) (realB_tri w K) (levels w K))

lemma bags_card_le_two (w : V → V → ℚ) (K : ℕ)
    (hw : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y ≤ (4:ℚ)^K) (x : SourceVertex V K) :
    (bags w K x).card≤2 := by
  have he := NumberedHierarchy.bags_equiv (realB w K) (realB_symm w K) (realB_tri w K)
    (realLeft K) (realRight K) (levels w K) x
  rw [bags,←he]
  apply Finset.card_image_le.trans
  have hw' : ∀ x y,x≠y → edgeActivity (fun x y=>(w x y:ℝ)) x y ≤ (4:ℝ)^K := by
    intro a b hab
    have ha:=hw a b hab
    have hec : ((BottleneckAlgorithm.edge w a b:ℚ):ℝ)=edgeActivity (fun x y=>(w x y:ℝ)) a b := by
      unfold BottleneckAlgorithm.edge edgeActivity
      split_ifs <;> norm_cast
    simpa only [hec,Rat.cast_pow,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr ha
  apply Hierarchy.membership_count
  · intro a b
    rw [realB_cast]
    exact sourceRealB_floor _ _ a b
  · intro e
    simpa only [realB_cast,levels_eq] using
      (source_strength_le_max (fun x y=>(w x y:ℝ)) K hw' e).trans_lt
        (maxSourceHeight_lt (fun x y=>(w x y:ℝ)) K hw')
  · intro a e f he hf
    simpa only [realB_cast] using source_strength_incident_near
      (fun x y=>(w x y:ℝ)) K hw' a e f he hf

end MatchingFPRAS.RationalSource

end OAI
