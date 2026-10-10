import Mathlib
import OAI.Analysis.HardSphere.Geometry.Vertex

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.Lattice
abbrev DiscreteTorus (K : ℕ) := Fin 3 → ZMod K

def torusProjection (K : ℕ) (x : Vertex) : DiscreteTorus K := fun i ↦ (x i : ZMod K)

def rangeStep (a : ℕ) (x y : Vertex) : Prop := x≠y ∧ ∀ i, |x i-y i|≤a

def torusRangeStep (K a : ℕ) (x y : DiscreteTorus K) : Prop :=
  x≠y ∧ ∃ d : Vertex, (∀ i, |d i|≤a) ∧ ∀ i, y i=x i+(d i : ZMod K)

lemma rangeStep_symm {a : ℕ} {x y : Vertex} (h : rangeStep a x y) : rangeStep a y x :=
  ⟨h.1.symm,fun i ↦ by rw [abs_sub_comm]; exact h.2 i⟩

lemma torusRangeStep_symm {K a : ℕ} {x y : DiscreteTorus K} (h : torusRangeStep K a x y) :
    torusRangeStep K a y x := by
  obtain ⟨hne,d,hd,he⟩ := h
  refine ⟨hne.symm,-d,fun i ↦ by simpa using hd i,fun i ↦ ?_⟩
  simp only [Pi.neg_apply,Int.cast_neg,he i]
  abel

def forbiddenCuts {K : ℕ} (S : Finset (DiscreteTorus K)) (a : ℕ) (i : Fin 3) : Finset (ZMod K) :=
  S.biUnion fun x ↦ (Finset.Icc 1 a).image fun j : ℕ ↦ x i+(j : ZMod K)

lemma forbiddenCuts_card {K : ℕ} (S : Finset (DiscreteTorus K)) (a : ℕ) (i : Fin 3) :
    (forbiddenCuts S a i).card≤a*S.card := by
  calc
    _ ≤ ∑ x∈S, ((Finset.Icc 1 a).image fun j : ℕ ↦ x i+(j : ZMod K)).card := Finset.card_biUnion_le
    _ ≤ ∑ _x∈S, a := by
      apply Finset.sum_le_sum
      intro x _
      simpa only [Nat.card_Icc,Nat.add_sub_cancel] using
        (Finset.card_image_le (s := Finset.Icc 1 a) (f := fun j : ℕ ↦ x i+(j : ZMod K)))
    _ = a*S.card := by simp [Nat.mul_comm]

lemma exists_vacant_cut {K : ℕ} [NeZero K] (S : Finset (DiscreteTorus K)) (a : ℕ)
    (hsmall : a*S.card<K) (i : Fin 3) : ∃ c : ZMod K, c∉forbiddenCuts S a i := by
  by_contra hn
  push Not at hn
  have he : forbiddenCuts S a i=Finset.univ := Finset.eq_univ_of_forall hn
  have hc := forbiddenCuts_card S a i
  rw [he,Finset.card_univ,ZMod.card K] at hc
  omega

lemma cut_coordinate_bound {K : ℕ} [NeZero K] (S : Finset (DiscreteTorus K)) (a : ℕ)
    (i : Fin 3) {c : ZMod K} (hc : c∉forbiddenCuts S a i) {x : DiscreteTorus K} (hx : x∈S) :
    (x i-c).val+a<K := by
  have hv := ZMod.val_lt (x i-c)
  by_contra hn
  have hj₁ : 1≤K-(x i-c).val := by omega
  have hj₂ : K-(x i-c).val≤a := by omega
  apply hc
  apply Finset.mem_biUnion.mpr
  refine ⟨x,hx,Finset.mem_image.mpr ⟨K-(x i-c).val,Finset.mem_Icc.mpr ⟨hj₁,hj₂⟩,?_⟩⟩
  rw [Nat.cast_sub hv.le,ZMod.natCast_self,ZMod.natCast_zmod_val]
  abel

def cutLift {K : ℕ} (cut : DiscreteTorus K) (x : DiscreteTorus K) : Vertex :=
  fun i ↦ (cut i).val+(x i-cut i).val

lemma cutLift_projection {K : ℕ} [NeZero K] (cut x : DiscreteTorus K) :
    torusProjection K (cutLift cut x)=x := by
  ext i
  simp only [torusProjection,cutLift,Int.cast_add,Int.cast_natCast,ZMod.natCast_zmod_val]
  abel

lemma small_multiple_zero {K : ℕ} {z : ℤ} (hz : (z : ZMod K)=0) (hsmall : |z|<K) : z=0 := by
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs ((ZMod.intCast_zmod_eq_zero_iff_dvd z K).mp hz)
  rw [← Int.natCast_natAbs] at hsmall
  simpa only [Int.natAbs_natCast] using (show z.natAbs<K by exact_mod_cast hsmall)

lemma cutLift_edge {K : ℕ} [NeZero K] (S : Finset (DiscreteTorus K)) (a : ℕ)
    (cut : DiscreteTorus K) (hcut : ∀ i, cut i∉forbiddenCuts S a i)
    {x y : DiscreteTorus K} (hx : x∈S) (hy : y∈S) (hxy : torusRangeStep K a x y) :
    rangeStep a (cutLift cut x) (cutLift cut y) := by
  obtain ⟨hne,d,hd,he⟩ := hxy
  refine ⟨fun h ↦ hne (by simpa only [cutLift_projection] using congrArg (torusProjection K) h),?_⟩
  intro i
  have hx' := cut_coordinate_bound S a i (hcut i) hx
  have hy' := cut_coordinate_bound S a i (hcut i) hy
  have hd' := abs_le.mp (hd i)
  have hprojX := congrFun (cutLift_projection cut x) i
  have hprojY := congrFun (cutLift_projection cut y) i
  change ((cutLift cut x i : ℤ) : ZMod K)=x i at hprojX
  change ((cutLift cut y i : ℤ) : ZMod K)=y i at hprojY
  have hzero : ((cutLift cut y i-cutLift cut x i-d i : ℤ) : ZMod K)=0 := by
    push_cast
    rw [hprojX,hprojY,he i]
    abel
  have hsmall : |cutLift cut y i-cutLift cut x i-d i|<K := by
    dsimp only [cutLift]
    apply abs_lt.mpr
    constructor <;> omega
  have heq := small_multiple_zero hzero hsmall
  rw [show cutLift cut x i-cutLift cut y i= -d i by omega,abs_neg]
  exact hd i

theorem small_set_lift {K : ℕ} [NeZero K] (S : Finset (DiscreteTorus K)) (a : ℕ)
    (hsmall : a*S.card<K) :
    ∃ f : DiscreteTorus K → Vertex,
      (∀ x, torusProjection K (f x)=x) ∧
      (∀ x∈S, ∀ y∈S, torusRangeStep K a x y → rangeStep a (f x) (f y)) := by
  choose cut hcut using exists_vacant_cut S a hsmall
  exact ⟨cutLift cut,cutLift_projection cut,fun _ hx _ hy hxy ↦ cutLift_edge S a cut hcut hx hy hxy⟩

lemma connected_coordinate_span {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.Preconnected) (f : V → Vertex) (a : ℕ)
    (hedge : ∀ x y, G.Adj x y → ∀ i, |f x i-f y i|≤a) (x y : V) (i : Fin 3) :
    |f x i-f y i|≤a*(Fintype.card V-1) := by
  obtain ⟨p⟩ := hG x y
  let q := p.toPath
  have hlen := q.isPath.length_lt
  have hwalk : ∀ {u v : V} (w : G.Walk u v), |f u i-f v i|≤(a:ℤ)*w.length := by
    intro u v w
    induction w with
    | nil => simp
    | @cons u v w huv p ih =>
      calc
        |f u i-f w i| ≤ |f u i-f v i|+|f v i-f w i| := abs_sub_le _ _ _
        _ ≤ (a:ℤ)+(a:ℤ)*p.length := add_le_add (hedge u v huv i) ih
        _ = (a:ℤ)*(SimpleGraph.Walk.cons huv p).length := by simp only [SimpleGraph.Walk.length_cons,Nat.cast_add,Nat.cast_one]; ring
  have hlen' : (q.val.length:ℤ)<Fintype.card V := by exact_mod_cast hlen
  exact (hwalk q.val).trans (mul_le_mul_of_nonneg_left (by omega) (by positivity))

def torusRangeGraph (K a : ℕ) : SimpleGraph (DiscreteTorus K) where
  Adj := torusRangeStep K a
  symm := ⟨by intro x y h; exact torusRangeStep_symm h⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

def periodicLift (K a : ℕ) (S : Finset (DiscreteTorus K)) (r : Vertex) : Set Vertex :=
  {x | torusProjection K x∈S ∧ Relation.ReflTransGen
    (fun u v ↦ torusProjection K u∈S ∧ torusProjection K v∈S ∧ rangeStep a u v) r x}

lemma short_projection_ne {K a : ℕ} (hK : 2*a<K) {x y : Vertex} (h : rangeStep a x y) :
    torusProjection K x≠torusProjection K y := by
  intro he
  apply h.1
  ext i
  apply sub_eq_zero.mp
  apply small_multiple_zero
  · simp only [Int.cast_sub]
    exact sub_eq_zero.mpr (congrFun he i)
  · exact (h.2 i).trans_lt (by exact_mod_cast (show a<K by omega))

lemma rangeStep_projection {K a : ℕ} (hK : 2*a<K) {x y : Vertex} (h : rangeStep a x y) :
    torusRangeStep K a (torusProjection K x) (torusProjection K y) := by
  refine ⟨short_projection_ne hK h,y-x,fun i ↦ ?_,fun i ↦ ?_⟩
  · simp only [Pi.sub_apply,abs_sub_comm]; exact h.2 i
  · simp only [Pi.sub_apply,torusProjection,Int.cast_sub]; abel

lemma lift_offset_step {K a : ℕ} (hK : 2*a<K) (S : Finset (DiscreteTorus K))
    (f : DiscreteTorus K → Vertex) (hf : ∀ x, torusProjection K (f x)=x)
    (hedge : ∀ x∈S, ∀ y∈S, torusRangeStep K a x y → rangeStep a (f x) (f y))
    {x y : Vertex} (hx : torusProjection K x∈S) (hy : torusProjection K y∈S)
    (hxy : rangeStep a x y) : y-f (torusProjection K y)=x-f (torusProjection K x) := by
  have hxy' := hedge _ hx _ hy (rangeStep_projection hK hxy)
  ext i
  have hxproj := congrFun (hf (torusProjection K x)) i
  have hyproj := congrFun (hf (torusProjection K y)) i
  change ((f (torusProjection K x) i:ℤ):ZMod K)=(x i:ZMod K) at hxproj
  change ((f (torusProjection K y) i:ℤ):ZMod K)=(y i:ZMod K) at hyproj
  have hzero : ((y i-f (torusProjection K y) i-(x i-f (torusProjection K x) i):ℤ):ZMod K)=0 := by
    push_cast
    rw [hxproj,hyproj]
    simp
  have hbd := abs_le.mp (hxy.2 i)
  have hbd' := abs_le.mp (hxy'.2 i)
  have hK' : (2:ℤ)*a<K := by exact_mod_cast hK
  have heq := small_multiple_zero hzero (show |y i-f (torusProjection K y) i-(x i-f (torusProjection K x) i)|<K by
    apply abs_lt.mpr; constructor <;> omega)
  dsimp only [Pi.sub_apply]
  omega

lemma lift_offset_reach {K a : ℕ} (hK : 2*a<K) (S : Finset (DiscreteTorus K))
    (f : DiscreteTorus K → Vertex) (hf : ∀ x, torusProjection K (f x)=x)
    (hedge : ∀ x∈S, ∀ y∈S, torusRangeStep K a x y → rangeStep a (f x) (f y))
    {r x : Vertex} (hx : x∈periodicLift K a S r) :
    x-f (torusProjection K x)=r-f (torusProjection K r) := by
  rcases hx with ⟨hmem,hreach⟩
  clear hmem
  induction hreach with
  | refl => rfl
  | @tail u v _ huv ih => exact (lift_offset_step hK S f hf hedge huv.1 huv.2.1 huv.2.2).trans ih

lemma translated_projection {K : ℕ} (f : DiscreteTorus K → Vertex)
    (hf : ∀ x, torusProjection K (f x)=x) (r : Vertex) (x : DiscreteTorus K) :
    torusProjection K (f x+(r-f (torusProjection K r)))=x := by
  ext i
  have h₁ := congrFun (hf x) i
  have h₂ := congrFun (hf (torusProjection K r)) i
  change ((f x i:ℤ):ZMod K)=x i at h₁
  change ((f (torusProjection K r) i:ℤ):ZMod K)=(r i:ZMod K) at h₂
  simp only [torusProjection,Pi.add_apply,Pi.sub_apply,Int.cast_add,Int.cast_sub,h₁,h₂,
    sub_self,add_zero]

lemma rangeStep_translate {a : ℕ} {x y : Vertex} (h : rangeStep a x y) (t : Vertex) :
    rangeStep a (x+t) (y+t) := by
  refine ⟨fun he ↦ h.1 (add_right_cancel he),fun i ↦ ?_⟩
  simpa only [Pi.add_apply,add_sub_add_right_eq_sub] using h.2 i

lemma translated_reach {K a : ℕ} (S : Finset (DiscreteTorus K))
    (hS : ((torusRangeGraph K a).induce (↑S)).Preconnected)
    (f : DiscreteTorus K → Vertex) (hf : ∀ x, torusProjection K (f x)=x)
    (hedge : ∀ x∈S, ∀ y∈S, torusRangeStep K a x y → rangeStep a (f x) (f y))
    (r : Vertex) (hr : torusProjection K r∈S) (x : DiscreteTorus K) (hx : x∈S) :
    f x+(r-f (torusProjection K r))∈periodicLift K a S r := by
  refine ⟨by simpa only [translated_projection f hf] using hx,?_⟩
  have hp := (SimpleGraph.reachable_iff_reflTransGen _ _).mp
    (hS ⟨torusProjection K r,hr⟩ ⟨x,hx⟩)
  have hmap : ∀ {u v : ↑(↑S : Set (DiscreteTorus K))},
      Relation.ReflTransGen ((torusRangeGraph K a).induce (↑S)).Adj u v →
      Relation.ReflTransGen
        (fun u v ↦ torusProjection K u∈S ∧ torusProjection K v∈S ∧ rangeStep a u v)
        (f u.val+(r-f (torusProjection K r))) (f v.val+(r-f (torusProjection K r))) := by
    intro u v huv
    induction huv using Relation.ReflTransGen.trans_induction_on with
    | refl => exact .refl
    | @single u v huv =>
      apply Relation.ReflTransGen.single
      refine ⟨?_,?_,rangeStep_translate (hedge u.val u.property v.val v.property huv) _⟩
      · simpa only [translated_projection f hf,Finset.mem_coe] using u.property
      · simpa only [translated_projection f hf,Finset.mem_coe] using v.property
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have h := hmap hp
  rw [show f (torusProjection K r)+(r-f (torusProjection K r))=r by abel] at h
  exact h

theorem small_periodic_lifts {K a : ℕ} [NeZero K] (hK : 2*a<K)
    (S : Finset (DiscreteTorus K)) (hsmall : a*S.card<K)
    (hS : ((torusRangeGraph K a).induce (↑S)).Preconnected)
    (r : Vertex) (hr : torusProjection K r∈S) :
    ∃ C : Finset Vertex,
      (↑C : Set Vertex)=periodicLift K a S r ∧
      Set.BijOn (torusProjection K) (↑C) (↑S) ∧
      (∀ x∈C, ∀ y∈C, ∀ i, |x i-y i|≤a*((S.card:ℤ)-1)) := by
  obtain ⟨f,hf,hedge⟩ := small_set_lift S a hsmall
  let g : DiscreteTorus K → Vertex := fun x ↦ f x+(r-f (torusProjection K r))
  let C : Finset Vertex := S.image g
  have hproj : ∀ x, torusProjection K (g x)=x := translated_projection f hf r
  have heq : (↑C : Set Vertex)=periodicLift K a S r := by
    ext x
    constructor
    · intro hx
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
      exact translated_reach S hS f hf hedge r hr u hu
    · intro hx
      refine Finset.mem_image.mpr ⟨torusProjection K x,hx.1,?_⟩
      have he := lift_offset_reach hK S f hf hedge hx
      dsimp only [g]
      rw [← he]
      abel
  refine ⟨C,heq,?_,?_⟩
  · refine ⟨?_,?_,?_⟩
    · intro x hx
      rw [heq] at hx
      exact hx.1
    · intro x hx y hy hxy
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
      rw [hproj,hproj] at hxy
      exact congrArg g hxy
    · intro x hx
      exact ⟨g x,Finset.mem_image.mpr ⟨x,hx,rfl⟩,hproj x⟩
  · intro x hx y hy i
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
    have hspan := connected_coordinate_span ((torusRangeGraph K a).induce (↑S)) hS
      (fun x ↦ f x.val) a (fun x y h i ↦ (hedge x.val x.property y.val y.property h).2 i)
      ⟨u,hu⟩ ⟨v,hv⟩ i
    simpa only [g,Pi.add_apply,add_sub_add_right_eq_sub,Fintype.card_coe,Finset.coe_sort_coe] using hspan

end HardSphere.Lattice

end

end OAI
