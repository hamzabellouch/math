import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.GeometricRootClosure
import OAI.Combinatorics.Chromatic.Walls.RootClosureFacts

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open RawShuffle SlopeArithmetic WeightedTorusSeries WallUnits UnitSelections PowerSeries
noncomputable section
variable {M J : Type*} [AddCommGroup M] [Fintype J]
variable (Ω : M→+M→+ℤ) (C : (J→ℤ)→+M) (L h : M→+ℝ) (V : AddSubmonoid M)

def orderedPlaneProducts : Set (PowerSeries (Torus LaurentRay.vUnit Ω)) :=
  {F | ∃l : List (WallUnitDatum M),
    (∀u∈l,u.Allowed C (fun p=>p∈V ∧ 0<L p)) ∧
    l.Pairwise (fun u v=>0≤Ω u.root v.root) ∧ F=(l.map (WallUnitDatum.value Ω)).prod}

lemma indexedUnit_bool (a : ℕ) (k : ℤ) :
    indexedUnit (if decide (a=0) then 0 else 1) k=indexedUnit a k := by
  by_cases ha : a=0 <;> simp [indexedUnit,ha]

lemma listLiteral_product (l : List (WallUnitDatum M)) :
    ((List.finRange l.length).map (literalAxis (fun i=> (l.get i).parameter)
      (fun i=>decide ((l.get i).kind=0)) Ω (rootSum (fun i=> (l.get i).root))
      (fun i=> (l.get i).degree))).prod=(l.map (WallUnitDatum.value Ω)).prod := by
  have H : (List.finRange l.length).map (literalAxis (fun i=> (l.get i).parameter)
      (fun i=>decide ((l.get i).kind=0)) Ω (rootSum (fun i=> (l.get i).root))
      (fun i=> (l.get i).degree)) =
      (List.finRange l.length).map (fun i=>(l.get i).value Ω) := by
    apply List.map_congr_left
    intro i hi
    unfold literalAxis literalAxisScalar elementaryDiagonal WallUnitDatum.value
    rw [rootSum_single,one_nsmul,indexedUnit_bool]
  rw [H]
  change ((List.finRange l.length).map (WallUnitDatum.value Ω ∘ l.get)).prod=_
  rw [←List.map_map,List.map_get_finRange]

variable (hΩ : ∀p,Ω p p=0) (t : ℝ)
variable (hplane : ∀p∈V,∀q∈V,(Ω p q:ℝ)=t*(h p*L q-L p*h q))

include hΩ hplane in
lemma orderedPlane_zero_finite {F : PowerSeries (Torus LaurentRay.vUnit Ω)}
    (hF : F∈orderedPlaneProducts Ω C L V) :
    InPrecisionClosure LaurentRay.vUnit Ω
      (literalRootProducts Ω C (fun p=>p∈V ∧ h p=0))
      (PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω h)
        (zeroProject LaurentRay.vUnit Ω h) F) := by
  classical
  obtain ⟨l,hl,ho,rfl⟩:=hF
  let p : Fin l.length→M := fun i=>(l.get i).root
  let w : Fin l.length→ℕ := fun i=>(l.get i).degree
  let c : Fin l.length→ℝ := fun i=>L (p i)
  let η : Fin l.length→ℝ := fun i=>h (p i)
  have hall : ∀i,(l.get i).Allowed C (fun p=>p∈V ∧ 0<L p) := fun i=>hl _ (List.get_mem _ _)
  let : Fact (∀i,0<w i) := ⟨fun i=>(hall i).1⟩
  have hc : ∀i,0<c i := fun i=>(hall i).2.2.2
  have hp : ∀i j,(Ω (p i) (p j):ℝ)=t*(η i*c j-c i*η j) :=
    fun i j=>hplane _ (hall i).2.2.1 _ (hall j).2.2.1
  have hh : ∀d,h (rootSum p d)=slopeValue c η 0 d := rootSum_slope_zero p h c
  have hsort : (List.finRange l.length).Pairwise (fun i j=>0≤Ω (p i) (p j)) := by
    apply (List.pairwise_map (f:=l.get)
      (R:=fun u v : WallUnitDatum M=>0≤Ω u.root v.root)).mp
    simpa only [List.map_get_finRange] using ho
  have hv : ∀d∈slopeDimensions c η hc 0,rootSum p d∈V ∧ h (rootSum p d)=0 := by
    intro d hd
    refine ⟨rootSum_mem p V (fun i=>(hall i).2.2.1) d,?_⟩
    rw [hh]
    by_cases h0 : d=0
    · subst d; exact slopeValue_zero c η 0
    · exact (slopeValue_eq_zero_iff c η hc 0 d h0).mpr (hd.resolve_left h0)
  rw [←listLiteral_product Ω l]
  exact geometric_zero_rootClosure Ω hΩ p (fun i=>(l.get i).parameter)
    (fun i=>decide ((l.get i).kind=0)) w c η hc t hp (List.finRange l.length)
    (List.nodup_finRange _) (List.toFinset_finRange _) hsort C
    (rootSum_rootDegree p w C (fun i=>(hall i).2.1)) h 0 hh
    (fun p=>p∈V ∧ h p=0) hv

lemma orderedPlaneProducts_graded {F : PowerSeries (Torus LaurentRay.vUnit Ω)}
    (hF : F∈orderedPlaneProducts Ω C L V) : SeriesGraded LaurentRay.vUnit Ω C F := by
  obtain ⟨l,hl,ho,H⟩:=hF
  exact literalRootProducts_graded Ω C (fun p=>p∈V ∧ 0<L p) ⟨l,hl,H⟩

include hΩ hplane in

theorem orderedPlane_zero_completed {F : PowerSeries (Torus LaurentRay.vUnit Ω)}
    (hF : InPrecisionClosure LaurentRay.vUnit Ω (orderedPlaneProducts Ω C L V) F) :
    InPrecisionClosure LaurentRay.vUnit Ω
      (literalRootProducts Ω C (fun p=>p∈V ∧ h p=0))
      (PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω h)
        (zeroProject LaurentRay.vUnit Ω h) F) := by
  apply hF.zeroFactor Ω C (fun G hG=>orderedPlaneProducts_graded Ω C L V hG) h
  exact fun G hG=>orderedPlane_zero_finite Ω C L h V hΩ t hplane hG
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision Filter WallUnits
noncomputable section
variable {M J A ι : Type*} [AddCommGroup M] [Fintype J]
variable (Ω : M→+M→+ℤ) (C : (J→ℤ)→+M)

lemma SeriesGraded.list_prod (s : List A)
    (F : A→PowerSeries (Torus LaurentRay.vUnit Ω))
    (hF : ∀a∈s,SeriesGraded LaurentRay.vUnit Ω C (F a)) :
    SeriesGraded LaurentRay.vUnit Ω C (s.map F).prod := by
  induction s with
  | nil=>simpa using SeriesGraded.one LaurentRay.vUnit Ω C
  | cons a s ih=>
    simpa only [List.map_cons,List.prod_cons] using
      (hF a (by simp)).mul LaurentRay.vUnit Ω C (ih (fun x hx=>hF x (by simp [hx])))

lemma SeriesConverges.list_prod (l : Filter ι) (s : List A)
    (f : A→ι→PowerSeries (Torus LaurentRay.vUnit Ω))
    (F : A→PowerSeries (Torus LaurentRay.vUnit Ω))
    (hf : ∀a∈s,SeriesConverges LaurentRay.vUnit Ω l (f a) (F a))
    (hg : ∀a∈s,∀i,SeriesGraded LaurentRay.vUnit Ω C (f a i))
    (hG : ∀a∈s,SeriesGraded LaurentRay.vUnit Ω C (F a)) :
    SeriesConverges LaurentRay.vUnit Ω l (fun i=>(s.map (fun a=>f a i)).prod) (s.map F).prod := by
  induction s with
  | nil=>simpa using seriesConverges_const LaurentRay.vUnit Ω l 1
  | cons a s ih=>
    simpa only [List.map_cons,List.prod_cons] using
      (hf a (by simp)).mul LaurentRay.vUnit Ω C l
        (ih (fun x hx=>hf x (by simp [hx])) (fun x hx=>hg x (by simp [hx]))
          (fun x hx=>hG x (by simp [hx])))
        (hg a (by simp))
        (fun i=>SeriesGraded.list_prod Ω C s (fun x=>f x i) (fun x hx=>hg x (by simp [hx]) i))
        (hG a (by simp))
        (SeriesGraded.list_prod Ω C s F (fun x hx=>hG x (by simp [hx])))

lemma literal_lists_ordered_product (L : M→+ℝ) (V : AddSubmonoid M)
    (s : List A) (P : A→M→Prop)
    (g : A→PowerSeries (Torus LaurentRay.vUnit Ω))
    (hg : ∀a∈s,g a∈literalRootProducts Ω C (P a))
    (hP : ∀a∈s,∀p,P a p→p∈V ∧ 0<L p)
    (hself : ∀a∈s,∀p q,P a p→P a q→0≤Ω p q)
    (hpair : s.Pairwise (fun a b=>∀p q,P a p→P b q→0≤Ω p q)) :
    (s.map g).prod∈orderedPlaneProducts Ω C L V := by
  classical
  let ls (a : A) : List (WallUnitDatum M) :=
    if ha : a∈s then Classical.choose (hg a ha) else []
  have hls : ∀a∈s,(∀u∈ls a,u.Allowed C (P a)) ∧
      g a=((ls a).map (WallUnitDatum.value Ω)).prod:=by
    intro a ha
    dsimp [ls]
    rw [dite_eq_left ha]
    exact Classical.choose_spec (hg a ha)
  refine ⟨s.flatMap ls,?_,?_,?_⟩
  · intro u hu
    obtain ⟨a,ha,hu⟩:=List.mem_flatMap.mp hu
    have H:=(hls a ha).1 u hu
    exact ⟨H.1,H.2.1,hP a ha u.root H.2.2⟩
  · rw [List.pairwise_flatMap]
    constructor
    · intro a ha
      apply List.pairwise_iff_getElem.mpr
      intro i j hi hj hij
      exact hself a ha _ _ ((hls a ha).1 _ (List.getElem_mem hi)).2.2
        ((hls a ha).1 _ (List.getElem_mem hj)).2.2
    · apply hpair.imp_of_mem
      intro a b ha hb H u hu w hw
      exact H u.root w.root ((hls a ha).1 u hu).2.2 ((hls b hb).1 w hw).2.2
  · rw [List.map_flatMap,List.flatMap_def,List.prod_flatten]
    simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha
    exact (hls a ha).2

theorem completed_ordered_ray_product (L : M→+ℝ) (V : AddSubmonoid M)
    (s : List A) (P : A→M→Prop)
    (F : A→PowerSeries (Torus LaurentRay.vUnit Ω))
    (hF : ∀a∈s,InPrecisionClosure LaurentRay.vUnit Ω (literalRootProducts Ω C (P a)) (F a))
    (hP : ∀a∈s,∀p,P a p→p∈V ∧ 0<L p)
    (hself : ∀a∈s,∀p q,P a p→P a q→0≤Ω p q)
    (hpair : s.Pairwise (fun a b=>∀p q,P a p→P b q→0≤Ω p q)) :
    InPrecisionClosure LaurentRay.vUnit Ω (orderedPlaneProducts Ω C L V) (s.map F).prod := by
  classical
  let g (a : A) (T : Finset (PrecisionTest (M:=M))) :=
    if ha : a∈s then precisionApprox LaurentRay.vUnit Ω (hF a ha) T else 1
  have hg : ∀a∈s,∀T,g a T∈literalRootProducts Ω C (P a):=by
    intro a ha T
    dsimp [g]
    rw [dite_eq_left ha]
    exact precisionApprox_mem LaurentRay.vUnit Ω (hF a ha) T
  have hconv : ∀a∈s,SeriesConverges LaurentRay.vUnit Ω Filter.atTop (g a) (F a):=by
    intro a ha
    have he : g a=precisionApprox LaurentRay.vUnit Ω (hF a ha):=by
      funext T; dsimp [g]; rw [dite_eq_left ha]
    rw [he]
    exact precisionApprox_converges LaurentRay.vUnit Ω (hF a ha)
  apply InPrecisionClosure.of_converges LaurentRay.vUnit Ω Filter.atTop
    (SeriesConverges.list_prod Ω C Filter.atTop s g F hconv
      (fun a ha T=>literalRootProducts_graded Ω C (P a) (hg a ha T))
      (fun a ha=>(hF a ha).graded Ω C (fun G hG=>literalRootProducts_graded Ω C (P a) hG)))
  apply Eventually.of_forall
  intro T
  exact inPrecisionClosure_self LaurentRay.vUnit Ω
    (literal_lists_ordered_product Ω C L V s P (fun a=>g a T)
      (fun a ha=>hg a ha T) hP hself hpair)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
