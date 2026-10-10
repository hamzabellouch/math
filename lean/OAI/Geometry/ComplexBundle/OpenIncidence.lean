import OAI.Geometry.ComplexBundle.PointExpansion

namespace OAI

noncomputable section

/-! Openness of kernel, graph, frame, and rank incidence conditions. -/

section
open scoped ContDiff Topology MeasureTheory
open Set MeasureTheory MeasureTheory.Measure Module
namespace Kaplansky.SmoothKernel
variable {X V W : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
local instance : CompleteSpace W := FiniteDimensional.complete ℂ W

/-- Nullity for a surjective family defined smoothly only on an open domain.
Values outside that domain need not be smooth, continuous or surjective. -/
theorem open_kernel_incidence_image_null [MeasurableSpace V] [BorelSpace V]
    (a : X → V →L[ℂ] W) (U : Set X) (hU : IsOpen U)
    (ha : ContDiffOn ℝ ∞ a U) (hs : ∀ x ∈ U, Function.Surjective (a x))
    (hd : finrank ℝ (X × KernelModel V W)<finrank ℝ V) :
    μH[finrank ℝ V] {v : V | ∃ x ∈ U, a x v=0}=0 := by
  let A : SurjectiveFamily U V W := ⟨fun x => a x,ha.continuousOn.domRestrict,fun x => hs x x.property⟩
  let D (i : U) : Set X := U ∩ a ⁻¹' splitDomain (A.rightInverse i)
  have hD : ∀ i, IsOpen (D i) := fun i =>
    ha.continuousOn.isOpen_inter_preimage hU (splitDomain_open (A.rightInverse i))
  have hcov : U ⊆ ⋃ i, D i := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hx,A.center_mem ⟨x,hx⟩⟩
  obtain ⟨c,hc,hcov⟩ := (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover D hD hcov
  let := hc.toEncodable
  let f (i : U) (p : X × KernelModel V W) : V :=
    kernelProjection (A.rightInverse i) (a p.1)
      (((LinearMap.ker (A.map i).toLinearMap).subtypeL).comp
        (A.modelEquiv i).toContinuousLinearMap p.2)
  have hf (i : U) : ContDiffOn ℝ ∞ (f i) (D i ×ˢ univ) := by
    intro p hp
    have hk := ((kernelProjection_smooth (A.rightInverse i) (a p.1) hp.1.2).restrict_scalars ℝ).comp p.1
      ((ha p.1 hp.1.1).contDiffAt (hU.mem_nhds hp.1.1))
    have hc := ((ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ).contDiff.contDiffAt.comp p.1 hk).comp p contDiffAt_fst
    have hz : ContDiffAt ℝ ∞ (fun p : X × KernelModel V W =>
        (((LinearMap.ker (A.map i).toLinearMap).subtypeL).comp
          (A.modelEquiv i).toContinuousLinearMap) p.2) p :=
      ((((LinearMap.ker (A.map i).toLinearMap).subtypeL).comp
        (A.modelEquiv i).toContinuousLinearMap).restrictScalars ℝ).contDiff.contDiffAt.comp p contDiffAt_snd
    exact (hc.clm_apply hz).contDiffWithinAt
  have hn (i : c) : μH[finrank ℝ V] (f i.val '' (D i.val ×ˢ univ))=0 :=
    Kaplansky.Incidence.smoothOn_open_image_null ((hD i.val).prod isOpen_univ)
      ((hf i.val).of_le (by simp)) hd
  apply measure_mono_null (t := ⋃ i : c, f i.val '' (D i.val ×ˢ univ)) ?_
    (measure_iUnion_null hn)
  rintro v ⟨x,hx,hv⟩
  obtain ⟨i,hi,hxi⟩ : ∃ i ∈ c, x ∈ D i := by
    simpa only [mem_iUnion,exists_prop] using hcov hx
  refine mem_iUnion.mpr ⟨⟨i,hi⟩,(x,A.toModel i v),⟨hxi,mem_univ _⟩,?_⟩
  exact A.fromModel_toModel i ⟨x,hx⟩ hxi.2 v hv

end Kaplansky.SmoothKernel

end

section
open scoped ContDiff MeasureTheory
open Module Set MeasureTheory MeasureTheory.Measure
namespace Kaplansky.Incidence
open ComplexGrassmann SmoothKernel
variable {s k t l q : ℕ}
variable {Y V : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
variable (ev : Y → V →L[ℂ] TupleAmbient q s k t l) (U : Set Y)

omit [FiniteDimensional ℝ Y] [FiniteDimensional ℂ V] in
theorem graphEvaluation_smoothOn (hU : IsOpen U) (he : ContDiffOn ℝ ∞ ev U) :
    ContDiffOn ℝ ∞ (graphEvaluation ev) (U ×ˢ univ) := by
  intro p hp
  have hc : ContDiff ℂ ∞ (fun z :
      (TupleAmbient q s k t l →L[ℂ] TupleTarget q s l) × (V →L[ℂ] TupleAmbient q s k t l) =>
      z.1.comp z.2) := contDiff_fst.clm_comp contDiff_snd
  have h1 := ((tupleGraphRestriction_smooth (q := q) (s := s) (k := k) (t := t) (l := l)).restrict_scalars ℝ).contDiffAt.comp p contDiffAt_snd
  have h2 := ((he p.1 hp.1).contDiffAt (hU.mem_nhds hp.1)).comp p contDiffAt_fst
  exact ((hc.restrict_scalars ℝ).contDiffAt.comp p (h1.prodMk h2)).contDiffWithinAt

/-- Actual graph incidence over an open base chart is null under the real
dimension gap; no extension of its evaluation map off the chart is assumed. -/
theorem open_graph_incidence_image_null [MeasurableSpace V] [BorelSpace V]
    (hU : IsOpen U) (he : ContDiffOn ℝ ∞ ev U)
    (hs : ∀ y ∈ U, Function.Surjective (ev y))
    (hgap : finrank ℝ Y+2*s*k+2*t*l<2*q*s*l) :
    μH[finrank ℝ V] {v : V | ∃ y ∈ U, ∃ (a : GraphSlope s k) (b : GraphSlope t l),
      ∀ i, ∀ x ∈ a.toLinearMap.graph, ev y v i x ∈ b.toLinearMap.graph}=0 := by
  by_cases hu : U.Nonempty
  · obtain ⟨y,hy⟩ := hu
    have hsur : ∀ p ∈ U ×ˢ (univ : Set (GraphSlope s k × GraphSlope t l)),
        Function.Surjective (graphEvaluation ev p) := fun p hp =>
      (tupleGraphRestriction_surjective p.2.1 p.2.2).comp (hs p.1 hp.1)
    have hr := (graphEvaluation ev (y,(0,0))).toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr (hsur _ ⟨hy,mem_univ _⟩),finrank_top,tupleTarget_finrank] at hr
    have hd : finrank ℝ ((Y × (GraphSlope s k × GraphSlope t l)) × KernelModel V (TupleTarget q s l)) < finrank ℝ V := by
      rw [incidence_model_finrank,finrank_real_of_complex]
      simp only [Nat.mul_assoc] at *
      omega
    have hn := open_kernel_incidence_image_null (graphEvaluation ev) (U ×ˢ univ)
      (hU.prod isOpen_univ) (graphEvaluation_smoothOn ev U hU he) hsur hd
    have heq : {v : V | ∃ p ∈ U ×ˢ (univ : Set (GraphSlope s k × GraphSlope t l)), graphEvaluation ev p v=0} =
        {v : V | ∃ y ∈ U, ∃ (a : GraphSlope s k) (b : GraphSlope t l), ∀ i, ∀ x ∈ a.toLinearMap.graph, ev y v i x ∈ b.toLinearMap.graph} := by
      ext v
      simp only [mem_ofPred_eq,Prod.exists,mem_prod,mem_univ,and_true,graphEvaluation_zero_iff]
      constructor
      · rintro ⟨y,a,b,hy,h⟩; exact ⟨y,hy,a,b,h⟩
      · rintro ⟨y,hy,a,b,h⟩; exact ⟨y,a,b,hy,h⟩
    rw [heq] at hn
    exact hn
  · have hempty : U=∅ := Set.not_nonempty_iff_eq_empty.mp hu
    simp [hempty]

end Kaplansky.Incidence

end

section
open scoped ContDiff MeasureTheory
open Set Module MeasureTheory MeasureTheory.Measure
namespace Kaplansky.Incidence
open ComplexGrassmann
variable {q s k t l : ℕ}
variable {Y V : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
variable (ev : Y → V →L[ℂ] TupleOperators q s k t l) (U : Set Y)

def OpenFrameBad : Set V :=
  {v | ∃ y ∈ U, ∃ (P : Grassmann s k) (Q : Grassmann t l),
    ∀ i, ∀ x ∈ P.val, ev y v i x ∈ Q.val}

theorem openFrameBad_null [MeasurableSpace V] [BorelSpace V]
    (hU : IsOpen U) (he : ContDiffOn ℝ ∞ ev U)
    (hs : ∀ y ∈ U, Function.Surjective (ev y))
    (hgap : finrank ℝ Y+2*s*k+2*t*l<2*q*s*l) :
    μH[finrank ℝ V] (OpenFrameBad ev U)=0 := by
  obtain ⟨c,hc,hcover⟩ := exists_countable_graph_cover (s := s) (k := k)
  obtain ⟨d,hd,hcover'⟩ := exists_countable_graph_cover (s := t) (k := l)
  let := hc.toEncodable
  let := hd.toEncodable
  let bad (i : c × d) : Set V := {v | ∃ y ∈ U, ∃ (a : GraphSlope s k) (b : GraphSlope t l),
    ∀ j, ∀ x ∈ a.toLinearMap.graph,
      frameEvaluation i.1.val i.2.val (ev y v) j x ∈ b.toLinearMap.graph}
  have hn (i : c × d) : μH[finrank ℝ V] (bad i)=0 := by
    let ef : Y → V →L[ℂ] TupleAmbient q s k t l := fun y =>
      (frameEvaluation i.1.val i.2.val).comp (ev y)
    have hf : ContDiffOn ℝ ∞ ef U := by
      have hh : ContDiff ℂ ∞ (fun L : V →L[ℂ] TupleOperators q s k t l =>
        (frameEvaluation i.1.val i.2.val).comp L) := contDiff_const.clm_comp contDiff_id
      exact (hh.restrict_scalars ℝ).comp_contDiffOn he
    exact open_graph_incidence_image_null ef U hU hf
      (fun y hy => (frameEvaluation_surjective i.1.val i.2.val).comp (hs y hy)) hgap
  apply measure_mono_null (t := ⋃ i : c × d, bad i) ?_ (measure_iUnion_null hn)
  rintro v ⟨y,hy,P,Q,hPQ⟩
  obtain ⟨F,hFc,hF⟩ := hcover P
  obtain ⟨G,hGd,hG⟩ := hcover' Q
  refine mem_iUnion.mpr ⟨(⟨F,hFc⟩,⟨G,hGd⟩),y,hy,slopeCoordinate F P,slopeCoordinate G Q,?_⟩
  apply (frame_incidence_iff F G (ev y v) _ _).mp
  have hp : graphPlane F (slopeCoordinate F P).toLinearMap=P.val :=
    congrArg Subtype.val (slopePoint_coordinate F P hF)
  have hq : graphPlane G (slopeCoordinate G Q).toLinearMap=Q.val :=
    congrArg Subtype.val (slopePoint_coordinate G Q hG)
  rw [hp,hq]
  exact hPQ

end Kaplansky.Incidence

end

open scoped ContDiff MeasureTheory
open Set Module MeasureTheory MeasureTheory.Measure
namespace Kaplansky.Incidence
variable {q d r : ℕ}
variable {Y V : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

def OpenRankBad (ev : Y → V →L[ℂ] MatrixTuple q d r) (U : Set Y) (s t : ℕ) : Set V :=
  {v | ∃ y ∈ U, ev y v ∈ RankBad s t}

theorem openRankBad_null [MeasurableSpace V] [BorelSpace V]
    (ev : Y → V →L[ℂ] MatrixTuple q d r) (U : Set Y)
    (hU : IsOpen U) (he : ContDiffOn ℝ ∞ ev U)
    (hs : ∀ y ∈ U, Function.Surjective (ev y)) {s t : ℕ}
    (hsd : s≤d) (htr : t≤r)
    (hgap : finrank ℝ Y+2*s*(d-s)+2*t*(r-t)<2*q*s*(r-t)) :
    μH[finrank ℝ V] (OpenRankBad ev U s t)=0 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hsd
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le htr
  have heq : OpenRankBad ev U s t=OpenFrameBad ev U := by
    ext v
    constructor
    · rintro ⟨y,hy,S,hS,T,hT,h⟩
      exact ⟨y,hy,⟨S,hS⟩,⟨T,hT⟩,h⟩
    · rintro ⟨y,hy,⟨S,hS⟩,⟨T,hT⟩,h⟩
      exact ⟨y,hy,S,hS,T,hT,h⟩
  rw [heq]
  exact openFrameBad_null ev U hU he hs (by simpa using hgap)

/-- A single parameter avoids every forbidden rank pair on every chart of a
countable family. The maps, kernels, graph coverage and nullity are actual;
only the smooth surjective coordinate evaluation data enter as hypotheses. -/
theorem exists_countable_chart_incidence_parameter {ι : Type*} [Countable ι]
    (ev : ι → Y → V →L[ℂ] MatrixTuple q d r) (U : ι → Set Y)
    (hU : ∀ j, IsOpen (U j)) (he : ∀ j, ContDiffOn ℝ ∞ (ev j) (U j))
    (hs : ∀ j y, y ∈ U j → Function.Surjective (ev j y))
    (pairs : Finset (ℕ × ℕ))
    (hpairs : ∀ p ∈ pairs, p.1≤d ∧ p.2≤r ∧
      finrank ℝ Y+2*p.1*(d-p.1)+2*p.2*(r-p.2)<2*q*p.1*(r-p.2)) :
    ∃ v : V, ∀ j y, y ∈ U j → ∀ p ∈ pairs, ∀ S : Submodule ℂ (Fin d → ℂ),
      finrank ℂ S=p.1 → p.2<finrank ℂ
        (⨆ i, S.map (ev j y v i).toLinearMap : Submodule ℂ (Fin r → ℂ)) := by
  borelize V
  have hn : μH[finrank ℝ V] (⋃ j, ⋃ p ∈ pairs, OpenRankBad (ev j) (U j) p.1 p.2)=0 :=
    measure_iUnion_null (fun j => measure_iUnion_null (fun p => measure_iUnion_null (fun hp =>
      openRankBad_null (ev j) (U j) (hU j) (he j) (hs j)
        (hpairs p hp).1 (hpairs p hp).2.1 (hpairs p hp).2.2)))
  have hev : ∃ v : V, v ∉ ⋃ j, ⋃ p ∈ pairs, OpenRankBad (ev j) (U j) p.1 p.2 := by
    by_contra h
    push Not at h
    have hu : (⋃ j, ⋃ p ∈ pairs, OpenRankBad (ev j) (U j) p.1 p.2)=univ := Set.eq_univ_of_forall h
    rw [hu] at hn
    exact (ne_of_gt (isOpen_univ.measure_pos (μH[finrank ℝ V]) Set.univ_nonempty)) hn
  obtain ⟨v,hv⟩ := hev
  refine ⟨v,fun j y hy p hp S hS => ?_⟩
  by_contra h
  have hd : finrank ℂ (⨆ i, S.map (ev j y v i).toLinearMap : Submodule ℂ (Fin r → ℂ))≤p.2 := by omega
  obtain ⟨T,hWT,hT⟩ := exists_super_finrank
    (⨆ i, S.map (ev j y v i).toLinearMap : Submodule ℂ (Fin r → ℂ)) hd
      (by simpa using (hpairs p hp).2.1)
  apply hv
  refine mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨p,mem_iUnion.mpr ⟨hp,y,hy,S,hS,T,hT,?_⟩⟩⟩
  intro i x hx
  exact hWT ((le_iSup (fun i => S.map (ev j y v i).toLinearMap) i)
    (Submodule.mem_map.mpr ⟨x,hx,rfl⟩))

end Kaplansky.Incidence

end

end OAI
