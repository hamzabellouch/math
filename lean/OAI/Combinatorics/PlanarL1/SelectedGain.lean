import OAI.Combinatorics.PlanarL1.SecondaryGain

namespace OAI


section

namespace PlanarL1.Columns.Model.BData
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)}

lemma comparison_distance (D : BData M) (lam : ℝ≥0) (hlam : lam≤(1:ℝ≥0)/100)
    (positive : Bool) (i j : Fin (k+1)) (H T : D.band) :
    |(D.comparison lam hlam positive).value i H-(D.comparison lam hlam positive).value j T|=
      |D.value lam i H-D.value lam j T| := by
  rw [D.comparison_convert lam hlam positive i H,D.comparison_convert lam hlam positive j T]
  rw [show D.offset+D.orientation positive*(D.comparison lam hlam positive).value i H-
      (D.offset+D.orientation positive*(D.comparison lam hlam positive).value j T)=
      D.orientation positive*((D.comparison lam hlam positive).value i H-
        (D.comparison lam hlam positive).value j T) by ring,
    abs_mul,D.orientation_unit,one_mul]
end PlanarL1.Columns.Model.BData

end



section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory SecondaryGeometry FiniteRandom
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable (b : Block (M := M) q p L U)
variable (c : M.Point (BandTrees.band broad b.lower) (BandTrees.root M broad b.lower b.1.2))
variable (i : GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG))
variable (w : M.Point (group A SA SB v hv i).broad (group A SA SB v hv i).broad_root)
variable (hw : w ∈ (group A SA SB v hv i).seeds)
variable (hfar : 1≤dist (A.point w.column w.height) (A.point c.column c.height))
variable (C : (group A SA SB v hv i).Component)
variable (x : M.Point (BandTrees.band narrow (group A SA SB v hv i).lower)
  ((group A SA SB v hv i).root C))
variable (positive : Bool) (hx : x ∈ (group A SA SB v hv i).admittedSeeds positive C)
variable (hl : (group A SA SB v hv i).lower+9*a₂/100 ≤ x.height)
variable (hu : x.height ≤ (group A SA SB v hv i).lower+a₂-9*a₂/100)
variable (hT : c.height ∈ (group A SA SB v hv i).data.band)
variable (hn : SB.name c.column c.height=(group A SA SB v hv i).index)
variable (hclose : ∀ hH : x.height ∈ (group A SA SB v hv i).data.band,
    |(group A SA SB v hv i).data.value Group.lam x.column ⟨x.height,hH⟩-
      (group A SA SB v hv i).data.value Group.lam c.column ⟨c.height,hT⟩|≤R/10000)
variable {m : ℕ} (hm : 0 < m)

include hw hfar hx hl hu hn hclose in
lemma gain_of_suppression
    (omega : Sample (group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) m)
    (ho : omega.1 (group A SA SB v hv i).index=positive)
    (hk : omega.2.1 i=true)
    (hs : ∀ j, Touch A SA SB v hv b c j → j≠i → omega.2.1 j=false) :
    kappaB*R/50 < (layer (group A SA SB v hv) hm omega).sets.separation x.column x.height c.column c.height := by
  let a := (group A SA SB v hv i).index
  have hx' : x ∈ (group A SA SB v hv i).admittedSeeds (omega.1 a) C := by
    rw [ho]
    exact hx
  let z : Acting (group A SA SB v hv) omega a := ⟨⟨i,C⟩,rfl,hk,⟨x,hx'⟩⟩
  have hy := batch_not_domain A SA SB v hv b c i w hw hfar hm omega a hs
  apply gain_external (group A SA SB v hv) hm omega a z x hx' hl hu c.column c.height hT hy hn
  intro hH
  calc
    _ = |(group A SA SB v hv i).data.value Group.lam x.column ⟨x.height,hH⟩-
      (group A SA SB v hv i).data.value Group.lam c.column ⟨c.height,hT⟩| :=
      (group A SA SB v hv i).data.comparison_distance Group.lam Group.lam_bound _ _ _ _ _
    _ ≤ _ := hclose hH

include hw hfar hx hl hu hn hclose in
lemma admitted_probability
    (hc : c.height ∈ BandTrees.band narrow b.lower₂)
    (hp : Tiling.Padded a₁ q c.height (a₁/10)) (hN : Tiling.Padded a₂ p c.height (a₂/10)) :
    1/(2:ℝ)^(SurvivingGroups.packBound+2) ≤ FiniteRandom.prob
      (fun omega : Sample (group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) m =>
        kappaB*R/50 < (layer (group A SA SB v hv) hm omega).sets.separation x.column x.height c.column c.height) := by
  let T := Finset.univ.filter (Touch A SA SB v hv b c (phaseD := phaseD) (phaseG := phaseG))
  have hcard : T.card≤SurvivingGroups.packBound := touching_finset_card A SA SB v hv b c hc hp hN
  have hprob := prob_orient_keep_suppress (group A SA SB v hv) m (group A SA SB v hv i).index positive i T hcard
  refine hprob.trans (@FiniteRandom.prob_mono_instances (Sample (group A SA SB v hv) m) _ _ _ _ ?_)
  intro omega he
  apply gain_of_suppression A SA SB v hv b c i w hw hfar C x positive hx hl hu hT hn hclose hm omega he.1 he.2.1
  intro j hj hji
  exact he.2.2 j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩) hji
end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Columns.Model.SecondaryGeometry.Group
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB (⟨lambda,by norm_num [lambda,R]⟩) Ω μ}
variable (G : SecondaryGeometry.Group A S)

noncomputable def componentOf (w : M.Point G.broad G.broad_root) : G.Component :=
  (M.activeGraph (BandTrees.band narrow G.lower)).connectedComponentMk w.column

noncomputable def endpoint (w : M.Point G.broad G.broad_root) (hw : w ∈ G.seeds) :
    M.Point (BandTrees.band narrow G.lower) (G.root (G.componentOf w)) where
  column := w.column
  height := w.height
  inBand := G.height w hw
  reachable := (G.componentOf w).reachable_of_mem_supp (BandTrees.root_mem _ _ _ _) rfl

lemma endpoint_mem (w : M.Point G.broad G.broad_root) (hw : w ∈ G.seeds) :
    G.endpoint w hw ∈ G.allSeeds (G.componentOf w) :=
  (G.allSeeds_description _ _).mpr ⟨w,hw,rfl,rfl⟩

lemma endpoint_admitted (w : M.Point G.broad G.broad_root) (hw : w ∈ G.seeds) (positive : Bool) :
    G.endpoint w hw ∈ G.admittedSeeds positive (G.componentOf w) ↔
      G.Admitted positive (G.componentOf w) (G.endpoint w hw) := by
  simp only [admittedSeeds,Finset.mem_filter,G.endpoint_mem w hw,true_and]
end PlanarL1.Columns.Model.SecondaryGeometry.Group

end



section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory SecondaryGeometry VertexTests
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
private lemma bvalue_transport {D E : BData M} (h : D=E) (j : Fin (k+1)) (H : ℝ)
    (hD : H∈D.band) (hE : H∈E.band) :
    D.value Group.lam j ⟨H,hD⟩=E.value Group.lam j ⟨H,hE⟩ := by subst E; rfl

variable (w : Endpoint A SA SB v L U hv q p phaseD phaseG)

lemma groupOf_index : (group A SA SB v hv (groupOf A SA SB v hv w)).index=indexB A SB v w.val := rfl
lemma groupOf_lower : (group A SA SB v hv (groupOf A SA SB v hv w)).lower=PairGeometry.narrowLower A v p w.val := rfl

noncomputable def selectedComponent :=
  (group A SA SB v hv (groupOf A SA SB v hv w)).componentOf (rawSeed A SA SB v hv w).point
noncomputable def selectedPoint :=
  (group A SA SB v hv (groupOf A SA SB v hv w)).endpoint (rawSeed A SA SB v hv w).point
    (groupOf_seed A SA SB v hv w)
lemma selectedPoint_column : (selectedPoint A SA SB v hv w).column=(v w.val).column := rfl
lemma selectedPoint_height : (selectedPoint A SA SB v hv w).height=(v w.val).height := rfl
lemma selectedPoint_mem : selectedPoint A SA SB v hv w ∈
    (group A SA SB v hv (groupOf A SA SB v hv w)).allSeeds (selectedComponent A SA SB v hv w) :=
  Group.endpoint_mem _ _ _

lemma selectedPoint_plateau :
    (group A SA SB v hv (groupOf A SA SB v hv w)).lower+9*a₂/100≤(selectedPoint A SA SB v hv w).height ∧
    (selectedPoint A SA SB v hv w).height≤(group A SA SB v hv (groupOf A SA SB v hv w)).lower+a₂-9*a₂/100 := by
  have h := (witness A SA SB v hv w).interior.2.1
  have hh := h
  dsimp only [Tiling.Padded] at hh
  change _≤(v w.val).height ∧ (v w.val).height≤_
  rw [groupOf_lower]
  dsimp [PairGeometry.narrowLower]
  have ha : 0<a₂ := by norm_num [a₂]
  constructor <;> linarith [hh.1,hh.2]

variable {y : V}
variable (hi : VertexBands.Interior A v (hv := hv) q p phaseD phaseG y)
noncomputable def blockFor : Block (M := M) q p L U :=
  ⟨VertexBands.bandComponent A v L U hv q y,
    ⟨⟨Tiling.index a₂ p (v y).height,
      (Tiling.mem_processed interpolationB.2.1 p L U _).mpr
        ⟨(v y).height,Tiling.mem_band_index interpolationB.2.1 p _,hv y⟩⟩,
      hi.narrow_sub A v⟩⟩

variable (he : Eligible A SA SB v w.val y) (ha : 1≤dist (v w.val) (v y))
variable (hc : Cutoffs A SA SB v w.val y)
variable (positive : Bool)
variable (had : (group A SA SB v hv (groupOf A SA SB v hv w)).Admitted positive
  (selectedComponent A SA SB v hv w) (selectedPoint A SA SB v hv w))
variable {m : ℕ} (hm : 0 < m)

include hi he ha hc had in
lemma selected_admitted_probability :
    1/(2:ℝ)^(SurvivingGroups.packBound+2) ≤ FiniteRandom.prob
      (fun omega : Sample (group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) m =>
        kappaB*R/50 < (layer (group A SA SB v hv) hm omega).sets.separation
          (v w.val).column (v w.val).height (v y).column (v y).height) := by
  let b := blockFor A v hv hi
  let c := VertexBands.point A v L U hv q y
  let i := groupOf A SA SB v hv w
  let G := group A SA SB v hv i
  have hT : c.height∈G.data.band := by
    change (v y).height∈(SB.chart (indexB A SB v w.val)).band
    rw [←he.namesB A SA SB v]
    exact SB.height_in _ _
  have hn : SB.name c.column c.height=G.index := he.namesB A SA SB v
  have hfar : 1≤dist (A.point (rawSeed A SA SB v hv w).point.column (rawSeed A SA SB v hv w).point.height)
      (A.point c.column c.height) := by
    change 1≤dist (A.point (v w.val).column (v w.val).height) (A.point (v y).column (v y).height)
    simpa only [A.coordinate_point] using ha
  have had' : selectedPoint A SA SB v hv w ∈ G.admittedSeeds positive (selectedComponent A SA SB v hv w) :=
    (Group.endpoint_admitted _ _ _ _).mpr had
  have hclose (hH : (selectedPoint A SA SB v hv w).height∈G.data.band) :
      |G.data.value Group.lam (selectedPoint A SA SB v hv w).column ⟨(selectedPoint A SA SB v hv w).height,hH⟩-
        G.data.value Group.lam c.column ⟨c.height,hT⟩|≤R/10000 := by
    change |fullValue A SB v w.val-(SB.chart (indexB A SB v w.val)).value Group.lam (v y).column ⟨(v y).height,hT⟩|≤_
    have hh := bvalue_transport (congrArg SB.chart (he.namesB A SA SB v).symm)
      (v y).column (v y).height hT (SB.height_in _ _)
    rw [hh]
    exact hc.2.2.le
  exact admitted_probability A SA SB v hv b c i (rawSeed A SA SB v hv w).point
    (groupOf_seed A SA SB v hv w) hfar (selectedComponent A SA SB v hv w)
    (selectedPoint A SA SB v hv w) positive had' (selectedPoint_plateau A SA SB v hv w).1
    (selectedPoint_plateau A SA SB v hv w).2 hT hn hclose hm
    (PairGeometry.narrow_height A v p y) hi.1 hi.2.1
end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Columns.Model
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace BData
variable {A : Ambient M} (H : A.History (R/200)) (region : Set (M.Point Set.univ A.root))
variable (hcross : ∀ j, 10≤(R/200)*H.radius j)
noncomputable def normalizedIncrement (D : BData M) (e : Bool) : M.Field D.band 5 :=
  D.auxiliaryField (D.incrementAuxiliary H 1 region e (by norm_num [R])
    (by norm_num [R]) (by norm_num) (by simpa using hcross))
    SecondaryGeometry.Group.lam SecondaryGeometry.Group.lam_bound
lemma normalizedIncrement_coordinates {D E : BData M} (h : D=E)
    {i j : Fin (k+1)} {s t : ℝ} (hi : i=j) (hs : s=t)
    (hI : s∈D.band) (hJ : t∈E.band) (e : Bool) :
    (normalizedIncrement H region hcross D e).value i ⟨s,hI⟩=
      (normalizedIncrement H region hcross E e).value j ⟨t,hJ⟩ := by
  subst E; subst j; subst t; rfl
end BData

namespace IncrementStep
variable (A : Ambient M) (S : BState M kappaB SecondaryGeometry.Group.lam Ω μ)
variable (hist : Fin (S.count+1) → A.History (R/200))
variable (hcross : ∀ a j, 10≤(R/200)*(hist a).radius j)
variable (hrec : ∀ a, (S.chart a).Recorded (hist a) (by norm_num [R]) (by norm_num [R]))

noncomputable def update (sign : Fin (S.count+1) → Bool) :
    BState M kappaB SecondaryGeometry.Group.lam Ω μ :=
  S.increment (r := 1) A hist sign (by norm_num [R]) (by norm_num [R]) (by norm_num)
    (by simpa using hcross) hrec verticalB.1 (by norm_num [kappaB,a₂])
    SecondaryGeometry.Group.lam_bound (by change kappaB*lambda*10≤1/8; norm_num [kappaB,a₂,lambda,R])

lemma names (sign : Fin (S.count+1) → Bool) :
    (update A S hist hcross hrec sign).name=S.name := rfl

lemma separation_lower (sign : Fin (S.count+1) → Bool) (a : Fin (S.count+1))
    (i j : Fin (k+1)) (s t : ℝ) (hi : S.name i s=a) (hj : S.name j t=a)
    (hs : s∈(S.chart a).band) (ht : t∈(S.chart a).band) :
    kappaB*|(BData.normalizedIncrement (hist a) (S.region A a) (hcross a) (S.chart a) (sign a)).value i ⟨s,hs⟩-
      (BData.normalizedIncrement (hist a) (S.region A a) (hcross a) (S.chart a) (sign a)).value j ⟨t,ht⟩|≤
      (update A S hist hcross hrec sign).sets.separation i s j t := by
  let F := S.incrementFields A hist sign (by norm_num [R]) (by norm_num [R])
    (by norm_num : (0:ℝ)<1) (by simpa using hcross) SecondaryGeometry.Group.lam_bound
  have he := S.fieldUpdate_separation F verticalB.1 (by norm_num [kappaB,a₂])
    SecondaryGeometry.Group.lam_bound
    (S.increment_boundary (r := 1) A hist sign (by norm_num [R]) (by norm_num [R]) (by norm_num)
      (by simpa using hcross) hrec verticalB.1 SecondaryGeometry.Group.lam_bound
      (by change kappaB*lambda*10≤1/8; norm_num [kappaB,a₂,lambda,R])) i j s t a hi hj
  change (update A S hist hcross hrec sign).sets.separation i s j t=
    max |s-t| |S.newValue F i s-S.newValue F j t| at he
  rw [he,S.newValue_eq F i s a hi,S.newValue_eq F j t a hj,
    ←mul_sub,abs_mul,abs_of_nonneg verticalB.1]
  exact le_max_right _ _

variable {a : Fin (S.count+1)} {D : OrderedData M}
variable (hD : S.chart a=.ordered D) {root : Fin (k+1)} (x y : M.Point D.band root)
variable (hx : A.Common S.name (A.point x.column x.height) 1 a)
variable (hy : A.Common S.name (A.point y.column y.height) 1 a)
variable (ho : (D.base.transverse (by norm_num) D.lower D.upper).eval x *
  (D.base.transverse (by norm_num) D.lower D.upper).eval y<0)
variable (hlx : R/100≤|(D.base.transverse (by norm_num) D.lower D.upper).eval x|)
variable (hly : R/100≤|(D.base.transverse (by norm_num) D.lower D.upper).eval y|)
variable (hux : |(D.base.transverse (by norm_num) D.lower D.upper).eval x|≤8)
variable (huy : |(D.base.transverse (by norm_num) D.lower D.upper).eval y|≤8)

include hD hx hy ho hlx hly hux huy in
/-- The actual simultaneous append of every old ordered history has at least
one favorable value of the common identifier's fair coin. -/
lemma favorable_sign : ∃ e : Bool, ∀ sign : Fin (S.count+1) → Bool, sign a=e →
    kappaB*lambda*R/50≤(update A S hist hcross hrec sign).sets.separation
      x.column x.height y.column y.height := by
  have hr : (BData.ordered D).Recorded (hist a) (by norm_num [R]) (by norm_num [R]) := by
    rw [←hD]
    exact hrec a
  obtain ⟨e,he⟩ := D.exists_increment_gain (hist a) (S.region A a) (hcross a) hr x y hx hy
    ho hlx hly hux huy
  refine ⟨e,fun sign hs => ?_⟩
  have hxi : S.name x.column x.height=a := hx.center A (by norm_num)
  have hyi : S.name y.column y.height=a := hy.center A (by norm_num)
  have hi := S.height_named x.column x.height a hxi
  have hj := S.height_named y.column y.height a hyi
  have hb := separation_lower A S hist hcross hrec sign a x.column y.column x.height y.height hxi hyi hi hj
  rw [hs] at hb
  have ex := BData.normalizedIncrement_coordinates (hist a) (S.region A a) (hcross a) hD
    (i := x.column) rfl (s := x.height) rfl hi x.inBand e
  have ey := BData.normalizedIncrement_coordinates (hist a) (S.region A a) (hcross a) hD
    (i := y.column) rfl (s := y.height) rfl hj y.inBand e
  rw [ex,ey] at hb
  have hh := mul_le_mul_of_nonneg_left he verticalB.1
  change kappaB*(lambda*R/50)≤kappaB*|_ - _| at hh
  calc
    kappaB*lambda*R/50 = kappaB*(lambda*R/50) := by ring
    _ ≤ _ := hh
    _ ≤ _ := hb

include hD hx hy ho hlx hly hux huy in
lemma success_probability : 1/2≤FiniteRandom.prob (fun sign : Fin (S.count+1) → Bool =>
    kappaB*lambda*R/50≤(update A S hist hcross hrec sign).sets.separation
      x.column x.height y.column y.height) := by
  obtain ⟨e,he⟩ := favorable_sign A S hist hcross hrec hD x y hx hy ho hlx hly hux huy
  rw [←FiniteRandom.prob_coin a e]
  exact @FiniteRandom.prob_mono_instances (Fin (S.count+1) → Bool) _ _ _ _ he
end IncrementStep
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory SecondaryGeometry VertexTests
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}

noncomputable def ofWitness {x : V} (W : Witness A SA SB v L U hv q p phaseD phaseG x) :
    Endpoint A SA SB v L U hv q p phaseD phaseG :=
  ⟨x,(mem_remaining A SA SB v hv x).mpr ⟨W⟩⟩

variable (w z : Endpoint A SA SB v L U hv q p phaseD phaseG)
variable (he : Eligible A SA SB v w.val z.val) (hc : Cutoffs A SA SB v w.val z.val)
variable (ha : 1≤dist (v w.val) (v z.val)) (hd : dist (v w.val) (v z.val)<2)

lemma ordered_of_rejected
    (hn : ¬(group A SA SB v hv (groupOf A SA SB v hv w)).Admitted true
      (selectedComponent A SA SB v hv w) (selectedPoint A SA SB v hv w)) :
    ∃ D : OrderedData M, SB.chart (indexB A SB v w.val)=.ordered D := by
  cases hD : SB.chart (indexB A SB v w.val) with
  | ordinary C =>
    apply False.elim
    apply hn
    left
    change (SB.chart (indexB A SB v w.val)).isOrdinary=true
    rw [hD]
    rfl
  | ordered D => exact ⟨D,rfl⟩

include he hc ha hd in
/-- The two actual retained endpoint groups, rather than hypothetical seeds,
force transverse values in their actual common old ordered chart. -/
theorem transverse_of_rejected
    (hwp : ¬(group A SA SB v hv (groupOf A SA SB v hv w)).Admitted true
      (selectedComponent A SA SB v hv w) (selectedPoint A SA SB v hv w))
    (hwn : ¬(group A SA SB v hv (groupOf A SA SB v hv w)).Admitted false
      (selectedComponent A SA SB v hv w) (selectedPoint A SA SB v hv w))
    (hzp : ¬(group A SA SB v hv (groupOf A SA SB v hv z)).Admitted true
      (selectedComponent A SA SB v hv z) (selectedPoint A SA SB v hv z))
    (hzn : ¬(group A SA SB v hv (groupOf A SA SB v hv z)).Admitted false
      (selectedComponent A SA SB v hv z) (selectedPoint A SA SB v hv z)) :
    ∃ (D : OrderedData M) (_hD : SB.chart (indexB A SB v w.val)=.ordered D)
      (x y : M.Point D.band (v w.val).column),
      x.column=(v w.val).column ∧ x.height=(v w.val).height ∧
      y.column=(v z.val).column ∧ y.height=(v z.val).height ∧
      (D.base.transverse (by norm_num) D.lower D.upper).eval x *
        (D.base.transverse (by norm_num) D.lower D.upper).eval y < 0 ∧
      R/100≤|(D.base.transverse (by norm_num) D.lower D.upper).eval x| ∧
      R/100≤|(D.base.transverse (by norm_num) D.lower D.upper).eval y| ∧
      |(D.base.transverse (by norm_num) D.lower D.upper).eval x|≤8 ∧
      |(D.base.transverse (by norm_num) D.lower D.upper).eval y|≤8 := by
  obtain ⟨D,hD⟩ := ordered_of_rejected A SA SB v hv w hwp
  have hband : (SB.chart (indexB A SB v w.val)).band=D.band := congrArg BData.band hD
  let x : M.Point D.band (v w.val).column :=
    ⟨(v w.val).column,(v w.val).height,hband ▸ SB.height_in _ _,SimpleGraph.Reachable.refl _⟩
  have hsub : {H : ℝ | |H-(v w.val).height|≤2} ⊆ D.band := by
    rw [←hband]
    exact SB.ball_band A he.2.2.1 (fun H hH => by rw [abs_sub_comm]; exact hH.trans (by norm_num))
  obtain ⟨y,hyc,hyh,hdy⟩ := Point.local_point (v w.val) (v z.val) x rfl rfl
    isClosed_univ (Set.subset_univ _) hsub hd.le
  have hG : (group A SA SB v hv (groupOf A SA SB v hv w)).data=.ordered D := hD
  have hH : (group A SA SB v hv (groupOf A SA SB v hv z)).data=.ordered D := by
    change SB.chart (indexB A SB v z.val)=.ordered D
    rw [he.namesB A SA SB v]
    exact hD
  have hl : (group A SA SB v hv (groupOf A SA SB v hv z)).lower=
      (group A SA SB v hv (groupOf A SA SB v hv w)).lower := by
    rw [groupOf_lower,groupOf_lower]
    exact PairGeometry.narrow_lower_eq A SA SB v hv (witness A SA SB v hv w).interior hc
  have hcut : |D.value Group.lam x.column ⟨x.height,x.inBand⟩-
      D.value Group.lam y.column ⟨y.height,y.inBand⟩|≤R/10000 := by
    have value_coordinates {D E : BData M} (h : D=E)
        {i j : Fin (k+1)} {H T : ℝ} (hc : i=j) (hH : H=T)
        (hI : H∈D.band) (hJ : T∈E.band) :
        D.value Group.lam i ⟨H,hI⟩=E.value Group.lam j ⟨T,hJ⟩ := by
      subst E; subst j; subst T; rfl
    have hx : D.value Group.lam x.column ⟨x.height,x.inBand⟩=fullValue A SB v w.val :=
      value_coordinates hD.symm rfl rfl _ _
    have hy : D.value Group.lam y.column ⟨y.height,y.inBand⟩=fullValue A SB v z.val :=
      value_coordinates (hD.symm.trans (congrArg SB.chart (he.namesB A SA SB v).symm)) hyc hyh _ _
    rw [hx,hy]
    exact hc.2.2.le
  refine ⟨D,hD,x,y,rfl,rfl,hyc,hyh,?_⟩
  exact Group.two_side_of_rejected _ _ hG hH hl _ _ _ _
    (selectedPoint_mem A SA SB v hv w) (selectedPoint_mem A SA SB v hv z)
    hwp hwn hzp hzn x y rfl rfl hyc hyh (by rw [hdy]; exact ha)
    (by rw [hdy]; exact hd.le) hcut
end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory SecondaryGeometry VertexTests
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable (hist : Fin (SB.count+1) → A.History (R/200))
variable (hcross : ∀ a j, 10≤(R/200)*(hist a).radius j)
variable (hrec : ∀ a, (SB.chart a).Recorded (hist a) (by norm_num [R]) (by norm_num [R]))
variable (w z : Endpoint A SA SB v L U hv q p phaseD phaseG)
variable (he : Eligible A SA SB v w.val z.val) (hc : Cutoffs A SA SB v w.val z.val)
variable (ha : 1≤dist (v w.val) (v z.val)) (hd : dist (v w.val) (v z.val)<2)

include he hc ha hd in
/-- Both actual endpoint rejections force success of the genuine simultaneous
history increment with one favorable independent fair identifier coin. -/
lemma rejected_increment_probability
    (hwp : ¬(group A SA SB v hv (groupOf A SA SB v hv w)).Admitted true
      (selectedComponent A SA SB v hv w) (selectedPoint A SA SB v hv w))
    (hwn : ¬(group A SA SB v hv (groupOf A SA SB v hv w)).Admitted false
      (selectedComponent A SA SB v hv w) (selectedPoint A SA SB v hv w))
    (hzp : ¬(group A SA SB v hv (groupOf A SA SB v hv z)).Admitted true
      (selectedComponent A SA SB v hv z) (selectedPoint A SA SB v hv z))
    (hzn : ¬(group A SA SB v hv (groupOf A SA SB v hv z)).Admitted false
      (selectedComponent A SA SB v hv z) (selectedPoint A SA SB v hv z)) :
    1/2≤FiniteRandom.prob (fun sign : Fin (SB.count+1) → Bool =>
      kappaB*lambda*R/50≤(IncrementStep.update A SB hist hcross hrec sign).sets.separation
        (v w.val).column (v w.val).height (v z.val).column (v z.val).height) := by
  obtain ⟨D,hD,x,y,hxc,hxh,hyc,hyh,ho,hlx,hly,hux,huy⟩ :=
    transverse_of_rejected A SA SB v hv w z he hc ha hd hwp hwn hzp hzn
  have hx : A.Common SB.name (A.point x.column x.height) 1 (indexB A SB v w.val) := by
    rw [hxc,hxh,A.coordinate_point]
    exact fun z hz => he.2.2.1 z (hz.trans (by norm_num))
  have hy : A.Common SB.name (A.point y.column y.height) 1 (indexB A SB v w.val) := by
    rw [hyc,hyh,A.coordinate_point]
    exact fun z hz => he.2.2.2 z (hz.trans (by norm_num))
  have h := IncrementStep.success_probability A SB hist hcross hrec hD x y hx hy ho hlx hly hux huy
  simpa only [hxc,hxh,hyc,hyh] using h
end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Columns.Model.SetSystem
open MeasureTheory
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
lemma separation_comm (S : SetSystem M Ω μ) (i : Fin (k+1)) (H : ℝ) (j : Fin (k+1)) (T : ℝ) :
    S.separation i H j T=S.separation j T i H := by
  unfold separation
  congr 1
  funext ω
  exact abs_sub_comm _ _
end PlanarL1.Columns.Model.SetSystem

namespace PlanarL1.Parameters
noncomputable def secondaryChance : ℝ := 1/(2:ℝ)^(Columns.Model.SurvivingGroups.packBound+2)
lemma secondaryChance_pos : 0 < secondaryChance := by unfold secondaryChance; positivity
lemma secondaryChance_le_quarter : secondaryChance≤1/4 := by
  unfold secondaryChance
  apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
  calc
    (4:ℝ) = 2^2 := by norm_num
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
end PlanarL1.Parameters

namespace PlanarL1.Columns.Model.PairGeometry
open Parameters MeasureTheory SecondaryGeometry VertexTests RetainedSelection
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable {x y : V} (he : Eligible A SA SB v x y)
variable (hi : VertexBands.Interior A v (hv := hv) q p phaseD phaseG x)
variable (hj : VertexBands.Interior A v (hv := hv) q p phaseD phaseG y)
variable (hc : Cutoffs A SA SB v x y) (ha : 1≤dist (v x) (v y)) (hd : dist (v x) (v y)<2)
variable (hist : Fin (SB.count+1) → A.History (R/200))
variable (hcross : ∀ a j, 10≤(R/200)*(hist a).radius j)
variable (hrec : ∀ a, (SB.chart a).Recorded (hist a) (by norm_num [R]) (by norm_num [R]))

include hj hc ha in
lemma retained_alternative {m : ℕ} (hm : 0 < m) (hr : Retained A SA SB v hv he hi hd) :
    secondaryChance ≤ FiniteRandom.prob
      (fun omega : Sample (group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) m =>
        kappaB*R/50 < (layer (group A SA SB v hv) hm omega).sets.separation
          (v x).column (v x).height (v y).column (v y).height) ∨
    1/2 ≤ FiniteRandom.prob (fun sign : Fin (SB.count+1) → Bool =>
      kappaB*lambda*R/50 ≤ (IncrementStep.update A SB hist hcross hrec sign).sets.separation
        (v x).column (v x).height (v y).column (v y).height) := by
  have hxmem : x ∈ remaining A SA SB v L U hv q p phaseD phaseG :=
    (mem_remaining A SA SB v hv x).mpr ⟨⟨y,⟨ha,hd,he⟩,hc,hi,hj,hr⟩⟩
  have hymem : y ∈ remaining A SA SB v L U hv q p phaseD phaseG :=
    (mem_remaining A SA SB v hv y).mpr ⟨⟨x,⟨by simpa only [dist_comm] using ha,
      by simpa only [dist_comm] using hd,he.symm A SA SB v⟩,hc.symm A SA SB v,hj,hi,
      hr.symm A SA SB v hv he hi hj hc hd⟩⟩
  let w : Endpoint A SA SB v L U hv q p phaseD phaseG := ⟨x,hxmem⟩
  let z : Endpoint A SA SB v L U hv q p phaseD phaseG := ⟨y,hymem⟩
  have hw (positive : Bool)
      (had : (group A SA SB v hv (groupOf A SA SB v hv w)).Admitted positive
        (selectedComponent A SA SB v hv w) (selectedPoint A SA SB v hv w)) :
      secondaryChance ≤ FiniteRandom.prob
        (fun omega : Sample (group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) m =>
          kappaB*R/50 < (layer (group A SA SB v hv) hm omega).sets.separation
            (v x).column (v x).height (v y).column (v y).height) :=
    selected_admitted_probability A SA SB v hv w hj he ha hc positive had hm
  have hz (positive : Bool)
      (had : (group A SA SB v hv (groupOf A SA SB v hv z)).Admitted positive
        (selectedComponent A SA SB v hv z) (selectedPoint A SA SB v hv z)) :
      secondaryChance ≤ FiniteRandom.prob
        (fun omega : Sample (group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) m =>
          kappaB*R/50 < (layer (group A SA SB v hv) hm omega).sets.separation
            (v x).column (v x).height (v y).column (v y).height) := by
    have hh := selected_admitted_probability A SA SB v hv z hi (he.symm A SA SB v)
      (by simpa only [dist_comm] using ha) (hc.symm A SA SB v) positive had hm
    exact hh.trans (FiniteRandom.prob_mono (fun omega h => by
      simpa only [SetSystem.separation_comm] using h))
  by_cases hwp : (group A SA SB v hv (groupOf A SA SB v hv w)).Admitted true
      (selectedComponent A SA SB v hv w) (selectedPoint A SA SB v hv w)
  · exact Or.inl (hw true hwp)
  by_cases hwn : (group A SA SB v hv (groupOf A SA SB v hv w)).Admitted false
      (selectedComponent A SA SB v hv w) (selectedPoint A SA SB v hv w)
  · exact Or.inl (hw false hwn)
  by_cases hzp : (group A SA SB v hv (groupOf A SA SB v hv z)).Admitted true
      (selectedComponent A SA SB v hv z) (selectedPoint A SA SB v hv z)
  · exact Or.inl (hz true hzp)
  by_cases hzn : (group A SA SB v hv (groupOf A SA SB v hv z)).Admitted false
      (selectedComponent A SA SB v hv z) (selectedPoint A SA SB v hv z)
  · exact Or.inl (hz false hzn)
  exact Or.inr (rejected_increment_probability A SA SB v hv hist hcross hrec w z he hc ha hd hwp hwn hzp hzn)
end PlanarL1.Columns.Model.PairGeometry

end

end OAI
