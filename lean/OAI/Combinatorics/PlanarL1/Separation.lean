import OAI.Combinatorics.PlanarL1.SurvivingSeeds

namespace OAI


section

namespace PlanarL1.Columns.Model
open MeasureTheory Parameters
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)}

namespace Ambient
variable (A : Ambient M)
lemma taper_of_ball {region : Set (M.Point Set.univ A.root)}
    (x : M.Point Set.univ A.root)
    (hx : ∀ z, dist x z≤1 → z ∈ region) : Increment.taper regionᶜ 1 x=1 := by
  apply Increment.taper_one (by norm_num)
  intro hn
  apply (Metric.le_infDist hn).mpr
  intro z hz
  exact le_of_not_gt (fun hd => hz (hx z hd.le))
end Ambient

namespace OrderedData
variable (D : OrderedData M) {A : Ambient M}
variable (H : A.History (R/200))
variable (region : Set (M.Point Set.univ A.root))
variable (hcross : ∀ j, 10≤(R/200)*H.radius j)
variable (hrec : (BData.ordered D).Recorded H (by norm_num [R]) (by norm_num [R]))

noncomputable def incrementField (e : Bool) : M.Field D.band 5 :=
  (BData.ordered D).auxiliaryField
    ((BData.ordered D).incrementAuxiliary H 1 region e (by norm_num [R])
      (by norm_num [R]) (by norm_num) (by simpa using hcross))
    SecondaryGeometry.Group.lam SecondaryGeometry.Group.lam_bound

include hrec in
lemma incrementField_eq (e : Bool) {root : Fin (k+1)} (x : M.Point D.band root)
    (hx : ∀ z, dist (A.point x.column x.height) z≤1 → z ∈ region)
    (hl : R/100≤|(D.base.transverse (by norm_num) D.lower D.upper).eval x|)
    (hu : |(D.base.transverse (by norm_num) D.lower D.upper).eval x|≤8) :
    (D.incrementField H region hcross e).eval x =
      D.value SecondaryGeometry.Group.lam x.column ⟨x.height,x.inBand⟩+
        (SecondaryGeometry.Group.lam:ℝ)*
          (if e then (D.base.transverse (by norm_num) D.lower D.upper).eval x
            else -(D.base.transverse (by norm_num) D.lower D.upper).eval x) := by
  have hd := BData.increment_difference D H 1 region e (by norm_num [R])
    (by norm_num [R]) (by norm_num) (by simpa using hcross) hrec
    SecondaryGeometry.Group.lam SecondaryGeometry.Group.lam_bound
    x.column ⟨x.height,x.inBand⟩
  have ht := A.taper_of_ball (A.point x.column x.height) hx
  have hs := Increment.scalar_plateau (a := R/200*1) (r := 1)
    (t := (D.base.transverse (by norm_num) D.lower D.upper).eval x)
    (by norm_num [R]) (by linarith) (by simpa using hu)
  change (D.incrementField H region hcross e).eval x-
    D.value SecondaryGeometry.Group.lam x.column ⟨x.height,x.inBand⟩ = _ at hd
  simp only [Increment.signedDamped,Increment.damped,Field.eval] at hd hs ⊢
  rw [hs,ht,mul_one] at hd
  linarith

include hrec in
/-- Genuine append-only histories have a favorable fair sign. The old field
may be arbitrary and is not discarded in this difference calculation. -/
lemma exists_increment_gain {root : Fin (k+1)} (x y : M.Point D.band root)
    (hx : ∀ z, dist (A.point x.column x.height) z≤1 → z ∈ region)
    (hy : ∀ z, dist (A.point y.column y.height) z≤1 → z ∈ region)
    (ho : (D.base.transverse (by norm_num) D.lower D.upper).eval x *
      (D.base.transverse (by norm_num) D.lower D.upper).eval y<0)
    (hlx : R/100≤|(D.base.transverse (by norm_num) D.lower D.upper).eval x|)
    (hly : R/100≤|(D.base.transverse (by norm_num) D.lower D.upper).eval y|)
    (hux : |(D.base.transverse (by norm_num) D.lower D.upper).eval x|≤8)
    (huy : |(D.base.transverse (by norm_num) D.lower D.upper).eval y|≤8) :
    ∃ e : Bool, lambda*R/50 ≤
      |(D.incrementField H region hcross e).eval x-(D.incrementField H region hcross e).eval y| := by
  let tx := (D.base.transverse (by norm_num) D.lower D.upper).eval x
  let ty := (D.base.transverse (by norm_num) D.lower D.upper).eval y
  let p := D.value SecondaryGeometry.Group.lam x.column ⟨x.height,x.inBand⟩-
    D.value SecondaryGeometry.Group.lam y.column ⟨y.height,y.inBand⟩
  have hb : R/50≤|tx-ty| := by
    rw [← Field.abs_add_eq_abs_sub_of_opposite ho]
    linarith
  have hgain : lambda*R/50≤|(SecondaryGeometry.Group.lam:ℝ)*(tx-ty)| := by
    rw [abs_mul,abs_of_nonneg (NNReal.coe_nonneg _)]
    change lambda*R/50≤lambda*|tx-ty|
    have h := mul_le_mul_of_nonneg_left hb (by norm_num [lambda,R] : 0≤lambda)
    linarith
  rcases Increment.opposite_sign_gain p ((SecondaryGeometry.Group.lam:ℝ)*(tx-ty)) with h | h
  · refine ⟨true,?_⟩
    rw [D.incrementField_eq H region hcross hrec true x hx hlx hux,
      D.incrementField_eq H region hcross hrec true y hy hly huy]
    simp only [ite_true]
    convert hgain.trans h using 1
    try dsimp only [p,tx,ty]
    try congr 1
    ring
  · refine ⟨false,?_⟩
    rw [D.incrementField_eq H region hcross hrec false x hx hlx hux,
      D.incrementField_eq H region hcross hrec false y hy hly huy]
    simp only [Bool.false_eq_true,ite_false]
    convert hgain.trans h using 1
    try dsimp only [p,tx,ty]
    try congr 1
    ring

end OrderedData
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Columns.Model
open MeasureTheory Parameters
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace SetSystem
noncomputable def separation (S : SetSystem M Ω μ) (i : Fin (k+1)) (H : ℝ)
    (j : Fin (k+1)) (T : ℝ) : ℝ :=
  ∫ ω, |(S.activity ω).indicator i H-(S.activity ω).indicator j T| ∂μ
lemma separation_nonneg (S : SetSystem M Ω μ) (i j : Fin (k+1)) (H T : ℝ) :
    0≤S.separation i H j T := integral_nonneg (fun _ => abs_nonneg _)
end SetSystem

namespace BState
variable {κ : ℝ} {lam : ℝ≥0} (S : BState M κ lam Ω μ)

lemma common_separation (i j : Fin (k+1)) (H T : ℝ) (a : Fin (S.count+1))
    (hi : S.name i H=a) (hj : S.name j T=a) :
    S.sets.separation i H j T=max |H-T| |S.oldValue i H-S.oldValue j T| := by
  unfold SetSystem.separation
  simp_rw [S.old_indicator,hi,hj]
  exact (S.labels a).distance _ _ _ _

lemma common_separation_height (i j : Fin (k+1)) (H T : ℝ) (a : Fin (S.count+1))
    (hi : S.name i H=a) (hj : S.name j T=a) :
    |H-T|≤S.sets.separation i H j T := by
  rw [S.common_separation i j H T a hi hj]
  exact le_max_left _ _

lemma common_separation_field (i j : Fin (k+1)) (H T : ℝ) (a : Fin (S.count+1))
    (hi : S.name i H=a) (hj : S.name j T=a) (hκ : 0≤κ)
    (hH : H ∈ (S.chart a).band) (hT : T ∈ (S.chart a).band) :
    κ*|(S.chart a).value lam i ⟨H,hH⟩-(S.chart a).value lam j ⟨T,hT⟩|≤
      S.sets.separation i H j T := by
  rw [S.common_separation i j H T a hi hj,S.oldValue_eq i H a hi,S.oldValue_eq j T a hj,
    ←mul_sub,abs_mul,abs_of_nonneg hκ]
  exact le_max_right _ _

lemma fieldUpdate_separation (F : ∀ a, M.Field (S.chart a).band 5)
    (hk : 0≤κ) (hsmall : κ*5≤1/2) (hlam : lam≤(1:ℝ≥0)/100)
    (hd : ∀ i H T, S.name i H≠S.name i T → |S.newValue F i H-S.oldValue i H|≤|H-T|/8)
    (i j : Fin (k+1)) (H T : ℝ) (a : Fin (S.count+1))
    (hi : S.name i H=a) (hj : S.name j T=a) :
    (S.fieldUpdate F hk hsmall hlam hd).separation i H j T=
      max |H-T| |S.newValue F i H-S.newValue F j T| := by
  unfold SetSystem.separation
  change (∫ ω, |(S.fieldActivity F hk hsmall hlam hd ω).indicator i H-
    (S.fieldActivity F hk hsmall hlam hd ω).indicator j T| ∂μ)=_
  simp_rw [S.field_indicator,hi,hj]
  exact (S.labels a).distance _ _ _ _
end BState

namespace OrdinaryState
variable {κ : ℝ} (S : OrdinaryState M κ Ω μ)
lemma common_separation (i j : Fin (k+1)) (H T : ℝ) (a : Fin (S.count+1))
    (hi : S.name i H=a) (hj : S.name j T=a) (hκ : 0≤κ)
    (hH : H ∈ (S.chart a).band) (hT : T ∈ (S.chart a).band) :
    S.sets.separation i H j T=max |H-T|
      (κ*|(S.chart a).comparison.value i ⟨H,hH⟩-(S.chart a).comparison.value j ⟨T,hT⟩|) := by
  have h := (BState.ofOrdinary (lam := (0:ℝ≥0)) S).common_separation i j H T a hi hj
  rw [BState.oldValue_eq _ i H a hi,BState.oldValue_eq _ j T a hj] at h
  change S.sets.separation i H j T=max |H-T|
    |κ*((S.chart a).constant+(S.chart a).orientation*(S.chart a).comparison.value i ⟨H,hH⟩)-
      κ*((S.chart a).constant+(S.chart a).orientation*(S.chart a).comparison.value j ⟨T,hT⟩)| at h
  rw [h]
  congr 1
  rw [show κ*((S.chart a).constant+(S.chart a).orientation*(S.chart a).comparison.value i ⟨H,hH⟩)-
      κ*((S.chart a).constant+(S.chart a).orientation*(S.chart a).comparison.value j ⟨T,hT⟩)=
      κ*(S.chart a).orientation*((S.chart a).comparison.value i ⟨H,hH⟩-
        (S.chart a).comparison.value j ⟨T,hT⟩) by ring,
    abs_mul,abs_mul,abs_of_nonneg hκ,(S.chart a).unit_orientation,mul_one]
end OrdinaryState
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Columns.Model.VertexTests
open MeasureTheory Parameters
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω Ξ V : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)

noncomputable def indexA (x : V) := SA.name (v x).column (v x).height
noncomputable def indexB (x : V) := SB.name (v x).column (v x).height
noncomputable def ordinaryValue (x : V) : ℝ :=
  (SA.chart (indexA A SA v x)).comparison.value (v x).column ⟨(v x).height,SA.height_in _ _⟩
noncomputable def fullValue (x : V) : ℝ :=
  (SB.chart (indexB A SB v x)).value SecondaryGeometry.Group.lam (v x).column
    ⟨(v x).height,SB.height_in _ _⟩

private lemma ordinary_value_transport {D E : OrdinaryData M} (he : D=E)
    (i : Fin (k+1)) (H : ℝ) (hD : H ∈ D.band) (hE : H ∈ E.band) :
    D.comparison.value i ⟨H,hD⟩=E.comparison.value i ⟨H,hE⟩ := by subst E; rfl
private lemma full_value_transport {D E : BData M} (he : D=E)
    (i : Fin (k+1)) (H : ℝ) (hD : H ∈ D.band) (hE : H ∈ E.band) :
    D.value SecondaryGeometry.Group.lam i ⟨H,hD⟩=
    E.value SecondaryGeometry.Group.lam i ⟨H,hE⟩ := by subst E; rfl

/-- The actual eligibility test in : both unrestricted closed
radius-five balls, with one common identifier in each of the two systems. -/
def Eligible (x y : V) : Prop :=
  A.Common SA.name (v x) 5 (indexA A SA v x) ∧
  A.Common SA.name (v y) 5 (indexA A SA v x) ∧
  A.Common SB.name (v x) 5 (indexB A SB v x) ∧
  A.Common SB.name (v y) 5 (indexB A SB v x)

def PairTest (p : V×V) : Prop :=
  1≤dist (v p.1) (v p.2) ∧ dist (v p.1) (v p.2)<2 ∧ Eligible A SA SB v p.1 p.2

def Cutoffs (x y : V) : Prop :=
  |(v x).height-(v y).height|<a₂/10000 ∧
  |ordinaryValue A SA v x-ordinaryValue A SA v y|<EA ∧
  |fullValue A SB v x-fullValue A SB v y|<R/10000

lemma Eligible.namesA {x y : V} (h : Eligible A SA SB v x y) :
    indexA A SA v y=indexA A SA v x := h.2.1.center A (by norm_num)
lemma Eligible.namesB {x y : V} (h : Eligible A SA SB v x y) :
    indexB A SB v y=indexB A SB v x := h.2.2.2.center A (by norm_num)
lemma Eligible.symm {x y : V} (h : Eligible A SA SB v x y) : Eligible A SA SB v y x := by
  unfold Eligible
  rw [h.namesA A SA SB v,h.namesB A SA SB v]
  exact ⟨h.2.1,h.1,h.2.2.2,h.2.2.1⟩
lemma Cutoffs.symm {x y : V} (h : Cutoffs A SA SB v x y) : Cutoffs A SA SB v y x := by
  simpa only [Cutoffs,abs_sub_comm] using h

noncomputable def cutoffGain : ℝ := min (a₂/10000) (min (kappaA*EA) (kappaB*R/10000))
lemma cutoffGain_pos : 0<cutoffGain := by norm_num [cutoffGain,a₂,kappaA,a₁,EA,epsilon,kappaB,R]

/-- A failed literal cutoff already supplies an actual cut separation. No
rescaling, refinement, or desired probability is hidden in this alternative. -/
lemma separation_of_cutoff_failure {x y : V} (h : Eligible A SA SB v x y)
    (hf : ¬Cutoffs A SA SB v x y) :
    cutoffGain≤SA.sets.separation (v x).column (v x).height (v y).column (v y).height ∨
    cutoffGain≤SB.sets.separation (v x).column (v x).height (v y).column (v y).height := by
  have hA := h.namesA A SA SB v
  have hB := h.namesB A SA SB v
  have hey : SA.name (v y).column (v y).height=indexA A SA v x := hA
  have hty : (v y).height ∈ (SA.chart (indexA A SA v x)).band := by
    rw [←hA]
    exact SA.height_in (v y).column (v y).height
  have hby : SB.name (v y).column (v y).height=indexB A SB v x := hB
  have htb : (v y).height ∈ (SB.chart (indexB A SB v x)).band := by
    rw [←hB]
    exact SB.height_in (v y).column (v y).height
  have hs := SA.common_separation (v x).column (v y).column (v x).height (v y).height
    (indexA A SA v x) rfl hey verticalA.1 (SA.height_in _ _) hty
  have ha : (SA.chart (indexA A SA v x)).comparison.value (v y).column ⟨(v y).height,hty⟩=
      ordinaryValue A SA v y := by
    exact ordinary_value_transport (congrArg SA.chart hA.symm) _ _ _ _
  rw [ha] at hs
  change SA.sets.separation (v x).column (v x).height (v y).column (v y).height =
    max |(v x).height-(v y).height| (kappaA*|ordinaryValue A SA v x-ordinaryValue A SA v y|) at hs
  by_cases hh : |(v x).height-(v y).height|<a₂/10000
  · by_cases hv : |ordinaryValue A SA v x-ordinaryValue A SA v y|<EA
    · have hb : R/10000≤|fullValue A SB v x-fullValue A SB v y| :=
        le_of_not_gt (fun hb => hf ⟨hh,hv,hb⟩)
      right
      have hd := SB.common_separation_field (v x).column (v y).column (v x).height (v y).height
        (indexB A SB v x) rfl hby verticalB.1 (SB.height_in _ _) htb
      have he : (SB.chart (indexB A SB v x)).value SecondaryGeometry.Group.lam
          (v y).column ⟨(v y).height,htb⟩=fullValue A SB v y := by
        exact full_value_transport (congrArg SB.chart hB.symm) _ _ _ _
      rw [he] at hd
      change kappaB*|fullValue A SB v x-fullValue A SB v y|≤_ at hd
      have hb' := mul_le_mul_of_nonneg_left hb verticalB.1
      calc cutoffGain ≤ kappaB*R/10000 := (min_le_right _ _).trans (min_le_right _ _)
           _ ≤ kappaB*|fullValue A SB v x-fullValue A SB v y| := by linarith
           _ ≤ _ := hd
    · left
      rw [hs]
      exact ((min_le_right _ _).trans (min_le_left _ _)).trans
        ((mul_le_mul_of_nonneg_left (le_of_not_gt hv) verticalA.1).trans (le_max_right _ _))
  · left
    rw [hs]
    exact (min_le_left _ _).trans ((le_of_not_gt hh).trans (le_max_left _ _))

variable [Fintype V]
noncomputable def eligiblePairs : Finset (V×V) := Finset.univ.filter (PairTest A SA SB v)
lemma mem_eligiblePairs (p : V×V) : p ∈ eligiblePairs A SA SB v ↔ PairTest A SA SB v p := by
  simp only [eligiblePairs,Finset.mem_filter,Finset.mem_univ,true_and]

end PlanarL1.Columns.Model.VertexTests

end

end OAI
