import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Matched paths joined at an arbitrary interior time -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

def weightedLeftTime (t : Ioo (0:ℝ) 1) (s : Time) : Time :=
  projIcc 0 1 zero_le_one ((s:ℝ)/(t:ℝ))

def weightedRightTime (t : Ioo (0:ℝ) 1) (s : Time) : Time :=
  projIcc 0 1 zero_le_one (((s:ℝ)-(t:ℝ))/(1-(t:ℝ)))

theorem weightedLeftTime_coe (t : Ioo (0:ℝ) 1) (s : Time) (hs : (s:ℝ) ≤ t) :
    (weightedLeftTime t s:ℝ)=(s:ℝ)/(t:ℝ) := by
  exact congrArg Subtype.val (projIcc_of_mem zero_le_one
    ⟨div_nonneg s.property.1 t.property.1.le,(div_le_one t.property.1).mpr hs⟩)

theorem weightedRightTime_coe (t : Ioo (0:ℝ) 1) (s : Time) (hs : (t:ℝ) ≤ s) :
    (weightedRightTime t s:ℝ)=((s:ℝ)-(t:ℝ))/(1-(t:ℝ)) := by
  exact congrArg Subtype.val (projIcc_of_mem zero_le_one
    ⟨div_nonneg (sub_nonneg.mpr hs) (sub_pos.mpr t.property.2).le,
      (div_le_one (sub_pos.mpr t.property.2)).mpr (sub_le_sub_right s.property.2 _)⟩)

theorem continuous_weightedLeftTime (t : Ioo (0:ℝ) 1) : Continuous (weightedLeftTime t) :=
  continuous_projIcc.comp (continuous_subtype_val.div_const _)

theorem continuous_weightedRightTime (t : Ioo (0:ℝ) 1) : Continuous (weightedRightTime t) :=
  continuous_projIcc.comp ((continuous_subtype_val.sub continuous_const).div_const _)

def weightedJoin (t : Ioo (0:ℝ) 1) (z : MatchedPaths X) : C(Time,X) where
  toFun s := if (s:ℝ) ≤ t then z.val.1 (weightedLeftTime t s) else z.val.2 (weightedRightTime t s)
  continuous_toFun := by
    apply Continuous.if_le (z.val.1.continuous.comp (continuous_weightedLeftTime t))
      (z.val.2.continuous.comp (continuous_weightedRightTime t)) continuous_subtype_val continuous_const
    intro s hs
    change z.val.1 (weightedLeftTime t s)=z.val.2 (weightedRightTime t s)
    have hl : weightedLeftTime t s=1 := by
      apply Subtype.ext
      rw [weightedLeftTime_coe t s hs.le,hs,div_self t.property.1.ne']
      rfl
    have hr : weightedRightTime t s=0 := by
      apply Subtype.ext
      rw [weightedRightTime_coe t s hs.ge,hs,sub_self,zero_div]
      rfl
    rw [hl,hr]
    exact z.property

theorem weightedJoin_continuous (t : Ioo (0:ℝ) 1) : Continuous (weightedJoin (X:=X) t) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : MatchedPaths X × Time => if (z.2:ℝ) ≤ t then
    z.1.val.1 (weightedLeftTime t z.2) else z.1.val.2 (weightedRightTime t z.2))
  apply Continuous.if_le
    (continuous_eval.comp (((continuous_subtype_val.comp continuous_fst).fst).prodMk
      ((continuous_weightedLeftTime t).comp continuous_snd)))
    (continuous_eval.comp (((continuous_subtype_val.comp continuous_fst).snd).prodMk
      ((continuous_weightedRightTime t).comp continuous_snd)))
    (continuous_subtype_val.comp continuous_snd) continuous_const
  intro z hz
  change (z.2:ℝ)=(t:ℝ) at hz
  change z.1.val.1 (weightedLeftTime t z.2)=z.1.val.2 (weightedRightTime t z.2)
  have hl : weightedLeftTime t z.2=1 := by
    apply Subtype.ext
    rw [weightedLeftTime_coe t z.2 hz.le,hz,div_self t.property.1.ne']
    rfl
  have hr : weightedRightTime t z.2=0 := by
    apply Subtype.ext
    rw [weightedRightTime_coe t z.2 hz.ge,hz,sub_self,zero_div]
    rfl
  rw [hl,hr]
  exact z.1.property

theorem weightedJoin_left (t : Ioo (0:ℝ) 1) (z : MatchedPaths X) (s : Time)
    (hs : (s:ℝ) ≤ t) : weightedJoin t z s=z.val.1 (weightedLeftTime t s) :=
  ite_eq_left hs

theorem weightedJoin_right (t : Ioo (0:ℝ) 1) (z : MatchedPaths X) (s : Time)
    (hs : (t:ℝ) ≤ s) : weightedJoin t z s=z.val.2 (weightedRightTime t s) := by
  rcases hs.eq_or_lt with he | he
  · have hl : weightedLeftTime t s=1 := by
      apply Subtype.ext
      rw [weightedLeftTime_coe t s he.ge,← he,div_self t.property.1.ne']
      rfl
    have hr : weightedRightTime t s=0 := by
      apply Subtype.ext
      rw [weightedRightTime_coe t s he.le,← he,sub_self,zero_div]
      rfl
    rw [weightedJoin_left t z s he.ge,hl,hr]
    exact z.property
  · exact ite_eq_right (not_le.mpr he)

@[simp] theorem weightedJoin_zero (t : Ioo (0:ℝ) 1) (z : MatchedPaths X) :
    weightedJoin t z 0=z.val.1 0 := by
  rw [weightedJoin_left t z 0 t.property.1.le]
  congr 1
  apply Subtype.ext
  rw [weightedLeftTime_coe t 0 t.property.1.le]
  simp

@[simp] theorem weightedJoin_one (t : Ioo (0:ℝ) 1) (z : MatchedPaths X) :
    weightedJoin t z 1=z.val.2 1 := by
  rw [weightedJoin_right t z 1 t.property.2.le]
  congr 1
  apply Subtype.ext
  rw [weightedRightTime_coe t 1 t.property.2.le]
  change (1-(t:ℝ))/(1-(t:ℝ))=1
  exact div_self (sub_pos.mpr t.property.2).ne'

@[simp] theorem weightedJoin_split (t : Ioo (0:ℝ) 1) (z : MatchedPaths X) :
    weightedJoin t z ⟨t,t.property.1.le,t.property.2.le⟩=z.val.1 1 := by
  rw [weightedJoin_left t z _ le_rfl]
  congr 1
  apply Subtype.ext
  rw [weightedLeftTime_coe t _ le_rfl,div_self t.property.1.ne']
  rfl

theorem weightedJoin_isGeodesic (t : Ioo (0:ℝ) 1) (z : MatchedPaths X)
    (h0 : IsGeodesic z.val.1) (h1 : IsGeodesic z.val.2)
    (ha : dist (z.val.1 0) (z.val.1 1)=(t:ℝ)*dist (z.val.1 0) (z.val.2 1))
    (hb : dist (z.val.2 0) (z.val.2 1)=(1-(t:ℝ))*dist (z.val.1 0) (z.val.2 1)) :
    IsGeodesic (weightedJoin t z) := by
  let c := dist (z.val.1 0) (z.val.2 1)
  have hleft (s u : Time) (hsu : s ≤ u) (hu : (u:ℝ) ≤ t) :
      dist (weightedJoin t z s) (weightedJoin t z u)=((u:ℝ)-(s:ℝ))*c := by
    change (s:ℝ) ≤ (u:ℝ) at hsu
    rw [weightedJoin_left t z s (hsu.trans hu),weightedJoin_left t z u hu,h0,
      weightedLeftTime_coe t s (hsu.trans hu),weightedLeftTime_coe t u hu,ha,
      abs_of_nonpos (sub_nonpos.mpr (div_le_div_of_nonneg_right hsu t.property.1.le))]
    dsimp only [c]
    field_simp [t.property.1.ne']
    ring
  have hright (s u : Time) (hsu : s ≤ u) (hs : (t:ℝ) ≤ s) :
      dist (weightedJoin t z s) (weightedJoin t z u)=((u:ℝ)-(s:ℝ))*c := by
    change (s:ℝ) ≤ (u:ℝ) at hsu
    rw [weightedJoin_right t z s hs,weightedJoin_right t z u (hs.trans hsu),h1,
      weightedRightTime_coe t s hs,weightedRightTime_coe t u (hs.trans hsu),hb,
      abs_of_nonpos (sub_nonpos.mpr (div_le_div_of_nonneg_right
        (sub_le_sub_right hsu _) (sub_pos.mpr t.property.2).le))]
    dsimp only [c]
    field_simp [(sub_pos.mpr t.property.2).ne']
    ring
  have hordered (s u : Time) (hsu : s ≤ u) :
      dist (weightedJoin t z s) (weightedJoin t z u) ≤ ((u:ℝ)-(s:ℝ))*c := by
    by_cases hu : (u:ℝ) ≤ t
    · exact (hleft s u hsu hu).le
    by_cases hs : (t:ℝ) ≤ s
    · exact (hright s u hsu hs).le
    let v : Time := ⟨t,t.property.1.le,t.property.2.le⟩
    have hv0 := hleft s v (le_of_not_ge hs) le_rfl
    have hv1 := hright v u (le_of_not_ge hu) le_rfl
    have htri := dist_triangle (weightedJoin t z s) (weightedJoin t z v) (weightedJoin t z u)
    rw [hv0,hv1] at htri
    dsimp only [v] at htri
    nlinarith only [htri]
  apply isGeodesic_of_dist_le
  intro s u
  rw [weightedJoin_zero,weightedJoin_one]
  rcases le_total s u with hsu | hus
  · rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (show (s:ℝ) ≤ (u:ℝ) from hsu))]
    exact hordered s u hsu
  · rw [abs_of_nonneg (sub_nonneg.mpr (show (u:ℝ) ≤ (s:ℝ) from hus)),dist_comm]
    exact hordered u s hus

variable [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem weightedJoin_law_left (t : Ioo (0:ℝ) 1) (ρ : Measure (MatchedPaths X))
    (q : Measure C(Time,X)) (hq : ρ.map (fun z => z.val.1)=q)
    (s : Time) (hs : (s:ℝ) ≤ t) :
    (ρ.map (weightedJoin t)).map (fun γ => γ s)=q.map (fun γ => γ (weightedLeftTime t s)) := by
  rw [Measure.map_map (measurable_path_eval s) (weightedJoin_continuous t).measurable,← hq,
    Measure.map_map (measurable_path_eval _) measurable_subtype_coe.fst]
  congr 1
  funext z
  exact weightedJoin_left t z s hs

theorem weightedJoin_law_right (t : Ioo (0:ℝ) 1) (ρ : Measure (MatchedPaths X))
    (q : Measure C(Time,X)) (hq : ρ.map (fun z => z.val.2)=q)
    (s : Time) (hs : (t:ℝ) ≤ s) :
    (ρ.map (weightedJoin t)).map (fun γ => γ s)=q.map (fun γ => γ (weightedRightTime t s)) := by
  rw [Measure.map_map (measurable_path_eval s) (weightedJoin_continuous t).measurable,← hq,
    Measure.map_map (measurable_path_eval _) measurable_subtype_coe.snd]
  congr 1
  funext z
  exact weightedJoin_right t z s hs

theorem weightedJoin_law_zero (t : Ioo (0:ℝ) 1) (ρ : Measure (MatchedPaths X))
    (q : Measure C(Time,X)) (hq : ρ.map (fun z => z.val.1)=q) :
    (ρ.map (weightedJoin t)).map (fun γ => γ 0)=q.map (fun γ => γ 0) := by
  rw [Measure.map_map (measurable_path_eval 0) (weightedJoin_continuous t).measurable,← hq,
    Measure.map_map (measurable_path_eval 0) measurable_subtype_coe.fst]
  simp only [Function.comp_def,weightedJoin_zero]

theorem weightedJoin_law_one (t : Ioo (0:ℝ) 1) (ρ : Measure (MatchedPaths X))
    (q : Measure C(Time,X)) (hq : ρ.map (fun z => z.val.2)=q) :
    (ρ.map (weightedJoin t)).map (fun γ => γ 1)=q.map (fun γ => γ 1) := by
  rw [Measure.map_map (measurable_path_eval 1) (weightedJoin_continuous t).measurable,← hq,
    Measure.map_map (measurable_path_eval 1) measurable_subtype_coe.snd]
  simp only [Function.comp_def,weightedJoin_one]

theorem weightedJoin_law_split (t : Ioo (0:ℝ) 1) (ρ : Measure (MatchedPaths X))
    (q : Measure C(Time,X)) (hq : ρ.map (fun z => z.val.1)=q) :
    (ρ.map (weightedJoin t)).map (fun γ => γ ⟨t,t.property.1.le,t.property.2.le⟩)=
      q.map (fun γ => γ 1) := by
  rw [Measure.map_map (measurable_path_eval _) (weightedJoin_continuous t).measurable,← hq,
    Measure.map_map (measurable_path_eval 1) measurable_subtype_coe.fst]
  simp only [Function.comp_def,weightedJoin_split]

end RegularPointCoordinates

end

end OAI
