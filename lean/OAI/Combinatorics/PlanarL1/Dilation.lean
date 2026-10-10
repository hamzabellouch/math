import OAI.Combinatorics.PlanarL1.SecondaryBatch

namespace OAI

section

namespace PlanarL1.Columns.Model
open Set
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (M : Model n) (c : ℝ) (hc : 0<c)

/-- Change physical units by a positive factor. This scales the actual switch
sets and vertical path lengths; the cyclic link graph is not changed. -/
noncomputable def dilate : Model n where
  link := M.link
  heights i j := (fun H => c*H) '' M.heights i j
  symm i j := by rw [M.symm i j]
  permitted i j H h := by
    obtain ⟨T,hT,rfl⟩ := h
    exact M.permitted i j T hT
  compact i j := (M.compact i j).image (continuous_const.mul continuous_id)
  noncrossing := M.noncrossing
  terminal i j ha hn := by
    obtain ⟨H,hH,hT⟩ := M.terminal i j ha hn
    refine ⟨c*H,by simp only [hH,image_singleton],?_⟩
    intro k T ht
    rcases ht with ⟨U,hU,rfl⟩ | ⟨U,hU,rfl⟩
    · exact mul_le_mul_of_nonneg_left (hT k U (Or.inl hU)) hc.le
    · exact mul_le_mul_of_nonneg_left (hT k U (Or.inr hU)) hc.le

include hc in
lemma mem_dilate_set {J : Set ℝ} {H : ℝ} :
    H ∈ (fun T => c*T) '' J ↔ H/c ∈ J := by
  constructor
  · rintro ⟨T,hT,rfl⟩
    simpa [hc.ne'] using hT
  · intro h
    exact ⟨H/c,h,mul_div_cancel₀ H hc.ne'⟩

lemma dilate_mem_heights {i j : Fin n} {H : ℝ} :
    H ∈ (M.dilate c hc).heights i j ↔ H/c ∈ M.heights i j :=
  mem_dilate_set c hc

lemma dilate_activeGraph (J : Set ℝ) :
    (M.dilate c hc).activeGraph ((fun T => c*T) '' J)=M.activeGraph J := by
  ext i j
  simp only [activeGraph,mem_dilate_set c hc,dilate_mem_heights]
  constructor
  · rintro ⟨H,hH,hs⟩
    exact ⟨H/c,hH,hs⟩
  · rintro ⟨H,hH,hs⟩
    exact ⟨c*H,by simpa [hc.ne'] using hH,by simpa [hc.ne'] using hs⟩

namespace Path
variable {M c} {J : Set ℝ} {i j : Fin n}

noncomputable def dilate : {i j : Fin n} → M.Path J i j →
    (M.dilate c hc).Path ((fun T => c*T) '' J) i j
  | _,_,.nil i => .nil i
  | _,_,.cons H hH hs p => .cons (c*H) ⟨H,hH,rfl⟩ ⟨H,hs,rfl⟩ (dilate p)

lemma dilate_length (p : M.Path J i j) (a b : ℝ) :
    (p.dilate hc).length (c*a) (c*b)=c*p.length a b := by
  induction p generalizing a with
  | nil => simp only [dilate,length,← mul_sub,abs_mul,abs_of_pos hc]
  | cons H hH hs p ih =>
    simp only [dilate,length,ih,← mul_sub,abs_mul,abs_of_pos hc,mul_add]

noncomputable def undilate : {i j : Fin n} →
    (M.dilate c hc).Path ((fun T => c*T) '' J) i j → M.Path J i j
  | _,_,.nil i => .nil i
  | _,_,.cons H hH hs p => .cons (H/c) ((mem_dilate_set c hc).mp hH)
      ((M.dilate_mem_heights c hc).mp hs) (undilate p)

lemma undilate_length (p : (M.dilate c hc).Path ((fun T => c*T) '' J) i j) (a b : ℝ) :
    c*(p.undilate hc).length (a/c) (b/c)=p.length a b := by
  induction p generalizing a with
  | nil =>
    simp only [undilate,length,← sub_div,abs_div,abs_of_pos hc]
    exact mul_div_cancel₀ _ hc.ne'
  | cons H hH hs p ih =>
    simp only [undilate,length,mul_add,ih,← sub_div,abs_div,abs_of_pos hc,
      mul_div_cancel₀ _ hc.ne']
end Path

namespace Point
variable {M c} {J : Set ℝ} {root : Fin n}

noncomputable def dilate (x : M.Point J root) :
    (M.dilate c hc).Point ((fun T => c*T) '' J) root where
  column := x.column
  height := c*x.height
  inBand := ⟨x.height,x.inBand,rfl⟩
  reachable := by rw [M.dilate_activeGraph]; exact x.reachable

noncomputable def undilate (x : (M.dilate c hc).Point ((fun T => c*T) '' J) root) :
    M.Point J root where
  column := x.column
  height := x.height/c
  inBand := (mem_dilate_set c hc).mp x.inBand
  reachable := by rw [← M.dilate_activeGraph c hc J]; exact x.reachable

lemma dilate_distance (x y : M.Point J root) :
    (x.dilate hc).distance (y.dilate hc)=c*x.distance y := by
  apply le_antisymm
  · rw [mul_comm c]
    apply (div_le_iff₀ hc).mp
    have := x.paths_nonempty y
    apply le_ciInf
    intro p
    have h := (x.dilate hc).distance_le (y.dilate hc) (p.dilate hc)
    change (x.dilate hc).distance (y.dilate hc) ≤
      (p.dilate hc).length (c*x.height) (c*y.height) at h
    rw [Path.dilate_length hc] at h
    exact (div_le_iff₀ hc).mpr (by nlinarith only [h])
  · have := (x.dilate hc).paths_nonempty (y.dilate hc)
    apply le_ciInf
    intro p
    have h := mul_le_mul_of_nonneg_left (x.distance_le y (p.undilate hc)) hc.le
    have he := p.undilate_length hc (c*x.height) (c*y.height)
    simp only [mul_div_cancel_left₀ _ hc.ne'] at he
    exact h.trans_eq he

lemma dilate_dist (x y : M.Point J root) :
    dist (x.dilate hc) (y.dilate hc)=c*dist x y := x.dilate_distance hc y

@[simp] lemma undilate_dilate (x : M.Point J root) : (x.dilate hc).undilate hc=x := by
  cases x
  simp only [dilate,undilate,mul_div_cancel_left₀ _ hc.ne']

@[simp] lemma dilate_undilate (x : (M.dilate c hc).Point ((fun T => c*T) '' J) root) :
    (x.undilate hc).dilate hc=x := by
  cases x
  simp only [dilate,undilate,mul_div_cancel₀ _ hc.ne']

lemma undilate_dist (x y : (M.dilate c hc).Point ((fun T => c*T) '' J) root) :
    dist (x.undilate hc) (y.undilate hc)=dist x y/c := by
  have h := (x.undilate hc).dilate_dist hc (y.undilate hc)
  rw [dilate_undilate,dilate_undilate] at h
  apply (eq_div_iff hc.ne').mpr
  nlinarith only [h]
end Point

include hc in
lemma dilate_set_closed {J : Set ℝ} (hJ : IsClosed J) :
    IsClosed ((fun T => c*T) '' J) := by
  have he : (fun T => c*T) '' J = (fun T => T/c) ⁻¹' J := by
    ext H
    exact mem_dilate_set c hc
  rw [he]
  exact hJ.preimage (continuous_id.div_const c)

include hc in
lemma dilate_set_convex {J : Set ℝ} (hJ : J.OrdConnected) :
    ((fun T => c*T) '' J).OrdConnected := by
  have he : (fun T => c*T) '' J = (fun T => T/c) ⁻¹' J := by
    ext H
    exact mem_dilate_set c hc
  rw [he]
  exact hJ.preimage_mono (fun _ _ h => div_le_div_of_nonneg_right h hc.le)

namespace Field
variable {M c} {J : Set ℝ} {L : ℝ≥0}

/-- Field values have length units too. The vertical Lipschitz constant does
not change on passing to new physical units. -/
noncomputable def dilate (F : M.Field J L) :
    (M.dilate c hc).Field ((fun T => c*T) '' J) L where
  value i H := c*F.value i ⟨H.val/c,(mem_dilate_set c hc).mp H.property⟩
  vertical i := by
    apply LipschitzWith.of_dist_le_mul
    intro H T
    have h := (F.vertical i).dist_le_mul
      ⟨H.val/c,(mem_dilate_set c hc).mp H.property⟩
      ⟨T.val/c,(mem_dilate_set c hc).mp T.property⟩
    simp only [Real.dist_eq,Subtype.dist_eq] at h ⊢
    rw [← mul_sub,abs_mul,abs_of_pos hc]
    apply (mul_le_mul_of_nonneg_left h hc.le).trans_eq
    rw [← sub_div,abs_div,abs_of_pos hc]
    field_simp
  switch i j H hs := by
    rw [F.switch i j ⟨H.val/c,(mem_dilate_set c hc).mp H.property⟩
      ((M.dilate_mem_heights c hc).mp hs)]

lemma dilate_eval (F : M.Field J L) {root : Fin n} (x : M.Point J root) :
    (F.dilate hc).eval (x.dilate hc)=c*F.eval x := by
  simp only [eval,dilate,Point.dilate,mul_div_cancel_left₀ _ hc.ne']

lemma dilate_orderedFrom {k : ℕ} {M : Model (k+1)} {J : Set ℝ} {L : ℝ≥0}
    (F : M.Field J L) {a b : Fin (k+1)} (ho : F.OrderedFrom a b) :
    (F.dilate hc).OrderedFrom a b := by
  refine ⟨?_,?_,?_⟩
  · intro H i
    exact mul_le_mul_of_nonneg_left (ho.1 ⟨H.val/c,(mem_dilate_set c hc).mp H.property⟩ i) hc.le
  · intro H i j hij hjb
    exact mul_le_mul_of_nonneg_left (ho.2.1 ⟨H.val/c,(mem_dilate_set c hc).mp H.property⟩ i j hij hjb) hc.le
  · intro H i j hbi hij
    exact mul_le_mul_of_nonneg_left (ho.2.2 ⟨H.val/c,(mem_dilate_set c hc).mp H.property⟩ i j hbi hij) hc.le
end Field

namespace Point
variable {M c} {J : Set ℝ} {root : Fin n}
lemma dilate_radialValue (o : M.Point J root) (i : Fin n)
    (H : (fun T => c*T) '' J) :
    (o.dilate hc).radialValue i H =
      c*o.radialValue i ⟨H.val/c,(mem_dilate_set c hc).mp H.property⟩ := by
  by_cases hi : (M.activeGraph J).Reachable root i
  · have hi' : ((M.dilate c hc).activeGraph ((fun T => c*T) '' J)).Reachable root i := by
      rwa [M.dilate_activeGraph]
    simp only [radialValue,dite_eq_left hi,dite_eq_left hi']
    let x : M.Point J root := ⟨i,H.val/c,(mem_dilate_set c hc).mp H.property,hi⟩
    have hx : (x.dilate hc)=(⟨i,H.val,H.property,hi'⟩ :
        (M.dilate c hc).Point ((fun T => c*T) '' J) root) := by
      simp only [x,dilate,mul_div_cancel₀ _ hc.ne']
    rw [← hx]
    exact o.dilate_dist hc x
  · have hi' : ¬((M.dilate c hc).activeGraph ((fun T => c*T) '' J)).Reachable root i := by
      rwa [M.dilate_activeGraph]
    simp only [radialValue,dite_eq_right hi,dite_eq_right hi',mul_zero]
end Point

namespace OrdinaryData
variable {M c}
noncomputable def dilate (D : OrdinaryData M) : OrdinaryData (M.dilate c hc) where
  band := (fun T => c*T) '' D.band
  closed := dilate_set_closed c hc D.closed
  convex := dilate_set_convex c hc D.convex
  origin := D.origin.map (fun o => ⟨o.1,o.2.dilate hc⟩)
  constant := c*D.constant
  orientation := D.orientation
  unit_orientation := D.unit_orientation

lemma dilate_comparison (D : OrdinaryData M) (i : Fin n) (H : (D.dilate hc).band) :
    (D.dilate hc).comparison.value i H =
      c*D.comparison.value i ⟨H.val/c,(mem_dilate_set c hc).mp H.property⟩ := by
  cases he : D.origin with
  | none => simp only [comparison,dilate,he,Option.map_none,Field.constant,mul_zero]
  | some o =>
    simp only [comparison,dilate,he,Option.map_some,Point.radialField]
    exact o.2.dilate_radialValue hc i H

lemma dilate_value (D : OrdinaryData M) (i : Fin n) (H : (D.dilate hc).band) :
    (D.dilate hc).value i H =
      c*D.value i ⟨H.val/c,(mem_dilate_set c hc).mp H.property⟩ := by
  simp only [value,dilate_comparison]
  change c*D.constant+D.orientation*(c*D.comparison.value i _) = _
  ring
end OrdinaryData

namespace OrderedData
variable {k : ℕ} {M : Model (k+1)} {c}
noncomputable def dilate (D : OrderedData M) : OrderedData (M.dilate c hc) where
  band := (fun T => c*T) '' D.band
  closed := dilate_set_closed c hc D.closed
  convex := dilate_set_convex c hc D.convex
  base := D.base.dilate hc
  lower := D.lower
  upper := D.upper
  ordered := D.base.dilate_orderedFrom hc D.ordered
  auxiliary := D.auxiliary.dilate hc

lemma dilate_value (D : OrderedData M) (lam : ℝ≥0) (i : Fin (k+1)) (H : (D.dilate hc).band) :
    (D.dilate hc).value lam i H =
      c*D.value lam i ⟨H.val/c,(mem_dilate_set c hc).mp H.property⟩ := by
  simp only [value,dilate,Field.dilate]
  ring
end OrderedData

namespace BData
variable {k : ℕ} {M : Model (k+1)} {c}
noncomputable def dilate : BData M → BData (M.dilate c hc)
  | .ordinary D => .ordinary (D.dilate hc)
  | .ordered D => .ordered (D.dilate hc)

lemma dilate_band (D : BData M) : (D.dilate hc).band=(fun T => c*T) '' D.band := by
  cases D <;> rfl

lemma dilate_value (D : BData M) (lam : ℝ≥0) (i : Fin (k+1)) (H : (D.dilate hc).band) :
    (D.dilate hc).value lam i H =
      c*D.value lam i ⟨H.val/c,(mem_dilate_set c hc).mp (D.dilate_band hc ▸ H.property)⟩ := by
  cases D with
  | ordinary D => exact D.dilate_value hc i H
  | ordered D => exact D.dilate_value hc lam i H
end BData
end PlanarL1.Columns.Model


namespace PlanarL1.Threshold
open MeasureTheory
open scoped ENNReal NNReal
variable (c : ℝ) (hc : 0<c)

include hc in
lemma dilation_preserving :
    MeasurePreserving (fun z : Bool × ℝ => (z.1,c*z.2))
      (ENNReal.ofReal c • labelMeasure) labelMeasure := by
  have hreal : MeasurePreserving (fun H : ℝ => c*H)
      (ENNReal.ofReal c • volume) volume := by
    refine ⟨measurable_const.mul measurable_id,?_⟩
    rw [Measure.map_smul (ENNReal.ofReal c) (f := fun H : ℝ => c*H)
      (measurable_const.mul measurable_id).aemeasurable]
    simpa only [abs_of_pos hc] using Real.smul_map_volume_mul_left hc.ne'
  have hp := (MeasurePreserving.id fair).prod hreal
  have hf : Prod.map (id : Bool → Bool) (fun H : ℝ => c*H) =
      (fun z : Bool × ℝ => (z.1,c*z.2)) := by
    funext z
    cases z
    rfl
  simpa only [Measure.prod_smul_right,← labelMeasure_eq,hf] using hp

namespace Variables
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {c}

noncomputable def dilate (Z : Variables Ω μ) :
    Variables Ω (ENNReal.ofReal c • μ) where
  value ω := ((Z.value ω).1,c*(Z.value ω).2)
  preserving := by
    apply (dilation_preserving c hc).comp
    refine ⟨Z.preserving.measurable,?_⟩
    rw [Measure.map_smul (hf := Z.preserving.measurable.aemeasurable),Z.preserving.map_eq]

lemma dilate_active (Z : Variables Ω μ) (H P : ℝ) (ω : Ω) :
    active (Z.dilate hc) H (c*P) ω ↔ active Z (H/c) P ω := by
  change c*(Z.value ω).2 < (if (Z.value ω).1 then H+c*P else H-c*P) ↔ _
  have hH : H=c*(H/c) := (mul_div_cancel₀ H hc.ne').symm
  rw [hH]
  unfold active
  cases hb : (Z.value ω).1 <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · rw [← mul_sub,mul_lt_mul_iff_right₀ hc,mul_div_cancel_left₀ _ hc.ne']
  · rw [← mul_add,mul_lt_mul_iff_right₀ hc,mul_div_cancel_left₀ _ hc.ne']
end Variables
end PlanarL1.Threshold

namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped ENNReal NNReal
variable {n : ℕ} {M : Model n} {c : ℝ} (hc : 0<c)

namespace Activity
noncomputable def dilate (A : Activity M) : Activity (M.dilate c hc) where
  active i H := A.active i (H/c)
  increasing i s t hst := A.increasing i (s/c) (t/c) (div_le_div_of_nonneg_right hst hc.le)
  switch i j H hH := A.switch i j (H/c) ((M.dilate_mem_heights c hc).mp hH)

lemma dilate_indicator (A : Activity M) (i : Fin n) (H : ℝ) :
    (A.dilate hc).indicator i H=A.indicator i (H/c) := rfl

lemma dilate_graph (A : Activity M) : (A.dilate hc).graph=A.graph := by
  ext i j
  constructor
  · rintro ⟨H,hH,hA⟩
    exact ⟨H/c,(M.dilate_mem_heights c hc).mp hH,hA⟩
  · rintro ⟨H,hH,hA⟩
    exact ⟨c*H,⟨H,hH,rfl⟩,by simpa only [dilate,mul_div_cancel_left₀ _ hc.ne'] using hA⟩

lemma dilate_component (A : Activity M) (i : Fin n) :
    (A.dilate hc).component i=A.component i := by
  unfold component
  rw [dilate_graph]

lemma dilate_vector (A : Activity M) (i : Fin n) (H : ℝ) (S : Set (Fin n)) :
    (A.dilate hc).vector i H S=A.vector i (H/c) S := by
  classical
  change (if A.active i (H/c) ∧ S=(A.dilate hc).component i then (1:ℝ) else 0) =
    (if A.active i (H/c) ∧ S=A.component i then 1 else 0)
  rw [dilate_component]

lemma dilate_cost (A : Activity M) (i j : Fin n) (H T : ℝ) :
    (A.dilate hc).cost i j H T=A.cost i j (H/c) (T/c) := by
  simp only [cost,dilate_vector]
end Activity

namespace SetSystem
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Change a cut system's physical units by the same factor as its columns.
The measure, height-coordinate variables, and every scalar chart are all scaled;
there is no implicit normalization of label mass. -/
noncomputable def dilate (A : SetSystem M Ω μ) :
    SetSystem (M.dilate c hc) Ω (ENNReal.ofReal c • μ) where
  activity ω := (A.activity ω).dilate hc
  measurable_active i H := A.measurable_active i (H/c)
  vertical_integrable i H T := (A.vertical_integrable i (H/c) (T/c)).smul_measure
    ENNReal.ofReal_ne_top
  vertical_bound i H T := by
    simp only [Activity.dilate_indicator,integral_smul_measure,smul_eq_mul,
      ENNReal.toReal_ofReal hc.le]
    calc
      _ ≤ c*|(H/c)-(T/c)| := mul_le_mul_of_nonneg_left (A.vertical_bound i (H/c) (T/c)) hc.le
      _ = |H-T| := by rw [← sub_div,abs_div,abs_of_pos hc,mul_div_cancel₀ _ hc.ne']

lemma dilate_movement (A B : SetSystem M Ω μ) (i : Fin n) (H : ℝ) :
    (A.dilate hc).movement (B.dilate hc) i H=c*A.movement B i (H/c) := by
  simp only [movement,dilate,Activity.movement,Activity.dilate_indicator,
    integral_smul_measure,smul_eq_mul,ENNReal.toReal_ofReal hc.le]
end SetSystem
end PlanarL1.Columns.Model


namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped ENNReal NNReal
variable {n : ℕ} {M : Model n} {c : ℝ} (hc : 0<c)

namespace OrdinaryData
lemma dilate_origin_reachable (D : OrdinaryData M) (i : Fin n)
    (h : ∀ r o, D.origin=some ⟨r,o⟩ → (M.activeGraph D.band).Reachable r i) :
    ∀ r o, (D.dilate hc).origin=some ⟨r,o⟩ →
      ((M.dilate c hc).activeGraph (D.dilate hc).band).Reachable r i := by
  intro r o ho
  obtain ⟨⟨s,p⟩,hp,he⟩ := Option.map_eq_some_iff.mp ho
  have hs : s=r := congrArg Sigma.fst he
  change ((M.dilate c hc).activeGraph ((fun T => c*T) '' D.band)).Reachable r i
  rw [M.dilate_activeGraph,← hs]
  exact h s p hp
end OrdinaryData

namespace BData
variable {k : ℕ} {M : Model (k+1)}
lemma dilate_uses (D : BData M) (i : Fin (k+1)) (h : D.Uses i) :
    (D.dilate hc).Uses i := by
  cases D with
  | ordinary D => exact D.dilate_origin_reachable hc i h
  | ordered D => trivial
end BData

namespace OrdinaryState
variable {κ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

noncomputable def dilate (S : OrdinaryState M κ Ω μ) :
    OrdinaryState (M.dilate c hc) κ Ω (ENNReal.ofReal c • μ) where
  sets := S.sets.dilate hc
  count := S.count
  chart q := (S.chart q).dilate hc
  labels q := (S.labels q).dilate hc
  name i H := S.name i (H/c)
  height_in i H := (mem_dilate_set c hc).mpr (S.height_in i (H/c))
  component_in i H := (S.chart (S.name i (H/c))).dilate_origin_reachable hc i
    (S.component_in i (H/c))
  switch_name i j H hH := S.switch_name i j (H/c) ((M.dilate_mem_heights c hc).mp hH)
  represents ω i H := by
    change (S.sets.activity ω).active i (H/c) ↔
      Threshold.active ((S.labels (S.name i (H/c))).dilate hc) H
        (κ*((S.chart (S.name i (H/c))).dilate hc).value i _) ω
    rw [OrdinaryData.dilate_value hc]
    rw [show κ*(c*(S.chart (S.name i (H/c))).value i _) =
        c*(κ*(S.chart (S.name i (H/c))).value i _) by ring]
    rw [Threshold.Variables.dilate_active hc]
    exact S.represents ω i (H/c)
end OrdinaryState

namespace BState
variable {k : ℕ} {M : Model (k+1)}
variable {κ : ℝ} {lam : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

noncomputable def dilate (S : BState M κ lam Ω μ) :
    BState (M.dilate c hc) κ lam Ω (ENNReal.ofReal c • μ) where
  sets := S.sets.dilate hc
  count := S.count
  chart q := (S.chart q).dilate hc
  labels q := (S.labels q).dilate hc
  name i H := S.name i (H/c)
  height_in i H := by
    rw [BData.dilate_band]
    exact (mem_dilate_set c hc).mpr (S.height_in i (H/c))
  component_in i H := (S.chart (S.name i (H/c))).dilate_uses hc i (S.component_in i (H/c))
  switch_name i j H hH := S.switch_name i j (H/c) ((M.dilate_mem_heights c hc).mp hH)
  represents ω i H := by
    change (S.sets.activity ω).active i (H/c) ↔
      Threshold.active ((S.labels (S.name i (H/c))).dilate hc) H
        (κ*((S.chart (S.name i (H/c))).dilate hc).value lam i _) ω
    rw [BData.dilate_value hc]
    rw [show κ*(c*(S.chart (S.name i (H/c))).value lam i _) =
        c*(κ*(S.chart (S.name i (H/c))).value lam i _) by ring]
    rw [Threshold.Variables.dilate_active hc]
    exact S.represents ω i (H/c)
end BState
end PlanarL1.Columns.Model



end

end OAI
