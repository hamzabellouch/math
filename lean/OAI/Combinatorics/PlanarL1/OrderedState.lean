import OAI.Combinatorics.PlanarL1.OrdinaryState

namespace OAI

section

namespace PlanarL1.Columns.Model.Field
open scoped NNReal
variable {k : ℕ} {M : Model (k+1)} {I : Set ℝ} {L : ℝ≥0}

noncomputable def negate (F : M.Field I L) : M.Field I L where
  value i H := -F.value i H
  vertical i := (F.vertical i).neg
  switch i j H hs := congrArg Neg.neg (F.switch i j H hs)

lemma ordered_negate (F : M.Field I L) {a b : Fin (k+1)} (ho : F.OrderedFrom a b) :
    F.negate.OrderedFrom b a := by
  have hrot (H : I) := Ordered.rotate_unimodal_neg (b-a)
    (fun i => F.value (finCycle a i) H)
    (by simpa only [finCycle_apply,zero_add] using fun i => ho.1 H (finCycle a i))
    (by simpa only [finCycle_symm_apply] using ho.2.1 H)
    (by simpa only [finCycle_symm_apply] using ho.2.2 H)
  have had (i : Fin (k+1)) : (i+(b-a))+a=i+b := by abel
  have hbal : -(b-a)=a-b := by abel
  refine ⟨?_,?_,?_⟩
  · intro H i
    exact neg_le_neg (F.ordered_maximum ho H i)
  · intro H i j hij hj
    have hh := (hrot H).2.1 i j hij (by simpa only [hbal,finCycle_symm_apply] using hj)
    simpa only [finCycle_apply,had,negate] using hh
  · intro H i j hi hij
    have hh := (hrot H).2.2 i j (by simpa only [hbal,finCycle_symm_apply] using hi) hij
    simpa only [finCycle_apply,had,negate] using hh

noncomputable def affine (F : M.Field I L) (c : ℝ) (q : ℝ≥0) : M.Field I (q*L) where
  value i H := c+q*F.value i H
  vertical i := by
    apply LipschitzWith.of_dist_le_mul
    intro H T
    have hh := (F.vertical i).dist_le_mul H T
    simp only [Real.dist_eq] at hh ⊢
    rw [show c+(q:ℝ)*F.value i H-(c+(q:ℝ)*F.value i T) =
      (q:ℝ)*(F.value i H-F.value i T) by ring, abs_mul,abs_of_nonneg q.coe_nonneg]
    simpa only [NNReal.coe_mul,mul_assoc] using mul_le_mul_of_nonneg_left hh q.coe_nonneg
  switch i j H hs := by rw [F.switch i j H hs]

lemma ordered_affine (F : M.Field I L) {a b : Fin (k+1)} (ho : F.OrderedFrom a b)
    (c : ℝ) (q : ℝ≥0) : (F.affine c q).OrderedFrom a b := by
  refine ⟨?_,?_,?_⟩
  · intro H i
    simpa only [affine,add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left (ho.1 H i) q.coe_nonneg) c
  · intro H i j hij hj
    simpa only [affine,add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left (ho.2.1 H i j hij hj) q.coe_nonneg) c
  · intro H i j hi hij
    simpa only [affine,add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left (ho.2.2 H i j hi hij) q.coe_nonneg) c

end PlanarL1.Columns.Model.Field


namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped NNReal

namespace Field
variable {n : ℕ} {M : Model n} {I : Set ℝ} {L K : ℝ≥0}

def weaken (F : M.Field I L) (h : L ≤ K) : M.Field I K where
  value := F.value
  vertical i := (F.vertical i).weaken h
  switch := F.switch

noncomputable def add (F : M.Field I L) (G : M.Field I K) : M.Field I (L+K) where
  value i H := F.value i H+G.value i H
  vertical i := (F.vertical i).add (G.vertical i)
  switch i j H h := by rw [F.switch i j H h,G.switch i j H h]
end Field

/-- The ordered-chart data. The base ordered field never
changes during this identifier's lifetime. The auxiliary field is replaced by
its actual signed increment history; its bound is 100, not an unbounded sum
of the individual increments. -/
structure OrderedData {k : ℕ} (M : Model (k+1)) where
  band : Set ℝ
  closed : IsClosed band
  convex : band.OrdConnected
  base : M.Field band 4
  lower : Fin (k+1)
  upper : Fin (k+1)
  ordered : base.OrderedFrom lower upper
  auxiliary : M.Field band 100

namespace OrderedData
variable {k : ℕ} {M : Model (k+1)}

noncomputable def value (D : OrderedData M) (lam : ℝ≥0) (i : Fin (k+1)) (H : D.band) : ℝ :=
  D.base.value i H+lam*D.auxiliary.value i H

noncomputable def field (D : OrderedData M) (lam : ℝ≥0) (hlam : lam ≤ (1:ℝ≥0)/100) :
    M.Field D.band 5 :=
  (D.base.add (D.auxiliary.affine 0 lam)).weaken (by nlinarith)

lemma field_value (D : OrderedData M) (lam : ℝ≥0) (hlam : lam ≤ (1:ℝ≥0)/100)
    (i : Fin (k+1)) (H : D.band) : (D.field lam hlam).value i H=D.value lam i H := by
  simp only [field,Field.weaken,Field.add,Field.affine,zero_add,value]

/-- Install the spatial ordered branch O_F, with zero auxiliary history.
The boolean is the conversion back to the old chart orientation. Negation
exchanges, rather than discards, the two circular boundary columns. -/
noncomputable def install {I : Set ℝ} (hI : IsClosed I) (hc : I.OrdConnected)
    (L : M.Field I 1) (a b : Fin (k+1)) (ho : L.OrderedFrom a b)
    (c : ℝ) (positive : Bool) : OrderedData M where
  band := I
  closed := hI
  convex := hc
  base := if positive then
    (L.affine c 4).weaken (by norm_num) else
    ((L.affine c 4).negate).weaken (by norm_num)
  lower := if positive then a else b
  upper := if positive then b else a
  ordered := by
    cases positive
    · exact (L.affine c 4).ordered_negate (L.ordered_affine ho c 4)
    · exact L.ordered_affine ho c 4
  auxiliary := (Field.constant M I 0).weaken (by norm_num)

lemma install_value {I : Set ℝ} (hI : IsClosed I) (hc : I.OrdConnected)
    (L : M.Field I 1) (a b : Fin (k+1)) (ho : L.OrderedFrom a b)
    (c : ℝ) (positive : Bool) (lam : ℝ≥0) (i : Fin (k+1)) (H : I) :
    (install hI hc L a b ho c positive).value lam i H =
      if positive then c+4*L.value i H else -(c+4*L.value i H) := by
  cases positive <;> simp [install,value,Field.weaken,Field.affine,Field.negate,Field.constant]
end OrderedData

/-- System B has precisely the ordinary and ordered chart alternatives. -/
inductive BData {k : ℕ} (M : Model (k+1))
  | ordinary : OrdinaryData M → BData M
  | ordered : OrderedData M → BData M

namespace BData
variable {k : ℕ} {M : Model (k+1)}

def band : BData M → Set ℝ
  | .ordinary D => D.band
  | .ordered D => D.band

lemma closed (D : BData M) : IsClosed D.band := by
  cases D with
  | ordinary D => exact D.closed
  | ordered D => exact D.closed

lemma convex (D : BData M) : D.band.OrdConnected := by
  cases D with
  | ordinary D => exact D.convex
  | ordered D => exact D.convex

noncomputable def value (lam : ℝ≥0) : (D : BData M) → Fin (k+1) → D.band → ℝ
  | .ordinary D => D.value
  | .ordered D => D.value lam

noncomputable def field (lam : ℝ≥0) (hlam : lam ≤ (1:ℝ≥0)/100) :
    (D : BData M) → M.Field D.band 5
  | .ordinary D => D.field.weaken (by norm_num)
  | .ordered D => D.field lam hlam

lemma field_value (lam : ℝ≥0) (hlam : lam ≤ (1:ℝ≥0)/100) (D : BData M)
    (i : Fin (k+1)) (H : D.band) : (D.field lam hlam).value i H=D.value lam i H := by
  cases D with
  | ordinary D => rfl
  | ordered D => exact D.field_value lam hlam i H

/-- Component restriction is attached only to a genuine point-source chart;
the ordered formula is defined on every component of its recorded band. -/
def Uses (D : BData M) (i : Fin (k+1)) : Prop :=
  match D with
  | .ordinary C => ∀ r o, C.origin=some ⟨r,o⟩ → (M.activeGraph C.band).Reachable r i
  | .ordered _ => True
end BData

structure BState {k : ℕ} (M : Model (k+1)) (κ : ℝ) (lam : ℝ≥0) (Ω : Type*)
    [MeasurableSpace Ω] (μ : Measure Ω) where
  sets : SetSystem M Ω μ
  count : ℕ
  chart : Fin (count+1) → BData M
  labels : Fin (count+1) → Threshold.Variables Ω μ
  name : Fin (k+1) → ℝ → Fin (count+1)
  height_in : ∀ i H, H ∈ (chart (name i H)).band
  component_in : ∀ i H, (chart (name i H)).Uses i
  switch_name : ∀ i j H, H ∈ M.heights i j → name i H = name j H
  represents : ∀ ω i H,
    (sets.activity ω).active i H ↔ Threshold.active (labels (name i H)) H
      (κ*(chart (name i H)).value lam i ⟨H,height_in i H⟩) ω

namespace BState
variable {k : ℕ} {M : Model (k+1)} {κ : ℝ} {lam : ℝ≥0}
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

noncomputable def ofOrdinary (S : OrdinaryState M κ Ω μ) : BState M κ lam Ω μ where
  sets := S.sets
  count := S.count
  chart a := .ordinary (S.chart a)
  labels := S.labels
  name := S.name
  height_in := S.height_in
  component_in := S.component_in
  switch_name := S.switch_name
  represents := S.represents

noncomputable def initial (M : Model (k+1)) (κ : ℝ) (lam : ℝ≥0) :
    BState M κ lam (Bool × ℝ) Threshold.labelMeasure :=
  ofOrdinary (OrdinaryState.initial M κ)

noncomputable def lift (S : BState M κ lam Ω μ) :
    BState M κ lam (Ω × Bool) (μ.prod Threshold.fair) where
  sets := S.sets.lift
  count := S.count
  chart := S.chart
  labels a := (S.labels a).lift
  name := S.name
  height_in := S.height_in
  component_in := S.component_in
  switch_name := S.switch_name
  represents ω i H := S.represents ω.1 i H

/-- Finite chart-table extension. Old identifiers are literally retained in the
right summand; installing a fresh chart never refines the old regions. -/
noncomputable def append (S : BState M κ lam Ω μ) (B : SetSystem M Ω μ)
    (m : ℕ) (D : Fin m → BData M) (Z : Fin m → Threshold.Variables Ω μ)
    (choose : Fin (k+1) → ℝ → Option (Fin m))
    (hin : ∀ i H a, choose i H = some a → H ∈ (D a).band)
    (hcomp : ∀ i H a, choose i H = some a → (D a).Uses i)
    (hswitch : ∀ i j H, H ∈ M.heights i j → choose i H = choose j H)
    (hold : ∀ ω i H, choose i H = none →
      ((B.activity ω).active i H ↔ (S.sets.activity ω).active i H))
    (hnew : ∀ ω i H a (hc : choose i H = some a),
      ((B.activity ω).active i H ↔ Threshold.active (Z a) H
        (κ*(D a).value lam i ⟨H,hin i H a hc⟩) ω)) : BState M κ lam Ω μ where
  sets := B
  count := m+S.count
  chart := Fin.addCases (m := m) (n := S.count+1) D S.chart
  labels := Fin.addCases (m := m) (n := S.count+1) Z S.labels
  name i H := match choose i H with
    | none => Fin.natAdd m (S.name i H)
    | some a => Fin.castAdd (S.count+1) a
  height_in i H := by
    cases hc : choose i H with
    | none => simpa only [hc,Fin.addCases_right] using S.height_in i H
    | some a => simpa only [hc,Fin.addCases_left] using hin i H a hc
  component_in i H := by
    let Uses (D : BData M) : Prop := D.Uses i
    change Uses (Fin.addCases (m := m) (n := S.count+1) D S.chart
      (match choose i H with
      | none => Fin.natAdd m (S.name i H)
      | some a => Fin.castAdd (S.count+1) a))
    cases hc : choose i H with
    | none =>
      simp only [Fin.addCases_right]
      exact S.component_in i H
    | some a =>
      simp only [Fin.addCases_left]
      exact hcomp i H a hc
  switch_name i j H hh := by
    have hc := hswitch i j H hh
    rw [hc]
    cases choose j H with
    | none => exact congrArg (Fin.natAdd m) (S.switch_name i j H hh)
    | some a => rfl
  represents ω i H := by
    let Rep (D : BData M) (Z : Threshold.Variables Ω μ) : Prop :=
      ∀ hi : H ∈ D.band, (B.activity ω).active i H ↔
        Threshold.active Z H (κ*D.value lam i ⟨H,hi⟩) ω
    have hr : Rep
        (Fin.addCases (m := m) (n := S.count+1) D S.chart
          (match choose i H with
          | none => Fin.natAdd m (S.name i H)
          | some a => Fin.castAdd (S.count+1) a))
        (Fin.addCases (m := m) (n := S.count+1) Z S.labels
          (match choose i H with
          | none => Fin.natAdd m (S.name i H)
          | some a => Fin.castAdd (S.count+1) a)) := by
      cases hc : choose i H with
      | none =>
        simp only [Fin.addCases_right]
        intro hi
        exact (hold ω i H hc).trans (S.represents ω i H)
      | some a =>
        simp only [Fin.addCases_left]
        intro hi
        exact hnew ω i H a hc
    exact hr _

/-- Deterministic chart distance on a common identifier, with no independence
assumed between different identifiers. -/
lemma chart_distance (S : BState M κ lam Ω μ) (i j : Fin (k+1)) (H T : ℝ)
    (he : S.name i H=S.name j T) :
    (∫ ω, |(S.sets.activity ω).indicator i H-(S.sets.activity ω).indicator j T| ∂μ) =
      max |H-T| |κ*(S.chart (S.name i H)).value lam i ⟨H,S.height_in i H⟩-
        κ*(S.chart (S.name j T)).value lam j ⟨T,S.height_in j T⟩| := by
  have hid (i : Fin (k+1)) (H : ℝ) (ω : Ω) :
      (S.sets.activity ω).indicator i H = Threshold.chartValue H
        (κ*(S.chart (S.name i H)).value lam i ⟨H,S.height_in i H⟩)
        ((S.labels (S.name i H)).value ω) := by
    simp only [Activity.indicator,S.represents,Threshold.active,Threshold.chartValue,Threshold.half]
  simp_rw [hid]
  rw [show S.labels (S.name j T)=S.labels (S.name i H) from congrArg S.labels he.symm]
  exact (S.labels (S.name i H)).distance _ _ _ _

end BState
end PlanarL1.Columns.Model



end

section

namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {κ : ℝ} {lam : ℝ≥0}
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace BState
variable (S : BState M κ lam Ω μ)

noncomputable def oldValue (i : Fin (k+1)) (H : ℝ) : ℝ :=
  κ*(S.chart (S.name i H)).value lam i ⟨H,S.height_in i H⟩

lemma oldValue_eq (i : Fin (k+1)) (H : ℝ) (a : Fin (S.count+1))
    (h : S.name i H=a) : S.oldValue i H =
      κ*(S.chart a).value lam i ⟨H,by simpa only [h] using S.height_in i H⟩ := by
  subst a
  rfl

noncomputable def newValue (F : ∀ a, M.Field (S.chart a).band 5)
    (i : Fin (k+1)) (H : ℝ) : ℝ :=
  κ*(F (S.name i H)).value i ⟨H,S.height_in i H⟩

lemma newValue_eq (F : ∀ a, M.Field (S.chart a).band 5)
    (i : Fin (k+1)) (H : ℝ) (a : Fin (S.count+1)) (h : S.name i H=a) :
    S.newValue F i H = κ*(F a).value i ⟨H,by simpa only [h] using S.height_in i H⟩ := by
  subst a
  rfl

lemma newValue_lipschitz (F : ∀ a, M.Field (S.chart a).band 5) (hk : 0 ≤ κ)
    (i : Fin (k+1)) (H T : ℝ) (he : S.name i H=S.name i T) :
    |S.newValue F i H-S.newValue F i T| ≤ (κ*5)*|H-T| := by
  rw [S.newValue_eq F i H (S.name i H) rfl,S.newValue_eq F i T (S.name i H) he.symm]
  rw [← mul_sub,abs_mul,abs_of_nonneg hk]
  have hb := ((F (S.name i H)).vertical i).dist_le_mul
    ⟨H,S.height_in i H⟩ ⟨T,by simpa only [he] using S.height_in i T⟩
  simp only [Real.dist_eq,Subtype.dist_eq,NNReal.coe_ofNat] at hb
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb hk

lemma oldValue_lipschitz (hk : 0 ≤ κ) (hlam : lam ≤ (1:ℝ≥0)/100)
    (i : Fin (k+1)) (H T : ℝ) (he : S.name i H=S.name i T) :
    |S.oldValue i H-S.oldValue i T| ≤ (κ*5)*|H-T| := by
  have hf (i H) : S.newValue (fun a => (S.chart a).field lam hlam) i H=S.oldValue i H := by
    simp only [newValue,oldValue,BData.field_value]
  simpa only [hf] using S.newValue_lipschitz (fun a => (S.chart a).field lam hlam) hk i H T he

/-- A simultaneous same-identifier update, defined by the actual new fields.
The boundary estimate is exactly what the ambient complement taper provides.
The name map is retained literally; it is not refined to a partition with
better-behaved boundaries. -/
noncomputable def fieldActivity (F : ∀ a, M.Field (S.chart a).band 5)
    (hk : 0 ≤ κ) (hsmall : κ*5 ≤ 1/2) (hlam : lam ≤ (1:ℝ≥0)/100)
    (hd : ∀ i H T, S.name i H≠S.name i T →
      |S.newValue F i H-S.oldValue i H| ≤ |H-T|/8)
    (ω : Ω) : Activity M where
  active i H := Threshold.active (S.labels (S.name i H)) H (S.newValue F i H) ω
  increasing i H T hHT := by
    apply Threshold.named_nested (S.name i) S.labels (S.oldValue i) (S.newValue F i)
      (fun H ω => (S.sets.activity ω).active i H)
      (fun ω s t hst => (S.sets.activity ω).increasing i s t hst)
      (fun H ω => S.represents ω i H)
      (fun s t he => (S.oldValue_lipschitz hk hlam i s t he).trans (by
        nlinarith [abs_nonneg (s-t)]))
      (fun s t he => (S.newValue_lipschitz F hk i s t he).trans (by
        nlinarith [abs_nonneg (s-t)]))
      (hd i) ω hHT
  switch i j H hh := by
    have he := S.switch_name i j H hh
    have hv : S.newValue F i H=S.newValue F j H := by
      rw [S.newValue_eq F i H (S.name i H) rfl,
        S.newValue_eq F j H (S.name i H) he.symm]
      rw [(F (S.name i H)).switch i j ⟨H,S.height_in i H⟩ hh]
    simp only [he,hv]

lemma field_indicator (F : ∀ a, M.Field (S.chart a).band 5)
    (hk : 0 ≤ κ) (hsmall : κ*5 ≤ 1/2) (hlam : lam ≤ (1:ℝ≥0)/100)
    (hd : ∀ i H T, S.name i H≠S.name i T →
      |S.newValue F i H-S.oldValue i H| ≤ |H-T|/8)
    (ω : Ω) (i : Fin (k+1)) (H : ℝ) :
    (S.fieldActivity F hk hsmall hlam hd ω).indicator i H =
      Threshold.chartValue H (S.newValue F i H) ((S.labels (S.name i H)).value ω) := rfl

lemma old_indicator (ω : Ω) (i : Fin (k+1)) (H : ℝ) :
    (S.sets.activity ω).indicator i H =
      Threshold.chartValue H (S.oldValue i H) ((S.labels (S.name i H)).value ω) := by
  simp only [Activity.indicator,S.represents,oldValue,
    Threshold.chartValue,Threshold.half,Threshold.active]
  rfl

noncomputable def fieldUpdate (F : ∀ a, M.Field (S.chart a).band 5)
    (hk : 0 ≤ κ) (hsmall : κ*5 ≤ 1/2) (hlam : lam ≤ (1:ℝ≥0)/100)
    (hd : ∀ i H T, S.name i H≠S.name i T →
      |S.newValue F i H-S.oldValue i H| ≤ |H-T|/8) : SetSystem M Ω μ :=
  S.sets.balancedUpdate (S.fieldActivity F hk hsmall hlam hd)
    (fun i H => Threshold.measurable_active _ _ _)
    (fun i H => by
      simp only [S.field_indicator,S.old_indicator]
      exact (S.labels (S.name i H)).integrable_difference _ _ _ _)
    (fun i H => by
      simp only [S.field_indicator,S.old_indicator]
      rw [(S.labels (S.name i H)).integral_difference,sub_self])

end BState
end PlanarL1.Columns.Model



end

section

namespace PlanarL1.Columns.Model
open scoped NNReal
namespace OrderedData
variable {k : ℕ} {M : Model (k+1)}

/-- Replace only the auxiliary history; all data determining t_s stay fixed. -/
def withAuxiliary (D : OrderedData M) (u : M.Field D.band 100) : OrderedData M :=
  { D with auxiliary := u }

lemma withAuxiliary_value (D : OrderedData M) (u : M.Field D.band 100)
    (lam : ℝ≥0) (i : Fin (k+1)) (H : D.band) :
    (D.withAuxiliary u).value lam i H-D.value lam i H =
      lam*(u.value i H-D.auxiliary.value i H) := by
  unfold withAuxiliary value
  ring

end OrderedData
end PlanarL1.Columns.Model




end

section

namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)}

namespace BData

def Auxiliary : BData M → Type
  | .ordinary _ => Unit
  | .ordered D => M.Field D.band 100

def withAuxiliary (D : BData M) (u : D.Auxiliary) : BData M :=
  match D with
  | .ordinary C => .ordinary C
  | .ordered C => .ordered (C.withAuxiliary u)

@[simp] lemma withAuxiliary_band (D : BData M) (u : D.Auxiliary) :
    (D.withAuxiliary u).band=D.band := by cases D <;> rfl

lemma withAuxiliary_uses (D : BData M) (u : D.Auxiliary) (i : Fin (k+1)) :
    (D.withAuxiliary u).Uses i ↔ D.Uses i := by cases D <;> rfl

noncomputable def auxiliaryField (D : BData M) (u : D.Auxiliary)
    (lam : ℝ≥0) (hlam : lam ≤ (1:ℝ≥0)/100) : M.Field D.band 5 :=
  match D with
  | .ordinary C => C.field.weaken (by norm_num)
  | .ordered C => (C.withAuxiliary u).field lam hlam

lemma auxiliaryField_value (D : BData M) (u : D.Auxiliary)
    (lam : ℝ≥0) (hlam : lam ≤ (1:ℝ≥0)/100) (i : Fin (k+1)) (H : D.band) :
    (D.auxiliaryField u lam hlam).value i H =
      (D.withAuxiliary u).value lam i ⟨H.val,by simp⟩ := by
  cases D with
  | ordinary C => rfl
  | ordered C => exact (C.withAuxiliary u).field_value lam hlam i H

end BData

namespace BState
variable {κ : ℝ} {lam : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  (S : BState M κ lam Ω μ)

/-- Simultaneously replace every ordered history, while retaining literally all
old chart names and all label variables. Ordinary charts are unaltered. -/
noncomputable def withAuxiliary (U : ∀ a, (S.chart a).Auxiliary)
    (hk : 0 ≤ κ) (hsmall : κ*5 ≤ 1/2) (hlam : lam ≤ (1:ℝ≥0)/100)
    (hd : ∀ i H T, S.name i H≠S.name i T →
      |S.newValue (fun a => (S.chart a).auxiliaryField (U a) lam hlam) i H-S.oldValue i H| ≤
        |H-T|/8) : BState M κ lam Ω μ where
  sets := S.fieldUpdate (fun a => (S.chart a).auxiliaryField (U a) lam hlam) hk hsmall hlam hd
  count := S.count
  chart a := (S.chart a).withAuxiliary (U a)
  labels := S.labels
  name := S.name
  height_in i H := by simpa only [BData.withAuxiliary_band] using S.height_in i H
  component_in i H := (BData.withAuxiliary_uses _ _ _).mpr (S.component_in i H)
  switch_name := S.switch_name
  represents ω i H := by
    change Threshold.active (S.labels (S.name i H)) H
      (S.newValue (fun a => (S.chart a).auxiliaryField (U a) lam hlam) i H) ω ↔ _
    unfold newValue
    rw [BData.auxiliaryField_value]

end BState
end PlanarL1.Columns.Model



end

end OAI
