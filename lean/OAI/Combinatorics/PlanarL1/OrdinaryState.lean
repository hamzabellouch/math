import OAI.Combinatorics.PlanarL1.MainCells

namespace OAI

section

namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped NNReal

namespace SetSystem
variable {n : ℕ} {M : Model n} {Ω Ω' : Type*} [MeasurableSpace Ω]
  [MeasurableSpace Ω'] {μ : Measure Ω} {μ' : Measure Ω'}

/-- Change label coordinates only: every individual set and component graph is
pulled back, and the upper invariant is transported by the actual measure. -/
noncomputable def pullback (A : SetSystem M Ω μ) {g : Ω' → Ω}
    (hg : MeasurePreserving g μ' μ) : SetSystem M Ω' μ' where
  activity ω := A.activity (g ω)
  measurable_active i H := (A.measurable_active i H).preimage hg.measurable
  vertical_integrable i s t := hg.integrable_comp_of_integrable (A.vertical_integrable i s t)
  vertical_bound i s t := by
    have he : (∫ ω, |(A.activity (g ω)).indicator i s-(A.activity (g ω)).indicator i t| ∂μ') =
        ∫ ω, |(A.activity ω).indicator i s-(A.activity ω).indicator i t| ∂μ := by
      calc
        _ = ∫ ω, |(A.activity ω).indicator i s-(A.activity ω).indicator i t|
            ∂Measure.map g μ' :=
          (integral_map_of_stronglyMeasurable hg.measurable
            (((A.measurable_indicator i s).sub
              (A.measurable_indicator i t)).abs.stronglyMeasurable)).symm
        _ = _ := congrArg (fun ν => ∫ ω,
          |(A.activity ω).indicator i s-(A.activity ω).indicator i t| ∂ν) hg.map_eq
    exact he.trans_le (A.vertical_bound i s t)

noncomputable def lift (A : SetSystem M Ω μ) : SetSystem M (Ω × Bool) (μ.prod Threshold.fair) :=
  A.pullback (measurePreserving_fst (μ := μ) (ν := Threshold.fair))

@[simp] lemma lift_active (A : SetSystem M Ω μ) (z : Ω × Bool) (i : Fin n) (H : ℝ) :
    (A.lift.activity z).active i H ↔ (A.activity z.1).active i H := Iff.rfl

end SetSystem

namespace Field
variable {n : ℕ} (M : Model n) (I : Set ℝ)
noncomputable def constant (c : ℝ) : M.Field I 1 where
  value _ _ := c
  vertical _ := (LipschitzWith.const c).weaken (by norm_num)
  switch _ _ _ _ := rfl
end Field

/-- The literal ordinary-chart scalar data. A nonconstant chart remembers its
old band component and its one point source, rather than just a Lipschitz bound.
The zero extension outside that component is never used on the chart's region. -/
structure OrdinaryData {n : ℕ} (M : Model n) where
  band : Set ℝ
  closed : IsClosed band
  convex : band.OrdConnected
  origin : Option (Σ r : Fin n, M.Point band r)
  constant : ℝ
  orientation : ℝ
  unit_orientation : |orientation| = 1

namespace OrdinaryData
variable {n : ℕ} {M : Model n}

noncomputable def comparison (D : OrdinaryData M) : M.Field D.band 1 :=
  match D.origin with
  | none => Field.constant M D.band 0
  | some o => o.2.radialField

noncomputable def value (D : OrdinaryData M) (i : Fin n) (H : D.band) : ℝ :=
  D.constant + D.orientation * D.comparison.value i H

lemma vertical (D : OrdinaryData M) (i : Fin n) : LipschitzWith 1 (D.value i) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [Real.dist_eq]
  change |D.constant+D.orientation*D.comparison.value i s-
    (D.constant+D.orientation*D.comparison.value i t)| ≤ _
  rw [show D.constant+D.orientation*D.comparison.value i s-
    (D.constant+D.orientation*D.comparison.value i t) =
    D.orientation*(D.comparison.value i s-D.comparison.value i t) by ring,
    abs_mul,D.unit_orientation,one_mul]
  exact (D.comparison.vertical i).dist_le_mul s t

lemma switch (D : OrdinaryData M) (i j : Fin n) (H : D.band)
    (h : H.val ∈ M.heights i j) : D.value i H = D.value j H := by
  simp only [value,D.comparison.switch i j H h]

noncomputable def field (D : OrdinaryData M) : M.Field D.band 1 :=
  ⟨D.value,D.vertical,D.switch⟩

noncomputable def initial (M : Model n) : OrdinaryData M where
  band := Set.univ
  closed := isClosed_univ
  convex := Set.ordConnected_univ
  origin := none
  constant := 0
  orientation := 1
  unit_orientation := by norm_num

@[simp] lemma initial_value (M : Model n) (i : Fin n) (H : ℝ) :
    (initial M).value i ⟨H,Set.mem_univ H⟩ = 0 := by
  simp [initial,value,comparison,Field.constant]

/-- Conversion of an actual signed atom back to the old ordinary orientation. -/
noncomputable def atom (D : OrdinaryData M) (J : Set ℝ) (hJ : IsClosed J)
    (hc : J.OrdConnected) {r : Fin n} (o : M.Point J r) (c η : ℝ) (hη : |η| = 1) :
    OrdinaryData M where
  band := J
  closed := hJ
  convex := hc
  origin := some ⟨r,o⟩
  constant := D.constant+D.orientation*c
  orientation := D.orientation*η
  unit_orientation := by rw [abs_mul,D.unit_orientation,hη,mul_one]

lemma atom_value (D : OrdinaryData M) (J : Set ℝ) (hJ : IsClosed J)
    (hc : J.OrdConnected) {r : Fin n} (o x : M.Point J r) (c η : ℝ) (hη : |η| = 1) :
    (D.atom J hJ hc o c η hη).value x.column ⟨x.height,x.inBand⟩ =
      D.constant+D.orientation*(c+η*dist o x) := by
  have he : o.radialField.value x.column ⟨x.height,x.inBand⟩=dist o x := o.radialField_eval x
  simp only [value,atom,comparison,he]
  ring

end OrdinaryData

/-- A finite ordinary chart partition for system A, with the actual globally
nested sets and actual jointly distributed label variables. Chart regions may
be disconnected; no artificial connected-component identifiers are introduced. -/
structure OrdinaryState {n : ℕ} (M : Model n) (κ : ℝ) (Ω : Type*)
    [MeasurableSpace Ω] (μ : Measure Ω) where
  sets : SetSystem M Ω μ
  count : ℕ
  chart : Fin (count+1) → OrdinaryData M
  labels : Fin (count+1) → Threshold.Variables Ω μ
  name : Fin n → ℝ → Fin (count+1)
  height_in : ∀ i H, H ∈ (chart (name i H)).band
  component_in : ∀ i H r o, (chart (name i H)).origin = some ⟨r,o⟩ →
    (M.activeGraph (chart (name i H)).band).Reachable r i
  switch_name : ∀ i j H, H ∈ M.heights i j → name i H = name j H
  represents : ∀ ω i H,
    (sets.activity ω).active i H ↔ Threshold.active (labels (name i H)) H
      (κ*(chart (name i H)).value i ⟨H,height_in i H⟩) ω

namespace OrdinaryState
variable {n : ℕ} {M : Model n} {κ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

noncomputable def initial (M : Model n) (κ : ℝ) :
    OrdinaryState M κ (Bool × ℝ) Threshold.labelMeasure where
  sets := Threshold.chartSystem (Field.constant M Set.univ 0) (by norm_num)
  count := 0
  chart _ := OrdinaryData.initial M
  labels _ := Threshold.Variables.initial
  name _ _ := 0
  height_in _ _ := Set.mem_univ _
  component_in _ _ r o h := by cases h
  switch_name _ _ _ _ := rfl
  represents ω i H := by
    simp only [Threshold.chartSystem,Threshold.chartActivity,OrdinaryData.initial_value,
      mul_zero,Field.constant,Threshold.active,Threshold.Variables.initial]
    rfl

noncomputable def lift (S : OrdinaryState M κ Ω μ) :
    OrdinaryState M κ (Ω × Bool) (μ.prod Threshold.fair) where
  sets := S.sets.lift
  count := S.count
  chart := S.chart
  labels j := (S.labels j).lift
  name := S.name
  height_in := S.height_in
  component_in := S.component_in
  switch_name := S.switch_name
  represents ω i H := S.represents ω.1 i H

/-- Deterministic chart distance on a common identifier, with no independence
assumed between different identifiers. -/
lemma chart_distance (S : OrdinaryState M κ Ω μ) (i j : Fin n) (H T : ℝ)
    (he : S.name i H=S.name j T) :
    (∫ ω, |(S.sets.activity ω).indicator i H-(S.sets.activity ω).indicator j T| ∂μ) =
      max |H-T| |κ*(S.chart (S.name i H)).value i ⟨H,S.height_in i H⟩-
        κ*(S.chart (S.name j T)).value j ⟨T,S.height_in j T⟩| := by
  have hid (i : Fin n) (H : ℝ) (ω : Ω) :
      (S.sets.activity ω).indicator i H = Threshold.chartValue H
        (κ*(S.chart (S.name i H)).value i ⟨H,S.height_in i H⟩)
        ((S.labels (S.name i H)).value ω) := by
    simp only [Activity.indicator,S.represents,Threshold.active,Threshold.chartValue,Threshold.half]
  simp_rw [hid]
  rw [show S.labels (S.name j T)=S.labels (S.name i H) from congrArg S.labels he.symm]
  exact (S.labels (S.name i H)).distance _ _ _ _

end OrdinaryState
end PlanarL1.Columns.Model


namespace PlanarL1.Columns.Model.Point.RadialTree
open PlanarL1.Interpolation
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
variable (R : RadialTree (M := M) (J := J) (root := root))

lemma atomName_depth_eq {k l : ℕ} (u v : M.Point J root) (t t' : Fin 3)
    (he : atomName k u t = atomName l v t') : k = l := by
  have hu := atomName_bounds k u t
  have hv := atomName_bounds l v t'
  rcases lt_trichotomy k l with h | h | h
  · have hm := Nat.mul_le_mul_left (3*n) (Nat.succ_le_of_lt h)
    simp only [Nat.succ_eq_add_one] at hm
    omega
  · exact h
  · have hm := Nat.mul_le_mul_left (3*n) (Nat.succ_le_of_lt h)
    simp only [Nat.succ_eq_add_one] at hm
    omega

lemma portalAt_mem {k : ℕ} (C : R.Node k) (i : Fin 2) :
    (R.portalAt C i).column ∈ ColumnOrder.componentColumns C := by
  by_cases hi : i = 0
  · simpa only [portalAt,ite_eq_left hi] using (R.portals C).left_mem
  · simpa only [portalAt,ite_eq_right hi] using (R.portals C).right_mem

lemma node_eq_of_portal_column {k : ℕ} (C D : R.Node k) (i j : Fin 2)
    (he : (R.portalAt C i).column=(R.portalAt D j).column) : C = D := by
  apply ColumnOrder.component_eq_of_column (R.portalAt_mem C i)
  rw [he]
  exact R.portalAt_mem D j

/-- A name is global to the whole interpolation tree, not only a chosen chain.
Different node occurrences cannot silently give one identifier two fields. -/
lemma nodeAtom_eq_global (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k l : ℕ} (C : R.Node k) (D : R.Node l) (i j : Fin 2) (t t' : Fin 3)
    (he : atomName k (R.portalAt C i) t = atomName l (R.portalAt D j) t') :
    R.nodeAtom p α C i t = R.nodeAtom p α D j t' := by
  have hk := atomName_depth_eq (R.portalAt C i) (R.portalAt D j) t t' he
  subst l
  obtain ⟨hc,ht⟩ := atomName_same_depth _ _ _ _ he
  have hC := R.node_eq_of_portal_column C D i j hc
  subst D
  exact R.nodeAtom_eq_of_name p α C i j t t' he

/-- The exact portal occurrence from which an atom identifier originates. -/
structure AtomSource (a : ℕ) where
  depth : ℕ
  node : R.Node depth
  portal : Fin 2
  kind : Fin 3
  name_eq : atomName depth (R.portalAt node portal) kind = a

lemma pasted_has_source (p : M.Point J root → ℝ) (α : Noise (n := n))
    (x : M.Point J root) : Nonempty (R.AtomSource (R.pasted p α x).name) := by
  obtain ⟨k,hk,i,t,he⟩ := R.formula_eq_atom p α (R.layerDepth x) (R.layerNode x) x
  refine ⟨⟨k,R.ancestor (R.layerNode x) k hk,i,t,?_⟩⟩
  exact (congrArg NamedValue.name he).symm

lemma pasted_name_lt (p : M.Point J root → ℝ) (α : Noise (n := n))
    (x : M.Point J root) : (R.pasted p α x).name < 3*n*R.depthCap := by
  exact (R.formula_name_bound p α (R.layerDepth x) (R.layerNode x) x).trans_le
    (Nat.mul_le_mul_left (3*n) (R.layerDepth_lt_cap x))

namespace AtomSource
variable {R} {a : ℕ}

noncomputable def eval (S : R.AtomSource a) (p : M.Point J root → ℝ)
    (α : Noise (n := n)) : M.Point J root → NamedValue :=
  R.nodeAtom p α S.node S.portal S.kind

lemma eval_eq (S T : R.AtomSource a) (p : M.Point J root → ℝ) (α : Noise (n := n)) :
    S.eval p α = T.eval p α :=
  R.nodeAtom_eq_global p α S.node T.node S.portal T.portal S.kind T.kind
    (S.name_eq.trans T.name_eq.symm)

noncomputable def center (S : R.AtomSource a) : M.Point J root := R.portalAt S.node S.portal

noncomputable def intercept (S : R.AtomSource a) (p : M.Point J root → ℝ)
    (α : Noise (n := n)) : ℝ :=
  (if S.kind = 0 then p S.center else R.parentValue p α S.depth S.node S.center) +
    (if S.kind = 1 then -α S.depth S.center.column S.kind else α S.depth S.center.column S.kind)

noncomputable def sign (S : R.AtomSource a) : ℝ := if S.kind = 2 then -1 else 1

lemma sign_unit (S : R.AtomSource a) : |S.sign| = 1 := by
  unfold sign
  split_ifs <;> norm_num

lemma eval_formula (S : R.AtomSource a) (p : M.Point J root → ℝ)
    (α : Noise (n := n)) (x : M.Point J root) :
    (S.eval p α x).value = S.intercept p α+S.sign*dist S.center x := by
  simp only [eval,nodeAtom,atomIntercept,intercept,sign,center]
  split_ifs <;> ring

/-- Convert back to the old ordinary orientation, as in /main-packing.
The -4E proposal shift is part of the literal atom constant. -/
noncomputable def chart (S : R.AtomSource a) (D : OrdinaryData M)
    (p : M.Point J root → ℝ) (α : Noise (n := n)) (E : ℝ) : OrdinaryData M :=
  D.atom J R.closed_band R.interval_band S.center (S.intercept p α-4*E) S.sign S.sign_unit

lemma chart_value (S : R.AtomSource a) (D : OrdinaryData M)
    (p : M.Point J root → ℝ) (α : Noise (n := n)) (E : ℝ) (x : M.Point J root) :
    (S.chart D p α E).value x.column ⟨x.height,x.inBand⟩ =
      D.constant+D.orientation*((S.eval p α x).value-4*E) := by
  calc _ = D.constant+D.orientation*((S.intercept p α-4*E)+S.sign*dist S.center x) :=
         OrdinaryData.atom_value D J R.closed_band R.interval_band S.center x _ _ _
       _ = _ := by rw [S.eval_formula]; ring

end AtomSource

/-- A finite globally consistent chart table for every possible spatial atom.
Unused identifiers get a constant chart and can never be selected by pasted. -/
noncomputable def atomChart (D : OrdinaryData M) (p : M.Point J root → ℝ)
    (α : Noise (n := n)) (E : ℝ) (a : ℕ) : OrdinaryData M := by
  classical
  exact if h : Nonempty (R.AtomSource a) then h.some.chart D p α E else OrdinaryData.initial M

lemma source_eval_pasted (p : M.Point J root → ℝ) (α : Noise (n := n))
    (x : M.Point J root) (S : R.AtomSource (R.pasted p α x).name) :
    S.eval p α x = R.pasted p α x := by
  obtain ⟨k,hk,i,t,he⟩ := R.formula_eq_atom p α (R.layerDepth x) (R.layerNode x) x
  have hn : atomName k (R.portalAt (R.ancestor (R.layerNode x) k hk) i) t =
      (R.pasted p α x).name := (congrArg NamedValue.name he).symm
  have hsame := R.nodeAtom_eq_global p α S.node (R.ancestor (R.layerNode x) k hk)
    S.portal i S.kind t (S.name_eq.trans hn.symm)
  exact (congrFun hsame x).trans he.symm

lemma atomChart_value (D : OrdinaryData M) (p : M.Point J root → ℝ)
    (α : Noise (n := n)) (E : ℝ) (x : M.Point J root) :
    ∃ h : x.height ∈ (R.atomChart D p α E (R.pasted p α x).name).band,
      (R.atomChart D p α E (R.pasted p α x).name).value x.column ⟨x.height,h⟩ =
        D.constant+D.orientation*((R.pasted p α x).value-4*E) := by
  have h := R.pasted_has_source p α x
  let Q : OrdinaryData M → Prop := fun T => ∃ hi : x.height ∈ T.band,
    T.value x.column ⟨x.height,hi⟩ =
      D.constant+D.orientation*((R.pasted p α x).value-4*E)
  change Q (R.atomChart D p α E (R.pasted p α x).name)
  have he : R.atomChart D p α E (R.pasted p α x).name = h.some.chart D p α E := dite_eq_left h
  rw [he]
  exact ⟨x.inBand,(AtomSource.chart_value h.some D p α E x).trans
    (by rw [R.source_eval_pasted])⟩

end PlanarL1.Columns.Model.Point.RadialTree


namespace PlanarL1.Columns.Model
open MeasureTheory
namespace OrdinaryState
variable {n : ℕ} {M : Model n} {κ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Finite chart-table extension. Old identifiers are literally retained in the
right summand; installing a fresh chart never refines the old regions. -/
noncomputable def append (S : OrdinaryState M κ Ω μ) (B : SetSystem M Ω μ)
    (k : ℕ) (D : Fin k → OrdinaryData M) (Z : Fin k → Threshold.Variables Ω μ)
    (choose : Fin n → ℝ → Option (Fin k))
    (hin : ∀ i H a, choose i H = some a → H ∈ (D a).band)
    (hcomp : ∀ i H a (_hc : choose i H = some a) r o,
      (D a).origin = some ⟨r,o⟩ → (M.activeGraph (D a).band).Reachable r i)
    (hswitch : ∀ i j H, H ∈ M.heights i j → choose i H = choose j H)
    (hold : ∀ ω i H, choose i H = none →
      ((B.activity ω).active i H ↔ (S.sets.activity ω).active i H))
    (hnew : ∀ ω i H a (hc : choose i H = some a),
      ((B.activity ω).active i H ↔ Threshold.active (Z a) H
        (κ*(D a).value i ⟨H,hin i H a hc⟩) ω)) : OrdinaryState M κ Ω μ where
  sets := B
  count := k+S.count
  chart := Fin.addCases (m := k) (n := S.count+1) D S.chart
  labels := Fin.addCases (m := k) (n := S.count+1) Z S.labels
  name i H := match choose i H with
    | none => Fin.natAdd k (S.name i H)
    | some a => Fin.castAdd (S.count+1) a
  height_in i H := by
    cases hc : choose i H with
    | none => simpa only [hc,Fin.addCases_right] using S.height_in i H
    | some a => simpa only [hc,Fin.addCases_left] using hin i H a hc
  component_in i H := by
    let Uses (D : OrdinaryData M) : Prop := ∀ r o,
      D.origin = some ⟨r,o⟩ → (M.activeGraph D.band).Reachable r i
    change Uses (Fin.addCases (m := k) (n := S.count+1) D S.chart
      (match choose i H with
      | none => Fin.natAdd k (S.name i H)
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
    | none => exact congrArg (Fin.natAdd k) (S.switch_name i j H hh)
    | some a => rfl
  represents ω i H := by
    let Rep (D : OrdinaryData M) (Z : Threshold.Variables Ω μ) : Prop :=
      ∀ hi : H ∈ D.band, (B.activity ω).active i H ↔
        Threshold.active Z H (κ*D.value i ⟨H,hi⟩) ω
    have hr : Rep
        (Fin.addCases (m := k) (n := S.count+1) D S.chart
          (match choose i H with
          | none => Fin.natAdd k (S.name i H)
          | some a => Fin.castAdd (S.count+1) a))
        (Fin.addCases (m := k) (n := S.count+1) Z S.labels
          (match choose i H with
          | none => Fin.natAdd k (S.name i H)
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

end OrdinaryState
end PlanarL1.Columns.Model


end

section

namespace PlanarL1.Columns.Model.OrdinaryData
variable {n : ℕ} {M : Model n}

/-- The actual chart domain, with the connected-component requirement made
explicit. Different copies of a quotient point satisfy the same condition. -/
def Contains (D : OrdinaryData M) (i : Fin n) (H : ℝ) : Prop :=
  H ∈ D.band ∧ ∀ r o, D.origin = some ⟨r,o⟩ → (M.activeGraph D.band).Reachable r i

lemma initial_contains (i : Fin n) (H : ℝ) : (initial M).Contains i H := by
  refine ⟨Set.mem_univ _,?_⟩
  intro r o he
  cases he

lemma atom_contains (D : OrdinaryData M) (J : Set ℝ) (hJ : IsClosed J)
    (hc : J.OrdConnected) {r : Fin n} (o x : M.Point J r) (c η : ℝ) (hη : |η|=1) :
    (D.atom J hJ hc o c η hη).Contains x.column x.height := by
  refine ⟨x.inBand,?_⟩
  intro r' o' he
  have hr : r=r' := congrArg (fun z : Option (Σ r : Fin n, M.Point J r) =>
    z.map Sigma.fst) he |> Option.some.inj
  subst r'
  exact x.reachable

end PlanarL1.Columns.Model.OrdinaryData

namespace PlanarL1.Columns.Model.Point.RadialTree
open PlanarL1.Interpolation
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
variable (R : RadialTree (M := M) (J := J) (root := root))

lemma atomChart_contains (D : OrdinaryData M) (p : M.Point J root → ℝ)
    (α : Noise (n := n)) (E : ℝ) (x : M.Point J root) :
    (R.atomChart D p α E (R.pasted p α x).name).Contains x.column x.height := by
  have h := R.pasted_has_source p α x
  have he : R.atomChart D p α E (R.pasted p α x).name = h.some.chart D p α E := dite_eq_left h
  rw [he]
  exact OrdinaryData.atom_contains D J R.closed_band R.interval_band h.some.center x _ _ _

end PlanarL1.Columns.Model.Point.RadialTree


end

end OAI
