import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarPulse
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.SuspensionExpressions
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.ExpressionCompiler

namespace OAI

/-! Scalar expressions for the planar processor after its phase is installed
as the third spatial coordinate. The expression contains only finite rational
data and the existing certified smooth profile syntax. -/

noncomputable section

namespace ShearFlows.PeriodicExpr

def quadratic (L a b c d p : ℚ) : PeriodicExpr :=
  ⟨L, a, d, .mul (.add .coord (.const (-p))) (ProfileExpr.potential a b c d p)⟩

theorem quadratic_valid {L a b c d p : ℚ} (hL : 0 < L) (hab : a < b) (hcd : c < d) :
    (quadratic L a b c d p).Valid := by
  refine ⟨hL, ?_⟩
  have hp := (potential_valid (p := p) hL hab hcd).2
  dsimp [quadratic]
  intro x hx
  apply hp
  change (x + ((-p : ℚ) : ℝ)) * (ProfileExpr.potential a b c d p).val x ≠ 0 at hx
  exact right_ne_zero_of_mul hx

theorem quadratic_body (L a b c d p : ℚ) (x : ℝ) :
    (quadratic L a b c d p).body.val x =
      (x - p) ^ 2 * closedCutoff a b c d x := by
  simp only [quadratic, ProfileExpr.val, ProfileExpr.val_potential, Rat.cast_neg]
  ring

def intervalPulse (a b : ℚ) : PeriodicExpr :=
  ⟨1, a, b, (ProfileExpr.ramp a b).diff⟩

theorem intervalPulse_valid {a b : ℚ} (hab : a < b) : (intervalPulse a b).Valid := by
  refine ⟨by norm_num [intervalPulse], ?_⟩
  dsimp [intervalPulse]
  rw [ProfileExpr.val_diff, ProfileExpr.val_ramp]
  exact (smoothPulse_support (by exact_mod_cast hab)).trans Set.Ioo_subset_Icc_self

theorem val_on_unit {p : PeriodicExpr} (hp : p.Valid) (hperiod : p.period = 1)
    (hl : 0 < p.lower) (hu : p.upper < 1) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    p.val x = p.body.val x := by
  apply periodize_eq_in_chart (A := 0) (B := 1) (by exact_mod_cast hp.1)
  · rw [hperiod]
    norm_num
  · intro y hy
    have h := hp.2 hy
    have h₀ : (0 : ℝ) < p.lower := by exact_mod_cast hl
    have h₁ : (p.upper : ℝ) < 1 := by exact_mod_cast hu
    exact ⟨h₀.trans_le h.1, h.2.trans_lt h₁⟩
  · exact hx

end ShearFlows.PeriodicExpr

namespace ForcedComputation.PlanarHamiltonian

open ShearFlows Set Filter
open scoped Topology

def Pulse.axisCutoff (p : Pulse) (j : Fin 2) : PeriodicExpr :=
  .cutoff 1 (p.rectangle.lower j - 2 * p.collar) (p.rectangle.lower j - p.collar)
    (p.rectangle.upper j + p.collar) (p.rectangle.upper j + 2 * p.collar)

def Pulse.axisLinear (p : Pulse) (j : Fin 2) (c : ℚ) : PeriodicExpr :=
  .potential 1 (p.rectangle.lower j - 2 * p.collar) (p.rectangle.lower j - p.collar)
    (p.rectangle.upper j + p.collar) (p.rectangle.upper j + 2 * p.collar) c

def Pulse.axisQuadratic (p : Pulse) (j : Fin 2) (c : ℚ) : PeriodicExpr :=
  .quadratic 1 (p.rectangle.lower j - 2 * p.collar) (p.rectangle.lower j - p.collar)
    (p.rectangle.upper j + p.collar) (p.rectangle.upper j + 2 * p.collar) c

theorem Pulse.axisCutoff_valid {p : Pulse} (hp : p.Valid) (j : Fin 2) :
    (p.axisCutoff j).Valid :=
  PeriodicExpr.cutoff_valid (by norm_num) (by linarith [hp.1]) (by linarith [hp.1])

theorem Pulse.axisLinear_valid {p : Pulse} (hp : p.Valid) (j : Fin 2) (c : ℚ) :
    (p.axisLinear j c).Valid :=
  PeriodicExpr.potential_valid (by norm_num) (by linarith [hp.1]) (by linarith [hp.1])

theorem Pulse.axisQuadratic_valid {p : Pulse} (hp : p.Valid) (j : Fin 2) (c : ℚ) :
    (p.axisQuadratic j c).Valid :=
  PeriodicExpr.quadratic_valid (by norm_num) (by linarith [hp.1]) (by linarith [hp.1])

def Pulse.spatialExpression (p : Pulse) : FieldExpr :=
  letI := ShearFlows.neZeroTwo
  letI := ShearFlows.neZeroFour
  Primitive.casesOn p.primitive
    (fun v =>
      .add (.mul (.const (v 0)) (.mul (.atom 1 (p.axisCutoff 0)) (.atom 2 (p.axisLinear 1 0))))
        (.mul (.const (-v 1)) (.mul (.atom 1 (p.axisLinear 0 0)) (.atom 2 (p.axisCutoff 1)))))
    (fun c a =>
      .mul (.const (a / 2)) (.mul (.atom 1 (p.axisCutoff 0)) (.atom 2 (p.axisQuadratic 1 (c 1)))))
    (fun c a =>
      .mul (.const (-a / 2)) (.mul (.atom 1 (p.axisQuadratic 0 (c 0))) (.atom 2 (p.axisCutoff 1))))

def Pulse.expression (p : Pulse) : FieldExpr :=
  letI := ShearFlows.neZeroFour
  .mul (.atom 3 (PeriodicExpr.intervalPulse p.start p.finish)) p.spatialExpression

theorem Pulse.spatialExpression_valid {p : Pulse} (hp : p.Valid) : p.spatialExpression.Valid := by
  unfold Pulse.spatialExpression
  cases p.primitive with
  | translation v =>
      exact ⟨⟨trivial, p.axisCutoff_valid hp 0, p.axisLinear_valid hp 1 0⟩,
        trivial, p.axisLinear_valid hp 0 0, p.axisCutoff_valid hp 1⟩
  | horizontal c a => exact ⟨trivial, p.axisCutoff_valid hp 0, p.axisQuadratic_valid hp 1 (c 1)⟩
  | vertical c a => exact ⟨trivial, p.axisQuadratic_valid hp 0 (c 0), p.axisCutoff_valid hp 1⟩

theorem Pulse.expression_valid {p : Pulse} (hp : p.Valid) : p.expression.Valid :=
  ⟨PeriodicExpr.intervalPulse_valid hp.2, p.spatialExpression_valid hp⟩

theorem Pulse.spatialExpression_noTime (p : Pulse) : SpatialExpression.NoTime p.spatialExpression := by
  unfold Pulse.spatialExpression
  cases p.primitive <;> simp [SpatialExpression.NoTime]

theorem Pulse.expression_noTime (p : Pulse) : SpatialExpression.NoTime p.expression :=
  ⟨by change (3 : Fin 4) ≠ 0; decide, p.spatialExpression_noTime⟩

theorem Pulse.spatialExpression_unitPeriods (p : Pulse) :
    SpatialExpression.UnitPeriods p.spatialExpression := by
  unfold Pulse.spatialExpression
  cases p.primitive <;>
    simp [SpatialExpression.UnitPeriods, Pulse.axisCutoff, Pulse.axisLinear, Pulse.axisQuadratic,
      PeriodicExpr.cutoff, PeriodicExpr.potential, PeriodicExpr.quadratic]

theorem Pulse.expression_unitPeriods (p : Pulse) : SpatialExpression.UnitPeriods p.expression :=
  ⟨rfl, p.spatialExpression_unitPeriods⟩

def Pulse.InUnit (p : Pulse) : Prop :=
  0 < p.start ∧ p.finish < 1 ∧ ∀ j,
    0 < p.rectangle.lower j - 2 * p.collar ∧ p.rectangle.upper j + 2 * p.collar < 1

def Pulse.axisMask (p : Pulse) (j : Fin 2) (x : ℝ) : ℝ :=
  closedCutoff (p.rectangle.lower j - 2 * p.collar) (p.rectangle.lower j - p.collar)
    (p.rectangle.upper j + p.collar) (p.rectangle.upper j + 2 * p.collar) x

theorem Pulse.axisCutoff_on_unit {p : Pulse} (hp : p.Valid) (hu : p.InUnit) (j : Fin 2)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : (p.axisCutoff j).val x = p.axisMask j x := by
  rw [PeriodicExpr.val_on_unit (p.axisCutoff_valid hp j) rfl (hu.2.2 j).1 (hu.2.2 j).2 hx]
  change (ProfileExpr.cutoff _ _ _ _).val x = _
  simpa only [Pulse.axisMask, Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat] using
    congrFun (ProfileExpr.val_cutoff
    (p.rectangle.lower j - 2 * p.collar) (p.rectangle.lower j - p.collar)
    (p.rectangle.upper j + p.collar) (p.rectangle.upper j + 2 * p.collar)) x

theorem Pulse.axisLinear_on_unit {p : Pulse} (hp : p.Valid) (hu : p.InUnit) (j : Fin 2) (c : ℚ)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (p.axisLinear j c).val x = (x - c) * p.axisMask j x := by
  rw [PeriodicExpr.val_on_unit (p.axisLinear_valid hp j c) rfl (hu.2.2 j).1 (hu.2.2 j).2 hx]
  change (ProfileExpr.potential _ _ _ _ _).val x = _
  simpa only [Pulse.axisMask, Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat] using
    congrFun (ProfileExpr.val_potential
    (p.rectangle.lower j - 2 * p.collar) (p.rectangle.lower j - p.collar)
    (p.rectangle.upper j + p.collar) (p.rectangle.upper j + 2 * p.collar) c) x

theorem Pulse.axisQuadratic_on_unit {p : Pulse} (hp : p.Valid) (hu : p.InUnit) (j : Fin 2) (c : ℚ)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (p.axisQuadratic j c).val x = (x - c) ^ 2 * p.axisMask j x := by
  rw [PeriodicExpr.val_on_unit (p.axisQuadratic_valid hp j c) rfl (hu.2.2 j).1 (hu.2.2 j).2 hx]
  simpa only [Pulse.axisQuadratic, Pulse.axisMask, Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat] using
    PeriodicExpr.quadratic_body 1
    (p.rectangle.lower j - 2 * p.collar) (p.rectangle.lower j - p.collar)
    (p.rectangle.upper j + p.collar) (p.rectangle.upper j + 2 * p.collar) c x

theorem Pulse.spatialExpression_on_unit {p : Pulse} (hp : p.Valid) (hu : p.InUnit)
    (y : SpaceTime) (hx : y.2 0 ∈ Icc (0 : ℝ) 1) (hy : y.2 1 ∈ Icc (0 : ℝ) 1) :
    p.spatialExpression.val y = p.hamiltonian (horizontal y.2) := by
  have hc₀ := p.axisCutoff_on_unit hp hu 0 hx
  have hc₁ := p.axisCutoff_on_unit hp hu 1 hy
  have hl₀ (c : ℚ) := p.axisLinear_on_unit hp hu 0 c hx
  have hl₁ (c : ℚ) := p.axisLinear_on_unit hp hu 1 c hy
  have hq₀ (c : ℚ) := p.axisQuadratic_on_unit hp hu 0 c hx
  have hq₁ (c : ℚ) := p.axisQuadratic_on_unit hp hu 1 c hy
  have hm : rectangleCutoff p.rectangle p.collar (horizontal y.2) =
      p.axisMask 0 (y.2 0) * p.axisMask 1 (y.2 1) := rfl
  cases h : p.primitive with
  | translation v =>
      simp only [Pulse.spatialExpression, h, FieldExpr.val]
      change (v 0 : ℝ) * ((p.axisCutoff 0).val (y.2 0) * (p.axisLinear 1 0).val (y.2 1)) +
        ((-v 1 : ℚ) : ℝ) * ((p.axisLinear 0 0).val (y.2 0) * (p.axisCutoff 1).val (y.2 1)) = _
      rw [hc₀, hc₁, hl₀, hl₁]
      unfold Pulse.hamiltonian
      rw [hm, h]
      simp only [Primitive.potential, translationPotential,
        horizontal, Matrix.cons_val_zero, Matrix.cons_val_one, Rat.cast_zero, sub_zero,
        Rat.cast_neg]
      ring
  | horizontal c a =>
      simp only [Pulse.spatialExpression, h, FieldExpr.val]
      change ((a / 2 : ℚ) : ℝ) *
        ((p.axisCutoff 0).val (y.2 0) * (p.axisQuadratic 1 (c 1)).val (y.2 1)) = _
      rw [hc₀, hq₁]
      unfold Pulse.hamiltonian
      rw [hm, h]
      simp only [Primitive.potential, horizontalPotential,
        horizontal, Matrix.cons_val_zero, Matrix.cons_val_one, Rat.cast_div, Rat.cast_ofNat]
      ring
  | vertical c a =>
      simp only [Pulse.spatialExpression, h, FieldExpr.val]
      change ((-a / 2 : ℚ) : ℝ) *
        ((p.axisQuadratic 0 (c 0)).val (y.2 0) * (p.axisCutoff 1).val (y.2 1)) = _
      rw [hq₀, hc₁]
      unfold Pulse.hamiltonian
      rw [hm, h]
      simp only [Primitive.potential, verticalPotential,
        horizontal, Matrix.cons_val_zero, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat]
      ring

theorem Pulse.expression_on_unit {p : Pulse} (hp : p.Valid) (hu : p.InUnit)
    (y : SpaceTime) (hx : y.2 0 ∈ Icc (0 : ℝ) 1) (hy : y.2 1 ∈ Icc (0 : ℝ) 1)
    (hz : y.2 2 ∈ Icc (0 : ℝ) 1) :
    p.expression.val y = smoothPulse p.start p.finish (y.2 2) * p.hamiltonian (horizontal y.2) := by
  have ht := PeriodicExpr.val_on_unit (PeriodicExpr.intervalPulse_valid hp.2) rfl hu.1 hu.2.1 hz
  change (PeriodicExpr.intervalPulse p.start p.finish).val (y.2 2) * p.spatialExpression.val y = _
  rw [ht, p.spatialExpression_on_unit hp hu y hx hy]
  rw [PeriodicExpr.intervalPulse, ProfileExpr.val_diff, ProfileExpr.val_ramp]
  rfl

def processorExpression {n : ℕ} (p : Fin n → Pulse) : FieldExpr :=
  FieldExpr.sum (List.ofFn (fun i => (p i).expression))

theorem processorExpression_valid {n : ℕ} {p : Fin n → Pulse} (hp : ∀ i, (p i).Valid) :
    (processorExpression p).Valid := by
  apply FieldExpr.valid_sum
  intro e he
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
  exact (p i).expression_valid (hp i)

theorem sum_noTime {l : List FieldExpr} (hl : ∀ e ∈ l, SpatialExpression.NoTime e) :
    SpatialExpression.NoTime (FieldExpr.sum l) := by
  induction l with
  | nil => trivial
  | cons e l ih => exact ⟨hl e (by simp), ih (fun f hf => hl f (by simp [hf]))⟩

theorem sum_unitPeriods {l : List FieldExpr} (hl : ∀ e ∈ l, SpatialExpression.UnitPeriods e) :
    SpatialExpression.UnitPeriods (FieldExpr.sum l) := by
  induction l with
  | nil => trivial
  | cons e l ih => exact ⟨hl e (by simp), ih (fun f hf => hl f (by simp [hf]))⟩

theorem processorExpression_noTime {n : ℕ} (p : Fin n → Pulse) :
    SpatialExpression.NoTime (processorExpression p) := by
  apply sum_noTime
  intro e he
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
  exact (p i).expression_noTime

theorem processorExpression_unitPeriods {n : ℕ} (p : Fin n → Pulse) :
    SpatialExpression.UnitPeriods (processorExpression p) := by
  apply sum_unitPeriods
  intro e he
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
  exact (p i).expression_unitPeriods

theorem processorExpression_on_unit {n : ℕ} {p : Fin n → Pulse}
    (hp : ∀ i, (p i).Valid) (hu : ∀ i, (p i).InUnit) (y : SpaceTime)
    (hx : y.2 0 ∈ Icc (0 : ℝ) 1) (hy : y.2 1 ∈ Icc (0 : ℝ) 1)
    (hz : y.2 2 ∈ Icc (0 : ℝ) 1) :
    (processorExpression p).val y = processorHamiltonian p (y.2 2) (horizontal y.2) := by
  rw [processorExpression, FieldExpr.val_sum]
  simp only [List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  exact (p i).expression_on_unit (hp i) (hu i) y hx hy hz

theorem processorExpression_planar_germ {n : ℕ} {p : Fin n → Pulse}
    (hp : ∀ i, (p i).Valid) (hu : ∀ i, (p i).InUnit) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) {x : Plane}
    (hx₀ : x 0 ∈ Ioo (0 : ℝ) 1) (hx₁ : x 1 ∈ Ioo (0 : ℝ) 1) :
    (fun z : Plane => (processorExpression p).val (0, atHeight z t)) =ᶠ[𝓝 x]
      processorHamiltonian p t := by
  have h₀ : {z : Plane | z 0 ∈ Ioo (0 : ℝ) 1} ∈ 𝓝 x :=
    (isOpen_Ioo.preimage (continuous_apply 0)).mem_nhds hx₀
  have h₁ : {z : Plane | z 1 ∈ Ioo (0 : ℝ) 1} ∈ 𝓝 x :=
    (isOpen_Ioo.preimage (continuous_apply 1)).mem_nhds hx₁
  filter_upwards [h₀, h₁] with z hz₀ hz₁
  have he := processorExpression_on_unit hp hu (0, atHeight z t)
    ⟨hz₀.1.le, hz₀.2.le⟩ ⟨hz₁.1.le, hz₁.2.le⟩ ht
  simpa only [atHeight_horizontal, show atHeight z t 2 = t from rfl] using he

theorem processorExpression_planar_field {n : ℕ} {p : Fin n → Pulse}
    (hp : ∀ i, (p i).Valid) (hu : ∀ i, (p i).InUnit) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) {x : Plane}
    (hx₀ : x 0 ∈ Ioo (0 : ℝ) 1) (hx₁ : x 1 ∈ Ioo (0 : ℝ) 1) :
    field (fun z : Plane => (processorExpression p).val (0, atHeight z t)) x =
      processorVelocity p t x :=
  field_congr_of_eventuallyEq (processorExpression_planar_germ hp hu ht hx₀ hx₁)

end ForcedComputation.PlanarHamiltonian

end

end OAI
