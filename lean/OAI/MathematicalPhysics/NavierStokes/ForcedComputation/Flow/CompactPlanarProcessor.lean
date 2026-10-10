import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarPulseExpressions

namespace OAI

/-! The compact planar interpretation of the finite scalar program. Its
time-periodic Hamiltonian has one common compact support inside the open
unit square, and generates a smooth divergence-free, zero-mean field. -/

noncomputable section
namespace ForcedComputation.PlanarHamiltonian
open ShearFlows Set MeasureTheory Filter
open scoped ContDiff BigOperators Topology

def periodicHamiltonian {n : ℕ} (p : Fin n → Pulse) (t : ℝ) (x : Plane) : ℝ :=
  ∑ i : Fin n, (PeriodicExpr.intervalPulse (p i).start (p i).finish).val t *
    (p i).hamiltonian x

def periodicVelocity {n : ℕ} (p : Fin n → Pulse) (t : ℝ) : Plane → Plane :=
  field (periodicHamiltonian p t)

def commonSupport {n : ℕ} (p : Fin n → Pulse) : Set Plane :=
  ⋃ i : Fin n, (rectangleCollar (p i).rectangle (p i).collar).carrier

theorem commonSupport_compact {n : ℕ} (p : Fin n → Pulse) :
    IsCompact (commonSupport p) :=
  isCompact_iUnion (fun i => rectangleCollar_compact (p i).rectangle (p i).collar)

theorem commonSupport_in_unit {n : ℕ} {p : Fin n → Pulse}
    (hu : ∀ i, (p i).InUnit) :
    commonSupport p ⊆ {x | ∀ j : Fin 2, 0 < x j ∧ x j < 1} := by
  intro x hx j
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  have h := hi j
  have hb := (hu i).2.2 j
  dsimp [rectangleCollar] at h
  push_cast at h
  have hl : (0 : ℝ) < ((p i).rectangle.lower j : ℝ) - 2 * (p i).collar := by
    exact_mod_cast hb.1
  have hr : ((p i).rectangle.upper j : ℝ) + 2 * (p i).collar < (1 : ℝ) := by
    exact_mod_cast hb.2
  exact ⟨hl.trans_le h.1, h.2.trans_lt hr⟩

theorem periodicHamiltonian_smooth {n : ℕ} {p : Fin n → Pulse}
    (hp : ∀ i, (p i).Valid) :
    ContDiff ℝ ∞ (fun y : ℝ × Plane => periodicHamiltonian p y.1 y.2) := by
  apply ContDiff.sum
  intro i _
  exact ((PeriodicExpr.smooth (PeriodicExpr.intervalPulse_valid (hp i).2)).comp
    contDiff_fst).mul ((p i).hamiltonian_smooth.comp contDiff_snd)

theorem periodicHamiltonian_slice_smooth {n : ℕ} (p : Fin n → Pulse) (t : ℝ) :
    ContDiff ℝ ∞ (periodicHamiltonian p t) := by
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul (p i).hamiltonian_smooth

theorem periodicHamiltonian_periodic {n : ℕ} (p : Fin n → Pulse) (x : Plane) :
    Function.Periodic (fun t => periodicHamiltonian p t x) 1 := by
  intro t
  apply Finset.sum_congr rfl
  intro i _
  have h := periodize_periodic (1 : ℝ)
    (PeriodicExpr.intervalPulse (p i).start (p i).finish).body.val t
  change _ * _ = _ * _
  have he : (PeriodicExpr.intervalPulse (p i).start (p i).finish).val (t + 1) =
      (PeriodicExpr.intervalPulse (p i).start (p i).finish).val t := by
    simpa only [PeriodicExpr.val, PeriodicExpr.intervalPulse, Rat.cast_one] using h
  rw [he]

theorem periodicHamiltonian_support {n : ℕ} {p : Fin n → Pulse}
    (hp : ∀ i, (p i).Valid) (t : ℝ) :
    tsupport (periodicHamiltonian p t) ⊆ commonSupport p := by
  apply closure_minimal _ (commonSupport_compact p).isClosed
  intro x hx
  by_contra hn
  apply hx
  apply Finset.sum_eq_zero
  intro i _
  have hn' : x ∉ tsupport (p i).hamiltonian := by
    intro hh
    apply hn
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    have hs : tsupport (p i).hamiltonian ⊆
        (rectangleCollar (p i).rectangle (p i).collar).carrier :=
      tsupport_mul_subset_left.trans (closure_minimal
        (rectangleCutoff_support (hp i).1)
        (rectangleCollar_compact (p i).rectangle (p i).collar).isClosed)
    exact hs hh
  rw [image_eq_zero_of_notMem_tsupport hn', mul_zero]

theorem periodicVelocity_eq_sum {n : ℕ} (p : Fin n → Pulse) (t : ℝ) (x : Plane) :
    periodicVelocity p t x = ∑ i : Fin n,
      (PeriodicExpr.intervalPulse (p i).start (p i).finish).val t • (p i).spatial x := by
  unfold periodicVelocity periodicHamiltonian
  rw [field_sum _ _ (fun i _ => contDiff_const.mul (p i).hamiltonian_smooth)]
  apply Finset.sum_congr rfl
  intro i _
  exact field_const_mul (p i).hamiltonian_smooth _ _

theorem periodicVelocity_smooth {n : ℕ} {p : Fin n → Pulse}
    (hp : ∀ i, (p i).Valid) :
    ContDiff ℝ ∞ (fun y : ℝ × Plane => periodicVelocity p y.1 y.2) := by
  have he : (fun y : ℝ × Plane => periodicVelocity p y.1 y.2) =
      fun y => ∑ i : Fin n, (PeriodicExpr.intervalPulse (p i).start (p i).finish).val y.1 •
        (p i).spatial y.2 := by
    funext y
    exact periodicVelocity_eq_sum p y.1 y.2
  rw [he]
  apply ContDiff.sum
  intro i _
  exact ((PeriodicExpr.smooth (PeriodicExpr.intervalPulse_valid (hp i).2)).comp
    contDiff_fst).smul ((p i).spatial_smooth.comp contDiff_snd)

theorem periodicVelocity_periodic {n : ℕ} (p : Fin n → Pulse) (x : Plane) :
    Function.Periodic (fun t => periodicVelocity p t x) 1 := by
  intro t
  have he : periodicHamiltonian p (t + 1) = periodicHamiltonian p t :=
    funext fun y => periodicHamiltonian_periodic p y t
  change field (periodicHamiltonian p (t + 1)) x = field (periodicHamiltonian p t) x
  rw [he]

theorem periodicVelocity_properties {n : ℕ} {p : Fin n → Pulse}
    (hp : ∀ i, (p i).Valid) (t : ℝ) :
    tsupport (periodicVelocity p t) ⊆ commonSupport p ∧
      (∀ x, divergence (periodicVelocity p t) x = 0) ∧
      (∫ x, periodicVelocity p t x) = 0 := by
  have hs := periodicHamiltonian_slice_smooth p t
  have hc : HasCompactSupport (periodicHamiltonian p t) :=
    (commonSupport_compact p).of_isClosed_subset (isClosed_tsupport _)
      (periodicHamiltonian_support hp t)
  exact ⟨(field_tsupport _).trans (periodicHamiltonian_support hp t),
    field_divergence hs, field_integral_eq_zero hs hc⟩

theorem periodicPulse_on_unit {p : Pulse} (hp : p.Valid) (hu : p.InUnit)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (PeriodicExpr.intervalPulse p.start p.finish).val t =
      smoothPulse p.start p.finish t := by
  rw [PeriodicExpr.val_on_unit (PeriodicExpr.intervalPulse_valid hp.2) rfl hu.1 hu.2.1 ht]
  change (ProfileExpr.ramp p.start p.finish).diff.val t = _
  rw [ProfileExpr.val_diff, ProfileExpr.val_ramp]
  rfl

theorem periodicHamiltonian_on_unit {n : ℕ} {p : Fin n → Pulse}
    (hp : ∀ i, (p i).Valid) (hu : ∀ i, (p i).InUnit)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x : Plane) :
    periodicHamiltonian p t x = processorHamiltonian p t x := by
  apply Finset.sum_congr rfl
  intro i _
  rw [periodicPulse_on_unit (hp i) (hu i) ht]

theorem periodicVelocity_on_unit {n : ℕ} {p : Fin n → Pulse}
    (hp : ∀ i, (p i).Valid) (hu : ∀ i, (p i).InUnit)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x : Plane) :
    periodicVelocity p t x = processorVelocity p t x := by
  have he : periodicHamiltonian p t = processorHamiltonian p t :=
    funext (periodicHamiltonian_on_unit hp hu ht)
  unfold periodicVelocity processorVelocity
  rw [he]

theorem periodicPulse_zero_near_zero {p : Pulse} (hp : p.Valid) (hu : p.InUnit) :
    (PeriodicExpr.intervalPulse p.start p.finish).val =ᶠ[𝓝 0] (fun _ => 0) := by
  let δ : ℝ := min (1 / 4) (min (p.start : ℝ) (1 - (p.finish : ℝ)) / 2)
  have ha : (0 : ℝ) < p.start := by exact_mod_cast hu.1
  have hb : (p.finish : ℝ) < 1 := by exact_mod_cast hu.2.1
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ₁ : δ ≤ 1 / 4 := min_le_left _ _
  have hδ₂ : 2 * δ ≤ p.start := by
    have hm := min_le_right (1 / 4 : ℝ) (min (p.start : ℝ) (1 - (p.finish : ℝ)) / 2)
    have hn := min_le_left (p.start : ℝ) (1 - (p.finish : ℝ))
    change δ ≤ _ at hm
    linarith
  have hδ₃ : 2 * δ ≤ 1 - (p.finish : ℝ) := by
    have hm := min_le_right (1 / 4 : ℝ) (min (p.start : ℝ) (1 - (p.finish : ℝ)) / 2)
    have hn := min_le_right (p.start : ℝ) (1 - (p.finish : ℝ))
    change δ ≤ _ at hm
    linarith
  have hn : Ioo (-δ) δ ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) hδ
  filter_upwards [hn] with t ht
  have hs : Function.support (PeriodicExpr.intervalPulse p.start p.finish).body.val ⊆
      Ioo (-δ) (1 - δ) := by
    intro x hx
    have h := (PeriodicExpr.intervalPulse_valid hp.2).2 hx
    change (p.start : ℝ) ≤ x ∧ x ≤ (p.finish : ℝ) at h
    constructor <;> linarith [h.1, h.2]
  have he := periodize_eq_in_chart (L := (1 : ℝ)) (A := -δ) (B := 1 - δ)
    (by norm_num) (by linarith) hs (x := t) ⟨ht.1.le, by linarith [ht.2]⟩
  have he' : (PeriodicExpr.intervalPulse p.start p.finish).val t =
      (PeriodicExpr.intervalPulse p.start p.finish).body.val t := by
    simpa only [PeriodicExpr.val, PeriodicExpr.intervalPulse, Rat.cast_one] using he
  rw [he']
  change (ProfileExpr.ramp p.start p.finish).diff.val t = 0
  rw [ProfileExpr.val_diff, ProfileExpr.val_ramp]
  exact smoothPulse_before (by exact_mod_cast hp.2) (by linarith [ht.2])

theorem periodicVelocity_zero_near_zero {n : ℕ} {p : Fin n → Pulse}
    (hp : ∀ i, (p i).Valid) (hu : ∀ i, (p i).InUnit) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x, periodicVelocity p t x = 0 := by
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i : Fin n,
      (PeriodicExpr.intervalPulse (p i).start (p i).finish).val t = 0 :=
    eventually_all.mpr (fun i => periodicPulse_zero_near_zero (hp i) (hu i))
  filter_upwards [he] with t ht
  intro x
  rw [periodicVelocity_eq_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [ht i, zero_smul]

end ForcedComputation.PlanarHamiltonian

end

end OAI
