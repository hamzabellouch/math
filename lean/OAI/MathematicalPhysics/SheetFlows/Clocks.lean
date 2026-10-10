import Mathlib
import OAI.MathematicalPhysics.SheetFlows.DirectForce
import OAI.MathematicalPhysics.SheetFlows.Profiles

namespace OAI

/-! SheetFlows clocks. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal
open Filter
open scoped Topology

def pulseClock (a b t : ℝ) : ℝ := Real.smoothTransition ((t - a) / (b - a))

def localPulse (a b : ℝ) : ℝ → ℝ := deriv (pulseClock a b)

def periodicPulse (a b : ℝ) : ℝ → ℝ := periodize 1 (localPulse a b)

theorem pulseClock_contDiff (a b : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (pulseClock a b) := by
  unfold pulseClock
  fun_prop

theorem pulseClock_zero {a b t : ℝ} (hab : a < b) (ht : t ≤ a) :
    pulseClock a b t = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr ht) (sub_pos.mpr hab).le)

theorem pulseClock_one {a b t : ℝ} (hab : a < b) (ht : b ≤ t) :
    pulseClock a b t = 1 :=
  Real.smoothTransition.one_of_one_le ((le_div_iff₀ (sub_pos.mpr hab)).mpr
    (by linarith))

theorem pulseClock_monotone {a b : ℝ} (hab : a < b) :
    Monotone (pulseClock a b) := by
  intro s t hst
  apply Real.smoothTransition.monotone
  exact div_le_div_of_nonneg_right (sub_le_sub_right hst a) (sub_pos.mpr hab).le

theorem localPulse_contDiff (a b : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (localPulse a b) :=
  (contDiff_infty_iff_deriv.mp (pulseClock_contDiff a b)).2

theorem localPulse_nonneg {a b : ℝ} (hab : a < b) (t : ℝ) :
    0 ≤ localPulse a b t := (pulseClock_monotone hab).deriv_nonneg

theorem localPulse_zero_left {a b t : ℝ} (hab : a < b) (ht : t ≤ a) :
    localPulse a b t = 0 := by
  have hd := ((pulseClock_contDiff a b).differentiable (by simp) t).hasDerivAt
  have hz : HasDerivWithinAt (pulseClock a b) 0 (Set.Iic t) t := by
    apply (hasDerivWithinAt_const t (Set.Iic t) (0 : ℝ)).congr
    · intro s hs
      exact pulseClock_zero hab (hs.trans ht)
    · exact pulseClock_zero hab ht
  exact (hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic t)).symm.trans
    (hz.derivWithin (uniqueDiffWithinAt_Iic t))

theorem localPulse_zero_right {a b t : ℝ} (hab : a < b) (ht : b ≤ t) :
    localPulse a b t = 0 := by
  have hd := ((pulseClock_contDiff a b).differentiable (by simp) t).hasDerivAt
  have hz : HasDerivWithinAt (pulseClock a b) 0 (Set.Ici t) t := by
    apply (hasDerivWithinAt_const t (Set.Ici t) (1 : ℝ)).congr
    · intro s hs
      exact pulseClock_one hab (ht.trans hs)
    · exact pulseClock_one hab ht
  exact (hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici t)).symm.trans
    (hz.derivWithin (uniqueDiffWithinAt_Ici t))

theorem periodicPulse_periodic (a b : ℝ) :
    Function.Periodic (periodicPulse a b) 1 := periodize_periodic _ _

theorem periodicPulse_contDiff {a b : ℝ} (hab : a < b) :
    ContDiff ℝ (⊤ : ℕ∞) (periodicPulse a b) := by
  apply periodize_contDiff (a := a) (b := b) (by norm_num)
  · intro t ht
    rcases ht with ht | ht
    · exact localPulse_zero_left hab ht.le
    · exact localPulse_zero_right hab ht.le
  · exact localPulse_contDiff a b

theorem periodicPulse_nonneg {a b : ℝ} (hab : a < b) (t : ℝ) :
    0 ≤ periodicPulse a b t :=
  tsum_nonneg (fun k => localPulse_nonneg hab (t - 1 * k))

theorem periodicPulse_on_chart {a b t : ℝ} (hab : a < b)
    (ha : 0 ≤ a) (hb : b ≤ 1) (ht : t ∈ Set.Icc 0 1) :
    periodicPulse a b t = localPulse a b t := by
  apply periodize_on_chart (by norm_num) _ _ ht
  intro s hs
  rcases hs with hs | hs
  · exact localPulse_zero_left hab (hs.trans ha)
  · exact localPulse_zero_right hab (hb.trans hs)

theorem periodicPulse_on_fraction {a b : ℝ} (hab : a < b)
    (ha : 0 ≤ a) (hb : b ≤ 1) (t : ℝ) :
    periodicPulse a b t = localPulse a b (Int.fract t) := by
  have hp := ((periodicPulse_periodic a b).int_mul ⌊t⌋).sub_eq t
  simp only [mul_one] at hp
  rw [← hp]
  change periodicPulse a b (Int.fract t) = _
  exact periodicPulse_on_chart hab ha hb ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩

theorem periodicPulse_integral_one {a b : ℝ} (hab : a < b)
    (ha : 0 ≤ a) (hb : b ≤ 1) :
    (∫ t in (0 : ℝ)..1, periodicPulse a b t) = 1 := by
  have he : (∫ t in (0 : ℝ)..1, periodicPulse a b t) =
      ∫ t in (0 : ℝ)..1, localPulse a b t := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact periodicPulse_on_chart hab ha hb (by simpa using ht)
  rw [he]
  change (∫ t in (0 : ℝ)..1, deriv (pulseClock a b) t) = 1
  rw [intervalIntegral.integral_deriv_eq_sub
    (fun _ _ => (pulseClock_contDiff a b).differentiable (by simp) _)
    ((localPulse_contDiff a b).continuous.intervalIntegrable _ _),
    pulseClock_one hab hb, pulseClock_zero hab ha, sub_zero]

def slotLeft (m : ℕ) (i : Fin m) : ℝ := 1/4 + (i : ℝ) / (2 * m)

def slotRight (m : ℕ) (i : Fin m) : ℝ := slotLeft m i + 1 / (4 * m)

def scheduledPulse (m : ℕ) (i : Fin m) : ℝ → ℝ :=
  periodicPulse (slotLeft m i) (slotRight m i)

theorem slot_bounds {m : ℕ} (i : Fin m) :
    (1/4 : ℝ) ≤ slotLeft m i ∧ slotLeft m i < slotRight m i ∧
      slotRight m i ≤ 3/4 := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  have hi₀ : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
  have hi₁ : (i : ℝ) + 1 ≤ m := by exact_mod_cast i.isLt
  dsimp [slotLeft, slotRight]
  constructor
  · exact le_add_of_nonneg_right (div_nonneg hi₀ (by positivity))
  constructor
  · exact lt_add_of_pos_right _ (by positivity)
  · field_simp
    nlinarith

theorem slot_ordered {m : ℕ} {i j : Fin m} (hij : i < j) :
    slotRight m i < slotLeft m j := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  have hi : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
  dsimp [slotLeft, slotRight]
  field_simp
  nlinarith

theorem scheduledPulse_contDiff {m : ℕ} (i : Fin m) :
    ContDiff ℝ (⊤ : ℕ∞) (scheduledPulse m i) :=
  periodicPulse_contDiff (slot_bounds i).2.1

theorem scheduledPulse_periodic {m : ℕ} (i : Fin m) :
    Function.Periodic (scheduledPulse m i) 1 := periodicPulse_periodic _ _

theorem scheduledPulse_nonneg {m : ℕ} (i : Fin m) (t : ℝ) :
    0 ≤ scheduledPulse m i t := periodicPulse_nonneg (slot_bounds i).2.1 t

theorem scheduledPulse_integral_one {m : ℕ} (i : Fin m) :
    (∫ t in (0 : ℝ)..1, scheduledPulse m i t) = 1 := by
  rcases slot_bounds i with ⟨ha, hab, hb⟩
  apply periodicPulse_integral_one hab <;> linarith

theorem scheduledPulse_active {m : ℕ} (i : Fin m) {t : ℝ}
    (ht : scheduledPulse m i t ≠ 0) :
    slotLeft m i < Int.fract t ∧ Int.fract t < slotRight m i := by
  rcases slot_bounds i with ⟨ha, hab, hb⟩
  change periodicPulse _ _ t ≠ 0 at ht
  rw [periodicPulse_on_fraction hab (by linarith) (by linarith)] at ht
  constructor
  · exact lt_of_not_ge (fun h => ht (localPulse_zero_left hab h))
  · exact lt_of_not_ge (fun h => ht (localPulse_zero_right hab h))

theorem scheduledPulse_disjoint {m : ℕ} {i j : Fin m} (hij : i ≠ j) (t : ℝ) :
    scheduledPulse m i t = 0 ∨ scheduledPulse m j t = 0 := by
  by_contra h
  push Not at h
  rcases scheduledPulse_active i h.1 with ⟨hi₀, hi₁⟩
  rcases scheduledPulse_active j h.2 with ⟨hj₀, hj₁⟩
  rcases lt_or_gt_of_ne hij with hij | hij
  · linarith [slot_ordered hij]
  · linarith [slot_ordered hij]

theorem scheduledPulse_integer_collar {m : ℕ} (i : Fin m)
    (n : ℤ) {t : ℝ} (ht : |t - (n : ℝ)| < 1/4) :
    scheduledPulse m i t = 0 := by
  rcases slot_bounds i with ⟨ha, hab, hb⟩
  change (∑' k : ℤ, localPulse _ _ (t - 1 * k)) = 0
  suffices h : ∀ k : ℤ, localPulse (slotLeft m i) (slotRight m i) (t - 1 * k) = 0 by
    simp only [h, tsum_zero]
  intro k
  rcases abs_lt.mp ht with ⟨ht₀, ht₁⟩
  by_cases hk : n ≤ k
  · have hk' : (n : ℝ) ≤ k := by exact_mod_cast hk
    apply localPulse_zero_left hab
    simp only [one_mul]
    linarith
  · have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast (show k + 1 ≤ n by omega)
    apply localPulse_zero_right hab
    simp only [one_mul]
    linarith

def tensorScalar (g : Fin 3 → ℝ → ℝ) (x : Space) : ℝ := ∏ j, g j (x j)

def tensorVelocity (i : Fin 3) (g : Fin 3 → ℝ → ℝ) : Field :=
  fun _ x => tensorScalar g x • basis i

theorem tensorScalar_contDiff (g : Fin 3 → ℝ → ℝ)
    (hg : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j)) :
    ContDiff ℝ (⊤ : ℕ∞) (tensorScalar g) :=
  contDiff_prod (fun j _ => (hg j).comp (contDiff_apply ℝ ℝ j))

theorem tensorVelocity_smooth (i : Fin 3) (g : Fin 3 → ℝ → ℝ)
    (hg : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j)) : Smooth (tensorVelocity i g) :=
  ((tensorScalar_contDiff g hg).comp contDiff_snd).smul contDiff_const

theorem tensorVelocity_spatially_periodic (i : Fin 3) (g : Fin 3 → ℝ → ℝ)
    (hg : ∀ j, Function.Periodic (g j) 10) : SpatiallyPeriodic (tensorVelocity i g) := by
  intro t x k
  dsimp [tensorVelocity, tensorScalar]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simpa only [Pi.add_apply, deck, mul_comm (10 : ℝ)] using (hg j).int_mul (k j) (x j)

theorem tensorScalar_integral (g : Fin 3 → ℝ → ℝ) :
    (∫ x in fundamentalCell, tensorScalar g x) =
      ∏ j, ∫ s in Set.Ico (0 : ℝ) 10, g j s := by
  change (∫ x, (∏ j, g j (x j)) ∂((Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))).restrict
    (Set.pi Set.univ fun _ => Set.Ico (0 : ℝ) 10))) = _
  rw [Measure.restrict_pi_pi]
  exact integral_fintype_prod_eq_prod _

theorem tensorVelocity_mean_zero (i : Fin 3) (g : Fin 3 → ℝ → ℝ)
    (j : Fin 3) (hg : (∫ s in Set.Ico (0 : ℝ) 10, g j s) = 0) :
    MeanZero (tensorVelocity i g) := by
  intro t
  dsimp [tensorVelocity]
  rw [integral_smul_const, tensorScalar_integral]
  have h : (∏ k, ∫ s in Set.Ico (0 : ℝ) 10, g k s) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ j) hg
  rw [h, zero_smul]

theorem tensorScalar_eraseAxis (i : Fin 3) (g : Fin 3 → ℝ → ℝ)
    (hg : ∀ s, g i s = 1) (x : Space) :
    tensorScalar g (eraseAxis i x) = tensorScalar g x := by
  apply Finset.prod_congr rfl
  intro j _
  by_cases hji : j = i
  · subst j
    rw [hg, hg]
  · simp [eraseAxis_apply, basis, Pi.single_eq_of_ne hji]

theorem tensorVelocity_eq_axial (i : Fin 3) (g : Fin 3 → ℝ → ℝ)
    (hg : ∀ s, g i s = 1) :
    tensorVelocity i g = axialField i (fun _ => tensorScalar g) := by
  funext t x
  change tensorScalar g x • basis i = tensorScalar g (eraseAxis i x) • basis i
  rw [tensorScalar_eraseAxis i g hg]

theorem tensorVelocity_divergence_free (i : Fin 3) (g : Fin 3 → ℝ → ℝ)
    (hsm : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j)) (hg : ∀ s, g i s = 1) :
    DivergenceFree (tensorVelocity i g) := by
  rw [tensorVelocity_eq_axial i g hg]
  exact axialField_divergence_free i _ (fun _ =>
    (tensorScalar_contDiff g hsm).differentiable (by simp))

theorem tensorVelocity_advection_zero (i : Fin 3) (g : Fin 3 → ℝ → ℝ)
    (hsm : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j)) (hg : ∀ s, g i s = 1) :
    ∀ t x, advection (tensorVelocity i g) t x = 0 := by
  rw [tensorVelocity_eq_axial i g hg]
  intro t x
  exact advection_axialField i _ t x
    ((tensorScalar_contDiff g hsm).differentiable (by simp) _)

end Solenoidal
end
end

end OAI
