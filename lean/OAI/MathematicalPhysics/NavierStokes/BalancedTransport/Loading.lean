import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Elementary

namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set

def loadingSwitch (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 1 / 2)

lemma loadingSwitch_contDiff : ContDiff ℝ (⊤ : ℕ∞) loadingSwitch := by
  unfold loadingSwitch
  fun_prop

lemma loadingSwitch_nonneg (t : ℝ) : 0 ≤ loadingSwitch t :=
  Real.smoothTransition.nonneg _

lemma loadingSwitch_le_one (t : ℝ) : loadingSwitch t ≤ 1 :=
  Real.smoothTransition.le_one _

lemma loadingSwitch_zero {t : ℝ} (ht : t ≤ 1 / 4) : loadingSwitch t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma loadingSwitch_one {t : ℝ} (ht : 3 / 4 ≤ t) : loadingSwitch t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

def loadingCenter (z : Space) (t : ℝ) : Space := loadingSwitch t • (z - fixedLabel)

def loadingVelocity (z : Space) (η : ℝ) : Velocity :=
  movingBoxVelocity fixedLabel fixedLabel (loadingCenter z) (fun _ => 1) η

def loadingPath (z : Space) : ℝ → Space :=
  affinePath (loadingCenter z) (fun _ => 1) fixedLabel

lemma loadingCenter_contDiff (z : Space) : ContDiff ℝ (⊤ : ℕ∞) (loadingCenter z) :=
  loadingSwitch_contDiff.smul contDiff_const

lemma loadingVelocity_jointSmooth (z : Space) (η : ℝ) :
    JointSmooth (loadingVelocity z η) :=
  movingBoxVelocity_jointSmooth (loadingCenter_contDiff z) contDiff_const
    (by intros; norm_num) _ _ _

lemma loadingVelocity_divergence (z : Space) (η t : ℝ) (x : Space) :
    div (loadingVelocity z η) t x = 0 :=
  movingBoxVelocity_divergence (loadingCenter_contDiff z) contDiff_const
    (by intros; norm_num) _ _ _ _ _

lemma loadingCenter_deriv_zero {z : Space} {t : ℝ} (ht : t < 1 / 4 ∨ 3 / 4 < t) :
    deriv (loadingCenter z) t = 0 := by
  rcases ht with ht | ht
  · have he : loadingCenter z =ᶠ[𝓝 t] fun _ => (0 : Space) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      simp [loadingCenter, loadingSwitch_zero hs.le]
    rw [he.deriv_eq, deriv_const]
  · have he : loadingCenter z =ᶠ[𝓝 t] fun _ => z - fixedLabel := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      simp [loadingCenter, loadingSwitch_one hs.le]
    rw [he.deriv_eq, deriv_const]

lemma loadingVelocity_zero {z : Space} {η t : ℝ} (ht : t < 1 / 4 ∨ 3 / 4 < t) :
    loadingVelocity z η t = 0 :=
  movingBoxVelocity_zero (loadingCenter_deriv_zero ht) (by intros; simp)

lemma loadingPath_hasDerivAt (z : Space) {η : ℝ} (hη : 0 < η) (t : ℝ) :
    HasDerivAt (loadingPath z) (loadingVelocity z η t (loadingPath z t)) t :=
  affinePath_hasDerivAt hη (loadingCenter_contDiff z) contDiff_const
    (by intros; norm_num) (by intros; simp) (by exact ⟨le_rfl, le_rfl⟩) t

lemma loadingPath_eq (z : Space) (t : ℝ) (i : Fin 3) :
    loadingPath z t i = (1 - loadingSwitch t) * fixedLabel i + loadingSwitch t * z i := by
  dsimp [loadingPath, affinePath, loadingCenter]
  ring

lemma loadingPath_start (z : Space) : loadingPath z 0 = fixedLabel := by
  ext i
  rw [loadingPath_eq, loadingSwitch_zero (by norm_num)]
  ring

lemma loadingPath_end (z : Space) : loadingPath z 1 = z := by
  ext i
  rw [loadingPath_eq, loadingSwitch_one (by norm_num)]
  ring

lemma loadingPath_between (z : Space) (t : ℝ) (i : Fin 3) :
    min (fixedLabel i) (z i) ≤ loadingPath z t i ∧
      loadingPath z t i ≤ max (fixedLabel i) (z i) := by
  rw [loadingPath_eq]
  have h₀ := loadingSwitch_nonneg t
  have h₁ := loadingSwitch_le_one t
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr (min_le_left (fixedLabel i) (z i)))
        (sub_nonneg.mpr h₁),
      mul_nonneg (sub_nonneg.mpr (min_le_right (fixedLabel i) (z i))) h₀]
  · nlinarith [mul_nonneg (sub_nonneg.mpr (le_max_left (fixedLabel i) (z i)))
        (sub_nonneg.mpr h₁),
      mul_nonneg (sub_nonneg.mpr (le_max_right (fixedLabel i) (z i))) h₀]

def loadingSupport (z : Space) (η : ℝ) : Set Space :=
  closedEnlargement (fun i => min (fixedLabel i) (z i))
    (fun i => max (fixedLabel i) (z i)) (2 * η)

lemma loadingSupport_compact (z : Space) (η : ℝ) : IsCompact (loadingSupport z η) :=
  isCompact_Icc

lemma loadingVelocity_supported (z : Space) {η : ℝ} (hη : 0 < η) :
    SpatiallySupported (loadingSupport z η) (loadingVelocity z η) := by
  intro t x hx
  apply image_eq_zero_of_notMem_tsupport
  intro ht
  apply hx
  have hh := tsupport_movingBoxVelocity_subset fixedLabel fixedLabel
      (loadingCenter z) (fun _ => 1) hη t ht
  unfold loadingSupport
  rw [mem_closedEnlargement] at hh ⊢
  intro i
  have hbound := loadingPath_between z t i
  have hpoint : lowerEndpoint fixedLabel (loadingCenter z) (fun _ => 1) t = loadingPath z t := rfl
  rw [hpoint] at hh
  constructor <;> linarith [(hh i).1, (hh i).2]

lemma loadingVelocity_repeats (z : Space) (η : ℝ) : RepeatsAfter 1 (loadingVelocity z η) := by
  intro t ht
  rw [loadingVelocity_zero (Or.inr (by linarith)),
    loadingVelocity_zero (Or.inr (by linarith))]

lemma loadingVelocity_boundedMixed (z : Space) {η : ℝ} (hη : 0 < η) :
    BoundedMixed (loadingVelocity z η) :=
  boundedMixed_of_compact_repeating (loadingSupport_compact z η)
    (loadingVelocity_jointSmooth z η) (loadingVelocity_supported z hη)
    (loadingVelocity_repeats z η)

theorem loadingPath_avoids_observer {z : Space} (hz : 4 ≤ z 0) (t : ℝ) :
    loadingPath z t ∉ observer := by
  intro h
  have hh : loadingPath z t 0 < 2 := (Set.mem_pi.mp h 0 (Set.mem_univ _)).2
  have hb := (loadingPath_between z t 0).1
  have hf : fixedLabel 0 = 4 := rfl
  rw [hf, min_eq_left hz] at hb
  linarith

theorem loading_realization (z : Space) {η : ℝ} (hη : 0 < η) :
    JointSmooth (loadingVelocity z η) ∧
    SpatiallySupported (loadingSupport z η) (loadingVelocity z η) ∧
    BoundedMixed (loadingVelocity z η) ∧
    (∀ x, loadingVelocity z η 0 x = 0) ∧
    loadingPath z 0 = fixedLabel ∧ loadingPath z 1 = z ∧
    (∀ t, HasDerivAt (loadingPath z) (loadingVelocity z η t (loadingPath z t)) t) ∧
    (4 ≤ z 0 → ∀ t, loadingPath z t ∉ observer) ∧
    ∀ ν : ℝ, ZeroDataSolution ν
      (affineForce (inertialCoefficient (loadingVelocity z η))
        (viscousCoefficient (loadingVelocity z η)) ν)
      (loadingVelocity z η) (fun _ _ => 0) := by
  have hzero : ∀ x, loadingVelocity z η 0 x = 0 := by
    intro x
    rw [loadingVelocity_zero (Or.inl (by norm_num))]
    rfl
  exact ⟨loadingVelocity_jointSmooth z η, loadingVelocity_supported z hη,
    loadingVelocity_boundedMixed z hη, hzero, loadingPath_start z, loadingPath_end z,
    loadingPath_hasDerivAt z hη, fun hz t => loadingPath_avoids_observer hz t,
    fun ν => residual_zero_pressure_solution ν _ (loadingVelocity_jointSmooth z η).smooth hzero
      (fun t _ x => loadingVelocity_divergence z η t x)⟩

end BalancedTransport.Geometry
end

end OAI
