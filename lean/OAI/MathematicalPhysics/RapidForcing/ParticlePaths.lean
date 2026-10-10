import OAI.MathematicalPhysics.RapidForcing.CurlDerivatives
import OAI.MathematicalPhysics.RapidForcing.JointSmoothness

namespace OAI

open scoped BigOperators ENNReal Topology
open Set MeasureTheory
namespace RapidForcing

lemma curl_affine_cross (a c x : Space) :
    curl (fun y => (1 / 2 : ℝ) • cross a (y - c)) x = a := by
  let v : Space → Space := fun y => (1 / 2 : ℝ) • cross a (y - c)
  have hv : DifferentiableAt ℝ v x := by
    have h : ContDiff ℝ 1 v := by
      apply (contDiff_piLp 2).mpr
      intro i
      fin_cases i <;> dsimp [v, cross, vec] <;> fun_prop
    exact h.differentiable (by norm_num) x
  have hf (i j : Fin 3) (b : Space) :
      fderiv ℝ (fun y : Space => (1 / 2 : ℝ) *
        (a i * (y j - c j) - a j * (y i - c i))) x b =
      (1 / 2 : ℝ) * (a i * b j - a j * b i) := by
    have h := (((((EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt (x := x)).sub_const (c j)).const_mul (a i)).sub
      ((((EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt (x := x)).sub_const (c i)).const_mul (a j))).const_mul (1 / 2 : ℝ)
    have hf := congrArg (fun L : Space →L[ℝ] ℝ => L b) h.fderiv
    simpa [PiLp.proj_apply, Pi.sub_apply] using hf
  change curl v x = a
  ext k
  fin_cases k
  · change (fderiv ℝ v x (basis 1)) 2 - (fderiv ℝ v x (basis 2)) 1 = a 0
    rw [← fderiv_coordinate hv 2, ← fderiv_coordinate hv 1]
    change fderiv ℝ (fun y : Space => (1 / 2 : ℝ) *
      (a 0 * (y 1 - c 1) - a 1 * (y 0 - c 0))) x (basis 1) -
      fderiv ℝ (fun y : Space => (1 / 2 : ℝ) *
      (a 2 * (y 0 - c 0) - a 0 * (y 2 - c 2))) x (basis 2) = _
    rw [hf, hf]
    simp [basis]
    ring
  · change (fderiv ℝ v x (basis 2)) 0 - (fderiv ℝ v x (basis 0)) 2 = a 1
    rw [← fderiv_coordinate hv 0, ← fderiv_coordinate hv 2]
    change fderiv ℝ (fun y : Space => (1 / 2 : ℝ) *
      (a 1 * (y 2 - c 2) - a 2 * (y 1 - c 1))) x (basis 2) -
      fderiv ℝ (fun y : Space => (1 / 2 : ℝ) *
      (a 0 * (y 1 - c 1) - a 1 * (y 0 - c 0))) x (basis 0) = _
    rw [hf, hf]
    simp [basis]
    ring
  · change (fderiv ℝ v x (basis 0)) 1 - (fderiv ℝ v x (basis 1)) 0 = a 2
    rw [← fderiv_coordinate hv 1, ← fderiv_coordinate hv 0]
    change fderiv ℝ (fun y : Space => (1 / 2 : ℝ) *
      (a 2 * (y 0 - c 0) - a 0 * (y 2 - c 2))) x (basis 0) -
      fderiv ℝ (fun y : Space => (1 / 2 : ℝ) *
      (a 1 * (y 2 - c 2) - a 2 * (y 1 - c 1))) x (basis 1) = _
    rw [hf, hf]
    simp [basis]
    ring

lemma curl_congr_of_eventuallyEq {v w : Space → Space} {x : Space}
    (h : v =ᶠ[𝓝 x] w) : curl v x = curl w x := by
  unfold curl
  rw [h.fderiv_eq]

lemma zeta_scaled_eventually_one (δ : ℝ) (c : Space) :
    ∀ᶠ y in 𝓝 c, ζ (δ⁻¹ • (y - c)) = 1 := by
  have ho : IsOpen {y : Space | ‖δ⁻¹ • (y - c)‖ < (1 / 16 : ℝ)} :=
    isOpen_lt (by fun_prop) continuous_const
  have he : ∀ᶠ y in 𝓝 c, ‖δ⁻¹ • (y - c)‖ < (1 / 16 : ℝ) :=
    ho.mem_nhds (by simp)
  filter_upwards [he] with y hy
  exact zeta_one (fun i => (PiLp.norm_apply_le (δ⁻¹ • (y - c)) i).trans hy.le)

theorem movingCurl_at_center (c : ℝ → Space) (δ σ : ℝ) :
    movingCurl c δ σ (c σ) = deriv c σ := by
  unfold movingCurl
  calc
    _ = curl (fun y => (1 / 2 : ℝ) • cross (deriv c σ) (y - c σ)) (c σ) := by
      apply curl_congr_of_eventuallyEq
      filter_upwards [zeta_scaled_eventually_one δ (c σ)] with y hy
      rw [hy, one_smul]
    _ = _ := curl_affine_cross _ _ _

lemma other_addressCurl_zero (M : Machine) (w : M.Input) (n m m' : ℕ)
    (hne : m' ≠ m) (σ : ℝ) :
    movingCurl (addressPath M (M.scaleData w) n m') ((M.scaleData w).δ n) σ
      (addressPath M (M.scaleData w) n m σ) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hx
  have h := abs_le.mp (addressCurl_tsupport_subset_box M w n m' σ hx 1)
  have h' := abs_le.mp (addressPath_bound M w n m σ 1)
  have hb := (M.scaleData w).b_lt_delta_div_eight n
  have hδ := (M.scaleData w).delta_pos n
  simp only [addressCenter, vec_one_coord] at h h'
  rcases lt_or_gt_of_ne hne with hm | hm
  · have hg : (m' : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith
  · have hg : (m : ℝ) + 1 ≤ (m' : ℝ) := by exact_mod_cast hm
    nlinarith

lemma addressedVelocity_on_step (M : Machine) (w : M.Input) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (1 + (n : ℝ)) (2 + (n : ℝ))) :
    addressedVelocity M w t = stepVelocity M w n t := by
  rw [addressedVelocity_eq_finite M w (n + 2) (by push_cast; linarith [ht.2])]
  rw [loadingVelocity_right_collar M w (by have := Nat.cast_nonneg (α := ℝ) n; linarith [ht.1]),
    zero_add]
  apply Finset.sum_eq_single n
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with hj | hj
    · apply stepVelocity_right_collar
      have : (j : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hj
      linarith [ht.1]
    · apply stepVelocity_left_collar
      have : (n : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hj
      linarith [ht.2]
  · intro hn
    exact (hn (Finset.mem_range.mpr (by omega))).elim

theorem addressedVelocity_at_addressPath (M : Machine) (w : M.Input) (n m : ℕ)
    (hm : m ≤ (M.scaleData w).D n) {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) :
    addressedVelocity M w (1 + (n : ℝ) + σ) (addressPath M (M.scaleData w) n m σ) =
      deriv (addressPath M (M.scaleData w) n m) σ := by
  rw [addressedVelocity_on_step M w n (by constructor <;> linarith [hσ.1, hσ.2])]
  unfold stepVelocity
  rw [show 1 + (n : ℝ) + σ - 1 - (n : ℝ) = σ by ring]
  calc
    _ = movingCurl (addressPath M (M.scaleData w) n m) ((M.scaleData w).δ n) σ
        (addressPath M (M.scaleData w) n m σ) := by
      apply Finset.sum_eq_single m
      · intro m' _ hne
        exact other_addressCurl_zero M w n m m' hne σ
      · intro hnm
        exact (hnm (Finset.mem_range.mpr (by omega))).elim
    _ = _ := movingCurl_at_center _ _ _

theorem addressedVelocity_at_loadingPath (M : Machine) (w : M.Input) {t : ℝ} (ht : t ≤ 1) :
    let c := fun s => θ s • vec (-1) ((M.scaleData w).δ 0 * (M.initialDigit w : ℝ)) 0
    addressedVelocity M w t (c t) = deriv c t := by
  dsimp
  unfold addressedVelocity
  rw [ite_eq_left ht]
  exact movingCurl_at_center _ _ _

end RapidForcing

end OAI
