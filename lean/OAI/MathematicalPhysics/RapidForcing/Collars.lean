import OAI.MathematicalPhysics.RapidForcing.CurlSupport

namespace OAI

open scoped BigOperators ENNReal Topology
open Set MeasureTheory
namespace RapidForcing

lemma addressCurl_tsupport_disjoint (M : Machine) (w : M.Input)
    (n m m' : ℕ) (hmm' : m ≠ m') (σ : ℝ) :
    Disjoint (tsupport (movingCurl (addressPath M (M.scaleData w) n m)
      ((M.scaleData w).δ n) σ))
      (tsupport (movingCurl (addressPath M (M.scaleData w) n m')
        ((M.scaleData w).δ n) σ)) := by
  apply Set.disjoint_left.mpr
  intro x hx hx'
  have h := abs_le.mp (addressCurl_tsupport_subset_box M w n m σ hx 1)
  have h' := abs_le.mp (addressCurl_tsupport_subset_box M w n m' σ hx' 1)
  simp only [addressCenter, vec_one_coord] at h h'
  rcases lt_or_gt_of_ne hmm' with hm | hm
  · have hg : (m : ℝ) + 1 ≤ (m' : ℝ) := by exact_mod_cast hm
    have hδ := (M.scaleData w).delta_pos n
    nlinarith
  · have hg : (m' : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hm
    have hδ := (M.scaleData w).delta_pos n
    nlinarith

@[simp] lemma cross_zero_left (v : Space) : cross 0 v = 0 := by
  simp [cross]

@[simp] lemma curl_zero : curl (fun _ : Space => 0) = fun _ => 0 := by
  funext x
  simp [curl]

lemma movingCurl_eq_zero_of_deriv_eq_zero (c : ℝ → Space) (δ σ : ℝ)
    (h : deriv c σ = 0) : movingCurl c δ σ = fun _ => 0 := by
  funext x
  simp [movingCurl, h]

lemma movingCurl_left_collar (a v : Space) (δ : ℝ) {σ : ℝ} (hσ : σ < 1 / 4) :
    movingCurl (fun s => a + θ s • v) δ σ = fun _ => 0 := by
  apply movingCurl_eq_zero_of_deriv_eq_zero
  have he : (fun s => a + θ s • v) =ᶠ[𝓝 σ] (fun _ => a) := by
    filter_upwards [Iio_mem_nhds hσ] with s hs
    rw [theta_zero (le_of_lt hs), zero_smul, add_zero]
  rw [he.deriv_eq, deriv_const]

lemma movingCurl_right_collar (a v : Space) (δ : ℝ) {σ : ℝ} (hσ : 3 / 4 < σ) :
    movingCurl (fun s => a + θ s • v) δ σ = fun _ => 0 := by
  apply movingCurl_eq_zero_of_deriv_eq_zero
  have he : (fun s => a + θ s • v) =ᶠ[𝓝 σ] (fun _ => a + v) := by
    filter_upwards [Ioi_mem_nhds hσ] with s hs
    rw [theta_one (le_of_lt hs), one_smul]
  rw [he.deriv_eq, deriv_const]

theorem addressedVelocity_initial_collar (M : Machine) (w : M.Input)
    {t : ℝ} (ht : t < 1 / 4) : addressedVelocity M w t = fun _ => 0 := by
  funext x
  unfold addressedVelocity
  rw [ite_eq_left (by linarith : t ≤ 1)]
  have h := movingCurl_left_collar 0
    (vec (-1) ((M.scaleData w).δ 0 * (M.initialDigit w : ℝ)) 0) 1 ht
  simp only [zero_add] at h
  exact congrFun h x

theorem addressedVelocity_initial (M : Machine) (w : M.Input) (x : Space) :
    addressedVelocity M w 0 x = 0 := by
  exact congrFun (addressedVelocity_initial_collar M w (by norm_num)) x

theorem addressed_fields_mixed_support (ν : ℝ) (M : Machine) (w : M.Input)
    (l : ℕ) (α : MultiIndex) :
    IsCompact K ∧ Supported (mixedD l α (addressedVelocity M w)) ∧
      Supported (mixedD l α (addressedForce ν M w)) :=
  ⟨K_compact, (addressedVelocity_supported M w).mixedD l α,
    (addressedForce_supported ν M w).mixedD l α⟩

end RapidForcing

end OAI
