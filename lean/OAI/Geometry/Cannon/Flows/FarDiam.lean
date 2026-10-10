import Mathlib
import OAI.Geometry.Cannon.Flows.Node

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
open Set MeasureTheory
open scoped BigOperators
open Set Topology
open Set Metric Filter Topology

namespace CannonMagnification

lemma exists_far_of_diam {X : Type*} [MetricSpace X] (A : Set X)
    (d : ℝ) (hd : 0 < d) (hdiam : d ≤ diam A) (x : X) :
    ∃ y ∈ A, d/3 ≤ dist x y := by
  by_contra hn
  push Not at hn
  have hh : diam A ≤ 2*d/3 := by
    apply diam_le_of_forall_dist_le (by positivity)
    intro y hy z hz
    have ht := dist_triangle y x z
    rw [dist_comm y x] at ht
    linarith [hn y hy,hn z hz]
  linarith

theorem wide_level_images_escape {X : Type*} [MetricSpace X]
    (h : ℕ → X ≃ₜ X) (x : ℕ → X) (z₀ b : X) (r : ℕ → ℝ)
    (C L d d₀ : ℝ) (hC : 0 ≤ C) (hd : 0 < d) (hd₀ : 0 < d₀)
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hexp : ∀ n, Expansion (h n) (x n) (r n) C L)
    (hz₀ : ∀ n, d₀ ≤ dist (x n) z₀)
    (hdiam : ∀ y z : X, dist y z ≤ 1)
    (hb : Tendsto (fun n => h n z₀) atTop (𝓝 b)) :
    ∀ ρ : ℝ, 0 < ρ → ∀ᶠ n in atTop, ∀ A : Set X,
      d ≤ diam A → ∃ y ∈ (h n) '' A, dist y b < ρ := by
  intro ρ hρ
  have ht : Tendsto (fun n => C*r n/((d/3)*d₀)) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_div] using
      ((tendsto_const_nhds.mul hrlim).div_const ((d/3)*d₀))
  have hp : Tendsto (fun n => dist (h n z₀) b) atTop (𝓝 0) := by
    simpa only [dist_self] using hb.dist (tendsto_const_nhds : Tendsto (fun _ : ℕ => b) atTop (𝓝 b))
  have hsum : Tendsto (fun n => C*r n/((d/3)*d₀)+dist (h n z₀) b) atTop (𝓝 0) := by
    simpa only [add_zero] using ht.add hp
  filter_upwards [hsum.eventually_lt_const hρ] with n hn
  intro A hA
  obtain ⟨y,hy,hyfar⟩ := exists_far_of_diam A d hd hA (x n)
  refine ⟨h n y,mem_image_of_mem _ hy,?_⟩
  have hm : dist (h n y) (h n z₀)*((d/3)*d₀) ≤ C*r n := by
    calc
      _ = dist (h n y) (h n z₀)*(d/3)*d₀ := by ring
      _ ≤ dist (h n y) (h n z₀)*max (r n) (dist (x n) y)*
          max (r n) (dist (x n) z₀) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (hyfar.trans (le_max_right _ _)) dist_nonneg
        · exact (hz₀ n).trans (le_max_right _ _)
        · exact hd₀.le
        · positivity
      _ ≤ C*r n*dist y z₀ := (hexp n y z₀).1
      _ ≤ C*r n := by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (hdiam y z₀) (mul_nonneg hC (hr n).le)
  have hynear : dist (h n y) (h n z₀) ≤ C*r n/((d/3)*d₀) := (le_div_iff₀ (mul_pos (div_pos hd (by norm_num)) hd₀)).mpr hm
  exact (dist_triangle (h n y) (h n z₀) b).trans_lt
    ((add_le_add hynear (le_refl (dist (h n z₀) b))).trans_lt hn)

end CannonMagnification

end
end
end
end
end
end
end
end
end
end

end OAI
