import Mathlib

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology NNReal
namespace UniformLocalLipschitz
variable {A X Y : Type*} [MetricSpace X] [CompactSpace X] [PseudoMetricSpace Y]

 theorem globalize {f : A → X → Y} {S : A → Set X}
     (hloc : ∀ z : X, ∃ r : ℝ, ∃ C : ℝ≥0, 0 < r ∧
       ∀ α, LipschitzOnWith C (f α) (Metric.ball z r ∩ S α))
     {D : ℝ} (hD : 0 ≤ D) (hbound : ∀ α, ∀ x ∈ S α, ∀ y ∈ S α, dist (f α x) (f α y) ≤ D) :
     ∃ C : ℝ≥0, ∀ α, LipschitzOnWith C (f α) (S α) := by
   classical
   choose r C hr hL using hloc
   obtain ⟨L,hLcover⟩ := (isCompact_univ : IsCompact (univ : Set X)).elim_finite_subcover
     (fun z => Metric.ball z (r z/2)) (fun _ => Metric.isOpen_ball)
     (fun x _ => mem_iUnion.mpr ⟨x,Metric.mem_ball_self (half_pos (hr x))⟩)
   have hnb : (⋂ z ∈ L, Iio (r z/2)) ∈ 𝓝 (0:ℝ) :=
     (Filter.biInter_mem L.finite_toSet).mpr (fun z _ => Iio_mem_nhds (half_pos (hr z)))
   obtain ⟨ε,hε,hεb⟩ := Metric.mem_nhds_iff.mp hnb
   let ρ := ε/2
   have hρ : 0 < ρ := half_pos hε
   have hsm (z : X) (hz : z ∈ L) : ρ < r z/2 := by
     apply mem_iInter₂.mp (hεb _) z hz
     simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hρ] using half_lt_self hε
   let B : ℝ≥0 := (∑ z ∈ L, C z)+⟨D/ρ,div_nonneg hD hρ.le⟩
   refine ⟨B,fun α => LipschitzOnWith.of_dist_le_mul (fun x hx y hy => ?_)⟩
   by_cases hxy : dist x y < ρ
   · obtain ⟨z,hz,hxz⟩ := mem_iUnion₂.mp (hLcover (mem_univ x))
     have hxB : x ∈ Metric.ball z (r z) := Metric.ball_subset_ball (half_le_self (hr z).le) hxz
     have hyB : y ∈ Metric.ball z (r z) := by
       change dist y z < r z
       have htri := dist_triangle y x z
       rw [dist_comm y x] at htri
       change dist x z < r z/2 at hxz
       linarith [hsm z hz]
     have hh := (hL z α).dist_le_mul (x := x) ⟨hxB,hx⟩ (y := y) ⟨hyB,hy⟩
     apply hh.trans
     apply mul_le_mul_of_nonneg_right _ dist_nonneg
     exact_mod_cast (show C z ≤ B from (Finset.single_le_sum (fun _ _ => bot_le) hz).trans (le_add_of_nonneg_right bot_le))
   · have hd : ρ ≤ dist x y := le_of_not_gt hxy
     calc
       dist (f α x) (f α y) ≤ D := hbound α x hx y hy
       _ ≤ (D/ρ)*dist x y := by rw [div_mul_eq_mul_div]; exact (le_div_iff₀ hρ).mpr (mul_le_mul_of_nonneg_left hd hD)
       _ ≤ (B:ℝ)*dist x y := mul_le_mul_of_nonneg_right (by
         change D/ρ ≤ (∑ z ∈ L, C z : ℝ≥0)+D/ρ
         exact le_add_of_nonneg_left (NNReal.coe_nonneg _)) dist_nonneg
end UniformLocalLipschitz
end

end WeakMTWGlobalSupport

end OAI
