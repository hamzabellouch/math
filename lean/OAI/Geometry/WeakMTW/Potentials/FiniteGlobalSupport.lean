import Mathlib
import OAI.Geometry.WeakMTW.Support.AllScales

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]
  {ι : Type*} [Fintype ι] [Nonempty ι]

 theorem activeProjection_bijective (hMTW : HasWeakMTW (n := n) (M := M))
     (y : ι → M) (h : ι → ℝ) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
     Function.Bijective (activeProjection (n := n) y h s) := by
   apply activeProjection_critical_bijective y h hMTW hs hs1
   · intro r hr hrs p hp
     rcases hr.eq_or_lt with hr | hr
     · subst r
       simpa only [zero_smul] using zero_mem_injectivity p.1
     · exact activeHull_scaled_mem_injectivity hMTW y h hr (hrs.trans hs1) p.1 hp
   · intro p hp
     exact injectivity_subset_minimizing p.1 (activeHull_scaled_mem_injectivity hMTW y h hs hs1 p.1 hp)

 theorem finite_active_minimizes (hMTW : HasWeakMTW (n := n) (M := M))
     (y : ι → M) (h : ι → ℝ) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
     {x : M} {b : TangentSpace (model n) x} (hb : b ∈ activeHull y h x) (z : M) :
     cost x (exp x (s•b))+s*finitePotential y h x ≤
       cost z (exp x (s•b))+s*finitePotential y h z :=
   activeProjection_injective_minimizes y h hs (activeProjection_bijective hMTW y h hs hs1).1 ⟨⟨x,b⟩,hb⟩ z

 theorem finite_active_unique_pole (hMTW : HasWeakMTW (n := n) (M := M))
     (y : ι → M) (h : ι → ℝ) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
     {x : M} {b : TangentSpace (model n) x} (hb : b ∈ activeHull y h x) {z : M}
     (hz : cost z (exp x (s•b))+s*finitePotential y h z =
       cost x (exp x (s•b))+s*finitePotential y h x) : z = x := by
   obtain ⟨w,hw,hn⟩ := exists_minimizing_vector (n := n) z (exp x (s•b))
   have hwm : w ∈ minimizingDomain z := by
     change dist z (exp z w) = ‖w‖
     rw [hw,hn]
   have hmin : ∀ z', cost z (exp z w)+s*finitePotential y h z ≤
       cost z' (exp z w)+s*finitePotential y h z' := by
     rw [hw,hz]
     exact finite_active_minimizes hMTW y h hs hs1 hb
   let q : ActivePoint (n := n) y h := ⟨⟨z,s⁻¹•w⟩,minimizing_pole_capture y h hwm hs hmin⟩
   let p : ActivePoint (n := n) y h := ⟨⟨x,b⟩,hb⟩
   have hqp : q = p := (activeProjection_bijective hMTW y h hs hs1).1 (by
     change exp z (s•(s⁻¹•w)) = exp x (s•b)
     simpa only [smul_smul,mul_inv_cancel₀ hs.ne',one_smul] using hw)
   exact congrArg (fun r : ActivePoint (n := n) y h => r.val.1) hqp

 theorem finite_active_global_support (hMTW : HasWeakMTW (n := n) (M := M))
     (y : ι → M) (h : ι → ℝ) {x : M} {b : TangentSpace (model n) x}
     (hb : b ∈ activeHull y h x) :
     b ∈ minimizingDomain x ∧ ∀ z, finitePotential y h x + cost x (exp x b)-cost z (exp x b) ≤ finitePotential y h z := by
   have ht : Tendsto (fun t : ℝ => t•b) (𝓝[<] (1:ℝ)) (𝓝 b) := by
     have hsml : Continuous (fun t : ℝ => t•b) := continuous_id.smul continuous_const
     simpa only [one_smul] using (hsml.tendsto (1:ℝ)).mono_left nhdsWithin_le_nhds
   have he := (exp_fibre_smooth x).continuous.continuousAt.tendsto.comp ht
   have hpos : ∀ᶠ t : ℝ in 𝓝[<] (1:ℝ), 0 < t :=
     (eventually_gt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
   have hlt : ∀ᶠ t : ℝ in 𝓝[<] (1:ℝ), t < 1 := self_mem_nhdsWithin
   constructor
   · apply (minimizingDomain_closed x).mem_of_tendsto ht
     filter_upwards [hpos,hlt] with t ht ht1
     exact injectivity_subset_minimizing x (activeHull_scaled_mem_injectivity hMTW y h ht ht1 x hb)
   · intro z
     have hcx := cost_continuous.continuousAt.tendsto.comp ((tendsto_const_nhds (x := x)).prodMk_nhds he)
     have hcz := cost_continuous.continuousAt.tendsto.comp ((tendsto_const_nhds (x := z)).prodMk_nhds he)
     have hid : Tendsto (fun t : ℝ => t) (𝓝[<] (1:ℝ)) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
     have hle : cost x (exp x b)+finitePotential y h x ≤ cost z (exp x b)+finitePotential y h z := by
       have h := le_of_tendsto_of_tendsto (hcx.add (hid.mul_const (finitePotential y h x)))
         (hcz.add (hid.mul_const (finitePotential y h z))) (by
           filter_upwards [hpos,hlt] with t ht ht1
           exact finite_active_minimizes hMTW y h ht ht1 hb z)
       simpa only [one_mul] using h
     linarith
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
