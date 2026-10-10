import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.MinimizerCapture
import OAI.Geometry.WeakMTW.Potentials.PotentialActiveLogs
import OAI.Geometry.WeakMTW.Geodesics.CostGeodesicTaylor

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

 theorem ordinarySubdiff_direction {u v : M → ℝ} (hv : Continuous v) (hu : u = cTransform v)
     {x : M} {p₀ : TangentSpace (model n) x} (hp₀ : p₀ ∈ ordinarySubdiff u x)
     (ξ : TangentSpace (model n) x) :
     ∃ a ∈ potentialActive u v x, inner ℝ p₀ ξ ≤ inner ℝ a ξ := by
   let l : ℕ → ℝ := fun j => 1/((j:ℝ)+1)
   have hl : Tendsto l atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
   have hlpos (j : ℕ) : 0 < l j := one_div_pos.mpr (by positivity)
   let p : ℕ → M := fun j => exp x (l j•ξ)
   have hp : Tendsto p atTop (𝓝 x) := by
     have hh := (geodesic_smooth (⟨x,ξ⟩ : TangentBundle (model n) M)).continuous.continuousAt.tendsto.comp hl
     have hexp_eq (t : ℝ) : exp x (t•ξ) = geodesic (⟨x,ξ⟩ : TangentBundle (model n) M) t :=
       exp_mul_eq_geodesic (⟨x,ξ⟩ : TangentBundle (model n) M) t
     simpa only [p,Function.comp_def,geodesic_zero,hexp_eq] using hh
   have hcu : Continuous u := hu ▸ cTransform_continuous hv
   choose a ha using fun j => potentialActive_nonempty (n := n) hv hu (p j)
   obtain ⟨a₀,ha₀,ρ,hρ,hlim⟩ := potentialActive_subseq (n := n) hcu hv hp a ha
   have hz : Tendsto (fun j => exp (p (ρ j)) ((1/2:ℝ)•a (ρ j))) atTop (𝓝 (exp x ((1/2:ℝ)•a₀))) :=
     scaledExp_continuous.continuousAt.tendsto.comp (tendsto_const_nhds.prodMk_nhds hlim)
   have hne : ∀ᶠ j in atTop, l (ρ j) ≠ 0 := Eventually.of_forall (fun j => (hlpos (ρ j)).ne')
   have htA := cost_geodesic_first_limit x (strict_radial_mem_injectivity ha₀.1 (by norm_num : (0:ℝ) ≤ 1/2)
       (by norm_num : (1/2:ℝ) < 1)) ξ hz (hl.comp hρ.tendsto_atTop) hne
   have hupper : Tendsto (fun j => -2*((cost (p (ρ j)) (exp (p (ρ j)) ((1/2:ℝ)•a (ρ j)))-
       cost x (exp (p (ρ j)) ((1/2:ℝ)•a (ρ j))))/l (ρ j))) atTop (𝓝 (inner ℝ a₀ ξ)) := by
     have hh := htA.const_mul (-2)
     have heq : (-2:ℝ)*(-inner ℝ ((1/2:ℝ)•a₀) ξ) = inner ℝ a₀ ξ := by
       simp only [inner_smul_left,conj_trivial]
       ring
     rw [heq] at hh
     exact hh
   have happrox (ε : ℝ) (hε : 0 < ε) : inner ℝ p₀ ξ - ε*‖ξ‖ ≤ inner ℝ a₀ ξ := by
     obtain ⟨δ,hδ,hδprop⟩ := hp₀ ε hε
     have hnorm : Tendsto (fun j => ‖l (ρ j)•ξ‖) atTop (𝓝 0) := by
       simpa only [zero_smul,norm_zero,Function.comp_def] using ((hl.comp hρ.tendsto_atTop).smul_const ξ).norm
     apply ge_of_tendsto hupper
     filter_upwards [hnorm.eventually (eventually_lt_nhds hδ)] with j hj
     have hsub := hδprop (l (ρ j)•ξ) hj
     have hupp := potentialActive_shortened_support hv hu (ha (ρ j))
       (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1) x
     simp only [inner_smul_right,norm_smul,Real.norm_eq_abs,abs_of_pos (hlpos (ρ j))] at hsub
     norm_num at hupp
     rw [← mul_div_assoc,le_div_iff₀ (hlpos (ρ j))]
     change u x + l (ρ j)*inner ℝ p₀ ξ - ε*(l (ρ j)*‖ξ‖) ≤ u (p (ρ j)) at hsub
     nlinarith
   refine ⟨a₀,ha₀,?_⟩
   apply le_of_forall_pos_le_add
   intro δ hδ
   have hden : 0 < ‖ξ‖+1 := by positivity
   have h := happrox (δ/(‖ξ‖+1)) (div_pos hδ hden)
   have he := div_mul_cancel₀ δ hden.ne'
   have hnon : 0 ≤ δ/(‖ξ‖+1) := (div_pos hδ hden).le
   nlinarith

 theorem ordinarySubdiff_subset_activeHull {u v : M → ℝ} (hv : Continuous v) (hu : u = cTransform v)
     (x : M) : ordinarySubdiff (n := n) u x ⊆ convexHull ℝ (potentialActive u v x) := by
   let : FiniteDimensional ℝ (TangentSpace (model n) x) :=
     VectorBundle.finiteDimensional ℝ (Model n) _ x
   let : CompleteSpace (TangentSpace (model n) x) := FiniteDimensional.complete ℝ _
   intro p hp
   apply closed_convex_mem_of_directions (potentialActiveHull_closed (n := n) (hu ▸ cTransform_continuous hv) hv x)
     (convex_convexHull ℝ _) ((potentialActive_nonempty (n := n) hv hu x).mono (subset_convexHull ℝ _))
   intro ξ
   obtain ⟨a,ha,h⟩ := ordinarySubdiff_direction hv hu hp ξ
   exact ⟨a,subset_convexHull ℝ _ ha,h⟩
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
