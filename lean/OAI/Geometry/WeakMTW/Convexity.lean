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

 theorem injectivityDomain_convex (hMTW : HasWeakMTW (n := n) (M := M)) (x : M) :
     Convex ℝ (injectivityDomain (n := n) x) := by
   intro v₀ hv₀ v₁ hv₁ a b ha hb hab
   obtain ⟨a₀,ha₀,hv₀⟩ := hv₀
   obtain ⟨a₁,ha₁,hv₁⟩ := hv₁
   let β : ℝ := (1+min a₀ a₁)/2
   have hmin : 1 < min a₀ a₁ := lt_min ha₀ ha₁
   have hβ : 1 < β := by dsimp [β]; linarith
   have hβmin : β < min a₀ a₁ := by dsimp [β]; linarith
   have hβ₀ : β < a₀ := hβmin.trans_le (min_le_left _ _)
   have hβ₁ : β < a₁ := hβmin.trans_le (min_le_right _ _)
   have hβpos : 0 < β := zero_lt_one.trans hβ
   have hM₀ : a₀•v₀ ∈ minimizingDomain x := by
     change dist x (exp x (a₀•v₀)) = ‖a₀•v₀‖
     simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos (zero_lt_one.trans ha₀)] using hv₀
   have hM₁ : a₁•v₁ ∈ minimizingDomain x := by
     change dist x (exp x (a₁•v₁)) = ‖a₁•v₁‖
     simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos (zero_lt_one.trans ha₁)] using hv₁
   have hU₀ : β•v₀ ∈ minimizingDomain x := by
     have hh := injectivity_subset_minimizing x (strict_radial_mem_injectivity hM₀
       (div_nonneg hβpos.le (zero_lt_one.trans ha₀).le)
       ((div_lt_one (zero_lt_one.trans ha₀)).mpr hβ₀))
     simpa only [smul_smul,div_mul_cancel₀ β (zero_lt_one.trans ha₀).ne'] using hh
   have hU₁ : β•v₁ ∈ minimizingDomain x := by
     have hh := injectivity_subset_minimizing x (strict_radial_mem_injectivity hM₁
       (div_nonneg hβpos.le (zero_lt_one.trans ha₁).le)
       ((div_lt_one (zero_lt_one.trans ha₁)).mpr hβ₁))
     simpa only [smul_smul,div_mul_cancel₀ β (zero_lt_one.trans ha₁).ne'] using hh
   let y : Bool → M := fun i => exp x (if i then β•v₁ else β•v₀)
   let h : Bool → ℝ := fun i => cost x (y i)
   have hφ : finitePotential y h x = 0 := by simp [finitePotential,h]
   have hA₀ : β•v₀ ∈ activeVelocities y h x := ⟨hU₀,false,rfl,by simpa only [h,sub_self] using hφ⟩
   have hA₁ : β•v₁ ∈ activeVelocities y h x := ⟨hU₁,true,rfl,by simpa only [h,sub_self] using hφ⟩
   have hHull : a•(β•v₀)+b•(β•v₁) ∈ activeHull y h x :=
     (convex_convexHull ℝ _ ) (subset_convexHull ℝ _ hA₀) (subset_convexHull ℝ _ hA₁) ha hb hab
   have hScale := activeHull_scaled_mem_injectivity hMTW y h (inv_pos.mpr hβpos)
     ((inv_lt_one₀ hβpos).mpr hβ) x hHull
   have heq : β⁻¹•(a•(β•v₀)+b•(β•v₁)) = a•v₀+b•v₁ := by
      rw [smul_add, smul_comm β⁻¹ a, smul_comm β⁻¹ b,
        inv_smul_smul₀ hβpos.ne', inv_smul_smul₀ hβpos.ne']
   rwa [heq] at hScale

end
end WeakMTW

theorem current_main_convexity
    {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [MetricSpace M] [ChartedSpace (WeakMTW.Model n) M]
    [IsManifold (WeakMTW.model n) ∞ M]
    [CompactSpace M] [ConnectedSpace M]
    [RiemannianBundle (fun x : M => TangentSpace (WeakMTW.model n) x)]
    [IsContMDiffRiemannianBundle (WeakMTW.model n) ∞ (WeakMTW.Model n)
      (fun x : M => TangentSpace (WeakMTW.model n) x)]
    [IsRiemannianManifold (WeakMTW.model n) M]
    (hmtw : WeakMTW.HasWeakMTW (n := n) (M := M)) :
    WeakMTW.MainConvexity (n := n) (M := M) := by
  obtain ⟨extraDimension, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact WeakMTW.injectivityDomain_convex hmtw
end

end WeakMTWGlobalSupport

end OAI
