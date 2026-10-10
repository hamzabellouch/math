import Mathlib
import OAI.Geometry.WeakMTW.Potentials.PotentialActiveLogs
import OAI.Geometry.WeakMTW.Potentials.FiniteGlobalSupport

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold BigOperators
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 omit [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
   [IsRiemannianManifold (model n) M] in
 theorem potential_activeHull_finite_reduction {u v : M → ℝ} (hv : Continuous v) (hu : u = cTransform v)
     {x : M} {b : TangentSpace (model n) x} (hb : b ∈ convexHull ℝ (potentialActive u v x)) :
     ∃ (y : ActiveIndex n → M) (h : ActiveIndex n → ℝ),
       (∀ z, finitePotential y h z ≤ u z) ∧ finitePotential y h x = u x ∧ b ∈ activeHull y h x := by
   let : FiniteDimensional ℝ (TangentSpace (model n) x) :=
     VectorBundle.finiteDimensional ℝ (Model n) _ x
   obtain ⟨a,θ,ha,hθ,hs,hbary⟩ := ConvexRepresentation.fixed_size hb
     (show Module.finrank ℝ (TangentSpace (model n) x)+1 ≤ Module.finrank ℝ (Model n)+1 by
       rw [VectorBundle.finrank_eq ℝ (Model n) (TangentSpace (model n)) x])
   let y : ActiveIndex n → M := fun i => exp x (a i)
   let h : ActiveIndex n → ℝ := fun i => u x + cost x (y i)
   have hφ : finitePotential y h x = u x := by simp [finitePotential,h]
   have hle (z : M) : finitePotential y h z ≤ u z := by
     apply Finset.sup'_le
     intro i _
     have hge := cTransform_ge hv z (y i)
     rw [← hu] at hge
     have hai := (ha i).2
     change u x+cost x (y i)+v (y i) = 0 at hai
     change u x+cost x (y i)-cost z (y i) ≤ u z
     linarith
   have hA (i : ActiveIndex n) : a i ∈ activeVelocities y h x :=
     ⟨(ha i).1,i,rfl,by rw [hφ]; dsimp [h]; ring⟩
   refine ⟨y,h,hle,hφ,?_⟩
   rw [← hbary]
   exact (convex_convexHull ℝ _).sum_mem (fun i _ => hθ i) hs
     (fun i _ => subset_convexHull ℝ _ (hA i))

 theorem potential_activeHull_support (hMTW : HasWeakMTW (n := n) (M := M))
     {u v : M → ℝ} (hv : Continuous v) (hu : u = cTransform v)
     {x : M} {b : TangentSpace (model n) x} (hb : b ∈ convexHull ℝ (potentialActive u v x)) :
     b ∈ minimizingDomain x ∧ ∀ z, u x+cost x (exp x b)-cost z (exp x b) ≤ u z := by
   obtain ⟨y,h,hle,hφ,hb⟩ := potential_activeHull_finite_reduction hv hu hb
   obtain ⟨hm,hs⟩ := finite_active_global_support hMTW y h hb
   refine ⟨hm,fun z => ?_⟩
   rw [hφ] at hs
   exact (hs z).trans (hle z)

 theorem potential_activeHull_intermediate (hMTW : HasWeakMTW (n := n) (M := M))
     {u v : M → ℝ} (hv : Continuous v) (hu : u = cTransform v)
     {x : M} {b : TangentSpace (model n) x} (hb : b ∈ convexHull ℝ (potentialActive u v x))
     {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
     s•b ∈ injectivityDomain x ∧ ∀ z, cost x (exp x (s•b))+s*u x ≤ cost z (exp x (s•b))+s*u z ∧
       (cost z (exp x (s•b))+s*u z = cost x (exp x (s•b))+s*u x → z = x) := by
   obtain ⟨y,h,hle,hφ,hb⟩ := potential_activeHull_finite_reduction hv hu hb
   refine ⟨activeHull_scaled_mem_injectivity hMTW y h hs hs1 x hb,?_⟩
   intro z
   have hmin := finite_active_minimizes hMTW y h hs hs1 hb z
   have hle' := mul_le_mul_of_nonneg_left (hle z) hs.le
   rw [hφ] at hmin
   refine ⟨by linarith,fun heq => ?_⟩
   apply finite_active_unique_pole hMTW y h hs hs1 hb
   rw [hφ]
   linarith
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
