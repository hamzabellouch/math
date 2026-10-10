import Mathlib
import OAI.Geometry.WeakMTW.Potentials.PotentialActiveLogs
import OAI.Geometry.WeakMTW.Potentials.FiniteGlobalSupport
import OAI.Geometry.WeakMTW.Potentials.LiftedSectionDefinitions

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

omit [CompactSpace M] in
 theorem cost_comm (x y : M) : cost x y = cost y x := by simp only [cost,dist_comm]
omit [CompactSpace M] [IsManifold (model n) ∞ M]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] in
 theorem minimizing_cost {x : M} {p : TangentSpace (model n) x} (hp : p ∈ minimizingDomain x) :
     cost x (exp x p) = ‖p‖^2/2 := by unfold cost; rw [show dist x (exp x p) = ‖p‖ from hp]

 theorem double_mountain (hMTW : HasWeakMTW (n := n) (M := M)) {x : M}
     {p₀ p₁ : TangentSpace (model n) x} (hp₀ : p₀ ∈ minimizingDomain x) (hp₁ : p₁ ∈ minimizingDomain x)
     {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b = 1) :
     a•p₀+b•p₁ ∈ minimizingDomain x ∧ ∀ z,
       cost x (exp x (a•p₀+b•p₁))-cost z (exp x (a•p₀+b•p₁)) ≤
         max (cost x (exp x p₀)-cost z (exp x p₀)) (cost x (exp x p₁)-cost z (exp x p₁)) := by
   let y : Bool → M := fun i => exp x (if i then p₁ else p₀)
   let h : Bool → ℝ := fun i => cost x (y i)
   have hφ : finitePotential y h x = 0 := by simp [finitePotential,h]
   have hA₀ : p₀ ∈ activeVelocities y h x := ⟨hp₀,false,rfl,by simpa only [h,sub_self] using hφ⟩
   have hA₁ : p₁ ∈ activeVelocities y h x := ⟨hp₁,true,rfl,by simpa only [h,sub_self] using hφ⟩
   have hHull : a•p₀+b•p₁ ∈ activeHull y h x :=
     (convex_convexHull ℝ _ ) (subset_convexHull ℝ _ hA₀) (subset_convexHull ℝ _ hA₁) ha hb hab
   obtain ⟨hm,hs⟩ := finite_active_global_support hMTW y h hHull
   refine ⟨hm,fun z => ?_⟩
   have hmax : finitePotential y h z ≤
       max (cost x (exp x p₀)-cost z (exp x p₀)) (cost x (exp x p₁)-cost z (exp x p₁)) := by
     apply Finset.sup'_le
     intro i _
     cases i
     · exact le_max_left _ _
     · exact le_max_right _ _
   have hh := (hs z).trans hmax
   simpa only [hφ,zero_add] using hh

 theorem minimizingDomain_convex (hMTW : HasWeakMTW (n := n) (M := M)) (x : M) :
     Convex ℝ (minimizingDomain (n := n) x) := by
   intro p₀ hp₀ p₁ hp₁ a b ha hb hab
   exact (double_mountain hMTW hp₀ hp₁ ha hb hab).1

 theorem liftedGap_continuous {u v : M → ℝ} (hv : Continuous v) (x : M) :
     Continuous (liftedGap (n := n) u v x) :=
   (continuous_const.add ((continuous_norm.pow 2).div_const 2)).add
     (hv.comp (exp_fibre_smooth x).continuous)

 theorem liftedGapSection_compact {u v : M → ℝ} (hv : Continuous v) (x : M) (r : ℝ) :
     IsCompact (liftedGapSection (n := n) u v x r) :=
   (minimizingDomain_compact x).inter_right (isClosed_le (liftedGap_continuous hv x) continuous_const)

omit [IsManifold (model n) ∞ M]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] in
 theorem liftedGap_nonneg {u v : M → ℝ} (hv : Continuous v) (hu : u = cTransform v)
     {x : M} {p : TangentSpace (model n) x} (hp : p ∈ minimizingDomain x) : 0 ≤ liftedGap u v x p := by
   have h := cTransform_ge hv x (exp x p)
   rw [←hu,minimizing_cost hp] at h
   dsimp [liftedGap]
   linarith

 theorem liftedGapSection_convex (hMTW : HasWeakMTW (n := n) (M := M))
     {u v : M → ℝ} (huv : IsDualPair u v) (x : M) (r : ℝ) :
     Convex ℝ (liftedGapSection (n := n) u v x r) := by
   intro p₀ hp₀ p₁ hp₁ a b ha hb hab
   obtain ⟨hm,hs⟩ := double_mountain hMTW hp₀.1 hp₁.1 ha hb hab
   refine ⟨hm,?_⟩
   obtain ⟨z,hz⟩ := cTransform_attained huv.1 (exp x (a•p₀+b•p₁))
   rw [←huv.2.2.2,cost_comm] at hz
   have hbound (p : TangentSpace (model n) x) (hp : p ∈ liftedGapSection (n := n) u v x r) :
       cost x (exp x p)-cost z (exp x p) ≤ r-u x+u z := by
     have h := cTransform_ge huv.1 (exp x p) z
     rw [←huv.2.2.2,cost_comm] at h
     rw [minimizing_cost hp.1]
     have hg := hp.2
     dsimp [liftedGap] at hg
     linarith
   have hle := (hs z).trans (max_le (hbound p₀ hp₀) (hbound p₁ hp₁))
   rw [minimizing_cost hm] at hle
   dsimp [liftedGap]
   rw [hz]
   linarith

 theorem liftedGapSection_diameter (hMTW : HasWeakMTW (n := n) (M := M))
     {u v : M → ℝ} (huv : IsDualPair u v) (x : M) (r : ℝ)
     (hne : (liftedGapSection (n := n) u v x r).Nonempty) (hr : 0 ≤ r) :
     (Metric.diam (liftedGapSection (n := n) u v x r))^2 ≤
       8*(r+sectionOscillation (n := n) v x (liftedGapSection (n := n) u v x r)) := by
   let S := liftedGapSection (n := n) u v x r
   let f : TangentSpace (model n) x → ℝ := fun p => v (exp x p)
   have hcompact : IsCompact S := liftedGapSection_compact huv.2.1 x r
   have hc : IsCompact (f '' S) := hcompact.image (huv.2.1.comp (exp_fibre_smooth x).continuous)
   have hconv : Convex ℝ S := liftedGapSection_convex hMTW huv x r
   have hpair (p₀ : TangentSpace (model n) x) (hp₀ : p₀ ∈ S)
       (p₁ : TangentSpace (model n) x) (hp₁ : p₁ ∈ S) :
       (dist p₀ p₁)^2 ≤ 8*(r+sectionOscillation (n := n) v x S) := by
     let pm : TangentSpace (model n) x := (1/2:ℝ)•p₀+(1/2:ℝ)•p₁
     have hpm : pm ∈ S := hconv hp₀ hp₁ (by norm_num) (by norm_num) (by norm_num)
     have hmid : ‖pm‖^2 = (‖p₀‖^2+‖p₁‖^2)/2-‖p₀-p₁‖^2/4 := by
       have heq : pm = (1/2:ℝ)•(p₀+p₁) := by simp only [pm,smul_add]
       rw [heq,norm_smul,mul_pow]
       norm_num
       nlinarith [parallelogram_law_with_norm ℝ p₀ p₁]
     have hm0 := liftedGap_nonneg huv.2.1 huv.2.2.1 hpm.1
     have h₀ := hp₀.2
     have h₁ := hp₁.2
     have hVm : f pm ≤ sSup (f '' S) := le_csSup hc.bddAbove (mem_image_of_mem f hpm)
     have hV₀ : sInf (f '' S) ≤ f p₀ := csInf_le hc.bddBelow (mem_image_of_mem f hp₀)
     have hV₁ : sInf (f '' S) ≤ f p₁ := csInf_le hc.bddBelow (mem_image_of_mem f hp₁)
     dsimp [liftedGap] at hm0 h₀ h₁
     change v (exp x pm) ≤ sSup (f '' S) at hVm
     change sInf (f '' S) ≤ v (exp x p₀) at hV₀
     change sInf (f '' S) ≤ v (exp x p₁) at hV₁
     change dist p₀ p₁ ^ 2 ≤ 8*(r+(sSup (f '' S)-sInf (f '' S)))
     rw [dist_eq_norm]
     nlinarith
   have hnonneg : 0 ≤ 8*(r+sectionOscillation (n := n) v x S) :=
     mul_nonneg (by norm_num) (add_nonneg hr
       (sub_nonneg.mpr (csInf_le_csSup (hne.image f) hc.bddBelow hc.bddAbove)))
   have hd : Metric.diam S ≤ Real.sqrt (8*(r+sectionOscillation (n := n) v x S)) := by
     apply Metric.diam_le_of_forall_dist_le (Real.sqrt_nonneg _)
     intro p₀ hp₀ p₁ hp₁
     exact (Real.le_sqrt (dist_nonneg : 0 ≤ dist p₀ p₁) hnonneg).mpr (hpair p₀ hp₀ p₁ hp₁)
   have hsq := Real.sq_sqrt hnonneg
   have hdn : 0 ≤ Metric.diam S := Metric.diam_nonneg
   change Metric.diam S ^ 2 ≤ 8*(r+sectionOscillation (n := n) v x S)
   nlinarith [Real.sqrt_nonneg (8*(r+sectionOscillation (n := n) v x S))]

 theorem convexLiftedSections (hMTW : HasWeakMTW (n := n) (M := M))
     {u v : M → ℝ} (huv : IsDualPair u v) : ConvexLiftedSections (n := n) u v := by
   intro x r
   exact ⟨liftedGapSection_compact huv.2.1 x r,liftedGapSection_convex hMTW huv x r,
     liftedGapSection_diameter hMTW huv x r⟩
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
