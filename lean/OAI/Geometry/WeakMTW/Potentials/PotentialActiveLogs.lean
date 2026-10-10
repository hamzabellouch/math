import Mathlib
import OAI.Geometry.WeakMTW.Support.ActiveGraphLimits
import OAI.Geometry.WeakMTW.Support.TangentHullCompact
import OAI.Geometry.WeakMTW.Potentials.PotentialDefinitions

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

 theorem cTransform_continuous {v : M → ℝ} (hv : Continuous v) : Continuous (cTransform v) := by
   change Continuous (fun x : M => sSup (range (fun y : M => -cost x y-v y)))
   have h := isCompact_univ.continuous_sSup (f := fun x y : M => -cost x y-v y)
     (cost_continuous.neg.sub (hv.comp continuous_snd))
   simpa only [image_univ] using h

 theorem cTransform_ge {v : M → ℝ} (hv : Continuous v) (x y : M) :
     -cost x y-v y ≤ cTransform v x := by
   apply le_csSup _ (mem_range_self y)
   have hc : Continuous (fun y : M => -cost x y-v y) :=
     (cost_continuous.comp (continuous_const.prodMk continuous_id)).neg.sub hv
   simpa only [image_univ] using (isCompact_univ.image hc).bddAbove

 theorem cTransform_attained {v : M → ℝ} (hv : Continuous v) (x : M) :
     ∃ y : M, cTransform v x = -cost x y-v y := by
   let : Nonempty M := ⟨x⟩
   have hc : Continuous (fun y : M => -cost x y-v y) :=
     (cost_continuous.comp (continuous_const.prodMk continuous_id)).neg.sub hv
   obtain ⟨y,hy,he⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hc.continuousOn
   refine ⟨y,le_antisymm ?_ (cTransform_ge hv x y)⟩
   exact csSup_le (range_nonempty _) (by rintro _ ⟨z,rfl⟩; exact he (mem_univ z))

 theorem isPotential_continuous {u : M → ℝ} (hu : IsPotential u) : Continuous u := by
   obtain ⟨v,hv,rfl⟩ := hu
   exact cTransform_continuous hv

 def potentialActive (u v : M → ℝ) (x : M) : Set (TangentSpace (model n) x) :=
   {a | a ∈ minimizingDomain x ∧ u x + cost x (exp x a)+v (exp x a) = 0}
 def potentialActiveGraph (u v : M → ℝ) : Set (TangentBundle (model n) M) :=
   {p | p.2 ∈ potentialActive u v p.1}

 theorem potentialActive_nonempty {u v : M → ℝ} (hv : Continuous v) (hu : u = cTransform v) (x : M) :
     (potentialActive (n := n) u v x).Nonempty := by
   obtain ⟨y,hy⟩ := cTransform_attained hv x
   obtain ⟨a,ha,han⟩ := exists_minimizing_vector (n := n) x y
   refine ⟨a,?_,?_⟩
   · change dist x (exp x a) = ‖a‖
     rw [ha,han]
   · rw [ha,hu,hy]
     ring

 theorem potentialActiveGraph_compact {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) :
     IsCompact (potentialActiveGraph (n := n) u v) := by
   have hb : Continuous (fun q : TangentBundle (model n) M => q.1) :=
     (contMDiff_proj (TangentSpace (model n)) (IB := model n) (n := ∞)).continuous
   have he : Continuous (fun q : TangentBundle (model n) M => exp q.1 q.2) := exp_total_smooth.continuous
   exact totalMinimizingSet_compact.inter_right
     (isClosed_eq (((hu.comp hb).add (cost_continuous.comp (hb.prodMk he))).add (hv.comp he)) continuous_const)

 theorem potentialActive_subseq {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
     {p : ℕ → M} {x : M} (hp : Tendsto p atTop (𝓝 x))
     (a : ∀ j, TangentSpace (model n) (p j))
     (ha : ∀ j, a j ∈ potentialActive u v (p j)) :
     ∃ a₀ ∈ potentialActive u v x, ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
       Tendsto (fun j => (⟨p (ρ j),a (ρ j)⟩ : TangentBundle (model n) M)) atTop (𝓝 ⟨x,a₀⟩) := by
   let := tangentBundle_firstCountable (n := n) (M := M)
   obtain ⟨⟨z,a₀⟩,ha₀,ρ,hρ,hlim⟩ := (potentialActiveGraph_compact hu hv).tendsto_subseq
     (fun j => show (⟨p j,a j⟩ : TangentBundle (model n) M) ∈ potentialActiveGraph u v from ha j)
   have hb : Continuous (fun q : TangentBundle (model n) M => q.1) :=
     (contMDiff_proj (TangentSpace (model n)) (IB := model n) (n := ∞)).continuous
   have hz : z = x := tendsto_nhds_unique (hb.continuousAt.tendsto.comp hlim) (hp.comp hρ.tendsto_atTop)
   subst z
   exact ⟨a₀,ha₀,ρ,hρ,hlim⟩

 theorem potentialActive_shortened_support {u v : M → ℝ} (hv : Continuous v) (hu : u = cTransform v)
     {x : M} {a : TangentSpace (model n) x} (ha : a ∈ potentialActive u v x)
     {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (z : M) :
     u x+(cost x (exp x (s•a))-cost z (exp x (s•a)))/s ≤ u z := by
   have hge := cTransform_ge hv z (exp x a)
   rw [← hu] at hge
   have hsplit := shortened_upper_difference ha.1 hs hs1 z
   rw [sub_div] at hsplit ⊢
   linarith [ha.2]

 theorem potentialActiveHull_closed {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (x : M) :
     IsClosed (convexHull ℝ (potentialActive (n := n) u v x)) :=
   (tangentHull_closed (potentialActiveGraph_compact hu hv)).preimage
     (FiberBundle.continuous_totalSpaceMk (Model n) (TangentSpace (model n)) x)
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
