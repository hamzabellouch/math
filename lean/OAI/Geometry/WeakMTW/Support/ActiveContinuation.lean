import Mathlib
import OAI.Geometry.WeakMTW.Support.ActiveSmallScale
import OAI.Geometry.WeakMTW.Geodesics.MinimizerCapture

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]
  {ι : Type*} [Fintype ι] [Nonempty ι]

 theorem activeProjection_critical_bijective (y : ι → M) (h : ι → ℝ)
     (hMTW : HasWeakMTW (n := n) (M := M)) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
     (hbelow : ∀ r, 0 ≤ r → r < s → ∀ p ∈ activeHullGraph (n := n) y h,
       r•p.2 ∈ injectivityDomain p.1)
     (hmin : ∀ p ∈ activeHullGraph (n := n) y h, s•p.2 ∈ minimizingDomain p.1) :
     Function.Bijective (activeProjection (n := n) y h s) := by
   let := tangentBundle_firstCountable (n := n) (M := M)
   let : T2Space (TangentBundle (model n) M) := tangentBundle_t2Space
   let : CompactSpace (ActivePoint (n := n) y h) := isCompact_iff_compactSpace.mp (activeHullGraph_compact (n := n) y h)
   let : PreconnectedSpace (Ioc (0 : ℝ) s) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioc
   let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (Model n) M
   let F : Ioc (0 : ℝ) s × ActivePoint (n := n) y h → M := fun q => activeProjection y h q.1.val q.2
   have hF : Continuous F := (activeProjection_continuous y h).comp
     ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
   have hsurj (t : Ioc (0 : ℝ) s) : Function.Surjective (fun p => F (t,p)) := by
     intro z
     obtain ⟨x,b,hb,he⟩ := activeHull_exp_surjective (n := n) y h t.property.1 z
     exact ⟨⟨⟨x,b⟩,hb⟩,he⟩
   have hexc (t : Ioc (0 : ℝ) s) : CompactContinuation.CollisionExclusionAt F t :=
     active_collision_exclusion y h hMTW hs hs1 hbelow hmin t
   obtain ⟨ε,hε,hεinj⟩ := activeProjection_small_injective y h hMTW
   let t₀ := min (s/2) (ε/2)
   have ht₀ : 0 < t₀ := lt_min (by linarith) (by linarith)
   have ht₀s : t₀ ≤ s := (min_le_left _ _).trans (by linarith)
   have ht₀ε : t₀ < ε := (min_le_right _ _).trans_lt (by linarith)
   have hstart : ∃ t : Ioc (0 : ℝ) s, Function.Injective (fun p => F (t,p)) :=
     ⟨⟨t₀,ht₀,ht₀s⟩,hεinj t₀ ht₀ ht₀ε⟩
   exact CompactContinuation.global_bijective hF hsurj hexc hstart ⟨s,hs,le_refl _⟩

 theorem activeProjection_injective_minimizes (y : ι → M) (h : ι → ℝ)
     {s : ℝ} (hs : 0 < s) (hinj : Function.Injective (activeProjection (n := n) y h s))
     (p : ActivePoint (n := n) y h) : ∀ x : M,
       cost p.val.1 (activeProjection y h s p) + s*finitePotential y h p.val.1 ≤
         cost x (activeProjection y h s p) + s*finitePotential y h x := by
   let z := activeProjection y h s p
   let : Nonempty M := ⟨p.val.1⟩
   have hc : Continuous (fun x : M => cost x z+s*finitePotential y h x) :=
     ((cost_continuous (M := M)).comp (continuous_id.prodMk continuous_const)).add
       ((finitePotential_continuous y h).const_mul s)
   obtain ⟨x,_,hx⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty) hc.continuousOn
   obtain ⟨w,hw,hn⟩ := exists_minimizing_vector (n := n) x z
   have hwm : w ∈ minimizingDomain x := by
     change dist x (exp x w) = ‖w‖
     rw [hw,hn]
   have hmin : ∀ x', cost x (exp x w)+s*finitePotential y h x ≤
       cost x' (exp x w)+s*finitePotential y h x' := by
     intro x'
     rw [hw]
     exact hx (mem_univ x')
   let q : ActivePoint (n := n) y h := ⟨⟨x,s⁻¹•w⟩,minimizing_pole_capture y h hwm hs hmin⟩
   have hqp : q = p := hinj (by
     change exp x (s•(s⁻¹•w)) = z
     simpa only [smul_smul,mul_inv_cancel₀ hs.ne',one_smul] using hw)
   have hxp : x = p.val.1 := congrArg (fun a : ActivePoint (n := n) y h => a.val.1) hqp
   intro x'
   have hxx : cost x z+s*finitePotential y h x ≤ cost x' z+s*finitePotential y h x' := hx (mem_univ x')
   simpa only [hxp] using hxx

 theorem activeProjection_injective_unique (y : ι → M) (h : ι → ℝ)
     {s : ℝ} (hs : 0 < s) (hinj : Function.Injective (activeProjection (n := n) y h s))
     {x : M} {b : TangentSpace (model n) x} (hb : b ∈ activeHull y h x)
     {w : TangentSpace (model n) x} (hw : w ∈ minimizingDomain x)
     (he : exp x w = exp x (s•b)) : w = s•b := by
   let p : ActivePoint (n := n) y h := ⟨⟨x,b⟩,hb⟩
   have hmin : ∀ z, cost x (exp x w)+s*finitePotential y h x ≤
       cost z (exp x w)+s*finitePotential y h z := by
     rw [he]
     exact activeProjection_injective_minimizes y h hs hinj p
   let q : ActivePoint (n := n) y h := ⟨⟨x,s⁻¹•w⟩,minimizing_pole_capture y h hw hs hmin⟩
   have hqp : q = p := hinj (by
     change exp x (s•(s⁻¹•w)) = exp x (s•b)
     simpa only [smul_smul,mul_inv_cancel₀ hs.ne',one_smul] using he)
   have hv : s⁻¹•w = b := TotalSpace.mk_injective x (congrArg Subtype.val hqp)
   have hv' := congrArg (fun a : TangentSpace (model n) x => s•a) hv
   simpa only [smul_smul,mul_inv_cancel₀ hs.ne',one_smul] using hv'

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
