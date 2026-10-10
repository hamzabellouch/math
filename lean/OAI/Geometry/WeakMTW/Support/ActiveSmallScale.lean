import Mathlib
import OAI.Geometry.WeakMTW.Support.TangentHullCompact
import OAI.Geometry.WeakMTW.Support.ActiveCollisionExclusion

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

omit [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem mulState_zero_eq_of_proj {p q : TangentBundle (model n) M} (he : p.1 = q.1) :
     mulState 0 p = mulState 0 q := by
   cases p with | mk x v =>
     cases q with | mk y w =>
       dsimp at he
       subst y
       simp only [mulState,zero_smul]

 theorem activeProjection_small_injective (y : ι → M) (h : ι → ℝ)
     (hMTW : HasWeakMTW (n := n) (M := M)) :
     ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε →
       Function.Injective (activeProjection (n := n) y h s) := by
   classical
   let := tangentBundle_firstCountable (n := n) (M := M)
   let : CompactSpace (ActivePoint (n := n) y h) := isCompact_iff_compactSpace.mp (activeHullGraph_compact (n := n) y h)
   by_contra hfail
   push Not at hfail
   let l : ℕ → ℝ := fun j => 1/((j:ℝ)+1)
   have hlpos (j : ℕ) : 0 < l j := one_div_pos.mpr (by positivity)
   choose r hr0 hrU hrbad using fun j => hfail (l j) (hlpos j)
   have hr : Tendsto r atTop (𝓝 0) := squeeze_zero (fun j => (hr0 j).le)
     (fun j => (hrU j).le) tendsto_one_div_add_atTop_nhds_zero_nat
   have hpq (j : ℕ) : ∃ p q : ActivePoint (n := n) y h,
       p ≠ q ∧ activeProjection y h (r j) p = activeProjection y h (r j) q ∧
       scaledPoleValue y h (r j) q.val ≤ scaledPoleValue y h (r j) p.val := by
     have hn := hrbad j
     simp only [Function.Injective] at hn
     push Not at hn
     obtain ⟨p,q,he,hne⟩ := hn
     by_cases hv : scaledPoleValue y h (r j) q.val ≤ scaledPoleValue y h (r j) p.val
     · exact ⟨p,q,hne,he,hv⟩
     · exact ⟨q,p,hne.symm,he.symm,(not_le.mp hv).le⟩
   choose p q hpq hcol hval using hpq
   obtain ⟨⟨p₀,q₀⟩,_,ρ,hρ,hlim⟩ :=
     (isCompact_univ : IsCompact (univ : Set (ActivePoint (n := n) y h × ActivePoint (n := n) y h))).tendsto_subseq
       (fun j => mem_univ (p j,q j))
   have hpLim : Tendsto (p ∘ ρ) atTop (𝓝 p₀) := continuous_fst.continuousAt.tendsto.comp hlim
   have hqLim : Tendsto (q ∘ ρ) atTop (𝓝 q₀) := continuous_snd.continuousAt.tendsto.comp hlim
   have hrLim := hr.comp hρ.tendsto_atTop
   have hpv : Tendsto (fun j => (p (ρ j)).val) atTop (𝓝 p₀.val) :=
     continuous_subtype_val.continuousAt.tendsto.comp hpLim
   have hqv : Tendsto (fun j => (q (ρ j)).val) atTop (𝓝 q₀.val) :=
     continuous_subtype_val.continuousAt.tendsto.comp hqLim
   have hfP := (activeProjection_continuous y h).continuousAt.tendsto.comp (hrLim.prodMk_nhds hpLim)
   have hfQ := (activeProjection_continuous y h).continuousAt.tendsto.comp (hrLim.prodMk_nhds hqLim)
   have hexy : p₀.val.1 = q₀.val.1 := by
     have he := tendsto_nhds_unique hfP
       (hfQ.congr' (Eventually.of_forall (fun j => (hcol (ρ j)).symm)))
     simpa only [activeProjection,zero_smul,exp_zero] using he
   have hqb : Tendsto (fun j => (q (ρ j)).val.1) atTop (𝓝 p₀.val.1) := by
     rw [hexy]
     exact (FiberBundle.continuous_proj (Model n) (TangentSpace (model n))).continuousAt.tendsto.comp hqv
   have hqS : Tendsto (fun j => mulState (r (ρ j)) (q (ρ j)).val) atTop (𝓝 (mulState 0 p₀.val)) := by
     rw [mulState_zero_eq_of_proj hexy]
     exact tangentScale_continuous.continuousAt.tendsto.comp (hrLim.prodMk_nhds hqv)
   apply critical_collision_sequence_false y h hMTW hpv hqb hrLim hqS
     (Eventually.of_forall (fun j => hr0 (ρ j))) (le_refl 0) zero_lt_one
     (fun j => (p (ρ j)).property) _ _ _ _ _
   · exact Eventually.of_forall (fun j he => hpq (ρ j) (Subtype.ext he))
   · exact Eventually.of_forall (fun j => hcol (ρ j))
   · exact Eventually.of_forall (fun j => hval (ρ j))
   · intro u hu hu0
     exact False.elim ((not_lt_of_ge hu) hu0)
   · simpa only [zero_smul] using nonconjugate_of_mem_injectivity p₀.val.1 (zero_mem_injectivity p₀.val.1)

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
