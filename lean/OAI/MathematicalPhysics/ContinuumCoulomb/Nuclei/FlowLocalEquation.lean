import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowLocalModel
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowVariational

namespace OAI

/-! A global C⁴ representative near one compact family of trajectories.
Its derivatives on the base trajectory are those of the original field. -/

noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
namespace ContinuumCoulomb

theorem flow_local_equation {U : Set (ℝ × Position)} (hU : IsOpen U)
    (hslab : Icc (0:ℝ) 1 ×ˢ (univ : Set Position) ⊆ U)
    (v : ℝ → Position → Position)
    (hv : ContDiffOn ℝ 4 (fun p : ℝ × Position => v p.1 p.2) U)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow v G) (x : Position) :
    ∃ (H W : ℝ × Position → Position) (O : Set Position),
      ContDiff ℝ 4 H ∧ ContDiff ℝ 4 W ∧ IsOpen O ∧ x ∈ O ∧
      (∀ y ∈ O, ∀ t ∈ Icc (0:ℝ) 1, G y t = H (t,y)) ∧
      (∀ y ∈ O, ∀ t ∈ Icc (0:ℝ) 1,
        HasDerivAt (fun s => H (s,y)) (W (t,H (t,y))) t) ∧
      (∀ t ∈ Icc (0:ℝ) 1,
        W =ᶠ[𝓝 (t,G x t)] (fun p : ℝ × Position => v p.1 p.2)) := by
  obtain ⟨H,hH,hEq⟩ := flow_local_model hU hslab v hv G hG x
  let A : ℝ → FlowPhase := fun t => (t,G x t)
  have hA : ContinuousOn A (Icc (0:ℝ) 1) :=
    continuousOn_id.prodMk (HasDerivWithinAt.continuousOn (hG.2 x))
  let K := A '' Icc (0:ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hA
  have hKU : K ⊆ U := by rintro _ ⟨t,ht,rfl⟩; exact hslab ⟨ht,mem_univ _⟩
  obtain ⟨g,V,hg,_hgc,hV,hKV,_hVU,hgv⟩ := flow_c4_compact_extension
    (f := fun p => (1,v p.1 p.2)) hU (contDiffOn_const.prodMk hv) hK hKU
  let W : ℝ × Position → Position := fun p => (g p).2
  have hW : ContDiff ℝ 4 W := contDiff_snd.comp hg
  have hWv (p : ℝ × Position) (hp : p ∈ V) : W p = v p.1 p.2 :=
    congrArg Prod.snd (hgv hp)
  have hbase (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : H (t,x) = G x t :=
    (hEq.self_of_nhds t ht).symm
  have hnear : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc (0:ℝ) 1, (t,H (t,y)) ∈ V := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hc : Continuous (fun p : Position × ℝ => (p.2,H (p.2,p.1))) :=
      continuous_snd.prodMk (hH.continuous.comp (continuous_snd.prodMk continuous_fst))
    apply hc.continuousAt.eventually
    apply hV.mem_nhds
    change (t,H (t,x)) ∈ V
    rw [hbase t ht]
    exact hKV ⟨t,ht,rfl⟩
  obtain ⟨O,hOsub,hO,hxO⟩ := mem_nhds_iff.mp (hEq.and hnear)
  refine ⟨H,W,O,hH,hW,hO,hxO,fun y hy => (hOsub hy).1,?_,?_⟩
  · intro y hy t ht
    have hwithin := (hG.2 y t ht).congr_of_mem
      (fun s hs => ((hOsub hy).1 s hs).symm) ht
    rw [(hOsub hy).1 t ht,←hWv (t,H (t,y)) ((hOsub hy).2 t ht)] at hwithin
    have hp : HasDerivAt (fun s : ℝ => (s,y)) ((1:ℝ),(0:Position)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
    have hd := ((hH.differentiable (by norm_num)) (t,y)).hasFDerivAt.comp_hasDerivAt t hp
    have he := flow_model_time_partial H hH (fun s z => W (s,z)) t ht y hwithin
    rw [he] at hd
    exact hd.congr_of_eventuallyEq (Eventually.of_forall (fun _ => rfl))
  · intro t ht
    filter_upwards [hV.mem_nhds (hKV ⟨t,ht,rfl⟩)] with p hp
    exact hWv p hp

end ContinuumCoulomb

end

end OAI
