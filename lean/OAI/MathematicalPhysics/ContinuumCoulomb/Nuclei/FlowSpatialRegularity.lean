import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowCompactExtension
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowIntervalUniqueness

namespace OAI

/-! Spatial C⁴ regularity on the entire closed transport interval, derived
from local C⁴ dependence and uniqueness along each compact trajectory. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace ContinuumCoulomb

theorem flow_lifted_local_model {f : FlowPhase → FlowPhase} {S : Set FlowPhase}
    (hS : IsOpen S) (hf : ContDiffOn ℝ 4 f S)
    (A : Position → ℝ → FlowPhase) (h0 : ∀ x, A x 0 = (0,x))
    (hA : ∀ x t, t ∈ Icc (0:ℝ) 1 →
      HasDerivWithinAt (A x) (f (A x t)) (Icc (0:ℝ) 1) t)
    (hAS : ∀ x, MapsTo (A x) (Icc (0:ℝ) 1) S) (x : Position) :
    ∃ H : ℝ × Position → FlowPhase, ContDiff ℝ 4 H ∧
      ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc (0:ℝ) 1, A y t = H (t,y) := by
  let K := A x '' Icc (0:ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn
    (HasDerivWithinAt.continuousOn (hA x))
  have hKS : K ⊆ S := by rintro _ ⟨s,hs,rfl⟩; exact hAS x hs
  obtain ⟨g,O,hg,hgc,hO,hKO,_hOS,hgf⟩ := flow_c4_compact_extension hS hf hK hKS
  obtain ⟨F,hF0,hF,hFC⟩ := flow_compact_global_exists hg hgc
  have hAxO (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : A x s ∈ O := hKO ⟨s,hs,rfl⟩
  have hbase : EqOn (A x) (F (0,x)) (Icc (0:ℝ) 1) := by
    apply flow_open_interval_unique isOpen_univ hg.contDiffOn
      (fun s hs => by simpa only [hgf (hAxO s hs)] using hA x s hs)
      (fun s _ => (hF (0,x) s).hasDerivWithinAt) (fun _ _ => mem_univ _)
      (show (0:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
    rw [h0,hF0]
  have hnear : ∀ᶠ y in 𝓝 x, ∀ s ∈ Icc (0:ℝ) 1, F (0,y) s ∈ O := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    have hc : Continuous (fun z : Position × ℝ => F (0,z.1) z.2) :=
      hFC.continuous.comp (continuous_snd.prodMk (continuous_const.prodMk continuous_fst))
    apply hc.continuousAt.eventually
    apply hO.mem_nhds
    change F (0,x) s ∈ O
    rw [←hbase hs]
    exact hAxO s hs
  refine ⟨fun z => F (0,z.2) z.1,
    hFC.comp (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)),?_⟩
  filter_upwards [hnear] with y hy
  apply flow_open_interval_unique hS hf (hA y)
    (fun s hs => by simpa only [hgf (hy s hs)] using
      (hF (0,y) s).hasDerivWithinAt (s := Icc (0:ℝ) 1))
    (hAS y) (show (0:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
  rw [h0,hF0]

theorem flow_lifted_interval_C4 {f : FlowPhase → FlowPhase} {S : Set FlowPhase}
    (hS : IsOpen S) (hf : ContDiffOn ℝ 4 f S)
    (A : Position → ℝ → FlowPhase) (h0 : ∀ x, A x 0 = (0,x))
    (hA : ∀ x t, t ∈ Icc (0:ℝ) 1 →
      HasDerivWithinAt (A x) (f (A x t)) (Icc (0:ℝ) 1) t)
    (hAS : ∀ x, MapsTo (A x) (Icc (0:ℝ) 1) S)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ContDiff ℝ 4 (fun x => A x t) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨H,hH,hEq⟩ := flow_lifted_local_model hS hf A h0 hA hAS x
  have hc : ContDiff ℝ 4 (fun y : Position => H (t,y)) :=
    hH.comp (contDiff_const.prodMk contDiff_id)
  exact hc.contDiffAt.congr_of_eventuallyEq (hEq.mono (fun _ hy => hy t ht))

theorem flow_spatial_C4 {U : Set (ℝ × Position)} (hU : IsOpen U)
    (hslab : Icc (0:ℝ) 1 ×ˢ (univ : Set Position) ⊆ U)
    (v : ℝ → Position → Position)
    (hv : ContDiffOn ℝ 4 (fun p : ℝ × Position => v p.1 p.2) U)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow v G)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ContDiff ℝ 4 (fun x => G x t) := by
  let f : FlowPhase → FlowPhase := fun p => (1,v p.1 p.2)
  let A : Position → ℝ → FlowPhase := fun x s => (s,G x s)
  have hf : ContDiffOn ℝ 4 f U := contDiffOn_const.prodMk hv
  have hA : ∀ x s, s ∈ Icc (0:ℝ) 1 →
      HasDerivWithinAt (A x) (f (A x s)) (Icc (0:ℝ) 1) s := by
    intro x s hs
    exact (hasDerivWithinAt_id s (Icc (0:ℝ) 1)).prodMk (hG.2 x s hs)
  have hc := flow_lifted_interval_C4 hU hf A
    (fun x => by simp only [A,hG.1]) hA (fun x s hs => hslab ⟨hs,mem_univ _⟩) t ht
  exact contDiff_snd.comp hc

end ContinuumCoulomb

end

end OAI
