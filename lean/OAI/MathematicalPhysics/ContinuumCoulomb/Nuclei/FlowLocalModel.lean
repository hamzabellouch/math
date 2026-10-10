import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowSpatialRegularity

namespace OAI

/-! A smooth local representative of the actual nonautonomous flow, with
agreement uniform over the entire closed time interval. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace ContinuumCoulomb

theorem flow_local_model {U : Set (ℝ × Position)} (hU : IsOpen U)
    (hslab : Icc (0:ℝ) 1 ×ˢ (univ : Set Position) ⊆ U)
    (v : ℝ → Position → Position)
    (hv : ContDiffOn ℝ 4 (fun p : ℝ × Position => v p.1 p.2) U)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow v G) (x : Position) :
    ∃ H : ℝ × Position → Position, ContDiff ℝ 4 H ∧
      ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc (0:ℝ) 1, G y t = H (t,y) := by
  let f : FlowPhase → FlowPhase := fun p => (1,v p.1 p.2)
  let A : Position → ℝ → FlowPhase := fun y s => (s,G y s)
  have hf : ContDiffOn ℝ 4 f U := contDiffOn_const.prodMk hv
  have hA : ∀ y s, s ∈ Icc (0:ℝ) 1 →
      HasDerivWithinAt (A y) (f (A y s)) (Icc (0:ℝ) 1) s := by
    intro y s hs
    exact (hasDerivWithinAt_id s (Icc (0:ℝ) 1)).prodMk (hG.2 y s hs)
  obtain ⟨H,hH,hEq⟩ := flow_lifted_local_model hU hf A
    (fun y => by simp only [A,hG.1]) hA (fun y s hs => hslab ⟨hs,mem_univ _⟩) x
  refine ⟨fun p => (H p).2,contDiff_snd.comp hH,?_⟩
  filter_upwards [hEq] with y hy
  intro t ht
  exact congrArg Prod.snd (hy t ht)

end ContinuumCoulomb

end

end OAI
