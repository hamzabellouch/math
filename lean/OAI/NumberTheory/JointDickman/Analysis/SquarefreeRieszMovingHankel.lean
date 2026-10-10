import OAI.NumberTheory.JointDickman.Analysis.SquarefreeRieszHankelExpansion
import OAI.NumberTheory.JointDickman.Analysis.SquarefreeRieszLocalBound
import OAI.NumberTheory.JointDickman.Analysis.LaplaceMovingLocal

namespace OAI

/-! # The all-order local expansion with a shrinking contour cutoff -/
namespace JointDickman
open Set Filter MeasureTheory Asymptotics Finset
open scoped Topology

theorem squarefreeRiesz_moving_hankel_expansion {z a α : ℝ}
    (hz : 0 < z) (hz1 : z < 1) (ha : 0 < a) (hα : 0 < α)
    {η : ℝ → ℝ} (hη : ∀ᶠ L in atTop, 0 ≤ η L)
    (hηlim : Tendsto η atTop (𝓝 0))
    (hgrowth : ∀ᶠ L in atTop, a*L^α ≤ L*η L/2) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z / 2 ∧ 0 < c 0 ∧
      ∀ H : ℕ, (fun L : ℝ => squarefreeRieszLocalHankel z (η L) L -
        ∑ j ∈ range (H+1), c j*L^(z-1-j)) =O[atTop] (fun L => L^(z-2-H)) := by
  obtain ⟨r,C,hr,hC,hcont,hbound⟩ := squarefreeRieszSingularFactor_local_bound hz.le hz1.le
  obtain ⟨c,hc,hcpos,hexp⟩ := squarefreeRiesz_local_hankel_real_expansion_below hz hz1 r hr
  refine ⟨c,hc,hcpos,fun H => ?_⟩
  obtain ⟨r₀,hr₀,hr₀r,hfixed⟩ := hexp H
  have hsub : Ioc (0:ℝ) r₀ ⊆ Icc 0 r := fun _ ht => ⟨ht.1.le,ht.2.trans hr₀r⟩
  have hsmall : ∀ᶠ L in atTop, η L < r₀ := hηlim.eventually (gt_mem_nhds hr₀)
  have hmove := laplace_moving_local_isLittleO hz1 hC ha hα
    (fun t : ℝ => squarefreeRieszSingularFactor z (1-(t:ℂ)))
    ((hcont.mono hsub).aestronglyMeasurable measurableSet_Ioc)
    (fun t ht => hbound t (hsub ht))
    (hη.and (hsmall.mono fun _ h => h.le)) hgrowth (z-2-H)
  have hcplx := hmove.const_smul_left (Real.sin (Real.pi*z)/Real.pi)
  have hreal : (fun L : ℝ => squarefreeRieszLocalHankel z r₀ L -
      squarefreeRieszLocalHankel z (η L) L) =o[atTop] (fun L => L^(z-2-H)) := by
    apply IsBigO.trans_isLittleO _ hcplx
    apply isBigO_of_le atTop
    intro L
    change ‖((Real.sin (Real.pi*z)/Real.pi) •
        (∫ t : ℝ in Ioc 0 r₀, (t^(-z)*Real.exp (-(L*t))) •
          squarefreeRieszSingularFactor z (1-(t:ℂ)))).re -
      ((Real.sin (Real.pi*z)/Real.pi) •
        (∫ t : ℝ in Ioc 0 (η L), (t^(-z)*Real.exp (-(L*t))) •
          squarefreeRieszSingularFactor z (1-(t:ℂ)))).re‖ ≤ _
    rw [←Complex.sub_re,←smul_sub]
    exact Complex.abs_re_le_norm _
  apply (hfixed.sub hreal.isBigO).congr_left
  intro L
  ring

end JointDickman

end OAI
