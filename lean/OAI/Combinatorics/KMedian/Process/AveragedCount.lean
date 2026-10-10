import Mathlib
import OAI.Combinatorics.KMedian.Process.PhysicalState
import OAI.Combinatorics.KMedian.Process.PhysicalCountLaw

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset FixedBatch PhysicalPotential SourceBalance
variable {F J : Type*} [Fintype F] [DecidableEq F] [Fintype J] [DecidableEq J] {Δ : ℕ}

theorem roundLaw_count_tail (s : State F J Δ) (μ : FiniteLaw (s.1 → Finset s.1))
    (d : J → F → ℝ) (x : ℝ) {g h φ b : ℝ}
    (hg : 0 < g) (hg1 : g ≤ 1) (hh : 0 < h) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hb : 0 < b) (hunit : g*(Δ:ℝ)=1) (hp1 : (1+φ)*(2*h*g) ≤ 1)
    (hsmall : 8*(2*h*g)*(Δ:ℝ) ≤ φ*g)
    (hG : ∀ G, 0 < μ.weight G → ∀ i, (G i).card=Δ) :
    let m := fun (G : s.1 → Finset s.1) a => mass g ((graphActions G).erase a)
    let H := fun G => univ.filter (fun a => max 1 (b*amount (m G)) < m G a)
    let q := fun G e => bias (m G) (2*h*g) φ (heavyParent (graphActions G) (H G) e)
    let hp0 : 0 ≤ 2*h*g := by positivity
    let hpp1 := (le_mul_of_one_le_left hp0 (by linarith only [hφ] : 1 ≤ 1+φ)).trans hp1
    let hq0 := fun G e => hp0.trans (bias_lower (m G) hp0 hφ.le _ : 2*h*g ≤ q G e)
    let hq1 := fun G e => (bias_upper (m G) hp0 hφ.le _ : q G e ≤ (1+φ)*(2*h*g)).trans hp1
    (roundLaw s μ H q x g h d hp0 hpp1 hq0 hq1).prob
      (fun t => mass g s.1+4/(g*b) < mass g t.1) ≤
        96*(Δ:ℝ)^2*b/((2*h*g)*φ^2*g) := by
  classical
  dsimp only
  let m := fun (G : s.1 → Finset s.1) a => mass g ((graphActions G).erase a)
  let H := fun G => univ.filter (fun a => max 1 (b*amount (m G)) < m G a)
  let q := fun G e => bias (m G) (2*h*g) φ (heavyParent (graphActions G) (H G) e)
  have hp0 : 0 ≤ 2*h*g := by positivity
  have hpp1 : 2*h*g ≤ 1 := (le_mul_of_one_le_left hp0 (by linarith only [hφ])).trans hp1
  let hq0 := fun G e => hp0.trans (bias_lower (m G) hp0 hφ.le _ : 2*h*g ≤ q G e)
  let hq1 := fun G e => (bias_upper (m G) hp0 hφ.le _ : q G e ≤ (1+φ)*(2*h*g)).trans hp1
  unfold FiniteLaw.prob roundLaw
  rw [FiniteLaw.expect_bind]
  simp only [FiniteLaw.expect_map]
  change μ.expect (fun G => (PhysicalBatchLaw.law
    (balancedActions (heavyActions (graphActions G) (H G)) Δ)
    (balancedConflicts (heavyActions (graphActions G) (H G)) Δ)
    (2*h*g) (q G) hp0 hpp1 (hq0 G) (hq1 G)).prob
      (fun Z => mass g s.1+4/(g*b) < mass g (next Δ s.1 (roundErased s.1 G (H G) Z) (roundOpened s.1 G (H G) Z)))) ≤ _
  rw [← μ.expect_const (96*(Δ:ℝ)^2*b/((2*h*g)*φ^2*g))]
  apply μ.expect_mono_support
  intro G hgG
  exact physical_count_tail s.1 G hg hg1 (by positivity) hφ hφ1 hb hunit (hG G hgG) hp1 hsmall

end MetricKMedian.CopyState
end
end

end OAI
