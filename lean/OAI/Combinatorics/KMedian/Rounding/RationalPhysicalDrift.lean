import Mathlib
import OAI.Combinatorics.KMedian.Process.PhysicalState
import OAI.Combinatorics.KMedian.Rounding.RationalPhysicalGraphInstance
import OAI.Combinatorics.KMedian.Rounding.RationalPhysicalReplay
import OAI.Combinatorics.KMedian.Sparse.SparseConditionalRoundDrift

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential FixedBatch Analytic CopyState
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {Δ : ℕ}
local instance rationalPhysicalDriftCopyOrder : LinearOrder (CopyState.Copy (F := F) Δ) := copyOrder

theorem step_drift (d₀ : F → F → ℚ) (location : F → X) (client : X)
    (hd₀ : ∀ i j, dist (location i) (location j)=(d₀ i j:ℝ))
    (g β p φ P : ℚ) (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (s : State F Δ g β) (S S₀ : Finset (Copy (F := F) Δ))
    {x h R ζ : ℝ} (hprob : (p:ℝ)=2*h*(g:ℝ))
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2) (hA : 1 ≤ mass (g:ℝ) s.1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hφ1 : (φ:ℝ) ≤ 1)
    (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction (g:ℝ))
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1/4) (he : |(P:ℝ)-Analytic.P x| ≤ ζ)
    (hactive : S ⊆ s.1) (hS : S ⊆ S₀) (hm₀ : mass (g:ℝ) S₀=1)
    (hR0 : 0 ≤ R) (hdR : ∀ i ∈ S₀, dist client (location i.1) ≤ R)
    (hR : ∃ i ∈ S₀, R=dist client (location i.1)) :
    (step d₀ g β p φ P hp hφ hupper s).expectation (fun t =>
      potential (x*Real.exp (-h)) (g:ℝ) (fun i => dist client (location i.1))
        (labels g β x (fun (_ : Unit) f => dist client (location f)) t (fun _ => S) ())
        (GroupCap.cap R (fun f => dist client (location f)) (integral Δ t.1))) ≤
      potential x (g:ℝ) (fun i => dist client (location i.1)) S
        (GroupCap.cap R (fun f => dist client (location f)) (integral Δ s.1))+
      h*((g:ℝ)+12*ζ)*PhysicalPotential.cost (g:ℝ) (fun i => dist client (location i.1)) S+
      batchConstant Δ*h*((φ:ℝ)+h)*R := by
  let d := fun f => dist client (location f)
  let V := PhysicalPotential.cost (g:ℝ) (fun i => d i.1) S
  let b := GroupCap.cap R d (integral Δ s.1)
  let f := potential x (g:ℝ) (fun i => d i.1) S b
  let a := timeRate x (mass (g:ℝ) S)*V
  let μ := graphLaw d₀ g P s.1
  let chargeSum := fun G => (g:ℝ)*∑ e ∈ relevant (graphActions G) (localSet s.1 S),
    charge (graphActions G) x (g:ℝ) b (fun i => d i.val.1) (localSet s.1 S) e
  let ν : (G : s.1 → Finset s.1) → SparseIntegerLaw
      (Finset (HeavyAction (RationalBatchData.graph G)
        (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β))) :=
    fun G => RationalBatchData.proposal G Δ g β p φ hp hφ hupper
    (RationalBatchData.enumeration (RationalBatchData.graph G)
      (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β))
  let v := fun (G : s.1 → Finset s.1) Z =>
    potential (x*Real.exp (-h)) (g:ℝ) (fun i => d i.1)
      (roundAlive s.1 S G (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β) Z x (g:ℝ) d)
      (GroupCap.cap R d (integral Δ (next Δ s.1
        (roundErased s.1 G (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β) Z)
        (roundOpened s.1 G (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β) Z))))
  obtain ⟨D,hgood,hfirst,hpair⟩ := graph_data d₀ location hd₀ g P s.1 hg hunit hP hP1 hA
  have hcond : ∀ G, 0 < μ.real.weight G →
      (ν G).real.expect (v G) ≤ f+h*(a+chargeSum G)+batchConstant Δ*h*((φ:ℝ)+h)*R := by
    intro G hG
    have hh := rational_conditional_round_drift s.1 S S₀ G g β p φ hp hφ hupper
      (RationalBatchData.enumeration (RationalBatchData.graph G)
        (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β)) d hprob
      (hgood G hG).1 (hgood G hG).2.1 hg hg1 hunit hx0 hx1 hh0 hh1 hφ1 hsmall
      hactive hS hm₀ (fun _ => dist_nonneg) hR0 hdR hR
    dsimp only at hh
    rw [FiniteLaw.expect_sub,FiniteLaw.expect_const] at hh
    change (ν G).real.expect (v G)-f ≤ h*(a+chargeSum G)+_ at hh
    linarith only [hh]
  have hav := μ.real.expect_mono_support hcond
  simp_rw [FiniteLaw.expect_add,FiniteLaw.expect_const,FiniteLaw.expect_mul] at hav
  rw [FiniteLaw.expect_add,FiniteLaw.expect_const] at hav
  have hy : mass (g:ℝ) (localSet s.1 S) ≤ 1 := by
    rw [localSet_mass _ _ hactive]
    exact (mass_mono hg.le hS).trans_eq hm₀
  have hgen := D.drift (b := b) μ.real client (localSet s.1 S) hg hunit hP.le hP1
    hx0 hx1 hy hζ0 hζ1 he hfirst hpair
  rw [localSet_mass _ _ hactive,localSet_cost _ _ hactive (g:ℝ)
    (fun i => dist client (location i.1))] at hgen
  change a+μ.real.expect chargeSum ≤ B x*(g:ℝ)*V+12*ζ*V at hgen
  have hVB := mul_le_mul_of_nonneg_right (B_le_one hx0)
    (mul_nonneg hg.le (cost_nonneg hg.le (fun _ _ => dist_nonneg) : 0 ≤ V))
  have hgen' : a+μ.real.expect chargeSum ≤ ((g:ℝ)+12*ζ)*V := by
    nlinarith only [hgen,hVB]
  have hmul := mul_le_mul_of_nonneg_left hgen' hh0
  have hfinish : μ.real.expect (fun G => (ν G).real.expect (v G)) ≤
      f+h*((g:ℝ)+12*ζ)*V+batchConstant Δ*h*((φ:ℝ)+h)*R := by
    linarith only [hav,hmul]
  rw [step_expectation]
  change μ.expectation (fun G => (ν G).expectation (v G)) ≤
    f+h*((g:ℝ)+12*ζ)*V+batchConstant Δ*h*((φ:ℝ)+h)*R
  rw [← SparseIntegerLaw.real_expect_all]
  have hpoint : ∀ G, (ν G).expectation (v G)=(ν G).real.expect (v G) :=
    fun G => (SparseIntegerLaw.real_expect_all (ν G) (v G)).symm
  simp_rw [hpoint]
  exact hfinish

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
