import Mathlib
import OAI.Combinatorics.KMedian.Probability.ProbabilitySupport
import OAI.Combinatorics.KMedian.Process.ConditionalRoundDrift
import OAI.Combinatorics.KMedian.Process.TaperGraph

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch Analytic
variable {F J X : Type*} [Fintype F] [DecidableEq F] [Fintype J] [DecidableEq J]
variable [PseudoMetricSpace X] {Δ : ℕ}

abbrev State (F J : Type*) (Δ : ℕ) := Finset (Copy (F := F) Δ) × (J → Finset (Copy (F := F) Δ))

noncomputable def advance (s : State F J Δ) (G : s.1 → Finset s.1) (H : Finset s.1)
    (Z : Finset (HeavyAction (graphActions G) H)) (x g : ℝ)
    (d : J → F → ℝ) : State F J Δ :=
  (next Δ s.1 (roundErased s.1 G H Z) (roundOpened s.1 G H Z),
    fun j => roundAlive s.1 (s.2 j) G H Z x g (d j))

noncomputable def statePotential (R : J → ℝ) (d : J → F → ℝ) (x g : ℝ)
    (s : State F J Δ) (j : J) : ℝ :=
  potential x g (fun i => d j i.1) (s.2 j) (GroupCap.cap (R j) (d j) (integral Δ s.1))

noncomputable def roundLaw (s : State F J Δ) (μ : FiniteLaw (s.1 → Finset s.1))
    (H : (s.1 → Finset s.1) → Finset s.1)
    (q : (G : s.1 → Finset s.1) → HeavyAction (graphActions G) (H G) → ℝ)
    (x g h : ℝ) (d : J → F → ℝ)
    (hp0 : 0 ≤ 2*h*g) (hp1 : 2*h*g ≤ 1)
    (hq0 : ∀ G e, 0 ≤ q G e) (hq1 : ∀ G e, q G e ≤ 1) : FiniteLaw (State F J Δ) := by
  classical
  exact μ.bind fun G =>
    (PhysicalBatchLaw.law (balancedActions (heavyActions (graphActions G) (H G)) Δ)
      (balancedConflicts (heavyActions (graphActions G) (H G)) Δ) (2*h*g) (q G)
        hp0 hp1 (hq0 G) (hq1 G)).map (fun Z => advance s G (H G) Z x g d)

 theorem roundLaw_property (s : State F J Δ) (μ : FiniteLaw (s.1 → Finset s.1))
    (H : (s.1 → Finset s.1) → Finset s.1)
    (q : (G : s.1 → Finset s.1) → HeavyAction (graphActions G) (H G) → ℝ)
    (x g h : ℝ) (d : J → F → ℝ) (hp0 : 0 ≤ 2*h*g) (hp1 : 2*h*g ≤ 1)
    (hq0 : ∀ G e, 0 ≤ q G e) (hq1 : ∀ G e, q G e ≤ 1)
    (P : State F J Δ → Prop)
    (hP : ∀ G, 0 < μ.weight G → ∀ Z, P (advance s G (H G) Z x g d)) :
    ∀ t, 0 < (roundLaw s μ H q x g h d hp0 hp1 hq0 hq1).weight t → P t := by
  classical
  apply μ.property_bind
  intro G hG
  apply FiniteLaw.property_map
  exact fun Z _ => hP G hG Z

theorem roundLaw_drift (s : State F J Δ) (S₀ : J → Finset (Copy (F := F) Δ))
    (R : J → ℝ) (location : F → X) (client : J → X)
    {P x g h φ ζ : ℝ}
    (D : Taper.GraphData Δ g P (fun i : s.1 => location i.val.1) (own Δ s.1))
    (μ : FiniteLaw (s.1 → Finset s.1))
    (H : (s.1 → Finset s.1) → Finset s.1)
    (q : (G : s.1 → Finset s.1) → HeavyAction (graphActions G) (H G) → ℝ)
    (hg : 0 < g) (hg1 : g ≤ 1) (hunit : g*(Δ:ℝ)=1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hp1 : 2*h*g ≤ 1)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hq0 : ∀ G e, 0 ≤ q G e) (hq1 : ∀ G e, q G e ≤ 1)
    (hq : ∀ G e, 2*h*g ≤ q G e ∧ q G e ≤ (1+φ)*(2*h*g))
    (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction g)
    (hP0 : 0 ≤ P) (hP1 : P ≤ 1/2) (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1/4)
    (he : |P-Analytic.P x| ≤ ζ) (hgood : ∀ G, 0 < μ.weight G → D.Good G)
    (hfirst : ∀ a i, μ.expect (fun G => GraphLaw.edge G a i)=D.marginal a i)
    (hpair : ∀ a b i j, i ≠ j → μ.expect (fun G => GraphLaw.edge G a i*GraphLaw.edge G b j)=
      D.marginal a i*D.marginal b j)
    (hactive : ∀ j, s.2 j ⊆ s.1) (hS : ∀ j, s.2 j ⊆ S₀ j)
    (hm₀ : ∀ j, mass g (S₀ j)=1) (hR0 : ∀ j, 0 ≤ R j)
    (hdR : ∀ j i, i ∈ S₀ j → dist (client j) (location i.1) ≤ R j)
    (hR : ∀ j, ∃ i ∈ S₀ j, R j=dist (client j) (location i.1)) (j : J) :
    (roundLaw s μ H q x g h (fun j f => dist (client j) (location f))
      (by positivity) hp1 hq0 hq1).expect
      (fun t => statePotential R (fun j f => dist (client j) (location f)) (x*Real.exp (-h)) g t j) ≤
    statePotential R (fun j f => dist (client j) (location f)) x g s j+
      h*(g+12*ζ)*PhysicalPotential.cost g (fun i => dist (client j) (location i.1)) (s.2 j)+
      batchConstant Δ*h*(φ+h)*R j := by
  classical
  let d : J → F → ℝ := fun j f => dist (client j) (location f)
  let V := PhysicalPotential.cost g (fun i => d j i.1) (s.2 j)
  let b := GroupCap.cap (R j) (d j) (integral Δ s.1)
  let f := statePotential R d x g s j
  let a := timeRate x (mass g (s.2 j))*V
  let chargeSum := fun G => g*∑ e ∈ relevant (graphActions G) (localSet s.1 (s.2 j)),
    charge (graphActions G) x g b (fun i => d j i.val.1) (localSet s.1 (s.2 j)) e
  have hcond : ∀ G, 0 < μ.weight G →
      (PhysicalBatchLaw.law (balancedActions (heavyActions (graphActions G) (H G)) Δ)
        (balancedConflicts (heavyActions (graphActions G) (H G)) Δ) (2*h*g) (q G)
        (by positivity) hp1 (hq0 G) (hq1 G)).expect
        (fun Z => statePotential R d (x*Real.exp (-h)) g (advance s G (H G) Z x g d) j) ≤
      f+h*(a+chargeSum G)+batchConstant Δ*h*(φ+h)*R j := by
    intro G hG
    have hh := conditional_round_drift s.1 (s.2 j) (S₀ j) G (H G) (q G) (d j)
      (hgood G hG).1 (hgood G hG).2.1 hg hg1 hunit hx0 hx1 hh0 hh1 hp1 hφ0 hφ1
      (hq0 G) (hq1 G) (hq G) hsmall (hactive j) (hS j) (hm₀ j) (fun _ => dist_nonneg)
      (hR0 j) (hdR j) (hR j)
    dsimp only at hh
    rw [FiniteLaw.expect_sub,FiniteLaw.expect_const] at hh
    change _ - f ≤ h*(a+chargeSum G)+_ at hh
    change _ ≤ f+h*(a+chargeSum G)+_
    dsimp only [statePotential,advance]
    linarith only [hh]
  have hav := μ.expect_mono_support hcond
  simp_rw [FiniteLaw.expect_add,FiniteLaw.expect_const,FiniteLaw.expect_mul] at hav
  rw [FiniteLaw.expect_add,FiniteLaw.expect_const] at hav
  have hy : mass g (localSet s.1 (s.2 j)) ≤ 1 := by
    rw [localSet_mass _ _ (hactive j)]
    exact (mass_mono hg.le (hS j)).trans_eq (hm₀ j)
  have hgen := D.drift (b := b) μ (client j) (localSet s.1 (s.2 j)) hg hunit hP0 hP1
    hx0 hx1 hy hζ0 hζ1 he hfirst hpair
  rw [localSet_mass _ _ (hactive j),localSet_cost _ _ (hactive j) g
    (fun i => dist (client j) (location i.1))] at hgen
  change a+μ.expect chargeSum ≤ B x*g*V+12*ζ*V at hgen
  have hVB := mul_le_mul_of_nonneg_right (B_le_one hx0)
    (mul_nonneg hg.le (cost_nonneg hg.le (fun _ _ => dist_nonneg) : 0 ≤ V))
  have hgen' : a+μ.expect chargeSum ≤ (g+12*ζ)*V := by
    nlinarith only [hgen,hVB]
  have hmul := mul_le_mul_of_nonneg_left hgen' hh0
  rw [roundLaw,FiniteLaw.expect_bind]
  simp_rw [FiniteLaw.expect_map]
  change _ ≤ f+h*(g+12*ζ)*V+_
  linarith only [hav,hmul]

end MetricKMedian.CopyState
end
end

end OAI
