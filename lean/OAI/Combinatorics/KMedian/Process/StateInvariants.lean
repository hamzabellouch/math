import Mathlib
import OAI.Combinatorics.KMedian.Process.ErasureDecay
import OAI.Combinatorics.KMedian.Process.PhysicalState
import OAI.Combinatorics.KMedian.Process.BackupInvariant

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch
variable {F J X : Type*} [Fintype F] [DecidableEq F] [Fintype J] [DecidableEq J]
variable [PseudoMetricSpace X] {Δ : ℕ}

def Valid (g : ℝ) (location : F → X) (client : J → X) (R : J → ℝ)
    (S₀ : J → Finset (Copy (F := F) Δ)) (s : State F J Δ) : Prop :=
  1 ≤ mass g s.1 ∧
    (∀ j, s.2 j ⊆ s.1) ∧ (∀ j, s.2 j ⊆ S₀ j) ∧
    ∀ j, (¬∃ f ∈ integral Δ s.1, dist (client j) (location f) ≤ 5*R j) → S₀ j ⊆ s.1

omit [Fintype J] [DecidableEq J] in
 theorem valid_initial (A : Finset (Copy (F := F) Δ)) (S₀ : J → Finset (Copy (F := F) Δ))
    (g : ℝ) (location : F → X) (client : J → X) (R : J → ℝ)
    (hA : 1 ≤ mass g A) (hS : ∀ j, S₀ j ⊆ A) : Valid g location client R S₀ (A,S₀) :=
  ⟨hA,hS,fun _ => Subset.rfl,fun j _ => hS j⟩

omit [Fintype J] [DecidableEq J] in
 theorem valid_advance (s : State F J Δ) (S₀ : J → Finset (Copy (F := F) Δ))
    (location : F → X) (client : J → X) (R : J → ℝ) {g P : ℝ}
    (D : Taper.GraphData Δ g P (fun i : s.1 => location i.val.1) (own Δ s.1))
    (G : s.1 → Finset s.1) (H : Finset s.1) (Z : Finset (HeavyAction (graphActions G) H))
    (x : ℝ) (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) (hP : 0 < P) (hP1 : P ≤ 1/2)
    (hR : ∀ j, 0 ≤ R j) (hm : ∀ j, mass g (S₀ j)=1)
    (hd : ∀ j i, i ∈ S₀ j → dist (client j) (location i.1) ≤ R j)
    (hgood : D.Good G) (hv : Valid g location client R S₀ s) :
    Valid g location client R S₀ (advance s G H Z x g (fun j f => dist (client j) (location f))) := by
  dsimp only [Valid, advance]
  refine ⟨round_mass_at_least_one s.1 G H Z hg hunit hv.1,?_,?_,?_⟩
  · intro j
    exact roundAlive_active s.1 (s.2 j) G H Z x g _
  · intro j
    exact (roundAlive_subset s.1 (s.2 j) G H Z x g _).trans (hv.2.2.1 j)
  · intro j
    exact round_backup s.1 (S₀ j) location (client j) D G H Z hg hP hP1 (hR j) (hm j)
      (hd j) hgood (hv.2.2.2 j)

 theorem roundLaw_valid (s : State F J Δ) (S₀ : J → Finset (Copy (F := F) Δ))
    (location : F → X) (client : J → X) (R : J → ℝ) {g P : ℝ}
    (D : Taper.GraphData Δ g P (fun i : s.1 => location i.val.1) (own Δ s.1))
    (μ : FiniteLaw (s.1 → Finset s.1)) (H : (s.1 → Finset s.1) → Finset s.1)
    (q : (G : s.1 → Finset s.1) → HeavyAction (graphActions G) (H G) → ℝ)
    (x h : ℝ) (hp0 : 0 ≤ 2*h*g) (hp1 : 2*h*g ≤ 1)
    (hq0 : ∀ G e, 0 ≤ q G e) (hq1 : ∀ G e, q G e ≤ 1)
    (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) (hP : 0 < P) (hP1 : P ≤ 1/2)
    (hR : ∀ j, 0 ≤ R j) (hm : ∀ j, mass g (S₀ j)=1)
    (hd : ∀ j i, i ∈ S₀ j → dist (client j) (location i.1) ≤ R j)
    (hgood : ∀ G, 0 < μ.weight G → D.Good G) (hv : Valid g location client R S₀ s) :
    ∀ t, 0 < (roundLaw s μ H q x g h (fun j f => dist (client j) (location f))
      hp0 hp1 hq0 hq1).weight t → Valid g location client R S₀ t := by
  apply roundLaw_property
  exact fun G hG Z => valid_advance s S₀ location client R D G (H G) Z x hg hunit hP hP1 hR hm hd
    (hgood G hG) hv

 theorem roundLaw_survival (s : State F J Δ) (μ : FiniteLaw (s.1 → Finset s.1))
    (H : (s.1 → Finset s.1) → Finset s.1)
    (q : (G : s.1 → Finset s.1) → HeavyAction (graphActions G) (H G) → ℝ)
    (x g h : ℝ) (d : J → F → ℝ)
    (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) (hh : 0 ≤ h) (hp1 : 2*h*g ≤ 1)
    (hq0 : ∀ G e, 0 ≤ q G e) (hq1 : ∀ G e, q G e ≤ 1)
    (hq : ∀ G e, 2*h*g ≤ q G e ∧ q G e ≤ 2*(2*h*g))
    (hsmall : (2*h*g)*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ)) ≤ 1)
    (hgood : ∀ G, 0 < μ.weight G → ∀ i, (G i).card=Δ)
    (hactive : ∀ j, s.2 j ⊆ s.1) (j : J) :
    (roundLaw s μ H q x g h d (by positivity) hp1 hq0 hq1).expect
      (fun t => mass g (t.2 j)) ≤ (1-h/2)*mass g (s.2 j) := by
  classical
  rw [roundLaw,FiniteLaw.expect_bind]
  simp_rw [FiniteLaw.expect_map]
  apply (μ.expect_mono_support (fun G hG =>
    conditional_round_survival s.1 (s.2 j) G (H G) (q G) (d j) (hgood G hG)
      hg hunit hh hp1 (hq0 G) (hq1 G) (hq G) hsmall (hactive j))).trans_eq
  exact μ.expect_const _

end MetricKMedian.CopyState
end
end

end OAI
