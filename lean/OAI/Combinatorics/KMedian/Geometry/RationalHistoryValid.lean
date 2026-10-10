import Mathlib
import OAI.Combinatorics.KMedian.Process.StateInvariants
import OAI.Combinatorics.KMedian.Rounding.RationalPhysicalGraph
import OAI.Combinatorics.KMedian.Rounding.RationalPhysicalInvariant
import OAI.Combinatorics.KMedian.Rounding.RationalPhysicalReplay

namespace OAI


                                            
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F J X : Type} [LinearOrder F] [Fintype F] [Fintype J] [DecidableEq J]
  [PseudoMetricSpace X] {Δ : ℕ}
local instance rationalHistoryValidCopyOrder : LinearOrder (CopyState.Copy (F := F) Δ) := copyOrder

omit [Fintype F] [Fintype J] [DecidableEq J] in

theorem graph_data_all (d : F → F → ℚ) (location : F → X)
    (hd : ∀ i j, dist (location i) (location j)=(d i j:ℝ))
    (g P : ℚ) (A : Finset (CopyState.Copy (F := F) Δ))
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2) (hA : 1 ≤ mass (g:ℝ) A) :
    ∃ D : Taper.GraphData Δ (g:ℝ) (P:ℝ) (fun i : A => location i.val.1) (CopyState.own Δ A),
      ∀ a : Fin (graphLaw d g P A).length, D.Good (graphLaw d g P A).states[a.val] := by
  let dA : A → A → ℚ := fun i j => d i.val.1 j.val.1
  have hd0 : ∀ i j, 0 ≤ dA i j := by
    intro i j
    have hh : 0 ≤ (dA i j:ℝ) := by rw [← hd]; exact dist_nonneg
    exact_mod_cast hh
  have hown : ∀ i j, j∈own A i → dA i j=0 := by
    intro i j hj
    have he : j.val.1=i.val.1 := (mem_filter.mp hj).2
    have hh : (dA i j:ℝ)=0 := by rw [← hd,he,dist_self]
    exact_mod_cast hh
  have htotal : 1 ≤ ∑ _i : A, (g:ℝ) := by
    simpa only [sum_const,card_univ,Fintype.card_coe,nsmul_eq_mul,mass,mul_comm] using hA
  let D := Taper.physicalGraphData Δ g P dA (fun i : A => location i.val.1) (own A)
    hg hunit hP hP1 hd0 (fun i j => hd _ _) htotal hown (own_card A)
  let q := fun h i : A => Taper.sourceMarginals g P (dA i) (own A i) Δ h
  have hall := fun i => Taper.rational_data g P (dA i) (own A i) Δ hg hunit hP hP1
    (hd0 i) htotal (hown i) (own_card A i)
  have hq : ∀ h i, 0 ≤ q h i ∧ q h i ≤ 1 := fun h i => ⟨(hall i).2.1 h,(hall i).2.2.1 h⟩
  have hs : ∀ i, (∑ h : Fin A.card, q (enumeration A h) i)=(Δ:ℚ) := by
    intro i
    rw [(enumeration A).sum_comp (fun h => q h i)]
    exact (hall i).2.2.2.2.1
  refine ⟨D,fun a => ⟨?_,?_,?_⟩⟩
  · exact SparseEnumeratedGraph.columns_card (enumeration A) q Δ hq hs a
  · intro i h he
    exact (SparseEnumeratedGraph.fixed (enumeration A) q Δ hq hs a h i).1
      ((hall i).2.2.2.2.2.1 h he)
  · intro h i hedge
    change (0:ℝ)<(q h i:ℝ)
    have hn : q h i≠0 := fun he =>
      (SparseEnumeratedGraph.fixed (enumeration A) q Δ hq hs a h i).2 he hedge
    exact_mod_cast lt_of_le_of_ne (hq h i).1 (Ne.symm hn)

omit [Fintype J] [DecidableEq J] in
theorem histories_valid (d₀ : F → F → ℚ) (location : F → X) (client : J → X)
    (hd₀ : ∀ i j, dist (location i) (location j)=(d₀ i j:ℝ))
    (g β p φ : ℚ) (P : ℕ → ℚ) (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A : Finset (CopyState.Copy (F := F) Δ)) (S₀ : J → Finset (CopyState.Copy (F := F) Δ))
    (R : J → ℝ) (T : ℕ) (x : ℕ → ℝ)
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : ∀ t<T, 0<(P t:ℝ)) (hP1 : ∀ t<T, (P t:ℝ)≤1/2)
    (hA : 1 ≤ mass (g:ℝ) A) (hSA : ∀ j, S₀ j⊆A)
    (hR : ∀ j, 0≤R j) (hm : ∀ j, mass (g:ℝ) (S₀ j)=1)
    (hdR : ∀ j i, i∈S₀ j → dist (client j) (location i.1)≤R j)
    (a : Fin (histories d₀ g β p φ P hp hφ hupper A T).length) :
    let z := (histories d₀ g β p φ P hp hφ hupper A T).states[a.val];
    CopyState.Valid (g:ℝ) location client R S₀
      (z.1.1, replay g β x (fun j f => dist (client j) (location f)) S₀ z) := by
  let d := fun j f => dist (client j) (location f)
  let κ := fun t => step (Δ:=Δ) d₀ g β p φ (P t) hp hφ hupper
  have hh : ∀ t≤T, ∀ a : Fin (SparseHistories.tree κ (A,none) t).length,
      let z := (SparseHistories.tree κ (A,none) t).states[a.val];
      CopyState.Valid (g:ℝ) location client R S₀ (z.1.1,replay g β x d S₀ z) := by
    intro t
    induction t with
    | zero =>
      intro _ a
      simpa only [SparseHistories.tree,SparseIntegerLaw.dirac,Vector.getElem_replicate,
        replay,replayList,labels] using CopyState.valid_initial A S₀ (g:ℝ) location client R hA hSA
    | succ t ih =>
      intro ht
      simp only [SparseHistories.tree]
      apply SparseIntegerLaw.bindIndexed_property _ _ (fun z =>
        CopyState.Valid (g:ℝ) location client R S₀ (z.1.1,replay g β x d S₀ z))
      intro b c
      let z := (SparseHistories.tree κ (A,none) t).states[b.val]
      have hv := ih (by omega) b
      have he := SparseIntegerLaw.map_states (κ t z.1) (SparseHistories.extend z) c
      change (SparseHistories.branch (κ t) z).states[c.val]=_ at he
      rw [he]
      rw [replay_extend]
      obtain ⟨D,hD⟩ := graph_data_all d₀ location hd₀ g (P t) z.1.1 hg hunit
        (hP t (by omega)) (hP1 t (by omega)) hv.1
      have hprop := RationalBatchData.events_property (graphLaw d₀ g (P t) z.1.1) Δ g β p φ
        hp hφ hupper (fun e => CopyState.Valid (g:ℝ) location client R S₀
          ((updateEvent g β z.1.1 e).1,
            labels g β (x z.2.length) d (updateEvent g β z.1.1 e) (replay g β x d S₀ z)))
        (fun i Z => by
          exact CopyState.valid_advance (z.1.1,replay g β x d S₀ z) S₀ location client R D
            (graphLaw d₀ g (P t) z.1.1).states[i.val]
            (RationalBatchData.heavySet
              (RationalBatchData.graphMass (graphLaw d₀ g (P t) z.1.1).states[i.val] g) β)
            Z (x z.2.length) hg.le hunit (hP t (by omega)) (hP1 t (by omega)) hR hm hdR (hD i) hv)
      have hevent := SparseIntegerLaw.map_states
        (RationalBatchData.events (graphLaw d₀ g (P t) z.1.1) Δ g β p φ hp hφ hupper)
        (updateEvent g β z.1.1) c
      change (κ t z.1).states[c.val]=_ at hevent
      simpa only [SparseHistories.extend,hevent] using hprop c
  exact hh T le_rfl a

end MetricKMedian.RationalPhysicalKernel
end

end OAI
