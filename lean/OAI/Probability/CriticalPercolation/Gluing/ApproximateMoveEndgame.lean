import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.CoordinateScheme
import OAI.Probability.CriticalPercolation.Gluing.CorridorScaleChoice
import OAI.Probability.CriticalPercolation.Gluing.CoordinateProspective

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open Corridor

variable {V E : Type*} (G : BondGraph V E)

lemma coordinateMove_sub_const (t z : V → ℝ) (a b : ℝ) (m : ℕ) (e : ℝ) (y : V) (s : ℝ) :
    G.coordinateMove (fun x => t x-a) (fun x => z x-b) m e y s=G.coordinateMove t z m e y s := by
  unfold coordinateMove
  simp only [sub_sub_sub_cancel_right]
  have ht : ∀ x, t x-a-(t y-a+1)=t x-(t y+1) := by intro x; ring
  have hz : ∀ x, z x-b-(z y-b+s)=z x-(z y+s) := by intro x; ring
  simp only [ht,hz]

theorem approximate_moves_contradiction
    (hconnected : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : 0<(G.criticalProbability : ℝ)) (hpc1 : (G.criticalProbability : ℝ)<1)
    (hmoves : ∀ e eta : ℝ, 0<e → e<1/10 → 0<eta → eta<1/10 →
      ∃ m : ℕ, ∀ rho : ℝ, 0<rho → ∃ t z : V → ℝ, ∃ p : unitInterval,
        (G.criticalProbability : ℝ)/2≤p ∧ p<G.criticalProbability ∧
        (∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v|≤rho) ∧
        (∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v|≤rho) ∧
        ∀ y s, |s|=1 → 1-eta≤(BernoulliProduct.law (fun _ : E => p)).real
          (G.coordinateMove t z m e y s)) : False := by
  let := G.countable_vertices hconnected hl
  let := G.countable_bonds hconnected hl
  obtain ⟨o⟩ := hconnected.nonempty
  obtain ⟨m,hm⟩ := hmoves ScaleChoice.e ScaleChoice.eta ScaleChoice.e_pos ScaleChoice.e_lt
    ScaleChoice.eta_pos ScaleChoice.eta_lt
  obtain ⟨D,_hDpos,hD⟩ := G.uniform_incident_bound hq
  obtain ⟨M,hM⟩ := G.uniform_ball_bound hq (4*m+2)
  obtain ⟨VM,hVM⟩ := G.uniform_ball_bound hq m
  obtain ⟨k,R,hk,hR,hRlarge⟩ := ScaleChoice.trial_scales (G.criticalProbability : ℝ) D (M+1) VM m
  obtain ⟨rho,hrho,hrhosmall⟩ := ScaleChoice.mesh R m
  obtain ⟨t,z,p,hpl,hpu,ht,hz,hmv⟩ := hm rho hrho
  let C : CoordinateData V E := {
    graph := G, origin := o, time := fun x => t x-t o, height := fun x => z x-z o,
    J := ScaleChoice.J, L := ScaleChoice.L, R := R, m := m, D := D, k := k,
    M := M+1, VM := VM, e := ScaleChoice.e, rho := rho, kappa := ScaleChoice.kappa,
    eta := ScaleChoice.eta, delta := ScaleChoice.delta, contour := ScaleChoice.contour,
    pc := G.criticalProbability, p := p }
  have hb : C.Bounds := {
    connected := hconnected
    locallyFinite := hl
    time_origin := sub_self _
    height_origin := sub_self _
    time_step := fun {_ _} h => by simpa only [C,sub_sub_sub_cancel_right] using ht h
    height_step := fun {_ _} h => by simpa only [C,sub_sub_sub_cancel_right] using hz h
    J_lower := ScaleChoice.J_lower
    L_lower := ScaleChoice.L_lower
    e_pos := ScaleChoice.e_pos
    rho_nonneg := hrho.le
    e_small := ScaleChoice.e_small
    rho_small := hrhosmall
    R_gt := hR
    pc_pos := hpc
    pc_lt := hpc1
    p_lower := hpl
    p_upper := hpu.le
    degree := hD
    M_pos := Nat.succ_pos M
    M_bound := fun v => (hM v).trans (Nat.le_succ M)
    VM_bound := hVM
    kappa_pos := ScaleChoice.kappa_pos
    kappa_le := ScaleChoice.kappa_le
    eta_nonneg := ScaleChoice.eta_pos.le
    eta_small := ScaleChoice.eta_small
    k_large := hk.le
    R_large := hRlarge
    delta_pos := ScaleChoice.delta_pos
    root_error := ScaleChoice.root_error
    contour_nonneg := ScaleChoice.contour_nonneg
    contour_small := ScaleChoice.contour_small
    test_error := ScaleChoice.test_error }
  apply C.moves_impossible_below_criticality hb hpu
  intro y s hs
  change 1-ScaleChoice.eta≤(BernoulliProduct.law (fun _ : E => p)).real
    (G.coordinateMove (fun x => t x-t o) (fun x => z x-z o) m ScaleChoice.e y s)
  rw [coordinateMove_sub_const]
  exact hmv y s hs

end CriticalPercolation.BondGraph
end
end
end

end OAI
