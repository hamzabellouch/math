import Mathlib
import OAI.Probability.CriticalPercolation.Gluing.MoveExit
import OAI.Probability.CriticalPercolation.Gluing.StripMoves
import OAI.Probability.CriticalPercolation.GraphGeometry.StripContinuity
import OAI.Probability.CriticalPercolation.GraphGeometry.StripLinear

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma exists_strip_scale (B K d : ℝ) (hd : 0<d) :
    ∃ U : ℝ, 0<U ∧ B<U ∧ K/U<d := by
  obtain ⟨U,hU⟩ := exists_gt (max 0 (max B (K/d)))
  have hU0 : 0<U := (le_max_left _ _).trans_lt hU
  have hBU : B<U := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hU
  have hKU : K/d<U := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hU
  exact ⟨U,hU0,hBU,(div_lt_iff₀ hU0).mpr (by nlinarith [(div_lt_iff₀ hd).mp hKU])⟩

theorem strip_origin_moves [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (u v : V → ℝ) (o : V) (D : ℝ) (p : unitInterval)
    (hD : 0≤D) (huo : u o=0) (hvo : v o=0)
    (hu : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |u x-u y|≤D)
    (hv : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |v x-v y|≤D)
    (hstrip : 0<(BernoulliProduct.law (fun _ : E => p)) (G.someStripPercolates v))
    (hdir : ∀ᵐ ω ∂BernoulliProduct.law (fun _ : E => p),
      ∀ a, (G.cluster ω a).Infinite → ∀ n : ℕ, ∃ x∈G.cluster ω a, (n : ℝ)<v x)
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂BernoulliProduct.law (fun _ : E => p), ∀ a,
      (G.cluster (ω∩G.inducedEdges {x | |u x|≤U ∧ |v x|≤W}) a).Finite)
    (eps eta : ℝ) (heps : 0<eps) (heps' : eps<1/10) (heta : 0<eta) :
    ∃ m : ℕ, ∀ rho : ℝ, 0<rho → ∃ U Q : ℝ, ∃ a b : Bool,
      0<U ∧ 0<Q ∧
      (∀ ⦃x y⦄, G.fullGraph.Adj x y →
        |stripTime u v U Q a b x-stripTime u v U Q a b y|≤rho) ∧
      (∀ ⦃x y⦄, G.fullGraph.Adj x y →
        |stripHeight u v U Q a b x-stripHeight u v U Q a b y|≤rho) ∧
      ∀ s : Bool, 1-eta<(BernoulliProduct.law (fun _ : E => p)).real
        (G.boxMove (stripTime u v U Q a b) (stripHeight u v U Q a b) m (eps/8) 30 o
          (Corridor.sign s)) := by
  obtain ⟨m,W,hW,hseed,hprob⟩ := G.exists_seed_strip_probability hc hl v o
    (fun _ : E => p) hstrip ((eta/30)^2) (sq_pos_of_pos (by linarith))
  refine ⟨m,?_⟩
  intro rho hrho
  let d := min (eps/1000) (rho/2)
  have hd : 0<d := lt_min (by linarith) (by linarith)
  have hde : d≤eps/1000 := min_le_left _ _
  have hdr : d≤rho/2 := min_le_right _ _
  obtain ⟨Q,hQ,hWQ,hKQ⟩ := exists_strip_scale W (max W D) d hd
  have hDQ : D/Q≤d := ((div_le_div_of_nonneg_right (le_max_right W D) hQ.le).trans hKQ.le)
  have hWQ' : W/Q≤d := ((div_le_div_of_nonneg_right (le_max_left W D) hQ.le).trans hKQ.le)
  obtain ⟨M,hMprob⟩ := G.exists_transverse_exit_probability u v (G.vertexBall o m) W Q D
    (fun _ : E => p) (1-(eta/30)^2) hD hv (fun a ha => (hseed a ha).trans_lt hWQ) hdir hprob
  obtain ⟨K,hK⟩ := ((G.vertexBall_finite hl o m).image (fun x => |u x|)).bddAbove
  obtain ⟨U,hU,hKU,hMU⟩ := exists_strip_scale K (max (M : ℝ) D) d hd
  have hDU : D/U≤d := ((div_le_div_of_nonneg_right (le_max_right (M : ℝ) D) hU.le).trans hMU.le)
  have hMU' : (M : ℝ)/U≤d := ((div_le_div_of_nonneg_right (le_max_left (M : ℝ) D) hU.le).trans hMU.le)
  have hUprob := G.longitudinal_exit_probability u v (G.vertexBall o m) W U D
    (fun _ : E => p) (1-(eta/30)^2) hD hu
    (fun a ha => ⟨(hK (Set.mem_image_of_mem _ ha)).trans_lt hKU,hseed a ha⟩)
    ((hbox U W).mono (fun _ h a _ => h a)) hprob
  have hesq : 1-(eta/10)^2≤1-(eta/30)^2 := by nlinarith [sq_nonneg eta]
  have hsignU := favored_of_union (fun _ : E => p) _ _
    (G.axisExit_upper u v _ U W D true) (G.axisExit_upper u v _ U W D false)
    (G.axisExit_finiteWitness u v _ U W D true) (G.axisExit_finiteWitness u v _ U W D false)
    (eta/10) (by linarith) (hesq.trans_lt hUprob)
  have hsignQ := favored_of_union (fun _ : E => p) _ _
    (G.axisExit_upper v u _ Q M D true) (G.axisExit_upper v u _ Q M D false)
    (G.axisExit_finiteWitness v u _ Q M D true) (G.axisExit_finiteWitness v u _ Q M D false)
    (eta/10) (by linarith) (hesq.trans_lt hMprob)
  have hbool : ∀ (F : Bool → ℝ), (1-eta/10<F true ∨ 1-eta/10<F false) →
      ∃ a : Bool, 1-eta<F a := by
    intro F h
    rcases h with h|h
    · exact ⟨true,(by linarith : 1-eta<1-eta/10).trans h⟩
    · exact ⟨false,(by linarith : 1-eta<1-eta/10).trans h⟩
  obtain ⟨a,ha⟩ := hbool (fun a => (BernoulliProduct.law (fun _ : E => p)).real
    (G.axisExit u v (G.vertexBall o m) U W D a)) hsignU
  obtain ⟨b,hb⟩ := hbool (fun b => (BernoulliProduct.law (fun _ : E => p)).real
    (G.axisExit v u (G.vertexBall o m) Q M D b)) hsignQ
  have hcmesh := G.strip_coordinate_increments u v U Q D a b hU hQ hu hv
  have hmesh : D/U+D/Q≤rho := by linarith
  refine ⟨U,Q,a,b,hU,hQ,(fun {_ _} h => (hcmesh.1 h).trans hmesh),
    (fun {_ _} h => (hcmesh.2 h).trans hmesh),?_⟩
  intro s
  cases s
  · apply hb.trans_le
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact measure_mono (G.transverse_exit_boxMove u v o m U Q M D eps a b huo hvo hU hQ heps heps'
      (hMU'.trans hde) (hDQ.trans hde))
  · apply ha.trans_le
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact measure_mono (G.longitudinal_exit_boxMove u v o m U Q W D eps a b huo hvo hU hQ heps heps'
      (hDU.trans hde) (hWQ'.trans hde))

end CriticalPercolation.BondGraph
end
end
end

end OAI
