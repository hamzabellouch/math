import OAI.Probability.BenjaminiSchramm.CriticalFullspaceProfiles
import OAI.Probability.BenjaminiSchramm.NormalizedQuarterMoment

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] [Infinite V] (G : BondGraph V E)

theorem critical_quarter_moment_finite
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (hpc1 : pc G < 1) (hu : ¬(criticalModel G).CombinatoriallyUnimodular) (o : V) :
    (criticalModel G).quarterThreeQuarterMoment (pc G) o < ⊤ := by
  let : Encodable V := Encodable.ofCountable V
  let H := criticalModel G
  have hHc := criticalModel_connected G hc
  have hHq := criticalModel_quasiTransitive G hq
  let : Finite H.VertexOrbit := H.finite_vertexOrbits hHq
  let : Fintype H.VertexOrbit := Fintype.ofFinite _
  obtain ⟨μ,hμ,_hmass,hstat⟩ := H.exists_positive_orbit_stationary hHc hl
  let a := H.stationaryOrbitWeight μ
  obtain ⟨m,M,hm,ha⟩ := H.stationaryOrbitWeight_uniform_bounds hHc hl μ hμ
  obtain ⟨K,hK⟩ := H.uniform_ball_bound hHq 1
  let D := Real.log M-Real.log m
  have hD : 0 ≤ D := sub_nonneg.mpr (Real.log_le_log hm ((ha o).1.trans (ha o).2))
  let R := D+max 0 (Real.log (K : ℝ))+1
  have hR1 : 1 ≤ R := by dsimp [R]; linarith [le_max_left (0 : ℝ) (Real.log (K : ℝ))]
  have hR : 0 < R := lt_of_lt_of_le (by norm_num) hR1
  have hjump : ∀ e v w, v ∈ G e → w ∈ G e → |H.orbitAdjustedHeight a v w| ≤ R := by
    intro e v w hv hw
    have hr := H.modularLogHeight_edge_jump hHc hl K hK v v w e hv hw
    rw [H.modularLogHeight_self,sub_zero] at hr
    have ht := abs_add_le (H.orbitAdjustedHeight a v w-H.modularLogHeight v w) (H.modularLogHeight v w)
    rw [sub_add_cancel] at ht
    apply (ht.trans (add_le_add (H.orbitAdjustedHeight_sub_bound a m M hm ha v w)
      (hr.trans (le_max_right _ _)))).trans
    dsimp [R,D]
    linarith
  obtain ⟨C,hC,hpos,hneg⟩ := critical_fullspace_threeQuarter_profiles G hc hl hq hpc1 hu μ hμ hstat R hR hjump
  exact raw_quarterMoment_lt_top_of_normalized_bands G hc hl a m M hm ha R hR1
    (pc G) o C hC (fun k hk => hpos k hk o) (fun k hk => hneg k hk o)

end Percolation.BenjaminiSchramm

end

end OAI
