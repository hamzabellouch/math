import OAI.Probability.BenjaminiSchramm.CriticalNormalizedCrossing

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Encodable V] [Countable E] [Nontrivial V] (G : BondGraph V E)

theorem critical_raw_halfspace_decay (hc : Connected G) (hl : LocallyFinite G)
    (hq : QuasiTransitive G) (hu : ¬ (criticalModel G).CombinatoriallyUnimodular) :
    ∃ C L : ℝ, 0 < C ∧ 0 < L ∧ ∀ r : ℝ, 0 ≤ r → ∀ (x : V) (t : ℝ), 0 ≤ t →
      (law (pc G)).real (restrictedHit G
        (internalEdges G {v | -r ≤ modularHeight G x v}) x {v | t ≤ modularHeight G x v}) ≤
          C*Real.exp (L*r-t) := by
  let H := criticalModel G
  have hHc := criticalModel_connected G hc
  have hHq := criticalModel_quasiTransitive G hq
  let : Finite H.VertexOrbit := H.finite_vertexOrbits hHq
  let : Fintype H.VertexOrbit := Fintype.ofFinite _
  obtain ⟨μ,hμ,_hmass,hstat⟩ := H.exists_positive_orbit_stationary hHc hl
  let a := H.stationaryOrbitWeight μ
  obtain ⟨A,B,hA,hB,hnorm⟩ := critical_normalized_halfspace_uniform G hc hl hq hu μ hμ hstat
  obtain ⟨D,hD,hdiff⟩ := H.stationaryOrbitHeight_uniform_comparison hHc hl μ hμ
  have hp : (0 : ℝ) < pc G := by exact_mod_cast pc_pos G hl hq
  let ell := -Real.log (pc G : ℝ)
  have hell : 0 ≤ ell := neg_nonneg.mpr (Real.log_nonpos hp.le (pc G).2.2)
  let C := Real.exp (ell*A*D+ell*B+D)
  let L := ell*A+1
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨C,L,Real.exp_pos _,hL,fun r hr x t ht => ?_⟩
  by_cases hDt : D ≤ t
  · have hsub : restrictedHit G (internalEdges G {v | -r ≤ modularHeight G x v}) x
        {v | t ≤ modularHeight G x v} ⊆ H.adjustedHalfspaceHit a x (-(r+D)) (t-D) := by
      rintro ω ⟨y,hy,hxy⟩
      refine ⟨y,?_,conn_mono G (Set.inter_subset_inter_right _ (internalEdges_mono G ?_)) hxy⟩
      · have hd := (abs_le.mp (hdiff x y)).1
        change t ≤ H.modularLogHeight x y at hy
        change t-D ≤ H.orbitAdjustedHeight a x y
        linarith
      · intro v hv
        have hd := (abs_le.mp (hdiff x v)).1
        change -r ≤ H.modularLogHeight x v at hv
        change -(r+D) ≤ H.orbitAdjustedHeight a x v
        linarith
    have hh := (measureReal_mono hsub).trans (hnorm (r+D) (add_nonneg hr hD) x (t-D)
      (sub_nonneg.mpr hDt))
    have he : (pc G : ℝ)^(-(A*(r+D)+B))*Real.exp (-(t-D)) =
        C*Real.exp (ell*A*r-t) := by
      rw [Real.rpow_def_of_pos hp,← Real.exp_add]
      change Real.exp _ = Real.exp (ell*A*D+ell*B+D)*Real.exp (ell*A*r-t)
      rw [← Real.exp_add]
      congr 1
      dsimp [ell]
      ring
    rw [he] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    dsimp [L]
    nlinarith
  · have hlo : 1 ≤ C*Real.exp (L*r-t) := by
      change 1 ≤ Real.exp (ell*A*D+ell*B+D)*Real.exp (L*r-t)
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      have hellA := mul_nonneg hell hA.le
      have hellAD := mul_nonneg hellA hD
      have hellB := mul_nonneg hell hB
      have hLr := mul_nonneg hL.le hr
      linarith
    exact (show (law (pc G)).real _ ≤ 1 by simp).trans hlo

end Percolation.BenjaminiSchramm

end

end OAI
