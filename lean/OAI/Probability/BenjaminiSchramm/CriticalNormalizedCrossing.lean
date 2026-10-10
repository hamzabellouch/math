import OAI.Probability.BenjaminiSchramm.HalfspaceRootComparison

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Encodable V] [Countable E] [Nontrivial V]
  (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem critical_normalized_halfspace_uniform (hc : Connected G) (hl : LocallyFinite G)
    (hq : QuasiTransitive G) (hu : ¬ (criticalModel G).CombinatoriallyUnimodular)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ = μ) :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ r : ℝ, 0 ≤ r → ∀ (x : V) (t : ℝ), 0 ≤ t →
      (law (pc G)).real ((criticalModel G).adjustedHalfspaceHit
        ((criticalModel G).stationaryOrbitWeight μ) x (-r) t) ≤
        (pc G : ℝ)^(-(A*r+B)) * Real.exp (-t) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  have hHc := criticalModel_connected G hc
  have hHq := criticalModel_quasiTransitive G hq
  obtain ⟨A,B,hA,hB,hpath⟩ := H.stationaryOrbitHeight_orbit_above hHc hl hHq μ hμ hstat hu
  obtain ⟨m,M,hm,hbounds⟩ := H.stationaryOrbitWeight_uniform_bounds hHc hl μ hμ
  have hauto := H.stationaryOrbitWeight_aut μ
  have hp : (0 : ℝ) < pc G := by exact_mod_cast pc_pos G hl hq
  refine ⟨A,B,hA,hB,fun r hr x t ht => ?_⟩
  let α : ℝ := (pc G : ℝ)^(A*r+B)
  have hα : 0 < α := Real.rpow_pos_of_pos hp _
  have hroot (u : V) :
      α*(law (pc G)).real (H.adjustedHalfspaceHit a x (-r) t) ≤
        (law (pc G)).real (H.adjustedHalfspaceHit a u 0 t) := by
    obtain ⟨y,w,horb,hlen,hw,hy⟩ := hpath r hr u (H.vertexOrbit x)
    obtain ⟨φ,hφ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact horb)
    change φ.vertex x = y at hφ
    have hcomp := H.adjustedHalfspaceHit_path_comparison hHc hl a (pc G) w r t hr hw hy
    have he := CriticalPercolation.BondGraph.Aut.adjustedHalfspaceHit_measure H a hauto φ (pc G) x (-r) t
    rw [hφ] at he
    have her := congrArg ENNReal.toReal he
    change (H.law (pc G)).real (H.adjustedHalfspaceHit a y (-r) t) =
      (H.law (pc G)).real (H.adjustedHalfspaceHit a x (-r) t) at her
    rw [her] at hcomp
    have hcoeff : α ≤ (pc G : ℝ)^w.length := by
      simpa only [Real.rpow_natCast] using
        Real.rpow_le_rpow_of_exponent_ge hp (pc G).2.2 hlen
    exact (mul_le_mul_of_nonneg_right hcoeff ENNReal.toReal_nonneg).trans hcomp
  have hmin : α*(law (pc G)).real (H.adjustedHalfspaceHit a x (-r) t) ≤
      (H.infimalAdjustedCrossing a (pc G) t).toReal := by
    have he : ENNReal.ofReal (α*(law (pc G)).real (H.adjustedHalfspaceHit a x (-r) t)) ≤
        H.infimalAdjustedCrossing a (pc G) t := by
      apply le_iInf
      intro u
      exact ENNReal.ofReal_le_of_le_toReal (hroot u)
    have hf := ENNReal.toReal_mono
      (ne_top_of_le_ne_top ENNReal.one_ne_top (H.infimalAdjustedCrossing_le_one a (pc G) t)) he
    have hnonneg : 0 ≤ α*(law (pc G)).real (H.adjustedHalfspaceHit a x (-r) t) :=
      mul_nonneg hα.le measureReal_nonneg
    rwa [ENNReal.toReal_ofReal hnonneg] at hf
  have hh := hmin.trans (critical_infimal_adjusted_crossing_bound G hc hl hq a hauto
    m M hm hbounds t ht)
  have hh' := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hα.le)
  rw [← mul_assoc,inv_mul_cancel₀ hα.ne',one_mul] at hh'
  have he : α⁻¹ = (pc G : ℝ)^(-(A*r+B)) := by
    exact (Real.rpow_neg (pc G).2.1 _).symm
  rwa [he] at hh'

end Percolation.BenjaminiSchramm

end

end OAI
