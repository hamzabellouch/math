import OAI.Probability.BenjaminiSchramm.LayerFirstMomentSubmultiplicative
import OAI.Probability.BenjaminiSchramm.LayerFirstMomentPositivity
import OAI.Probability.BenjaminiSchramm.LayerMomentFekete

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] [Nontrivial V]
  (G : BondGraph V E) [Fintype G.VertexOrbit]

theorem subcritical_normalized_layer_rate
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hql : Percolation.QuasiTransitive G.ends)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ) (hu : ¬G.CombinatoriallyUnimodular)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (hpc : p < Percolation.pc G.ends) :
    ∃ β : ℝ, 0 ≤ β ∧
      (∀ n : ℕ, Real.exp (-β*n) ≤
        (G.supAdjustedUpLayerMoment (G.stationaryOrbitWeight μ) R p n).toReal) ∧
      (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
        G.supAdjustedUpLayerMoment (G.stationaryOrbitWeight μ) R p n ≤
          ENNReal.ofReal (K*Real.exp (-(β-ε)*n))) ∧
      Tendsto (fun n : ℕ => -Real.log
        (G.supAdjustedUpLayerMoment (G.stationaryOrbitWeight μ) R p n).toReal/n) atTop (𝓝 β) := by
  let a := G.stationaryOrbitWeight μ
  let S := G.supAdjustedUpLayerMoment a R p
  let P : ℕ → ℝ := fun n => (S n).toReal
  obtain ⟨C,hC,hbound⟩ := G.subcritical_supAdjustedUpLayerMoment_bound hl hql a R p hpc
  have hne (n : ℕ) : S n ≠ ⊤ := (lt_of_le_of_lt (hbound n) hC).ne
  obtain ⟨A,B,hA,hB,hlower⟩ := G.adjustedUpLayerMoment_finite_energy hc hl hq μ hμ hstat hu R hR hjump p hp
  have hlow (n : ℕ) : (p : ℝ)^(A*n+B) ≤ P n := by
    have hh := ENNReal.toReal_mono (hne n)
      ((hlower n (Classical.arbitrary V) 0).trans (G.adjustedUpLayerMoment_le_sup a R p n _ 0))
    rwa [ENNReal.toReal_ofReal (Real.rpow_pos_of_pos hp _).le] at hh
  have hP (n : ℕ) : 0 < P n := (Real.rpow_pos_of_pos hp _).trans_le (hlow n)
  have hP0 : 1 ≤ P 0 := by
    have hh := ENNReal.toReal_mono (hne 0)
      ((G.adjustedUpLayerMoment_zero_ge_one a R p (Classical.arbitrary V) 0).trans
        (G.adjustedUpLayerMoment_le_sup a R p 0 _ 0))
    simpa only [ENNReal.toReal_one] using hh
  have hmul (m n : ℕ) : P (m+n) ≤ P m*P n := by
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top (hne m) (hne n))
      (G.supAdjustedUpLayerMoment_submultiplicative hc hl a R hR hjump p m n)
    simpa only [ENNReal.toReal_mul] using hh
  have hboundr (n : ℕ) : P n ≤ C.toReal := ENNReal.toReal_mono hC.ne (hbound n)
  have hlog : Real.log (p : ℝ) ≤ 0 := Real.log_nonpos hp.le p.2.2
  have hexp (n : ℕ) : Real.exp (-(-A*Real.log (p : ℝ))*n-(-B*Real.log (p : ℝ))) ≤ P n := by
    have hh := hlow n
    rw [Real.rpow_def_of_pos hp] at hh
    convert hh using 1
    congr 1
    ring
  obtain ⟨β,hβ,hlo,hupp,hlim⟩ := positive_layer_moment_rate P hP hP0 hmul C.toReal hboundr
    (-A*Real.log (p : ℝ)) (-B*Real.log (p : ℝ))
    (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hA.le) hlog)
      (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hB) hlog) hexp
  refine ⟨β,hβ,hlo,?_,hlim⟩
  intro ε hε
  obtain ⟨K,hK,hKbound⟩ := hupp ε hε
  refine ⟨K,hK,fun n => ?_⟩
  have hh := ENNReal.ofReal_le_ofReal (hKbound n)
  rwa [ENNReal.ofReal_toReal (hne n)] at hh

end CriticalPercolation.BondGraph

end

end OAI
