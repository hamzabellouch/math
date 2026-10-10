import OAI.Probability.BenjaminiSchramm.SubcriticalFullLayerProfile
import OAI.Probability.BenjaminiSchramm.LayerSecondMomentDecomposition
import OAI.Probability.BenjaminiSchramm.SubcriticalLayerConvolution

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Encodable V] [Countable E] [Nontrivial V]
  (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem subcritical_full_layer_profile_at_rate
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hpc : p < pc G) (β K : ℝ) (hβ : R < β) (hK : 0 < K)
    (hup : ∀ n : ℕ, (criticalModel G).supAdjustedUpLayerMoment
      ((criticalModel G).stationaryOrbitWeight μ) R p n ≤ ENNReal.ofReal (K*Real.exp (-β*n))) :
    ∃ C : ℝ, 0 < C ∧ ∀ i : ℤ,
      (criticalModel G).supAdjustedFullLayerMoment ((criticalModel G).stationaryOrbitWeight μ) R p i ≤
        ENNReal.ofReal (C*Real.exp (-(β-R)*|(i : ℝ)|)) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  have hHc := criticalModel_connected G hc
  have hHq := criticalModel_quasiTransitive G hq
  obtain ⟨χ,hχ,hrow⟩ := subcritical_ennreal_row_bound G hl hq p hpc
  obtain ⟨m,M,hm,hweights⟩ := H.stationaryOrbitWeight_uniform_bounds hHc hl μ hμ
  let O := H.orbitRepresentatives hHq
  let D : ℝ≥0∞ := (ENNReal.ofReal m)⁻¹*(∑ r ∈ O.roots, ENNReal.ofReal (a r))
  have hD : D ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hm))
    (ENNReal.sum_ne_top.mpr fun r _ => ENNReal.ofReal_ne_top)
  have hDEq : ENNReal.ofReal D.toReal=D := ENNReal.ofReal_toReal hD
  have hbase (i : ℤ) : H.supAdjustedFullLayerMoment a R p i ≤ ENNReal.ofReal χ :=
    H.supAdjustedFullLayerMoment_le_row_bound a R p _ hrow i
  have hpositive (n : ℕ) : H.supAdjustedFullLayerMoment a R p n ≤
      ENNReal.ofReal (K*χ*Real.exp (-β*n)) := by
    apply (H.supAdjustedFullLayerMoment_up_bound hHc hl a R hR hjump p _ hrow n).trans
    apply (mul_le_mul' (hup n) le_rfl).trans_eq
    rw [←ENNReal.ofReal_mul (mul_nonneg hK.le (Real.exp_nonneg _))]
    congr 1
    ring
  have hnegative (n : ℕ) (hn : 3 ≤ n) : H.supAdjustedFullLayerMoment a R p (-(n : ℤ)) ≤
      ENNReal.ofReal (D.toReal*K*χ*Real.exp (R+2*β)*Real.exp (-(β-R)*n)) := by
    have hb : H.supAdjustedFullLayerMoment a R p (-(n : ℤ)) ≤
        D*ENNReal.ofReal (Real.exp (R*((n : ℝ)+1)))*
          (H.supAdjustedUpLayerMoment a R p (n-2)*ENNReal.ofReal χ) := by
      apply iSup_le
      intro x
      apply iSup_le
      intro u
      exact H.adjustedFullLayerMoment_negative_bound O hHc hl a
        (H.stationaryOrbitWeight_pos hHc hl μ hμ) (H.stationaryOrbitWeight_aut μ)
        m hm (fun x => (hweights x).1) R hR hjump p _ hrow n hn x u
    apply hb.trans
    apply (mul_le_mul' le_rfl (mul_le_mul' (hup (n-2)) le_rfl)).trans_eq
    nth_rw 1 [←hDEq]
    rw [←ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ←ENNReal.ofReal_mul (mul_nonneg hK.le (Real.exp_nonneg _)),
      ←ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg (Real.exp_nonneg _))]
    congr 1
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    push_cast
    rw [show D.toReal*Real.exp (R*((n : ℝ)+1))*(K*Real.exp (-β*((n : ℝ)-2))*χ) =
      D.toReal*K*χ*(Real.exp (R*((n : ℝ)+1))*Real.exp (-β*((n : ℝ)-2))) by ring,
      ←Real.exp_add,show R*((n : ℝ)+1)+ -β*((n : ℝ)-2) = R+2*β + (-(β-R)*(n : ℝ)) by ring,
      Real.exp_add]
    ring
  obtain ⟨C,hC,hprof⟩ := symmetric_exponential_profile
    (H.supAdjustedFullLayerMoment a R p) χ K D.toReal R β hχ hK.le ENNReal.toReal_nonneg
      hR hβ hbase hpositive hnegative
  exact ⟨C,hC,hprof⟩

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem adjusted_downward_layer_second_moment_at_rate
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ) (R : ℝ)
    (p : unitInterval) (β C : ℝ) (hβ : R < β) (hC : 0 < C)
    (hprofile : ∀ i : ℤ, G.supAdjustedFullLayerMoment a R p i ≤
      ENNReal.ofReal (C*Real.exp (-(β-R)*|(i : ℝ)|))) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ (k l : ℕ) (x : V) (u : ℝ),
      (∫⁻ ω, restrictedLayerCount G.ends Set.univ
          {y | G.adjustedLayerIndex a R u x y = -(k : ℤ)} ω x *
        restrictedLayerCount G.ends Set.univ
          {y | G.adjustedLayerIndex a R u x y = -(l : ℤ)} ω x ∂G.law p) ≤
      K*ENNReal.ofReal (Real.exp (-(β-R)*((max k l : ℕ) : ℝ))) := by
  have hprof (i : ℤ) : G.supAdjustedFullLayerMoment a R p i ≤
      ENNReal.ofReal C*expAbsLayerKernel (β-R) i := by
    simpa only [expAbsLayerKernel,ENNReal.ofReal_mul hC.le] using hprofile i
  obtain ⟨K,hK,hconv⟩ := subcritical_three_profile_uniform_bound (sub_pos.mpr hβ)
    (ENNReal.ofReal C) ENNReal.ofReal_lt_top
  refine ⟨K,hK,fun k l x u => ?_⟩
  exact (G.adjusted_full_layer_second_moment_bound hc hl a R p x u
    (-(k : ℤ)) (-(l : ℤ))).trans
      (hconv (G.supAdjustedFullLayerMoment a R p) (G.supAdjustedFullLayerMoment a R p)
        (G.supAdjustedFullLayerMoment a R p) hprof hprof hprof k l)

end CriticalPercolation.BondGraph

end

end OAI
