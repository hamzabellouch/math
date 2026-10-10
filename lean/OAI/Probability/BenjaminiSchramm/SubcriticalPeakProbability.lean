import OAI.Probability.BenjaminiSchramm.PeakBandProbability
import OAI.Probability.BenjaminiSchramm.PeakSurgeryAverage
import OAI.Probability.BenjaminiSchramm.UpwardFrontierProbability

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Encodable V] [Countable E] [Nontrivial V]
  (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem subcritical_peak_band_probability
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (hpc : p < pc G) :
    ∃ β : ℝ, R < β ∧ ∃ K : ℝ, 0 < K ∧
      (∀ n : ℕ, (criticalModel G).supAdjustedUpLayerMoment
        ((criticalModel G).stationaryOrbitWeight μ) R p n ≤ ENNReal.ofReal (K*Real.exp (-β*n))) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → ∃ x : V,
      ENNReal.ofReal (c*Real.exp (-β*n)) ≤
        (criticalModel G).law p ((criticalModel G).strictPeakBandEvent
          ((criticalModel G).stationaryOrbitWeight μ) (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) x) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  have hHc := criticalModel_connected G hc
  obtain ⟨β,hβR,hlo,K,hK,hup⟩ := subcritical_layer_prefactor G hc hl hq μ hμ hstat hu R hR hjump p hp hpc
  have hβ : 0 < β := hR.trans hβR
  obtain ⟨χ,hχ,hrow⟩ := subcritical_ennreal_row_bound G hl hq p hpc
  obtain ⟨A,hA,hsecond⟩ := H.adjusted_upper_layer_second_moment_constant hHc hl a R hR hjump p
    χ hχ hrow β K hβ hK hup
  obtain ⟨L,hsurgery⟩ := normalized_peak_surgery G hc hl hq μ hμ hstat hu R hR hjump
  obtain ⟨d,_hd,hd⟩ := exists_degree_bound G hq
  obtain ⟨N,hN⟩ := exists_nat_gt (max (4*A*χ*K) 1)
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hN.le)
  have hNscale : 4*A*χ*K ≤ (N : ℝ) := (le_max_left _ _).trans hN.le
  let δ : ℝ := min (p : ℝ) (1-p)
  have hp1 : (p : ℝ) < 1 := (show (p : ℝ) < (pc G : ℝ) from hpc).trans_le (pc G).2.2
  have hδ : 0 < δ := lt_min hp (sub_pos.mpr hp1)
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans p.2.2
  let ε : ℝ := δ^(d*(N+L+1))
  have hε : 0 < ε := pow_pos hδ _
  refine ⟨β,hβR,K,hK,hup,ε/(4*A),div_pos hε (by positivity),?_⟩
  intro n hn
  let t := Real.exp (-β*n)
  have ht : 0 < t := Real.exp_pos _
  have hfront := H.adjusted_frontier_probability_lower a R p β A hA hlo hsecond n hn
  have hhalf : ENNReal.ofReal (t/(2*A)) < H.supAdjustedFrontierProbability a R p n := by
    apply lt_of_lt_of_le _ hfront
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < t/A)).mpr
    apply (div_lt_div_iff₀ (by positivity : 0 < 2*A) hA).mpr
    nlinarith
  obtain ⟨x,hx⟩ := lt_iSup_iff.mp hhalf
  obtain ⟨offset,hoffset⟩ := lt_iSup_iff.mp hx
  let f := H.adjustedLayerIndex a R offset x
  let I := internalEdges G {v | f v < (n : ℤ)}
  let Z : Set E → ℝ≥0∞ := fun ω => frontierCount G I Set.univ ω x
  have hfx : f x < (n : ℤ) := by
    simp only [f,H.adjustedLayerIndex_self]
    exact_mod_cast hn
  have hfj : ∀ e v w, v ∈ G e → w ∈ G e → f w ≤ f v+1 := by
    intro e v w hv hw
    exact (H.adjustedLayerIndex_edge_jump hHc hl a R offset hR hjump x v w e hv hw).2
  have hmoment : (∫⁻ ω, Z ω ∂law p) ≤ ENNReal.ofReal (χ*K*t) := by
    apply (lintegral_mono fun ω => integer_frontierCount_le_fullLayerCount G f n hfj ω x hfx).trans
    apply (H.adjustedFullLayerMoment_up_bound hHc hl a R hR hjump p _ hrow n x offset).trans
    apply (mul_le_mul' (hup n) le_rfl).trans_eq
    rw [←ENNReal.ofReal_mul (mul_nonneg hK.le ht.le)]
    congr 1
    ring
  have hscale : 2*(χ*K*t) ≤ (N : ℝ)*(t/(2*A)) := by
    calc
      _ = (4*A*χ*K*t)/(2*A) := by field_simp; ring
      _ ≤ ((N : ℝ)*t)/(2*A) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hNscale ht.le) (by positivity)
      _ = _ := by ring
  have hsmall := small_frontier_probability_lower p {ω | 0 < Z ω} Z
    (measurable_frontierCount G I Set.univ x) (t/(2*A)) (χ*K*t) N
    (by positivity) (by positivity) hNpos hoffset.le hmoment hscale
  have hfin : ∀ᵐ ω ∂law p, (cluster G (ω ∩ I) x).Finite := by
    filter_upwards [subcritical_cluster_finite_ae G p hpc x] with ω hω
    exact hω.subset (fun y hy => conn_mono G Set.inter_subset_left hy)
  let B := H.strictPeakBandEvent a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) x
  have hlocal (S F : Finset V)
      (hcell : (lowerFrontierCell G I Set.univ x (S : Set V) (F : Set V)).Nonempty)
      (hgood : 0 < F.card ∧ F.card ≤ N) :
      law p (lowerFrontierCell G I Set.univ x (S : Set V) (F : Set V))*
        ENNReal.ofReal (δ^(d*(F.card+L+1))) ≤
          law p (lowerFrontierCell G I Set.univ x (S : Set V) (F : Set V) ∩ B) :=
    hsurgery p d hd n hn x offset S F hcell (Finset.card_pos.mp hgood.1)
  have hs := peak_probability_of_frontier_surgery G hl p I Set.univ x hfin B
    (H.measurableSet_strictPeakBandEvent a _ _ x) N L d δ hδ.le hδ1 hlocal
  refine ⟨x,?_⟩
  apply le_trans _ hs
  have hsmall' : ENNReal.ofReal (t/(4*A)) ≤
      law p {ω | 0 < Z ω ∧ Z ω ≤ (N : ℝ≥0∞)} := by
    convert hsmall using 1
    · congr 1
      ring
    · simp only [ENNReal.ofReal_natCast]
      congr 1
  apply (mul_le_mul' hsmall' le_rfl).trans_eq'
  rw [←ENNReal.ofReal_mul (by positivity : 0 ≤ t/(4*A))]
  congr 1
  change (t/(4*A))*ε=ε/(4*A)*t
  ring

end Percolation.BenjaminiSchramm

end

end OAI
