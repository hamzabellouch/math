import OAI.Probability.BenjaminiSchramm.PeakSurgeryProbability
import OAI.Probability.BenjaminiSchramm.IntegerFrontierCrossing

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] [Nontrivial V]
  (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem normalized_peak_surgery
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R) :
    ∃ L : ℕ, ∀ (p : unitInterval) (d : ℕ), (∀ v, degree G v ≤ d) →
      ∀ (n : ℕ), 0 < n → ∀ (x : V) (u : ℝ) (S F : Finset V),
      (lowerFrontierCell G
        (internalEdges G {v | (criticalModel G).adjustedLayerIndex
          ((criticalModel G).stationaryOrbitWeight μ) R u x v < (n : ℤ)}) Set.univ x (S : Set V) (F : Set V)).Nonempty →
      F.Nonempty →
      law p (lowerFrontierCell G
        (internalEdges G {v | (criticalModel G).adjustedLayerIndex
          ((criticalModel G).stationaryOrbitWeight μ) R u x v < (n : ℤ)}) Set.univ x (S : Set V) (F : Set V))*
        ENNReal.ofReal ((min (p : ℝ) (1-p))^(d*(F.card+L+1))) ≤
      law p (lowerFrontierCell G
        (internalEdges G {v | (criticalModel G).adjustedLayerIndex
          ((criticalModel G).stationaryOrbitWeight μ) R u x v < (n : ℤ)}) Set.univ x (S : Set V) (F : Set V) ∩
        {ω | ∃ z, R*((n : ℝ)+1) < (criticalModel G).orbitAdjustedHeight
            ((criticalModel G).stationaryOrbitWeight μ) x z ∧
          (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x z ≤ R*((n : ℝ)+4) ∧
          ω ∈ strictHeightPeakConnection G
            ((criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x) x z}) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  have hHc := criticalModel_connected G hc
  have hHq := criticalModel_quasiTransitive G hq
  obtain ⟨L,hpath⟩ := H.stationaryOrbitHeight_bounded_peak_extension hHc hl hHq μ hμ hstat hu R hR hjump
  refine ⟨L,fun p d hd n hn x offset S F hcell hF => ?_⟩
  let f := H.adjustedLayerIndex a R offset x
  let h := H.orbitAdjustedHeight a x
  have hfx : f x < (n : ℤ) := by
    simp only [f,H.adjustedLayerIndex_self]
    exact_mod_cast hn
  have hfj : ∀ e v w, v ∈ G e → w ∈ G e → f w ≤ f v+1 := by
    intro e v w hv hw
    exact (H.adjustedLayerIndex_edge_jump hHc hl a R offset hR hjump x v w e hv hw).2
  obtain ⟨η,hη⟩ := hcell
  have hSlevel (v : V) (hv : v ∈ S) : f v < (n : ℤ) := by
    apply conn_internalEdges_end_mem G η {v | f v < (n : ℤ)} hfx
    change v ∈ cluster G (η ∩ internalEdges G {v | f v < (n : ℤ)}) x
    rw [hη.1]
    exact hv
  have hFlevel (v : V) (hv : v ∈ F) : f v=(n : ℤ) := by
    apply integer_lower_frontier_level G f (n : ℤ) hfj η x hfx
    have hfront : openFrontier G η (cluster G (η ∩ internalEdges G {v | f v < (n : ℤ)}) x)=(F : Set V) := by
      rw [hη.1]
      simpa only [Set.inter_univ] using hη.2
    rwa [hfront]
  obtain ⟨v,hv⟩ := hF
  obtain ⟨z,w,hwlen,hwmin,hwheight,hwpeak⟩ := hpath v
  have hvheight := H.adjustedLayerIndex_height_bounds a R offset hR x v
  change R*((f v : ℝ)-1) < h v ∧ h v < R*((f v : ℝ)+1) at hvheight
  rw [hFlevel v hv] at hvheight
  simp only [Int.cast_natCast] at hvheight
  have hzadd : h z=h v+H.orbitAdjustedHeight a v z := H.orbitAdjustedHeight_change_base hHc hl a x v z
  have hzband : R*((n : ℝ)+1) < h z ∧ h z ≤ R*((n : ℝ)+4) := by
    change R*((n : ℝ)-1) < h v ∧ h v < R*((n : ℝ)+1) at hvheight
    constructor <;> nlinarith [hwheight.1,hwheight.2]
  have hbelow : ∀ v' ∈ (S : Set V) ∪ (F : Set V), h v' < h z := by
    intro v' hv'
    have hh := (H.adjustedLayerIndex_height_bounds a R offset hR x v').2
    change h v' < R*((f v' : ℝ)+1) at hh
    rcases hv' with hvS | hvF
    · have hi : (f v' : ℝ)+1 ≤ (n : ℝ) := by exact_mod_cast (show f v'+1 ≤ (n : ℤ) by have := hSlevel v' hvS; omega)
      nlinarith [hzband.1]
    · rw [hFlevel v' hvF] at hh
      simp only [Int.cast_natCast] at hh
      exact hh.trans hzband.1
  have havoid : ∀ v' ∈ w.support, v' ∉ (S : Set V) := by
    intro v' hv' hvS
    have hh := hwmin v' hv'
    have hheight : h v ≤ h v' := by
      have he := H.orbitAdjustedHeight_change_base hHc hl a x v v'
      change h v'=h v+H.orbitAdjustedHeight a v v' at he
      linarith
    have hidx : f v ≤ f v' := by
      unfold f CriticalPercolation.BondGraph.adjustedLayerIndex
      apply sub_le_sub_right
      apply Int.floor_mono
      have hh := div_le_div_of_nonneg_right hheight hR.le
      change h v/R+offset ≤ h v'/R+offset
      linarith
    rw [hFlevel v hv] at hidx
    have := hSlevel v' hvS
    omega
  have hpeak : ∀ v' ∈ w.support, v' ≠ z → h v' < h z := by
    intro v' hv' hvz
    have hh := hwpeak v' hv' hvz
    change H.orbitAdjustedHeight a x v' < H.orbitAdjustedHeight a x z
    rw [H.orbitAdjustedHeight_change_base hHc hl a x v v',
      H.orbitAdjustedHeight_change_base hHc hl a x v z]
    change H.orbitAdjustedHeight a v v' < H.orbitAdjustedHeight a v z at hh
    linarith
  have hg : H.fullGraph=openSimpleGraph G Set.univ := criticalModel_openGraph G Set.univ
  let ι : H.fullGraph →g openSimpleGraph G Set.univ := ⟨id,fun {_ _} h => by simpa only [←hg,id_eq] using h⟩
  have hsupport (v' : V) : v' ∈ (w.map ι).support ↔ v' ∈ w.support := by
    simp only [SimpleGraph.Walk.support_map]
    change v' ∈ w.support.map id ↔ _
    simp only [List.map_id_fun,id_eq]
  have hb := lowerFrontierCell_strict_peak_probability G hl d hd p {v | f v < (n : ℤ)}
    (S : Set V) F x v z h hv (w.map ι)
      (fun v' hv' => havoid v' ((hsupport v').mp hv')) hbelow
      (fun v' hv' => hpeak v' ((hsupport v').mp hv'))
  have hδ : 0 ≤ min (p : ℝ) (1-p) := le_min p.2.1 (sub_nonneg.mpr p.2.2)
  have hδ1 : min (p : ℝ) (1-p) ≤ 1 := (min_le_left _ _).trans p.2.2
  apply le_trans _ (hb.trans (measure_mono ?_))
  · exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hδ hδ1
      (Nat.mul_le_mul_left d (by simpa only [SimpleGraph.Walk.length_map] using Nat.add_le_add_right (Nat.add_le_add_left hwlen F.card) 1))))
  · rintro ω ⟨hc',hp'⟩
    exact ⟨hc',z,hzband.1,hzband.2,hp'⟩

end Percolation.BenjaminiSchramm

end

end OAI
