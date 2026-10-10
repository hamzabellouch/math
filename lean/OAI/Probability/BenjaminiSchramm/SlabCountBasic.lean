import OAI.Probability.BenjaminiSchramm.FractionalSlabGeometry
import OAI.Probability.BenjaminiSchramm.LayerFrontierLocalization

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma restrictedLayerCount_zero_or_one_le (I : Set E) (W : Set V) (ω : Set E) (x : V) :
    restrictedLayerCount G I W ω x=0 ∨ 1 ≤ restrictedLayerCount G I W ω x := by
  by_cases hex : ∃ y, y ∈ W ∧ Conn G (ω ∩ I) x y
  · obtain ⟨y,hy⟩ := hex
    apply Or.inr
    unfold restrictedLayerCount
    exact ((show (1 : ℝ≥0∞)=(if y ∈ W ∧ Conn G (ω ∩ I) x y then 1 else 0) from
      (ite_eq_left hy).symm).le.trans (ENNReal.le_tsum
        (f := fun z => if z ∈ W ∧ Conn G (ω ∩ I) x z then 1 else 0) y))
  · exact Or.inl (ENNReal.tsum_eq_zero.mpr fun y => ite_eq_right (fun h => hex ⟨y,h⟩))

lemma restrictedLayerCount_lt_top_of_finite (I : Set E) (W : Set V) (ω : Set E) (x : V)
    (hfin : (cluster G ω x).Finite) : restrictedLayerCount G I W ω x < ⊤ := by
  have hIF : (cluster G (ω ∩ I) x ∩ W).Finite :=
    (hfin.subset fun z hz => conn_mono G Set.inter_subset_left hz.1)
  let S := hIF.toFinset
  have he : restrictedLayerCount G I W ω x=S.card :=
    restrictedLayerCount_eq_card G I W ω x S (fun y => by
      simp only [S,hIF.mem_toFinset,Set.mem_inter_iff]
      exact and_comm)
  rw [he]
  exact ENNReal.natCast_lt_top _

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma adjustedSlabBandCount_rpow_mono_exponent (a : V → ℝ) (d c l u : ℝ)
    (ω : Set E) (x : V) {q q' : ℝ} (hq : 0 < q) (hqq' : q ≤ q') :
    (G.adjustedSlabBandCount a d c l u ω x)^q ≤
      (G.adjustedSlabBandCount a d c l u ω x)^q' := by
  simp only [G.adjustedSlabBandCount_eq_restricted]
  rcases restrictedLayerCount_zero_or_one_le G.ends _ _ ω x with hz | ho
  · rw [hz,ENNReal.zero_rpow_of_pos hq,ENNReal.zero_rpow_of_pos (hq.trans_le hqq')]
  · exact ENNReal.rpow_le_rpow_of_exponent_le ho hqq'

lemma one_le_adjustedSlabZeroBandCount (a : V → ℝ) (d c B : ℝ)
    (hB : 0 ≤ B) (ω : Set E) (x : V) :
    1 ≤ G.adjustedSlabBandCount a d c (-B) B ω x := by
  apply le_trans _ (ENNReal.le_tsum x)
  unfold adjustedSlabBandTransport
  rw [ite_eq_left]
  exact ⟨Percolation.conn_refl G.ends _ x,by simpa using neg_nonpos.mpr hB,by simpa using hB⟩

lemma adjustedSlabBandCount_lt_top_of_finite (a : V → ℝ) (d c l u : ℝ)
    (ω : Set E) (x : V) (hfin : (Percolation.cluster G.ends ω x).Finite) :
    G.adjustedSlabBandCount a d c l u ω x < ⊤ := by
  rw [G.adjustedSlabBandCount_eq_restricted]
  exact restrictedLayerCount_lt_top_of_finite G.ends _ _ ω x hfin

end CriticalPercolation.BondGraph

end

end OAI
