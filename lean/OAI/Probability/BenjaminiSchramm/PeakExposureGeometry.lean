import OAI.Probability.BenjaminiSchramm.PeakComparisonAveraging
import OAI.Probability.BenjaminiSchramm.PeakHalfspaceGeometry

namespace OAI

noncomputable section
open Set
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma upper_mask_lower_bound (f : V → ℝ) (R b d : ℝ)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e → |f w-f v| ≤ R)
    (D : Set E) (hd : d ≤ b-R) :
    D \ internalEdges G {z | f z ≤ b} ⊆ internalEdges G {z | d ≤ f z} := by
  intro e he v hve
  have hn : ¬∀ z ∈ G e, f z ≤ b := he.2
  push Not at hn
  obtain ⟨z,hze,hz⟩ := hn
  have hh := (abs_le.mp (hjump e z v hze hve)).1
  change d ≤ f v
  linarith

lemma upper_cluster_crossing_cover (f : V → ℝ) (R b : ℝ)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e → |f w-f v| ≤ R)
    (D : Set E) (ω : Set E) (x y : V) (hx : b < f x) (hy : f y ≤ b)
    (hxy : Conn G (ω ∩ D) x y) :
    ∃ z, b-R ≤ f z ∧ f z ≤ b ∧
      Conn G (ω ∩ (D \ internalEdges G {z | f z ≤ b})) x z := by
  let K := D \ internalEdges G {z | f z ≤ b}
  have aux : ∀ z, Conn G (ω ∩ D) x z →
      (∃ v, b-R ≤ f v ∧ f v ≤ b ∧ Conn G (ω ∩ K) x v) ∨
        (b < f z ∧ Conn G (ω ∩ K) x z) := by
    intro z hz
    induction hz with
    | refl => exact Or.inr ⟨hx,conn_refl G _ x⟩
    | @tail v w hxv hvw ih =>
      rcases ih with ih | ⟨hv,hxv⟩
      · exact Or.inl ih
      · obtain ⟨e,he,heq⟩ := hvw
        have heK : e ∈ K := ⟨he.2,fun hh => (not_le_of_gt hv) (hh v (by rw [heq]; simp))⟩
        have hxw : Conn G (ω ∩ K) x w := hxv.tail ⟨e,⟨he.1,heK⟩,heq⟩
        by_cases hw : f w ≤ b
        · have hh := (abs_le.mp (hjump e v w (by rw [heq]; simp) (by rw [heq]; simp))).1
          exact Or.inl ⟨w,by linarith,hw,hxw⟩
        · exact Or.inr ⟨lt_of_not_ge hw,hxw⟩
  rcases aux y hxy with hh | hh
  · exact hh
  · exact ((not_lt_of_ge hy) hh.1).elim

lemma connection_restrict_below_peak (D J : Set E) (hJD : J ⊆ D)
    (f : V → ℝ) (c : ℝ) (ω : Set E) (x y : V)
    (hpeak : ∀ z, Conn G (ω ∩ D) x z → f z ≤ c)
    (hxy : Conn G (ω ∩ J) x y) :
    Conn G (ω ∩ (J ∩ internalEdges G {z | f z ≤ c})) x y := by
  have hh := conn_restrict_cluster_of_subset G (ω ∩ D) x
    (Set.inter_subset_inter_right _ hJD) (mem_cluster_self G _ x) hxy
  have hs : cluster G (ω ∩ D) x ⊆ {z | f z ≤ c} := hpeak
  simpa only [Set.inter_assoc] using conn_mono G
    (Set.inter_subset_inter_right _ (internalEdges_mono G hs)) hh

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma adjustedStrictHalfspacePeak_iff_avoid (a : V → ℝ) (d : ℝ) (ω : Set E) (x : V) :
    G.adjustedStrictHalfspacePeak a d ω x x ↔
      ω ∉ restrictedHit G.ends (Percolation.internalEdges G.ends
        {z | d ≤ G.orbitAdjustedHeight a x z}) x
          {z | z ≠ x ∧ 0 ≤ G.orbitAdjustedHeight a x z} := by
  constructor
  · intro hp ⟨z,⟨hzx,hz⟩,hconn⟩
    exact (not_lt_of_ge hz) (hp z hconn hzx)
  · intro hp z hz hzx
    exact lt_of_not_ge fun hh => hp ⟨z,⟨hzx,hh⟩,hz⟩

lemma strict_peak_slab_band_count_eq (a : V → ℝ) (r l u : ℝ) (hlu : l ≤ u)
    (ω : Set E) (x : V) :
    G.strictPeakSlabBandCount a r l u ω x =
      (restrictedHit G.ends (Percolation.internalEdges G.ends
        {z | l-r ≤ G.orbitAdjustedHeight a x z}) x
          {z | z ≠ x ∧ 0 ≤ G.orbitAdjustedHeight a x z})ᶜ.indicator
      (fun ω => restrictedLayerCount G.ends (Percolation.internalEdges G.ends
        {z | u-r ≤ G.orbitAdjustedHeight a x z})
          {z | l ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ u} ω x) ω := by
  by_cases hp : G.adjustedStrictHalfspacePeak a (l-r) ω x x
  · have havoid := (G.adjustedStrictHalfspacePeak_iff_avoid a (l-r) ω x).mp hp
    rw [Set.indicator_of_mem havoid]
    apply tsum_congr
    intro y
    have hupper : ∀ z, Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
        {z | l-r ≤ G.orbitAdjustedHeight a x z}) x z → G.orbitAdjustedHeight a x z ≤ 0 := by
      intro z hz
      by_cases hzx : z=x
      · simp only [hzx,G.orbitAdjustedHeight_self,le_refl]
      · exact (hp z hz hzx).le
    have hc : Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
        {z | u-r ≤ G.orbitAdjustedHeight a x z}) x y ↔
      Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
        {z | u-r ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ 0}) x y := by
      constructor
      · intro hh
        have hj : Percolation.internalEdges G.ends {z | u-r ≤ G.orbitAdjustedHeight a x z} ⊆
            Percolation.internalEdges G.ends {z | l-r ≤ G.orbitAdjustedHeight a x z} :=
          Percolation.internalEdges_mono G.ends (fun z hz => by
            change u-r ≤ G.orbitAdjustedHeight a x z at hz
            change l-r ≤ G.orbitAdjustedHeight a x z
            linarith)
        have h := connection_restrict_below_peak G.ends _ _ hj (G.orbitAdjustedHeight a x) 0 ω x y hupper hh
        apply Percolation.conn_mono G.ends (Set.inter_subset_inter_right _ ?_) h
        rintro e ⟨he,he'⟩ z hze
        exact ⟨he z hze,he' z hze⟩
      · exact Percolation.conn_mono G.ends (Set.inter_subset_inter_right _
          (Percolation.internalEdges_mono G.ends (fun _ hz => hz.1)))
    unfold strictPeakSlabBandTransport
    simp only [hp,true_and,←hc,Set.mem_ofPred_eq,and_comm]
    split_ifs <;> rfl
  · have havoid := mt (G.adjustedStrictHalfspacePeak_iff_avoid a (l-r) ω x).mpr hp
    rw [Set.indicator_of_notMem havoid]
    apply ENNReal.tsum_eq_zero.mpr
    intro y
    simp only [strictPeakSlabBandTransport,hp,false_and,ite_false]

end CriticalPercolation.BondGraph

end

end OAI
