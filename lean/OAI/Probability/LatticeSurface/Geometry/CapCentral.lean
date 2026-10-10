import Mathlib
import OAI.Probability.LatticeSurface.Convexity.BrunnMinkowski
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.WeightedPrekopa
import OAI.Probability.LatticeSurface.Dynamics.DisplacementInequality

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace FacetVolume

end FacetVolume

namespace ExtremalEdges

open scoped ENNReal

lemma finite_volume_brunn_minkowski {I : Type*} [Fintype I]
    {K L M : Set (I → ℝ)} {s t : ℝ}
    (hK : IsCompact K) (hL : IsCompact L) (hM : IsCompact M)
    (hKn : K.Nonempty) (hLn : L.Nonempty) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+t=1)
    (hcomb : ∀ x ∈ K, ∀ y ∈ L, s • x+t • y ∈ M) :
    ((volume K).toReal)^s*((volume L).toReal)^t ≤ (volume M).toReal := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card I) => ℝ) (Fintype.equivFin I)
  have hec : Continuous e := (Homeomorph.piCongrLeft (Fintype.equivFin I)).continuous
  have hemp := (volume_measurePreserving_piCongrLeft
    (fun _ : Fin (Fintype.card I) => ℝ) (Fintype.equivFin I)).symm e
  have hv (S : Set (I → ℝ)) (hS : IsCompact S) : volume (e '' S) = volume S := by
    rw [e.image_eq_preimage_symm]
    exact hemp.measure_preimage hS.measurableSet.nullMeasurableSet
  have hm := FacetVolume.compact_volume_brunn_minkowski
    (hK.image hec) (hL.image hec) (hM.image hec) (hKn.image _) (hLn.image _) hs ht hst
    (fun x hx y hy => by
      rcases hx with ⟨a,ha,rfl⟩
      rcases hy with ⟨b,hb,rfl⟩
      refine ⟨s • a+t • b,hcomb a ha b hb,?_⟩
      funext i
      simp [e, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply])
  simpa only [hv K hK, hv L hL, hv M hM] using hm

def productSlice {I J : Type*} (K : Set ((I → ℝ) × (J → ℝ))) (a : J → ℝ) :
    Set (I → ℝ) := {h | (h,a) ∈ K}

lemma compact_productSlice {I J : Type*} [Fintype I] [Fintype J]
    {K : Set ((I → ℝ) × (J → ℝ))} (hK : IsCompact K) (a : J → ℝ) :
    IsCompact (productSlice K a) := by
  have he : Prod.fst '' (K ∩ {p | p.2 = a}) = productSlice K a := by
    ext h
    constructor
    · rintro ⟨⟨h,b⟩,⟨hh,hb⟩,rfl⟩
      dsimp at hb
      subst b
      exact hh
    · intro hh; exact ⟨(h,a),⟨hh,rfl⟩,rfl⟩
  rw [← he]
  exact (hK.inter_right (isClosed_eq continuous_snd continuous_const)).image continuous_fst

lemma volume_productSlice_neg {I J : Type*} [Fintype I] [Fintype J]
    {K : Set ((I → ℝ) × (J → ℝ))} (hK : IsCompact K)
    (hn : ∀ p ∈ K, -p ∈ K) (a : J → ℝ) :
    volume (productSlice K (-a)) = volume (productSlice K a) := by
  have he : productSlice K (-a) = Neg.neg ⁻¹' productSlice K a := by
    ext h
    change (h,-a) ∈ K ↔ (-h,a) ∈ K
    constructor
    · intro hh; simpa using hn _ hh
    · intro hh; simpa using hn _ hh
  rw [he]
  exact (Measure.measurePreserving_neg volume).measure_preimage
    (compact_productSlice hK a).measurableSet.nullMeasurableSet

theorem central_productSlice_max {I J : Type*} [Fintype I] [Fintype J]
    {K : Set ((I → ℝ) × (J → ℝ))} (hK : IsCompact K) (hc : Convex ℝ K)
    (hn : ∀ p ∈ K, -p ∈ K) (a : J → ℝ) :
    volume (productSlice K a) ≤ volume (productSlice K 0) := by
  apply (ENNReal.toReal_le_toReal (compact_productSlice hK a).measure_ne_top
    (compact_productSlice hK 0).measure_ne_top).mp
  by_cases hz : (volume (productSlice K a)).toReal = 0
  · rw [hz]; positivity
  have hp : 0 < (volume (productSlice K a)).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz)
  have hsn : (productSlice K a).Nonempty := by
    by_contra hh
    simp [Set.not_nonempty_iff_eq_empty.mp hh] at hp
  have hnn : (productSlice K (-a)).Nonempty := by
    obtain ⟨x,hx⟩ := hsn
    exact ⟨-x, by simpa only [productSlice, mem_ofPred_eq, Prod.neg_mk] using hn (x,a) hx⟩
  have hb := finite_volume_brunn_minkowski (compact_productSlice hK a)
    (compact_productSlice hK (-a)) (compact_productSlice hK 0) hsn hnn
    (s := 1/2) (t := 1/2) (by norm_num) (by norm_num) (by norm_num)
    (fun x hx y hy => by
      have hh := hc hx hy (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ)+1/2=1)
      have he : (1/2:ℝ) • (x,a)+(1/2:ℝ) • (y,-a) = ((1/2:ℝ) • x+(1/2:ℝ) • y,0) := by
        ext i <;> simp
      change ((1/2:ℝ) • x+(1/2:ℝ) • y, 0) ∈ K
      rw [← he]
      exact hh)
  rw [volume_productSlice_neg hK hn, ← Real.rpow_add hp] at hb
  norm_num at hb
  exact hb

theorem product_small_set_bound {I J : Type*} [Fintype I] [Fintype J]
    {K : Set ((I → ℝ) × (J → ℝ))} (hK : IsCompact K) (hc : Convex ℝ K)
    (hn : ∀ p ∈ K, -p ∈ K) (S : Set (J → ℝ)) (hS : MeasurableSet S) :
    volume (K ∩ Prod.snd ⁻¹' S) ≤ volume S * volume (productSlice K 0) := by
  change ((volume : Measure (I → ℝ)).prod (volume : Measure (J → ℝ))) _ ≤ _
  rw [Measure.prod_apply_symm (hK.measurableSet.inter (hS.preimage measurable_snd))]
  calc
    (∫⁻ a, volume ((fun h : I → ℝ => (h,a)) ⁻¹' (K ∩ Prod.snd ⁻¹' S))) ≤
        ∫⁻ a, S.indicator (fun _ => volume (productSlice K 0)) a := by
      apply lintegral_mono
      intro a
      by_cases ha : a ∈ S
      · rw [Set.indicator_of_mem ha]
        have he : ((fun h : I → ℝ => (h,a)) ⁻¹' (K ∩ Prod.snd ⁻¹' S)) = productSlice K a := by
          ext h; simp [productSlice, ha]
        simpa only [he] using central_productSlice_max hK hc hn a
      · rw [Set.indicator_of_notMem ha]
        have he : ((fun h : I → ℝ => (h,a)) ⁻¹' (K ∩ Prod.snd ⁻¹' S)) = ∅ := by
          ext h; simp [ha]
        simp only [he, measure_empty, le_refl]
    _ = _ := by rw [lintegral_indicator hS, lintegral_const, Measure.restrict_apply_univ, mul_comm]

end ExtremalEdges

end

end OAI
