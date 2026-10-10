import Mathlib
import OAI.Probability.LatticeSurface.Convexity.BrunnMinkowski
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.FacetDeficitAnalytic
import OAI.Probability.LatticeSurface.Convexity.FacetQuantile
import OAI.Probability.LatticeSurface.Convexity.InteriorQuantile
import OAI.Probability.LatticeSurface.Convexity.QuantileCentroid
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.QuantitativeTransport
import OAI.Probability.LatticeSurface.Convexity.SliceDensity
import OAI.Probability.LatticeSurface.Convexity.SliceGeometry
import OAI.Probability.LatticeSurface.Convexity.SliceMoments
import OAI.Probability.LatticeSurface.Convexity.WeightedPrekopa
import OAI.Probability.LatticeSurface.Dynamics.DisplacementInequality

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace FacetVolume

end FacetVolume

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace SliceTransport

end SliceTransport

namespace FacetVolume

lemma midpoint_slice_volume {n : ℕ} {K L M : Set (Fin (n+1) → ℝ)} {u v : ℝ}
    (hK : IsCompact K) (hL : IsCompact L) (hM : IsCompact M)
    (hKu : 0 < sliceVolume K u) (hLv : 0 < sliceVolume L v)
    (hcomb : ∀ x ∈ K, ∀ y ∈ L, (1/2 : ℝ) • x+(1/2 : ℝ) • y ∈ M) :
    Real.sqrt (sliceVolume K u*sliceVolume L v) ≤ sliceVolume M ((u+v)/2) := by
  have h := slices_combination_volume hK hL hM (slice_nonempty_of_volume_pos hKu)
    (slice_nonempty_of_volume_pos hLv) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ)+1/2=1) hcomb
  convert h using 1
  · rw [Real.sqrt_mul (sliceVolume_nonneg K u), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  · congr 1
    ring

lemma exists_midpoint_Ioo {a b c d z : ℝ} (hab : a < b) (hcd : c < d)
    (hz : z ∈ Ioo ((a+c)/2) ((b+d)/2)) :
    ∃ x ∈ Ioo a b, ∃ y ∈ Ioo c d, (x+y)/2=z := by
  let θ := (2*z-a-c)/(b+d-a-c)
  have hden : 0 < b+d-a-c := by linarith
  have hθ : 0 < θ := div_pos (by linarith [hz.1]) hden
  have hθ1 : θ < 1 := by
    rw [div_lt_one hden]
    linarith [hz.2]
  refine ⟨a+θ*(b-a), ⟨?_,?_⟩, c+θ*(d-c), ⟨?_,?_⟩, ?_⟩
  · nlinarith [mul_pos hθ (sub_pos.mpr hab)]
  · nlinarith [mul_pos (sub_pos.mpr hθ1) (sub_pos.mpr hab)]
  · nlinarith [mul_pos hθ (sub_pos.mpr hcd)]
  · nlinarith [mul_pos (sub_pos.mpr hθ1) (sub_pos.mpr hcd)]
  · dsimp only [θ]
    field_simp
    ring

lemma midpoint_sliceVolume_pos {n : ℕ} {K L M : Set (Fin (n+1) → ℝ)} {a b c d : ℝ}
    (hK : IsCompact K) (hL : IsCompact L) (hM : IsCompact M)
    (hab : a < b) (hcd : c < d)
    (hKpos : ∀ u ∈ Ioo a b, 0 < sliceVolume K u)
    (hLpos : ∀ v ∈ Ioo c d, 0 < sliceVolume L v)
    (hcomb : ∀ x ∈ K, ∀ y ∈ L, (1/2 : ℝ) • x+(1/2 : ℝ) • y ∈ M) :
    ∀ z ∈ Ioo ((a+c)/2) ((b+d)/2), 0 < sliceVolume M z := by
  intro z hz
  obtain ⟨u,hu,v,hv,rfl⟩ := exists_midpoint_Ioo hab hcd hz
  exact (Real.sqrt_pos.2 (mul_pos (hKpos u hu) (hLpos v hv))).trans_le
    (midpoint_slice_volume hK hL hM (hKpos u hu) (hLpos v hv) hcomb)

theorem compact_body_facet_deficit {n : ℕ} {K L M : Set (Fin (n+1) → ℝ)}
    {a b c d C A : ℝ} {zK zL : Fin (n+1) → ℝ}
    (hK : IsCompact K) (hL : IsCompact L) (hM : IsCompact M)
    (hcK : Convex ℝ K) (hcL : Convex ℝ L) (hcM : Convex ℝ M)
    (hab : a < b) (hcd : c < d) (hC : 0 < C)
    (hzK : zK ∈ K) (hzKa : zK 0=a) (hzL : zL ∈ L) (hzLc : zL 0=c)
    (hKproj : ∀ z ∈ K, z 0 ∈ Icc a b) (hLproj : ∀ z ∈ L, z 0 ∈ Icc c d)
    (hKtop : 0 < sliceVolume K b) (hLtop : 0 < sliceVolume L d)
    (hKwidth : b-a ≤ C) (hLwidth : d-c ≤ C)
    (hKA : b-a ≤ A) (hLA : d-c ≤ A)
    (hKfacet : (volume K).toReal ≤ C*sliceVolume K b)
    (hLfacet : (volume L).toReal ≤ C*sliceVolume L d)
    (hcomb : ∀ x ∈ K, ∀ y ∈ L, (1/2 : ℝ) • x+(1/2 : ℝ) • y ∈ M) :
    ((b-(∫ z in K, z 0)/(volume K).toReal)-
      (d-(∫ z in L, z 0)/(volume L).toReal))^2/(8*C^2+A^2) ≤
    Real.log ((volume M).toReal/Real.sqrt ((volume K).toReal*(volume L).toReal)) := by
  have hKpos := sliceVolume_pos_Ioc hK hcK hzK hzKa hKtop
  have hLpos := sliceVolume_pos_Ioc hL hcL hzL hzLc hLtop
  have hKi : ∀ u ∈ Ioo a b, 0 < sliceVolume K u := fun u hu => hKpos u (Ioo_subset_Ioc_self hu)
  have hLi : ∀ u ∈ Ioo c d, 0 < sliceVolume L u := fun u hu => hLpos u (Ioo_subset_Ioc_self hu)
  have hMi := midpoint_sliceVolume_pos hK hL hM hab hcd hKi hLi hcomb
  have hf : SliceTransport.IntervalDensity (sliceVolume K) a b :=
    ⟨(integrable_sliceVolume hK).intervalIntegrable,
      continuousOn_sliceVolume hK hcK (convex_Ioo a b) isOpen_Ioo hKi⟩
  have hg : SliceTransport.IntervalDensity (sliceVolume L) c d :=
    ⟨(integrable_sliceVolume hL).intervalIntegrable,
      continuousOn_sliceVolume hL hcL (convex_Ioo c d) isOpen_Ioo hLi⟩
  have hh : SliceTransport.IntervalDensity (sliceVolume M) ((a+c)/2) ((b+d)/2) :=
    ⟨(integrable_sliceVolume hM).intervalIntegrable,
      continuousOn_sliceVolume hM hcM (convex_Ioo _ _) isOpen_Ioo hMi⟩
  have hvf : ∀ p ∈ Ioo 0 1, SliceTransport.velocity (sliceVolume K) a b p ≤ C/p := by
    intro p hp
    apply SliceTransport.velocity_le_div_probability hf hab hKpos
      (log_sliceVolume_concave hK hcK (convex_Ioc a b) hKpos) hKwidth _ hp
    rwa [intervalIntegral_sliceVolume hK hab.le hKproj]
  have hvg : ∀ p ∈ Ioo 0 1, SliceTransport.velocity (sliceVolume L) c d p ≤ C/p := by
    intro p hp
    apply SliceTransport.velocity_le_div_probability hg hcd hLpos
      (log_sliceVolume_concave hL hcL (convex_Ioc c d) hLpos) hLwidth _ hp
    rwa [intervalIntegral_sliceVolume hL hcd.le hLproj]
  have h1 := SliceTransport.interval_facet_deficit hf hg hh hab hcd hC hKi hLi hvf hvg hKA hLA
    (sliceVolume_nonneg M) (fun x hx y hy => midpoint_slice_volume hK hL hM (hKi x hx) (hLi y hy) hcomb)
  rw [intervalIntegral_sliceVolume hK hab.le hKproj,
    intervalIntegral_sliceVolume hL hcd.le hLproj,
    intervalIntegral_sliceMoment hK hab.le hKproj,
    intervalIntegral_sliceMoment hL hcd.le hLproj] at h1
  refine h1.trans (Real.log_le_log ?_ ?_)
  · apply div_pos
    · exact SliceTransport.integral_positive hh hMi (by linarith)
    · apply Real.sqrt_pos.2
      apply mul_pos
      · rw [← intervalIntegral_sliceVolume hK hab.le hKproj]
        exact SliceTransport.integral_positive hf hKi hab
      · rw [← intervalIntegral_sliceVolume hL hcd.le hLproj]
        exact SliceTransport.integral_positive hg hLi hcd
  · apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    rw [intervalIntegral.integral_of_le (by linarith : (a+c)/2 ≤ (b+d)/2), ← integral_sliceVolume hM]
    exact setIntegral_le_integral (integrable_sliceVolume hM)
      (Filter.Eventually.of_forall (sliceVolume_nonneg M))

end FacetVolume

end
end

end OAI
