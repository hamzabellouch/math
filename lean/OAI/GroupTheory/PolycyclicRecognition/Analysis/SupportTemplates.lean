import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportNorm
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace OAI

/-! # Support exponents of compact templates

The support exponent is the finite maximum of word-basis exponents, with
each letter allowed its own supporting point. Balance gives translation
invariance, and segments recover the support norm.
-/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open scoped BigOperators

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
  (D : PolycyclicRecognition.SupportDatum W I B)

def weightSupport (E : Set W) (i : I) : ℝ := sSup (D.weight i '' E)

def basisTemplateSupport (E : Set W) (b : B) : ℝ :=
  ∑ i, (D.multiplicity b i : ℝ) * D.weightSupport E i

def templateSupport (E : Set W) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (D.basisTemplateSupport E)

omit [Nonempty B] in
theorem weight_le_weightSupport {E : Set W} (hE : IsCompact E)
    {x : W} (hx : x ∈ E) (i : I) : D.weight i x ≤ D.weightSupport E i :=
  le_csSup (hE.image (D.weight i).continuous_of_finiteDimensional).bddAbove ⟨x, hx, rfl⟩

omit [Nonempty B] in
theorem exists_weightSupport_point {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (i : I) : ∃ x ∈ E, D.weightSupport E i = D.weight i x :=
  hE.exists_sSup_image_eq hne (D.weight i).continuous_of_finiteDimensional.continuousOn

omit [Nonempty B] in
theorem weightSupport_translate {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (w : W) (i : I) :
    D.weightSupport ((fun x => x + w) '' E) i = D.weightSupport E i + D.weight i w := by
  let E' := (fun x => x + w) '' E
  have hc : IsCompact E' := hE.image (continuous_id.add_const w)
  have hn : E'.Nonempty := hne.image _
  obtain ⟨x, hx, hsup⟩ := D.exists_weightSupport_point hE hne i
  obtain ⟨y, ⟨z, hz, rfl⟩, hsup'⟩ := D.exists_weightSupport_point hc hn i
  apply le_antisymm
  · rw [hsup', map_add]
    linarith [D.weight_le_weightSupport hE hz i]
  · rw [hsup, ← map_add]
    exact D.weight_le_weightSupport hc ⟨x, hx, rfl⟩ i

omit [Nonempty B] in
theorem weightSupport_convexHull {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (i : I) : D.weightSupport (convexHull ℝ E) i = D.weightSupport E i := by
  have hb : ∀ x ∈ convexHull ℝ E, D.weight i x ≤ D.weightSupport E i := by
    apply convexHull_min
    · exact fun x hx => D.weight_le_weightSupport hE hx i
    · exact convex_halfSpace_le (show IsLinearMap ℝ (D.weight i) from ⟨(D.weight i).map_add, (D.weight i).map_smul⟩) _
  have hne' : (D.weight i '' convexHull ℝ E).Nonempty :=
    (hne.mono (subset_convexHull ℝ E)).image _
  apply le_antisymm
  · exact csSup_le hne' (by rintro _ ⟨x, hx, rfl⟩; exact hb x hx)
  · obtain ⟨x, hx, hsup⟩ := D.exists_weightSupport_point hE hne i
    rw [hsup]
    exact le_csSup ⟨D.weightSupport E i, by rintro _ ⟨x, hx, rfl⟩; exact hb x hx⟩
      ⟨x, subset_convexHull ℝ E hx, rfl⟩

omit [Nonempty B] [FiniteDimensional ℝ W] in
theorem weightSupport_segment (w : W) (i : I) :
    D.weightSupport (segment ℝ 0 w) i = max 0 (D.weight i w) := by
  unfold weightSupport
  change sSup ((D.weight i).toAffineMap '' segment ℝ 0 w) = _
  rw [image_segment]
  simp only [LinearMap.coe_toAffineMap, map_zero]
  rw [segment_eq_Icc']
  exact csSup_Icc min_le_max

omit [Nonempty B] in
theorem basisTemplateSupport_translate {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (w : W) (b : B) :
    D.basisTemplateSupport ((fun x => x + w) '' E) b = D.basisTemplateSupport E b := by
  simp only [basisTemplateSupport, D.weightSupport_translate hE hne, mul_add,
    Finset.sum_add_distrib, D.balanced, add_zero]

theorem templateSupport_translate {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (w : W) : D.templateSupport ((fun x => x + w) '' E) = D.templateSupport E := by
  simp only [templateSupport, D.basisTemplateSupport_translate hE hne]

theorem templateSupport_convexHull {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) :
    D.templateSupport (convexHull ℝ E) = D.templateSupport E := by
  unfold templateSupport
  congr 1
  funext b
  simp only [basisTemplateSupport, D.weightSupport_convexHull hE hne]

omit [FiniteDimensional ℝ W] in
@[simp] theorem templateSupport_segment (w : W) :
    D.templateSupport (segment ℝ 0 w) = D.segmentSupport w := by
  unfold templateSupport segmentSupport
  congr 1
  funext b
  simp only [basisTemplateSupport, D.weightSupport_segment, basisSupport]

omit [Nonempty B] in
theorem basisTemplateSupport_nonneg {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (b : B) : 0 ≤ D.basisTemplateSupport E b := by
  obtain ⟨x, hx⟩ := hne
  calc
    0 = ∑ i, (D.multiplicity b i : ℝ) * D.weight i x := (D.balanced b x).symm
    _ ≤ _ := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (D.weight_le_weightSupport hE hx i) (Nat.cast_nonneg _))

omit [FiniteDimensional ℝ W] in
theorem basisTemplateSupport_le (E : Set W) (b : B) :
    D.basisTemplateSupport E b ≤ D.templateSupport E :=
  Finset.le_sup' (f := D.basisTemplateSupport E) (Finset.mem_univ b)

omit [FiniteDimensional ℝ W] in
theorem templateSupport_le {E : Set W} {r : ℝ}
    (h : ∀ b, D.basisTemplateSupport E b ≤ r) : D.templateSupport E ≤ r :=
  Finset.sup'_le _ _ fun b _ => h b

theorem templateSupport_nonneg {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) :
    0 ≤ D.templateSupport E := by
  obtain ⟨b⟩ := ‹Nonempty B›
  exact (D.basisTemplateSupport_nonneg hE hne b).trans (D.basisTemplateSupport_le E b)

omit [Nonempty B] in
/-- Nearby support positions change each letter exponent by at most the
operator norm of that letter times the error in position. -/
theorem weightSupport_le_of_nearby {E F : Set W} (hE : IsCompact E) (hneE : E.Nonempty)
    (hF : IsCompact F) {δ : ℝ}
    (hnear : ∀ x ∈ E, ∃ y ∈ F, ‖x - y‖ ≤ δ) (i : I) :
    D.weightSupport E i ≤ D.weightSupport F i + ‖(D.weight i).toContinuousLinearMap‖ * δ := by
  obtain ⟨x, hx, hsup⟩ := D.exists_weightSupport_point hE hneE i
  obtain ⟨y, hy, hxy⟩ := hnear x hx
  have hop := (D.weight i).toContinuousLinearMap.le_opNorm (x - y)
  change ‖D.weight i (x - y)‖ ≤ _ at hop
  rw [map_sub, Real.norm_eq_abs] at hop
  have hh := hop.trans (mul_le_mul_of_nonneg_left hxy
    (norm_nonneg (D.weight i).toContinuousLinearMap))
  have hy' := D.weight_le_weightSupport hF hy i
  rw [hsup]
  linarith [le_abs_self (D.weight i x - D.weight i y)]

/-- A fixed Lipschitz constant for the full template support. -/
def templateSupportConstant : ℝ :=
  ∑ b, ∑ i, (D.multiplicity b i : ℝ) * ‖(D.weight i).toContinuousLinearMap‖

omit [Nonempty B] in
theorem templateSupportConstant_nonneg : 0 ≤ D.templateSupportConstant :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
    (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)))

theorem templateSupport_le_of_nearby {E F : Set W} (hE : IsCompact E) (hneE : E.Nonempty)
    (hF : IsCompact F) {δ : ℝ} (hδ : 0 ≤ δ)
    (hnear : ∀ x ∈ E, ∃ y ∈ F, ‖x - y‖ ≤ δ) :
    D.templateSupport E ≤ D.templateSupport F + D.templateSupportConstant * δ := by
  apply D.templateSupport_le
  intro b
  have hc : (∑ i, (D.multiplicity b i : ℝ) * ‖(D.weight i).toContinuousLinearMap‖) ≤
      D.templateSupportConstant := by
    unfold templateSupportConstant
    exact Finset.single_le_sum
      (f := fun b => ∑ i, (D.multiplicity b i : ℝ) * ‖(D.weight i).toContinuousLinearMap‖)
      (fun b _ => Finset.sum_nonneg
        (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))) (Finset.mem_univ b)
  calc
    D.basisTemplateSupport E b ≤
        ∑ i, (D.multiplicity b i : ℝ) *
          (D.weightSupport F i + ‖(D.weight i).toContinuousLinearMap‖ * δ) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (D.weightSupport_le_of_nearby hE hneE hF hnear i) (Nat.cast_nonneg _))
    _ = D.basisTemplateSupport F b +
        (∑ i, (D.multiplicity b i : ℝ) * ‖(D.weight i).toContinuousLinearMap‖) * δ := by
      simp only [basisTemplateSupport, mul_add, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]
    _ ≤ D.templateSupport F + D.templateSupportConstant * δ :=
      add_le_add (D.basisTemplateSupport_le F b) (mul_le_mul_of_nonneg_right hc hδ)

/-- The form needed when the two compact height ranges approximate one
another, as in the forward/inverse stationary path comparison. -/
theorem abs_templateSupport_sub_le_of_nearby {E F : Set W}
    (hE : IsCompact E) (hneE : E.Nonempty) (hF : IsCompact F) (hneF : F.Nonempty)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hEF : ∀ x ∈ E, ∃ y ∈ F, ‖x - y‖ ≤ δ)
    (hFE : ∀ y ∈ F, ∃ x ∈ E, ‖y - x‖ ≤ δ) :
    |D.templateSupport E - D.templateSupport F| ≤ D.templateSupportConstant * δ := by
  have hf := D.templateSupport_le_of_nearby hE hneE hF hδ hEF
  have hg := D.templateSupport_le_of_nearby hF hneF hE hδ hFE
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The template exponent is Lipschitz for Hausdorff distance on nonempty
compact sets, with one constant depending only on the finite word data. -/
theorem abs_templateSupport_sub_le_hausdorffDist {E F : Set W}
    (hE : IsCompact E) (hneE : E.Nonempty) (hF : IsCompact F) (hneF : F.Nonempty) :
    |D.templateSupport E - D.templateSupport F| ≤
      D.templateSupportConstant * Metric.hausdorffDist E F := by
  have hfin := Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
    hneE hneF hE.isBounded hF.isBounded
  apply D.abs_templateSupport_sub_le_of_nearby hE hneE hF hneF Metric.hausdorffDist_nonneg
  · intro x hx
    obtain ⟨y, hy, heq⟩ := hF.exists_infDist_eq_dist hneF x
    refine ⟨y, hy, ?_⟩
    rw [← dist_eq_norm, ← heq]
    exact Metric.infDist_le_hausdorffDist_of_mem hx hfin
  · intro y hy
    obtain ⟨x, hx, heq⟩ := hE.exists_infDist_eq_dist hneE y
    refine ⟨x, hx, ?_⟩
    rw [← dist_eq_norm, ← heq, Metric.hausdorffDist_comm]
    exact Metric.infDist_le_hausdorffDist_of_mem hy
      (by rwa [Metric.hausdorffEDist_comm])

end PolycyclicRecognition.SupportDatum

end

end OAI
