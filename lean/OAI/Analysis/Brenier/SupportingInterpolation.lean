import OAI.Analysis.Brenier.Translation

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace Problem358.SupportingMapInterpolation

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A globally supporting selection; finite affine maximizers satisfy this directly. -/
def Supports (u : F → ℝ) (T : F → F) : Prop :=
  ∀ x z, u x + ⟪z - x, T x⟫ ≤ u z

def quotient (u : F → ℝ) (h : ℝ) (e x : F) : ℝ :=
  (u (x + h • e) - u x) / h

def slope (T : F → F) (e x : F) : ℝ := ⟪e, T x⟫

/-- Supporting inequalities at the two ends sandwich the forward quotient.
This avoids all differentiability and null-set choices in finite-map interpolation. -/
lemma slope_le_quotient_le_shift {u : F → ℝ} {T : F → F}
    (hs : Supports u T) {h : ℝ} (hh : 0 < h) (e x : F) :
    slope T e x ≤ quotient u h e x ∧
      quotient u h e x ≤ slope T e (x + h • e) := by
  have h₀ := hs x (x + h • e)
  have h₁ := hs (x + h • e) x
  have he₀ : x + h • e - x = h • e := by abel
  have he₁ : x - (x + h • e) = (-h) • e := by
    rw [neg_smul]
    abel
  rw [he₀, real_inner_smul_left] at h₀
  rw [he₁, real_inner_smul_left] at h₁
  unfold slope quotient
  constructor
  · apply (le_div_iff₀ hh).mpr
    linarith
  · apply (div_le_iff₀ hh).mpr
    linarith

lemma slope_monotone_shift {u : F → ℝ} {T : F → F}
    (hs : Supports u T) {h : ℝ} (hh : 0 < h) (e x : F) :
    slope T e x ≤ slope T e (x + h • e) :=
  (slope_le_quotient_le_shift hs hh e x).1.trans
    (slope_le_quotient_le_shift hs hh e x).2

lemma abs_slope_le {T : F → F} {L : ℝ} (hL : ∀ x, ‖T x‖ ≤ L)
    {e : F} (he : ‖e‖ ≤ 1) (x : F) : |slope T e x| ≤ L := by
  unfold slope
  calc
    |⟪e, T x⟫| ≤ ‖e‖ * ‖T x‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 * L := mul_le_mul he (hL x) (norm_nonneg _) (by norm_num)
    _ = L := one_mul _

/-- Squared quotient error is controlled by the monotone slope increment. -/
lemma quotient_error_sq_le {u : F → ℝ} {T : F → F}
    (hs : Supports u T) {h L : ℝ} (hh : 0 < h)
    (hL : ∀ x, ‖T x‖ ≤ L) {e : F} (he : ‖e‖ ≤ 1) (x : F) :
    (quotient u h e x - slope T e x) ^ 2 ≤
      2 * L * (slope T e (x + h • e) - slope T e x) := by
  have hq := slope_le_quotient_le_shift hs hh e x
  have hx := abs_le.mp (abs_slope_le hL he x)
  have hsx := abs_le.mp (abs_slope_le hL he (x + h • e))
  have hL0 : 0 ≤ L := (norm_nonneg (T x)).trans (hL x)
  have hδ : 0 ≤ quotient u h e x - slope T e x := sub_nonneg.mpr hq.1
  have hδbound : quotient u h e x - slope T e x ≤ 2 * L := by linarith
  have hprod := mul_nonneg hδ (sub_nonneg.mpr hδbound)
  nlinarith

lemma quotient_sub (u v : F → ℝ) (h : ℝ) (e x : F) :
    quotient (fun z => u z - v z) h e x = quotient u h e x - quotient v h e x := by
  unfold quotient
  ring

/-- The pointwise estimate whose integral gives cubic-root map stability. -/
lemma slope_difference_sq_le {u v : F → ℝ} {T S : F → F}
    (hu : Supports u T) (hv : Supports v S) {h L : ℝ} (hh : 0 < h)
    (hT : ∀ x, ‖T x‖ ≤ L) (hS : ∀ x, ‖S x‖ ≤ L)
    {e : F} (he : ‖e‖ ≤ 1) (x : F) :
    (slope T e x - slope S e x) ^ 2 ≤
      3 * (quotient (fun z => u z - v z) h e x) ^ 2 +
      6 * L * ((slope T e (x + h • e) - slope T e x) +
        (slope S e (x + h • e) - slope S e x)) := by
  have h₀ := quotient_error_sq_le hu hh hT he x
  have h₁ := quotient_error_sq_le hv hh hS he x
  rw [quotient_sub]
  nlinarith [sq_nonneg (quotient u h e x - quotient v h e x +
    (quotient u h e x - slope T e x)),
    sq_nonneg (quotient u h e x - quotient v h e x -
    (quotient v h e x - slope S e x)),
    sq_nonneg ((quotient u h e x - slope T e x) +
    (quotient v h e x - slope S e x))]

lemma slope_difference_sq_le_four {T S : F → F} {L : ℝ}
    (hT : ∀ x, ‖T x‖ ≤ L) (hS : ∀ x, ‖S x‖ ≤ L)
    {e : F} (he : ‖e‖ ≤ 1) (x : F) :
    (slope T e x - slope S e x) ^ 2 ≤ 4 * L ^ 2 := by
  have ht := abs_le.mp (abs_slope_le hT he x)
  have hs := abs_le.mp (abs_slope_le hS he x)
  have hL0 : 0 ≤ L := (norm_nonneg (T x)).trans (hT x)
  nlinarith [mul_nonneg (show 0 ≤ 2*L - (slope T e x - slope S e x) by linarith)
    (show 0 ≤ 2*L + (slope T e x - slope S e x) by linarith)]

end Problem358.SupportingMapInterpolation

namespace Problem358.SupportingMapInterpolation

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {μ : Measure F} [Measure.IsAddRightInvariant μ]

lemma measurable_slope {T : F → F} (hT : Measurable T) (e : F) :
    Measurable (slope T e) := by
  unfold slope
  exact (continuous_const.inner continuous_id).measurable.comp hT

omit [Measure.IsAddRightInvariant μ] in
lemma integrableOn_slope {T : F → F} (hT : Measurable T)
    {K : Set F} (hKfin : μ K ≠ ⊤) {L : ℝ} (hL : ∀ x, ‖T x‖ ≤ L)
    {e : F} (he : ‖e‖ ≤ 1) : IntegrableOn (slope T e) K μ := by
  apply μ.integrableOn_of_bounded hKfin (measurable_slope hT e).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using abs_slope_le hL he x

omit [Measure.IsAddRightInvariant μ] in
lemma integrableOn_slope_difference_sq {T S : F → F}
    (hT : Measurable T) (hS : Measurable S)
    {K : Set F} (hKfin : μ K ≠ ⊤) {L : ℝ}
    (hTL : ∀ x, ‖T x‖ ≤ L) (hSL : ∀ x, ‖S x‖ ≤ L)
    {e : F} (he : ‖e‖ ≤ 1) :
    IntegrableOn (fun x => (slope T e x - slope S e x) ^ 2) K μ := by
  have hm : Measurable (fun x => (slope T e x - slope S e x) ^ 2) :=
    ((measurable_slope hT e).sub (measurable_slope hS e)).pow_const 2
  apply μ.integrableOn_of_bounded hKfin hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact slope_difference_sq_le_four hTL hSL he x

/-- A derivative-free directional interpolation estimate.  All geometry of the
source is isolated in the lost mass of its translation core. -/
theorem integral_slope_difference_sq_le
    {u v : F → ℝ} {T S : F → F}
    (hu : Supports u T) (hv : Supports v S)
    (hT : Measurable T) (hS : Measurable S)
    {K : Set F} (hK : MeasurableSet K) (hKfin : μ K ≠ ⊤)
    {L h : ℝ} (hTL : ∀ x, ‖T x‖ ≤ L) (hSL : ∀ x, ‖S x‖ ≤ L)
    (hh : 0 < h) {e : F} (he : ‖e‖ ≤ 1)
    (hfm : Measurable (fun x => u x - v x))
    (hf : IntegrableOn (fun x => (u x - v x) ^ 2) K μ) :
    (∫ x in K, (slope T e x - slope S e x) ^ 2 ∂μ) ≤
      (12 / h ^ 2) * (∫ x in K, (u x - v x) ^ 2 ∂μ) +
      28 * L ^ 2 * μ.real (K \ (K ∩ (fun x => x + h • e) ⁻¹' K)) := by
  let A : Set F := K ∩ (fun x => x + h • e) ⁻¹' K
  have hA : MeasurableSet A := hK.inter (hK.preimage (measurable_id.add_const _))
  have hAK : A ⊆ K := Set.inter_subset_left
  have hBK : (fun x : F => x + h • e) '' A ⊆ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  have hAfin : μ A ≠ ⊤ := measure_ne_top_of_subset hAK hKfin
  have hL0 : 0 ≤ L := (norm_nonneg (T 0)).trans (hTL 0)
  have htK := integrableOn_slope hT hKfin hTL he
  have hsK := integrableOn_slope hS hKfin hSL he
  have hqK := integrableOn_slope_difference_sq hT hS hKfin hTL hSL he
  have htA := htK.mono_set hAK
  have hsA := hsK.mono_set hAK
  have htShift : IntegrableOn (fun x => slope T e (x + h • e)) A μ := by
    apply μ.integrableOn_of_bounded hAfin
      ((measurable_slope hT e).comp (measurable_id.add_const _)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, Function.comp_apply, id_eq] using abs_slope_le hTL he (x + h • e)
  have hsShift : IntegrableOn (fun x => slope S e (x + h • e)) A μ := by
    apply μ.integrableOn_of_bounded hAfin
      ((measurable_slope hS e).comp (measurable_id.add_const _)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, Function.comp_apply, id_eq] using abs_slope_le hSL he (x + h • e)
  have htInc : IntegrableOn (fun x => slope T e (x + h • e) - slope T e x) A μ := htShift.sub htA
  have hsInc : IntegrableOn (fun x => slope S e (x + h • e) - slope S e x) A μ := hsShift.sub hsA
  have hquot : IntegrableOn (fun x => (quotient (fun z => u z - v z) h e x) ^ 2) A μ :=
    integrableOn_translation_quotient_sq K hK (fun x => u x - v x) (h • e) h hfm hf
  have hcore := integral_mono_ae (hqK.mono_set hAK)
    ((hquot.const_mul 3).add ((htInc.add hsInc).const_mul (6 * L)))
    (Filter.Eventually.of_forall fun x => slope_difference_sq_le hu hv hh hTL hSL he x)
  simp only [Pi.add_apply] at hcore
  have hadd := integral_add (hquot.const_mul 3) ((htInc.add hsInc).const_mul (6 * L))
  have haddInc := integral_add htInc hsInc
  simp only [Pi.add_apply] at hadd haddInc
  rw [hadd, integral_const_mul, integral_const_mul, haddInc] at hcore
  have hpres : MeasurePreserving (fun x : F => x + h • e) μ μ :=
    measurePreserving_add_right μ (h • e)
  have hemb : MeasurableEmbedding (fun x : F => x + h • e) :=
    (MeasurableEquiv.addRight (h • e)).measurableEmbedding
  have htBound := abs_integral_increment_le_boundary hpres hemb hKfin hA hAK hBK htK
    (fun x _ => abs_slope_le hTL he x)
  have hsBound := abs_integral_increment_le_boundary hpres hemb hKfin hA hAK hBK hsK
    (fun x _ => abs_slope_le hSL he x)
  have htUpper := (le_abs_self _).trans htBound
  have hsUpper := (le_abs_self _).trans hsBound
  have hfBound := setIntegral_translation_quotient_sq_le K hK
    (fun x => u x - v x) (h • e) h hf
  change (∫ x in A, (quotient (fun z => u z - v z) h e x) ^ 2 ∂μ) ≤
    (4 / h ^ 2) * (∫ x in K, (u x - v x) ^ 2 ∂μ) at hfBound
  have hcoreBound : (∫ x in A, (slope T e x - slope S e x) ^ 2 ∂μ) ≤
      (12 / h ^ 2) * (∫ x in K, (u x - v x) ^ 2 ∂μ) +
      24 * L ^ 2 * μ.real (K \ A) := by
    calc
      _ ≤ 3 * (∫ x in A, (quotient (fun z => u z - v z) h e x) ^ 2 ∂μ) +
          6 * L * ((∫ x in A, slope T e (x + h • e) - slope T e x ∂μ) +
            ∫ x in A, slope S e (x + h • e) - slope S e x ∂μ) := hcore
      _ ≤ 3 * ((4 / h ^ 2) * (∫ x in K, (u x - v x) ^ 2 ∂μ)) +
          6 * L * (2 * L * μ.real (K \ A) + 2 * L * μ.real (K \ A)) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hfBound (by norm_num))
          (mul_le_mul_of_nonneg_left (add_le_add htUpper hsUpper) (by positivity))
      _ = _ := by ring
  have hstripfin : μ (K \ A) < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.sdiff_subset) hKfin.lt_top
  have hstripBound : (∫ x in K \ A, (slope T e x - slope S e x) ^ 2 ∂μ) ≤
      4 * L ^ 2 * μ.real (K \ A) := by
    have hb := norm_setIntegral_le_of_norm_le_const (f := fun x =>
        (slope T e x - slope S e x) ^ 2) (C := 4 * L ^ 2) hstripfin
      (fun x _ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact slope_difference_sq_le_four hTL hSL he x)
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hb)
  rw [setIntegral_sdiff hA hqK hAK] at hstripBound
  change (∫ x in K, (slope T e x - slope S e x) ^ 2 ∂μ) ≤
    (12 / h ^ 2) * (∫ x in K, (u x - v x) ^ 2 ∂μ) + 28 * L ^ 2 * μ.real (K \ A)
  linarith

end Problem358.SupportingMapInterpolation

namespace Problem358.SupportingMapInterpolation

variable {ι : Type*} [Fintype ι]
  {μ : Measure (EuclideanSpace ℝ ι)} [Measure.IsAddRightInvariant μ]

/-- Summing the directional estimate gives full-dimensional interpolation for
bounded supporting maps. Only a linear boundary-strip estimate is needed. -/
theorem integral_norm_sub_sq_le_of_boundary_strip
    {u v : EuclideanSpace ℝ ι → ℝ}
    {T S : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hu : Supports u T) (hv : Supports v S)
    (hT : Measurable T) (hS : Measurable S)
    {K : Set (EuclideanSpace ℝ ι)} (hK : MeasurableSet K) (hKfin : μ K ≠ ⊤)
    {L C h : ℝ} (hTL : ∀ x, ‖T x‖ ≤ L) (hSL : ∀ x, ‖S x‖ ≤ L)
    (hh : 0 < h)
    (hfm : Measurable (fun x => u x - v x))
    (hf : IntegrableOn (fun x => (u x - v x) ^ 2) K μ)
    (hstrip : ∀ e : EuclideanSpace ℝ ι, ‖e‖ ≤ 1 →
      μ.real {x | x ∈ K ∧ x + h • e ∉ K} ≤ C * h) :
    (∫ x in K, ‖T x - S x‖ ^ 2 ∂μ) ≤
      (12 * (Fintype.card ι : ℝ) / h ^ 2) * (∫ x in K, (u x - v x) ^ 2 ∂μ) +
      28 * (Fintype.card ι : ℝ) * L ^ 2 * C * h := by
  classical
  have hcoordInt (i : ι) : IntegrableOn (fun x => (T x i - S x i) ^ 2) K μ := by
    simpa only [slope, EuclideanSpace.inner_single_left, map_one, one_mul] using
      (integrableOn_slope_difference_sq hT hS hKfin hTL hSL
        (e := EuclideanSpace.single i 1) (by simp))
  have hcoordBound (i : ι) :
      (∫ x in K, (T x i - S x i) ^ 2 ∂μ) ≤
        (12 / h ^ 2) * (∫ x in K, (u x - v x) ^ 2 ∂μ) + 28 * L ^ 2 * C * h := by
    let e : EuclideanSpace ℝ ι := EuclideanSpace.single i 1
    have he : ‖e‖ ≤ 1 := by simp [e]
    have hb := integral_slope_difference_sq_le hu hv hT hS hK hKfin hTL hSL
      hh he hfm hf
    have hset : K \ (K ∩ (fun x => x + h • e) ⁻¹' K) =
        {x | x ∈ K ∧ x + h • e ∉ K} := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
      tauto
    rw [hset] at hb
    have hbound := hb.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (hstrip e he) (by positivity : 0 ≤ 28 * L ^ 2)))
    simpa only [e, slope, EuclideanSpace.inner_single_left, map_one, one_mul, mul_assoc] using hbound
  calc
    (∫ x in K, ‖T x - S x‖ ^ 2 ∂μ) =
        ∫ x in K, ∑ i, (T x i - S x i) ^ 2 ∂μ := by
      congr 1
      funext x
      simp [EuclideanSpace.real_norm_sq_eq]
    _ = ∑ i, ∫ x in K, (T x i - S x i) ^ 2 ∂μ :=
      integral_finsetSum _ fun i _ => hcoordInt i
    _ ≤ ∑ _i : ι, ((12 / h ^ 2) * (∫ x in K, (u x - v x) ^ 2 ∂μ) + 28 * L ^ 2 * C * h) :=
      Finset.sum_le_sum fun i _ => hcoordBound i
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end Problem358.SupportingMapInterpolation

end

end OAI
