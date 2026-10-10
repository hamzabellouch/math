import OAI.Analysis.SignedDisk.DiskScales1

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real

noncomputable section

namespace SignedDisk

namespace LocalCancellation

section
open DiskKernels DiskGeometry

/-- An integrable aggregate of vectors in a fixed acute cone. It covers the
positive pieces by taking their sum; no direction is imposed on errors. -/
structure ConeDensity (e : ℂ) (κ : ℝ) where
  density : ℂ → ℂ
  integrable : Integrable density
  cone : ∀ᵐ y, κ*‖density y‖ ≤ inner ℝ e (density y)

lemma inner_unit_bound {e p : ℂ} (he : ‖e‖ = 1) : |inner ℝ e p| ≤ ‖p‖ := by
  simpa only [he,one_mul] using abs_real_inner_le_norm e p

lemma negative_projection_le_norm {e p : ℂ} (he : ‖e‖ = 1) :
    max 0 (-inner ℝ e p) ≤ ‖p‖ := by
  exact max_le (norm_nonneg _) ((neg_le_abs _).trans (inner_unit_bound he))

lemma negative_projection_change (e p q : ℂ) (he : ‖e‖ = 1) :
    max 0 (-inner ℝ e q) ≤ max 0 (-inner ℝ e p)+‖q-p‖ := by
  have h := inner_unit_bound (p := q-p) he
  rw [inner_sub_right] at h
  apply max_le
  · positivity
  · have hh := neg_le_abs (inner ℝ e q-inner ℝ e p)
    have hm := le_max_right (0 : ℝ) (-inner ℝ e p)
    linarith

lemma cone_pairing {e : ℂ} {κ : ℝ} (a : ConeDensity e κ)
    {K : ℂ → ℝ} (hK : AEStronglyMeasurable K) (hK0 : ∀ y, 0 ≤ K y)
    (hK1 : ∀ y, K y ≤ 1) :
    κ*(∫ y, K y*‖a.density y‖) ≤ inner ℝ e (∫ y, (K y : ℂ)*a.density y) := by
  have hKn (y : ℂ) : ‖K y‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (hK0 y)]; exact hK1 y
  have hi : Integrable (fun y => K y*‖a.density y‖) := a.integrable.norm.bdd_mul hK (ae_of_all _ hKn)
  have hia : Integrable (fun y => (K y : ℂ)*a.density y) :=
    a.integrable.bdd_mul (Complex.continuous_ofReal.comp_aestronglyMeasurable hK)
      (ae_of_all _ (fun y => by simpa only [Complex.norm_real] using hKn y))
  rw [← integral_const_mul, ← integral_inner hia e]
  apply integral_mono_ae (hi.const_mul κ) ((innerSL ℝ e).integrable_comp hia)
  filter_upwards [a.cone] with y hy
  change κ*(K y*‖a.density y‖) ≤ inner ℝ e ((K y : ℂ)*a.density y)
  rw [← Complex.real_smul, inner_smul_right]
  nlinarith [mul_le_mul_of_nonneg_left hy (hK0 y)]

/-- Nonpositive total projection bounds the weighted good mass by the error. -/
lemma cone_mass_of_nonpositive {e : ℂ} {κ : ℝ} (a : ConeDensity e κ)
    (he : ‖e‖ = 1) (hκ : 0 < κ) {K : ℂ → ℝ} (hK : AEStronglyMeasurable K)
    (hK0 : ∀ y, 0 ≤ K y) (hK1 : ∀ y, K y ≤ 1) {p : ℂ}
    (hp : inner ℝ e ((∫ y, (K y : ℂ)*a.density y)+p) ≤ 0) :
    (∫ y, K y*‖a.density y‖) ≤ ‖p‖/κ := by
  apply (le_div_iff₀ hκ).mpr
  have hh := cone_pairing a hK hK0 hK1
  have hb := inner_unit_bound (p := p) he
  rw [inner_add_right] at hp
  have hn := neg_le_abs (inner ℝ e p)
  nlinarith

/-- Crossing the zero projection selects a genuine convex kernel, not an
arbitrary discontinuous truncation. -/
lemma crossing_interpolation (e p q : ℂ) (hq : inner ℝ e q < 0) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
      inner ℝ e (θ • p+(1-θ) • q) ≤ 0 ∧
      max 0 (-inner ℝ e (θ • p+(1-θ) • q)) = max 0 (-inner ℝ e p) := by
  by_cases hp : inner ℝ e p ≤ 0
  · refine ⟨1,zero_le_one,le_rfl,?_,?_⟩
    · simpa using hp
    · simp
  · obtain ⟨θ,hθ0,hθ1,hzero⟩ := convex_zero (le_of_not_ge hp) hq.le
    refine ⟨θ,hθ0,hθ1,?_,?_⟩
    · simp only [inner_add_right, inner_smul_right, hzero, le_refl]
    · rw [inner_add_right, inner_smul_right, inner_smul_right, hzero,
        neg_zero, max_self, max_eq_left (by linarith : -inner ℝ e p ≤ 0)]

/-- The cap cost of the good density is weighted interior mass, not its
possibly enormous total mass. -/
lemma cone_corrected_cap {a : ℂ → ℂ} (ha : Integrable a)
    {K L : ℂ → ℝ} (hK : AEStronglyMeasurable K) (hL : AEStronglyMeasurable L)
    (hK0 : ∀ y, 0 ≤ K y) (hK1 : ∀ y, K y ≤ 1)
    (hL0 : ∀ y, 0 ≤ L y) (hL1 : ∀ y, L y ≤ 1)
    {D : Set ℂ} (hD : MeasurableSet D) (hsupp : ∀ y, L y-K y ≠ 0 → y ∈ D)
    (x z : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hz : (1 : ℝ)/2 ≤ ‖z-x‖)
    (hD3 : ∀ y ∈ D, ‖y-x‖ ≤ 3) :
    ‖∫ y, correction x z y*((L y : ℂ)-K y)*a y‖ ≤
      2*ρ*(∫ y, (L y+K y)*‖a y‖)+7*(∫ y in D \ Metric.ball z ρ, ‖a y‖) := by
  have hi : Integrable (fun y => (L y+K y)*‖a y‖) :=
    ha.norm.bdd_mul (c := 2) (hL.add hK) (ae_of_all _ (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (hL0 y) (hK0 y))]
      linarith [hK1 y,hL1 y]))
  let B := D \ Metric.ball z ρ
  have hB : MeasurableSet B := hD.diff measurableSet_ball
  have hbi : Integrable (B.indicator (fun y => ‖a y‖)) := ha.norm.indicator hB
  have hmaj : ‖∫ y, correction x z y*((L y : ℂ)-K y)*a y‖ ≤
      ∫ y, 2*ρ*((L y+K y)*‖a y‖)+7*B.indicator (fun y => ‖a y‖) y := by
    apply norm_integral_le_of_norm_le ((hi.const_mul _).add (hbi.const_mul _))
    filter_upwards with y
    change ‖correction x z y*((L y : ℂ)-K y)*a y‖ ≤ 2*ρ*((L y+K y)*‖a y‖)+7*B.indicator (fun y => ‖a y‖) y
    have hk := hK0 y
    have hl := hL0 y
    have hb : 0 ≤ B.indicator (fun y => ‖a y‖) y := Set.indicator_nonneg (fun _ _ => norm_nonneg _) y
    have hf : ‖((L y : ℂ)-K y)‖ = |L y-K y| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hsum : |L y-K y| ≤ L y+K y := abs_le.mpr ⟨by linarith [hL0 y], by linarith [hK0 y]⟩
    have hone : |L y-K y| ≤ 1 := abs_le.mpr ⟨by linarith [hL0 y,hK1 y],by linarith [hL1 y,hK0 y]⟩
    by_cases hzero : L y-K y = 0
    · have hc : (L y : ℂ)-K y = 0 := by exact_mod_cast hzero
      rw [hc, mul_zero, zero_mul, norm_zero]
      positivity
    · have hyD := hsupp y hzero
      by_cases hyB : y ∈ Metric.ball z ρ
      · have hc := correction_cap_bound hz (show ‖y-z‖ ≤ ρ from by simpa only [dist_eq_norm] using (Metric.mem_ball.mp hyB).le)
        rw [indicator_of_notMem (show y ∉ B from fun h => h.2 hyB), mul_zero, add_zero,
          norm_mul, norm_mul, hf]
        have hh := mul_le_mul hc hsum (abs_nonneg _) (by positivity : 0 ≤ 2*ρ)
        nlinarith [mul_le_mul_of_nonneg_right hh (norm_nonneg (a y))]
      · rw [indicator_of_mem (show y ∈ B from ⟨hyD,hyB⟩),norm_mul,norm_mul,hf]
        have hc := mul_le_mul (correction_bounded hz (hD3 y hyD)) hone (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 7)
        have hh := mul_le_mul_of_nonneg_right hc (norm_nonneg (a y))
        have hn : 0 ≤ 2*ρ*((L y+K y)*‖a y‖) := by positivity
        nlinarith
  rw [integral_add (hi.const_mul _) (hbi.const_mul _), integral_const_mul,
    integral_const_mul, integral_indicator hB] at hmaj
  exact hmaj

open DiskKernels DiskGeometry DiskScales
variable {ι : Type*} [Fintype ι]

/-- The error contribution to the corrected first active step; no moment
cancellation for the errors alone is presumed. -/
lemma corrected_error_bound {Cs α δ ρ : ℝ} (b : ι → ErrorPiece Cs) (hCs : 0 ≤ Cs)
    (hα : α ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hρ : 0 ≤ ρ)
    {L : ℝ≥0} {F : ℂ → ℂ} (hF : LipschitzWith L F) {D : Set ℂ} (hD : MeasurableSet D)
    (hFb : ∀ y, ‖F y‖ ≤ 1) (hFD : ∀ y, F y ≠ 0 → y ∈ D) (x z : ℂ)
    (hz : (1 : ℝ)/2 ≤ ‖z-x‖) (hD3 : ∀ y ∈ D, ‖y-x‖ ≤ 3) :
    ‖∑ d, ∫ y, correction x z y*F y*(b d).density y‖ ≤
      2*ρ*coarseMass b δ univ+7*coarseMass b δ (D \ Metric.ball z ρ)+
      ((L : ℝ)+2*(3*(L : ℝ)+1))*Cs*δ^(2*(1-α))*errorPrice b α := by
  classical
  have hnorm : ∀ y, F y ≠ 0 → ‖y-x‖ ≤ (3 : ℝ) := fun y hy => hD3 y (hFD y hy)
  have hH : ‖(star (z-x))⁻¹‖ ≤ (2 : ℝ) := by
    rw [norm_inv, norm_star]
    have hn : 0 < ‖z-x‖ := by linarith
    rw [inv_eq_one_div, div_le_iff₀ hn]
    linarith
  have hcorr : LipschitzWith (L+2*(3*L+1)) (fun y => correction x z y*F y) :=
    corrected_lipschitz (M := 1) (R := 3) (H := 2) hF hFb x z hnorm hH
  have hsplit : (∑ d, ∫ y, correction x z y*F y*(b d).density y) =
      (∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size), ∫ y, correction x z y*F y*(b d).density y)+
      (∑ d ∈ Finset.univ.filter (fun d => (b d).size < δ^2), ∫ y, correction x z y*F y*(b d).density y) := by
    simpa only [not_le] using (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun d => δ^2 ≤ (b d).size) (fun d => ∫ y, correction x z y*F y*(b d).density y)).symm
  rw [hsplit]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · calc
      _ ≤ ∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size),
          ‖∫ y, correction x z y*F y*(b d).density y‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size),
          (2*ρ*(∫ y, ‖(b d).density y‖)+7*(∫ y in D \ Metric.ball z ρ, ‖(b d).density y‖)) :=
        Finset.sum_le_sum (fun d _ => corrected_pairing_cap (b d).integrable hD hFb hFD x z hρ hz hD3)
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        simp only [coarseMass, Measure.restrict_univ]
  · exact fine_pairing_bound b hCs hα hδ hδ1 hcorr

end

open DiskKernels DiskGeometry DiskScales
variable {ι : Type*} [Fintype ι]

lemma increment_bound_general {Cs α δ M : ℝ} (b : ι → ErrorPiece Cs) (hCs : 0 ≤ Cs)
    (hα : α ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {L : ℝ≥0} {F : ℂ → ℂ} (hF : LipschitzWith L F) {D : Set ℂ} (hD : MeasurableSet D)
    (hFb : ∀ y, ‖F y‖ ≤ M) (hFD : ∀ y, F y ≠ 0 → y ∈ D) :
    ‖∑ d, ∫ y, F y*(b d).density y‖ ≤
      M*coarseMass b δ D+(L : ℝ)*Cs*δ^(2*(1-α))*errorPrice b α := by
  classical
  have he : (∑ d, ∫ y, F y*(b d).density y) =
      (∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size), ∫ y, F y*(b d).density y)+
      (∑ d ∈ Finset.univ.filter (fun d => (b d).size < δ^2), ∫ y, F y*(b d).density y) := by
    simpa only [not_le] using (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun d => δ^2 ≤ (b d).size) (fun d => ∫ y, F y*(b d).density y)).symm
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · calc
      _ ≤ ∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size), ‖∫ y, F y*(b d).density y‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size), M*(∫ y in D, ‖(b d).density y‖) := by
        apply Finset.sum_le_sum
        intro d _
        have hh := pairing_majorant (b d).integrable hD 0 M (fun y => by
          by_cases hy : y ∈ D
          · simpa only [indicator_of_mem hy, mul_one, zero_add] using hFb y
          · have hf : F y = 0 := by by_contra h; exact hy (hFD y h)
            simp only [hf,norm_zero,indicator_of_notMem hy,mul_zero,add_zero,le_refl])
        simpa only [zero_mul,zero_add] using hh
      _ = _ := by rw [← Finset.mul_sum]; rfl
  · exact fine_pairing_bound b hCs hα hδ hδ1 hF

lemma correction_kernel_bound {F : ℂ → ℂ} (hFb : ∀ y, ‖F y‖ ≤ 1)
    (x z : ℂ) (hz : (1 : ℝ)/2 ≤ ‖z-x‖) (hD3 : ∀ y, F y ≠ 0 → ‖y-x‖ ≤ 3) :
    ∀ y, ‖correction x z y*F y‖ ≤ 7 := by
  intro y
  by_cases hy : F y = 0
  · simp only [hy,mul_zero,norm_zero]; norm_num
  · rw [norm_mul]
    simpa only [mul_one] using mul_le_mul (correction_bounded hz (hD3 y hy)) (hFb y) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 7)

lemma corrected_inactive_bound {Cs α δ : ℝ} (b : ι → ErrorPiece Cs) (hCs : 0 ≤ Cs)
    (hα : α ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {L : ℝ≥0} {F : ℂ → ℂ} (hF : LipschitzWith L F) {D : Set ℂ} (hD : MeasurableSet D)
    (hFb : ∀ y, ‖F y‖ ≤ 1) (hFD : ∀ y, F y ≠ 0 → y ∈ D) (x z : ℂ)
    (hz : (1 : ℝ)/2 ≤ ‖z-x‖) (hD3 : ∀ y ∈ D, ‖y-x‖ ≤ 3) :
    ‖∑ d, ∫ y, correction x z y*F y*(b d).density y‖ ≤
      7*coarseMass b δ D+((L : ℝ)+2*(3*(L : ℝ)+1))*Cs*δ^(2*(1-α))*errorPrice b α := by
  have hnorm : ∀ y, F y ≠ 0 → ‖y-x‖ ≤ (3 : ℝ) := fun y hy => hD3 y (hFD y hy)
  have hH : ‖(star (z-x))⁻¹‖ ≤ (2 : ℝ) := by
    rw [norm_inv, norm_star]
    have hn : 0 < ‖z-x‖ := by linarith
    rw [inv_eq_one_div, div_le_iff₀ hn]
    linarith
  have hcorr : LipschitzWith (L+2*(3*L+1)) (fun y => correction x z y*F y) :=
    corrected_lipschitz (M := 1) (R := 3) (H := 2) hF hFb x z hnorm hH
  exact increment_bound_general b hCs hα hδ hδ1 hcorr hD (correction_kernel_bound hFb x z hz hnorm)
    (fun y hy => hFD y (fun h => hy (by rw [h,mul_zero])))

end LocalCancellation

/-- A finite last-active-index induction. Its hypotheses are local gaps, not
an assumed global estimate, and no infinite list of active indices is chosen. -/
lemma last_active_bound (active : ℕ → Prop) (N a : ℕ → ℝ) (B : ℝ)
    (ha : ∀ i, 0 ≤ a i)
    (hfirst : ∀ n, (∀ i < n, ¬active i) → N n ≤ B+∑ i ∈ Finset.range n, a i)
    (hgap : ∀ j n, j < n → active j → (∀ i, j < i → i < n → ¬active i) →
      N n ≤ N j+a j) : ∀ n, N n ≤ B+∑ i ∈ Finset.range n, a i := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    let S := (Finset.range n).filter active
    by_cases hS : S.Nonempty
    · let j := S.max' hS
      have hjmem : j ∈ S := Finset.max'_mem S hS
      have hjn : j < n := Finset.mem_range.mp (Finset.mem_filter.mp hjmem).1
      have hjact : active j := (Finset.mem_filter.mp hjmem).2
      have hng : ∀ i, j < i → i < n → ¬active i := by
        intro i hji hin hi
        have his : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hin,hi⟩
        exact (not_lt_of_ge (Finset.le_max' S i his)) hji
      have hh := hgap j n hjn hjact hng
      have hb := ih j hjn
      have hs : (∑ i ∈ Finset.range (j+1), a i) ≤ ∑ i ∈ Finset.range n, a i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_of_lt hjn)) (fun i _ _ => ha i)
      rw [Finset.sum_range_succ] at hs
      linarith
    · apply hfirst n
      intro i hi hai
      exact hS ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,hai⟩⟩

lemma last_active_limit (active : ℕ → Prop) (N a : ℕ → ℝ) (B Z : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hsm : Summable a) (hN : Tendsto N atTop (𝓝 Z))
    (hfirst : ∀ n, (∀ i < n, ¬active i) → N n ≤ B+∑ i ∈ Finset.range n, a i)
    (hgap : ∀ j n, j < n → active j → (∀ i, j < i → i < n → ¬active i) →
      N n ≤ N j+a j) : Z ≤ B+∑' i, a i := by
  apply le_of_tendsto hN
  filter_upwards with n
  exact (last_active_bound active N a B ha hfirst hgap n).trans
    (add_le_add le_rfl (hsm.sum_le_tsum (Finset.range n) (fun i _ => ha i)))

namespace LocalCancellation
open DiskKernels DiskGeometry DiskScales

lemma real_weight_integrable {a : ℂ → ℂ} (ha : Integrable a) {K : ℂ → ℝ}
    (hK : AEStronglyMeasurable K) (hK0 : ∀ y, 0 ≤ K y) (hK1 : ∀ y, K y ≤ 1) :
    Integrable (fun y => (K y : ℂ)*a y) :=
  integrable_bounded_pairing ha (Complex.continuous_ofReal.comp_aestronglyMeasurable hK)
    (fun y => by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hK0 y)]; exact hK1 y)

lemma real_weight_norm_integrable {a : ℂ → ℂ} (ha : Integrable a) {K : ℂ → ℝ}
    (hK : AEStronglyMeasurable K) (hK0 : ∀ y, 0 ≤ K y) (hK1 : ∀ y, K y ≤ 1) :
    Integrable (fun y => K y*‖a y‖) :=
  ha.norm.bdd_mul hK (ae_of_all _ fun y => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hK0 y)]; exact hK1 y)

lemma convex_pairing {a : ℂ → ℂ} {K L : ℂ → ℝ}
    (hiK : Integrable (fun y => (K y : ℂ)*a y))
    (hiL : Integrable (fun y => (L y : ℂ)*a y)) (θ : ℝ) :
    (∫ y, ((θ*K y+(1-θ)*L y : ℝ) : ℂ)*a y) =
      θ • (∫ y, (K y : ℂ)*a y)+(1-θ) • (∫ y, (L y : ℂ)*a y) := by
  have he : (fun y => ((θ*K y+(1-θ)*L y : ℝ) : ℂ)*a y) =
      (fun y => θ • ((K y : ℂ)*a y)+(1-θ) • ((L y : ℂ)*a y)) := by
    ext y
    simp only [Complex.ofReal_add,Complex.ofReal_mul,Complex.real_smul]
    ring
  rw [he]
  calc
    _ = (∫ y, θ • ((K y : ℂ)*a y))+(∫ y, (1-θ) • ((L y : ℂ)*a y)) :=
      integral_add (hiK.smul θ) (hiL.smul (1-θ))
    _ = _ := by rw [integral_smul,integral_smul]

/-- Analytic comparison of two balanced mixtures at a negative later
projection. The only error term is their fixed-correction difference. -/
lemma negative_gap_cap {e : ℂ} {κ B ρ H : ℝ} (a : ConeDensity e κ)
    (he : ‖e‖ = 1) (hκ : 0 < κ) (hρ : 0 ≤ ρ)
    {K L : ℂ → ℝ} (hK : AEStronglyMeasurable K) (hL : AEStronglyMeasurable L)
    (hK0 : ∀ y, 0 ≤ K y) (hK1 : ∀ y, K y ≤ 1)
    (hL0 : ∀ y, 0 ≤ L y) (hL1 : ∀ y, L y ≤ 1)
    {D : Set ℂ} (hD : MeasurableSet D) (hsupp : ∀ y, L y-K y ≠ 0 → y ∈ D)
    (x z : ℂ) (hz : (1 : ℝ)/2 ≤ ‖z-x‖) (hD3 : ∀ y ∈ D, ‖y-x‖ ≤ 3)
    (hcap : (∫ y in D \ Metric.ball z ρ, ‖a.density y‖) ≤ H)
    {p q R : ℂ} (hp : ‖p‖ ≤ B) (hq : ‖q‖ ≤ B)
    (hneg : inner ℝ e ((∫ y, (L y : ℂ)*a.density y)+q) < 0)
    (hcor : ((∫ y, (L y : ℂ)*a.density y)+q)-((∫ y, (K y : ℂ)*a.density y)+p) =
      (∫ y, correction x z y*((L y : ℂ)-K y)*a.density y)+R) :
    max 0 (-inner ℝ e ((∫ y, (L y : ℂ)*a.density y)+q)) ≤
      max 0 (-inner ℝ e ((∫ y, (K y : ℂ)*a.density y)+p))+
        4*ρ*(B/κ)+7*H+‖R‖ := by
  let P := (∫ y, (K y : ℂ)*a.density y)+p
  let Q := (∫ y, (L y : ℂ)*a.density y)+q
  obtain ⟨θ,hθ0,hθ1,hθneg,hθeq⟩ := crossing_interpolation e P Q hneg
  let J (y : ℂ) := θ*K y+(1-θ)*L y
  have hJ0 (y : ℂ) : 0 ≤ J y := add_nonneg (mul_nonneg hθ0 (hK0 y)) (mul_nonneg (sub_nonneg.mpr hθ1) (hL0 y))
  have hJ1 (y : ℂ) : J y ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_left (hK1 y) hθ0
    have h2 := mul_le_mul_of_nonneg_left (hL1 y) (sub_nonneg.mpr hθ1)
    dsimp [J]
    nlinarith
  have hJ : AEStronglyMeasurable J := (hK.const_mul θ).add (hL.const_mul (1-θ))
  have hiK := real_weight_integrable a.integrable hK hK0 hK1
  have hiL := real_weight_integrable a.integrable hL hL0 hL1
  let pstar := θ • p+(1-θ) • q
  have hpstar : ‖pstar‖ ≤ B := by
    calc
      ‖pstar‖ ≤ ‖θ • p‖+‖(1-θ) • q‖ := norm_add_le _ _
      _ = θ*‖p‖+(1-θ)*‖q‖ := by
        rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
          abs_of_nonneg hθ0,abs_of_nonneg (sub_nonneg.mpr hθ1)]
      _ ≤ θ*B+(1-θ)*B := add_le_add (mul_le_mul_of_nonneg_left hp hθ0)
        (mul_le_mul_of_nonneg_left hq (sub_nonneg.mpr hθ1))
      _ = B := by ring
  have hstar : (∫ y, (J y : ℂ)*a.density y)+pstar = θ • P+(1-θ) • Q := by
    rw [show (∫ y, (J y : ℂ)*a.density y) = _ from convex_pairing hiK hiL θ]
    dsimp [P,Q,pstar]
    ring
  have hsmass := cone_mass_of_nonpositive a he hκ hJ hJ0 hJ1
    (show inner ℝ e ((∫ y, (J y : ℂ)*a.density y)+pstar) ≤ 0 by rw [hstar]; exact hθneg)
  have hlmass := cone_mass_of_nonpositive a he hκ hL hL0 hL1 hneg.le
  have hweighted : (∫ y, (L y+J y)*‖a.density y‖) ≤ 2*(B/κ) := by
    have hiLn := real_weight_norm_integrable a.integrable hL hL0 hL1
    have hiJn := real_weight_norm_integrable a.integrable hJ hJ0 hJ1
    simp_rw [add_mul]
    rw [integral_add hiLn hiJn]
    have hs := hsmass.trans (div_le_div_of_nonneg_right hpstar hκ.le)
    have hl := hlmass.trans (div_le_div_of_nonneg_right hq hκ.le)
    linarith
  have hJdiff (y : ℂ) : L y-J y = θ*(L y-K y) := by dsimp [J]; ring
  have hJDs : ∀ y, L y-J y ≠ 0 → y ∈ D := by
    intro y hy
    apply hsupp y
    intro h
    exact hy (by rw [hJdiff,h,mul_zero])
  let G := ∫ y, correction x z y*((L y : ℂ)-J y)*a.density y
  have hG : ‖G‖ ≤ 4*ρ*(B/κ)+7*H := by
    have hh := cone_corrected_cap a.integrable hJ hL hJ0 hJ1 hL0 hL1 hD hJDs x z hρ hz hD3
    change ‖G‖ ≤ _ at hh
    have hg := mul_le_mul_of_nonneg_left hweighted (by positivity : 0 ≤ 2*ρ)
    have hc := mul_le_mul_of_nonneg_left hcap (by norm_num : (0 : ℝ) ≤ 7)
    nlinarith
  have hGid : G = θ • (∫ y, correction x z y*((L y : ℂ)-K y)*a.density y) := by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards with y
    change correction x z y*((L y : ℂ)-(θ*K y+(1-θ)*L y : ℝ))*a.density y =
      θ • (correction x z y*((L y : ℂ)-K y)*a.density y)
    simp only [Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one,Complex.real_smul]
    ring
  have hdiff : Q-(θ • P+(1-θ) • Q) = G+θ • R := by
    have hh : Q-P = (∫ y, correction x z y*((L y : ℂ)-K y)*a.density y)+R := hcor
    rw [hGid, ← smul_add, ← hh]
    simp only [sub_smul,one_smul,smul_sub]
    abel
  have hR : ‖θ • R‖ ≤ ‖R‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hθ0]
    exact mul_le_of_le_one_left (norm_nonneg _) hθ1
  have hn := negative_projection_change e (θ • P+(1-θ) • Q) Q he
  rw [hθeq,hdiff] at hn
  have hh := (norm_add_le G (θ • R)).trans (add_le_add hG hR)
  change max 0 (-inner ℝ e Q) ≤ max 0 (-inner ℝ e P)+4*ρ*(B/κ)+7*H+‖R‖
  linarith

end LocalCancellation

end SignedDisk

end

end OAI
