import OAI.Analysis.LipschitzHilbert.Geometry.LineConvolutionFar
import OAI.Analysis.LipschitzHilbert.Estimates.GeometricScaleWeights

namespace OAI

/-! The local and far parts of the actual smooth projection Carleson
estimate on a finite dyadic scale range. -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem lineConvolution_indicator_split (K f : ℝ → ℂ)
    (hK : Integrable K) (hfm : Measurable f) (B : ℝ)
    (hB : 0≤B) (hfb : ∀ x, ‖f x‖≤B) (S : Set ℝ)
    (hS : MeasurableSet S) (x : ℝ) :
    lineConvolution K f x=lineConvolution K (S.indicator f) x+
      lineConvolution K (Sᶜ.indicator f) x := by
  have hb (T : Set ℝ) (y : ℝ) : ‖T.indicator f y‖≤B := by
    by_cases hy : y∈T
    · simpa only [indicator_of_mem hy] using hfb y
    · simpa only [indicator_of_notMem hy,norm_zero] using hB
  have hs := lineConvolution_integrand_of_bounded K (S.indicator f) hK
    (hfm.indicator hS) B (hb S) x
  have ht := lineConvolution_integrand_of_bounded K (Sᶜ.indicator f) hK
    (hfm.indicator hS.compl) B (hb Sᶜ) x
  unfold lineConvolution
  rw [←integral_add hs ht]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases hy : x-t∈S <;> simp [hy]

theorem lineProjection_far_integrable (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W)
    (f : ℝ → ℂ) (hfm : Measurable f) (B d : ℝ) (hB : 0≤B) (hd : 0<d)
    (hfb : ∀ y, ‖f y‖≤B) (J : Set ℝ) (hJ : MeasurableSet J) (hJf : volume J≠⊤)
    (hgap : ∀ x∈J, ∀ t, |t|<d → f (x-t)=0) :
    IntegrableOn (fun x => ‖lineConvolution (lineProjectionKernel q W hW.ne') f x‖^2) J := by
  apply (integrableOn_const (C:=((B*W/d)*
    (∫ t, |t| *‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖))^2) hJf).mono'
    ((lineConvolution_measurable _ (lineProjectionKernel q W hW.ne').continuous.measurable
      f hfm).norm.pow_const 2).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem hJ] with x hx
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (lineProjection_far_bound q W hW f B d x hB hd hfb (hgap x hx)) 2

/-- A bounded function produces a Carleson square sum for any fixed smooth
annular window having the indicated finite Fourier square bound. -/
theorem lineProjection_smooth_carleson (q : SchwartzMap ℝ ℂ) (N : ℕ)
    (a b : ℝ) (hab : a<b) (M : ℝ) (hM : 0≤M)
    (hframe : ∀ eta, (∑ n∈Finset.range N,
      ‖q (((b-a)/(2:ℝ)^n)*eta)‖^2)≤M)
    (f : ℝ → ℂ) (hfm : Measurable f) (B : ℝ) (hB : 0≤B)
    (hfb : ∀ x, ‖f x‖≤B) :
    (∑ n∈Finset.range N, ∫ x in Icc a b,
      ‖lineConvolution (lineProjectionKernel q ((b-a)/(2:ℝ)^n)
        (by positivity)) f x‖^2)≤
      (6*M+4*(∫ t, |t| *‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖)^2)*B^2*(b-a) := by
  let d := b-a
  let S := Icc (a-d) (b+d)
  let W := fun n : ℕ => d/(2:ℝ)^n
  let K := fun n => lineProjectionKernel q (W n) (by dsimp [W,d]; positivity)
  let near := S.indicator f
  let far := Sᶜ.indicator f
  let A := ∫ t, |t| *‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖
  have hd : 0<d := sub_pos.mpr hab
  have hW (n : ℕ) : 0<W n := by dsimp [W]; positivity
  have hS : MeasurableSet S := measurableSet_Icc
  have hnear : Measurable near := hfm.indicator hS
  have hfar : Measurable far := hfm.indicator hS.compl
  have hb (T : Set ℝ) (x : ℝ) : ‖T.indicator f x‖≤B := by
    by_cases hx : x∈T
    · simpa only [indicator_of_mem hx] using hfb x
    · simpa only [indicator_of_notMem hx,norm_zero] using hB
  have hn := bounded_indicator_memLp f hfm S hS measure_Icc_lt_top.ne B hfb
  have hni (n : ℕ) : Integrable (fun x => ‖lineConvolution (K n) near x‖^2) :=
    (lineConvolution_energy_bound (K n) (K n).integrable (K n).continuous.measurable
      near hnear hn).1.integrable_norm_pow (by decide : 2≠0)
  have hgap (x : ℝ) (hx : x∈Icc a b) (t : ℝ) (ht : |t|<d) : far (x-t)=0 :=
    outside_enlarged_interval_gap f a b d x t hx ht
  have hfi (n : ℕ) : IntegrableOn (fun x => ‖lineConvolution (K n) far x‖^2) (Icc a b) :=
    lineProjection_far_integrable q (W n) (hW n) far hfar B d hB hd
      (hb Sᶜ) _ measurableSet_Icc measure_Icc_lt_top.ne hgap
  have hsplit (n : ℕ) (x : ℝ) : lineConvolution (K n) f x=
      lineConvolution (K n) near x+lineConvolution (K n) far x :=
    lineConvolution_indicator_split (K n) f (K n).integrable hfm B hB hfb S hS x
  have hs (n : ℕ) : (∫ x in Icc a b, ‖lineConvolution (K n) f x‖^2)≤
      2*(∫ x, ‖lineConvolution (K n) near x‖^2)+
      2*(∫ x in Icc a b, ‖lineConvolution (K n) far x‖^2) := by
    calc
      _ ≤ ∫ x in Icc a b, 2*‖lineConvolution (K n) near x‖^2+
          2*‖lineConvolution (K n) far x‖^2 := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _)
          (((hni n).integrableOn.const_mul 2).add ((hfi n).const_mul 2))
        filter_upwards [] with x
        rw [hsplit]
        change ‖lineConvolution (K n) near x+lineConvolution (K n) far x‖^2≤
          2*‖lineConvolution (K n) near x‖^2+2*‖lineConvolution (K n) far x‖^2
        have ht := norm_add_le (lineConvolution (K n) near x) (lineConvolution (K n) far x)
        have ht2 := pow_le_pow_left₀ (norm_nonneg _) ht 2
        nlinarith [sq_nonneg (‖lineConvolution (K n) near x‖-‖lineConvolution (K n) far x‖)]
      _ = 2*(∫ x in Icc a b, ‖lineConvolution (K n) near x‖^2)+
          2*(∫ x in Icc a b, ‖lineConvolution (K n) far x‖^2) := by
        rw [integral_add ((hni n).integrableOn.const_mul 2) ((hfi n).const_mul 2),
          integral_const_mul,integral_const_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left
        (integral_mono_measure Measure.restrict_le_self
          (Filter.Eventually.of_forall fun _ => sq_nonneg _) (hni n)) (by norm_num : (0:ℝ)≤2)) le_rfl
  have hv : volume.real S=3*d := by
    change volume.real (Icc (a-d) (b+d))=3*d
    rw [Real.volume_real_Icc_of_le (by dsimp [d]; linarith)]
    dsimp [d]; ring
  have hlocal : (∑ n∈Finset.range N, ∫ x, ‖lineConvolution (K n) near x‖^2)≤
      3*M*B^2*d := by
    have hh := lineConvolution_local_frame (Finset.range N) (fun _ => q) W
      (fun n => (hW n).ne') M hM hframe f hfm B hB hfb S hS measure_Icc_lt_top.ne
    rw [hv] at hh
    convert hh using 1; ring
  have hfarbound (n : ℕ) : (∫ x in Icc a b, ‖lineConvolution (K n) far x‖^2)≤
      B^2*A^2*d*(1/2:ℝ)^n := by
    have hh := lineProjection_far_energy q (W n) (hW n) far B d hB hd (hb Sᶜ)
      (Icc a b) measure_Icc_lt_top hgap
    rw [Real.volume_real_Icc_of_le hab.le] at hh
    have he : ((B*W n/d)*A)^2*(b-a)=B^2*A^2*d*((1/2:ℝ)^n)^2 := by
      dsimp [W]
      rw [div_pow,one_pow]
      field_simp
      ring
    rw [he] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hp : (1/2:ℝ)^n≤1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤1/2) n]
  have hfarSum : (∑ n∈Finset.range N, ∫ x in Icc a b,
      ‖lineConvolution (K n) far x‖^2)≤2*B^2*A^2*d := by
    calc
      _ ≤ ∑ n∈Finset.range N, B^2*A^2*d*(1/2:ℝ)^n := Finset.sum_le_sum fun n _ => hfarbound n
      _ = B^2*A^2*d*(∑ n∈Finset.range N, (1/2:ℝ)^n) := by rw [Finset.mul_sum]
      _ ≤ B^2*A^2*d*2 := mul_le_mul_of_nonneg_left (sum_half_powers_le_two N) (by positivity)
      _ = _ := by ring
  change (∑ n∈Finset.range N, ∫ x in Icc a b, ‖lineConvolution (K n) f x‖^2)≤_
  calc
    _ ≤ ∑ n∈Finset.range N, (2*(∫ x, ‖lineConvolution (K n) near x‖^2)+
        2*(∫ x in Icc a b, ‖lineConvolution (K n) far x‖^2)) :=
      Finset.sum_le_sum fun n _ => hs n
    _ = 2*(∑ n∈Finset.range N, ∫ x, ‖lineConvolution (K n) near x‖^2)+
        2*(∑ n∈Finset.range N, ∫ x in Icc a b, ‖lineConvolution (K n) far x‖^2) := by
      rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]
    _ ≤ 2*(3*M*B^2*d)+2*(2*B^2*A^2*d) := by linarith
    _ = _ := by dsimp [A,d]; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
