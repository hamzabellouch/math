import OAI.NumberTheory.CubicMoment.Estimates.PrimeLogReplacement
import OAI.NumberTheory.CubicMoment.Estimates.PrimaryConvolutionEnergy

namespace OAI

/-! The actual error in replacing a convolution of prime indicators by
normalized von Mangoldt coefficients has sparse prime-power support. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primeLogConvolutionError (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (b : Eisenstein) : ℂ :=
  orderedConvolution S (fun i a => (normalizedVonMangoldt a:ℂ)*w i a) b-
    orderedConvolution S (fun i a => (primeIndicator a:ℂ)*w i a) b

lemma primeLogConvolutionError_sum (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (b : Eisenstein) :
    primeLogConvolutionError S w b =
      ∑ f ∈ (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b),
        ((∏ i, (normalizedVonMangoldt (f i):ℂ)*w i (f i))-
          ∏ i, (primeIndicator (f i):ℂ)*w i (f i)) := by
  unfold primeLogConvolutionError orderedConvolution
  rw [Finset.sum_sub_distrib]

lemma primeLogConvolutionError_support_of_norm_le (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) {Y c : ℝ}
    (hS : ∀ i, ∀ a ∈ S i, primary a ∧ Y^c < norm a)
    {b : Eisenstein} (hbY : norm b ≤ Y) (hb : primeLogConvolutionError S w b ≠ 0) :
    b ∈ largePrimePowerSupport Y c := by
  rw [primeLogConvolutionError_sum] at hb
  obtain ⟨f,hf,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  obtain ⟨hfs,hfb⟩ := Finset.mem_filter.mp hf
  have hex : ∃ i, primeLogCorrection (f i) ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    have he : (∏ i, (normalizedVonMangoldt (f i):ℂ)*w i (f i)) =
        ∏ i, (primeIndicator (f i):ℂ)*w i (f i) := by
      apply Finset.prod_congr rfl
      intro i _
      have hi : normalizedVonMangoldt (f i) = primeIndicator (f i) :=
        sub_eq_zero.mp (h i)
      rw [hi]
    exact sub_eq_zero.mpr he
  obtain ⟨i,hi⟩ := hex
  have hfi := hS i (f i) (Fintype.mem_piFinset.mp hfs i)
  obtain ⟨p,j,hp,hj,he⟩ := primeLogCorrection_support hfi.1 hi
  have hprod0 : (∏ i, f i) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => primary_ne_zero (hS i (f i) (Fintype.mem_piFinset.mp hfs i)).1)
  refine Finset.mem_filter.mpr ⟨mem_nonzeroNormBall.mpr
    ⟨hbY,hfb ▸ hprod0⟩,p,j,hp,hj,?_,?_⟩
  · rw [← he]
    exact hfi.2
  · rw [← he,← hfb]
    exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)

lemma primeLogConvolutionError_support (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) {Y c : ℝ}
    (hS : ∀ i, ∀ a ∈ S i, primary a ∧ Y^c < norm a)
    (hY : ∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y)
    {b : Eisenstein} (hb : primeLogConvolutionError S w b ≠ 0) :
    b ∈ largePrimePowerSupport Y c := by
  have hs := hb
  rw [primeLogConvolutionError_sum] at hs
  obtain ⟨f,hf,_⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  obtain ⟨hfs,hfb⟩ := Finset.mem_filter.mp hf
  exact primeLogConvolutionError_support_of_norm_le S w hS (hfb ▸ hY f hfs) hb


lemma primeLog_factor_norm_le (w : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M)
    {a : Eisenstein} (ha : primary a) (hw : ‖w a‖ ≤ M) :
    ‖(normalizedVonMangoldt a:ℂ)*w a‖ ≤ M ∧
    ‖(primeIndicator a:ℂ)*w a‖ ≤ M := by
  constructor
  · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (normalizedVonMangoldt_nonneg ha)]
    exact (mul_le_mul (normalizedVonMangoldt_le_one ha) hw (_root_.norm_nonneg _) zero_le_one).trans_eq
      (one_mul M)
  · by_cases hp : Prime a
    · simpa only [primeIndicator,ite_eq_left hp,Complex.ofReal_one,one_mul] using hw
    · simp only [primeIndicator,ite_eq_right hp,Complex.ofReal_zero,zero_mul,norm_zero]
      exact hM

/-- A divisor bound gives the genuine error coefficient a subpower amplitude. -/
theorem primeLogConvolutionError_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y : ℝ),
      (∀ i, ∀ a ∈ S i, primary a) → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) → 1 ≤ Y →
      ∀ b ∈ orderedConvolutionSupport S, norm b ≤ Y →
      ‖primeLogConvolutionError S w b‖ ≤ C*Y^ε*(∏ i, M i) := by
  obtain ⟨C,hC,hfiber⟩ := primary_tuple_fiber_small_power (ι := ι) hε
  refine ⟨2*C,by positivity,?_⟩
  intro S w M Y hS hM hw hY b hb hbY
  have hMp : 0 ≤ ∏ i, M i := Finset.prod_nonneg (fun i _ => hM i)
  have ht (f : ι → Eisenstein) (hf : f ∈ Fintype.piFinset S) :
      ‖(∏ i, (normalizedVonMangoldt (f i):ℂ)*w i (f i))-
        ∏ i, (primeIndicator (f i):ℂ)*w i (f i)‖ ≤ 2*∏ i, M i := by
    have hl (i : ι) := primeLog_factor_norm_le (w i) (hM i)
      (hS i (f i) (Fintype.mem_piFinset.mp hf i))
      (hw i (f i) (Fintype.mem_piFinset.mp hf i))
    have h1 : ‖∏ i, (normalizedVonMangoldt (f i):ℂ)*w i (f i)‖ ≤ ∏ i, M i := by
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun _ _ => _root_.norm_nonneg _) (fun i _ => (hl i).1)
    have h2 : ‖∏ i, (primeIndicator (f i):ℂ)*w i (f i)‖ ≤ ∏ i, M i := by
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun _ _ => _root_.norm_nonneg _) (fun i _ => (hl i).2)
    exact (norm_sub_le _ _).trans (by linarith)
  rw [primeLogConvolutionError_sum]
  calc
    _ ≤ ∑ f ∈ (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b),
        ‖(∏ i, (normalizedVonMangoldt (f i):ℂ)*w i (f i))-
          ∏ i, (primeIndicator (f i):ℂ)*w i (f i)‖ := norm_sum_le _ _
    _ ≤ ∑ _f ∈ (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b), 2*∏ i, M i :=
      Finset.sum_le_sum (fun f hf => ht f (Finset.mem_filter.mp hf).1)
    _ = (((Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)).card:ℝ)*(2*∏ i, M i) := by simp
    _ ≤ (C*Y^ε)*(2*∏ i, M i) :=
      mul_le_mul_of_nonneg_right (hfiber S hS Y hY b hb hbY) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
