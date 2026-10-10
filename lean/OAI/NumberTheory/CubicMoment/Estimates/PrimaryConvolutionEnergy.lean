import OAI.NumberTheory.CubicMoment.Estimates.IdealDivisorPower
import OAI.NumberTheory.CubicMoment.Estimates.PrimeConvolutionMoments
import OAI.NumberTheory.CubicMoment.Estimates.OrdinaryMixedSieve

namespace OAI

/-! Fixed-length convolutions of arbitrary primary elements. The divisor
bound absorbs the tuple multiplicity in any positive norm power. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma orderedPrimarySupport_primary (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ a ∈ S i, primary a) {b : Eisenstein}
    (hb : b ∈ orderedConvolutionSupport S) : primary b := by
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
  exact primary_finset_prod _ _ (fun i _ => hS i (f i) (Fintype.mem_piFinset.mp hf i))

/-- The tuple multiplicity is uniformly a small power even when each
factor has arbitrarily many distinct prime divisors. -/
theorem primary_tuple_fiber_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein),
      (∀ i, ∀ a ∈ S i, primary a) → ∀ Y : ℝ, 1 ≤ Y →
      ∀ b ∈ orderedConvolutionSupport S, norm b ≤ Y →
      (((Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)).card : ℝ) ≤ C*Y^ε := by
  let k : ℝ := Fintype.card ι
  let δ : ℝ := ε/(k+1)
  have hk : 0 ≤ k := Nat.cast_nonneg _
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδε : δ*k ≤ ε := by
    have h := div_mul_cancel₀ ε (show k+1 ≠ 0 by positivity)
    change δ*(k+1) = ε at h
    nlinarith
  obtain ⟨D,hD,hdiv⟩ := primary_divisor_card_small_power hδ
  refine ⟨D^(Fintype.card ι),pow_pos hD _,?_⟩
  intro S hS Y hY b hb hbY
  have hb0 := primary_ne_zero (orderedPrimarySupport_primary S hS hb)
  have hsub : (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b) ⊆
      Fintype.piFinset (fun i => (S i).filter (fun a => a ∣ b)) := by
    intro f hf
    obtain ⟨hfs,hfb⟩ := Finset.mem_filter.mp hf
    apply Fintype.mem_piFinset.mpr
    intro i
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp hfs i,?_⟩
    rw [← hfb]
    exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)
  have hcard (i : ι) : (((S i).filter (fun a => a ∣ b)).card : ℝ) ≤ D*Y^δ :=
    (hdiv (S i) (hS i) b hb0).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg b) hbY hδ.le) hD.le)
  calc
    _ ≤ ((Fintype.piFinset (fun i => (S i).filter (fun a => a ∣ b))).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ = ∏ i, (((S i).filter (fun a => a ∣ b)).card : ℝ) := by
      rw [Fintype.card_piFinset,Nat.cast_prod]
    _ ≤ ∏ _i : ι, D*Y^δ := Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
      (fun i _ => hcard i)
    _ = D^(Fintype.card ι)*Y^(δ*k) := by
      rw [Finset.prod_const,Finset.card_univ,mul_pow,← Real.rpow_mul_natCast (by linarith)]
    _ ≤ D^(Fintype.card ι)*Y^ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hY hδε) (by positivity)

/-- Exact independent coefficient energies, with only a small norm-power
loss when collecting arbitrary primary tuples by their product. -/
theorem primary_orderedConvolution_energy {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ), (∀ i, ∀ a ∈ S i, primary a) →
      ∀ Y : ℝ, 1 ≤ Y → (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y) →
      (∑ b ∈ orderedConvolutionSupport S, ‖orderedConvolution S w b‖^2) ≤
        C*Y^ε*primeConvolutionEnergy S w := by
  obtain ⟨C,hC,hfiber⟩ := primary_tuple_fiber_small_power (ι := ι) hε
  refine ⟨C,hC,?_⟩
  intro S w hS Y hY hprod
  let T := Fintype.piFinset S
  let W : (ι → Eisenstein) → ℂ := fun f => ∏ i, w i (f i)
  have hrow (b : Eisenstein) (hb : b ∈ orderedConvolutionSupport S) :
      ‖orderedConvolution S w b‖^2 ≤
        C*Y^ε*∑ f ∈ T with (∏ i, f i) = b, ‖W f‖^2 := by
    have hCS := complex_bilinear_rows_sq (T.filter (fun f => (∏ i, f i) = b))
      (fun _ => (1:ℂ)) W
    simp only [one_mul,norm_one,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hCS
    change ‖orderedConvolution S w b‖^2 ≤ _ at hCS
    apply hCS.trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    apply hfiber S hS Y hY b hb
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
    exact hprod f hf
  calc
    _ ≤ ∑ b ∈ orderedConvolutionSupport S,
        C*Y^ε*∑ f ∈ T with (∏ i, f i) = b, ‖W f‖^2 := Finset.sum_le_sum hrow
    _ = C*Y^ε*∑ f ∈ T, ‖W f‖^2 := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_fiberwise_of_maps_to
        (fun f hf => Finset.mem_image_of_mem _ hf) _
    _ = _ := by
      congr 1
      simp only [W,norm_prod,← Finset.prod_pow]
      exact (Finset.prod_univ_sum S (fun i a => ‖w i a‖^2)).symm

theorem primary_orderedConvolution_twisted_energy {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ), (∀ i, ∀ a ∈ S i, primary a) →
      ∀ Y : ℝ, 1 ≤ Y → (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y) →
      ∀ χ : Eisenstein → ℂ, (∀ b ∈ orderedConvolutionSupport S, ‖χ b‖ ≤ 1) →
      (∑ b ∈ orderedConvolutionSupport S, ‖orderedConvolution S w b*χ b‖^2) ≤
        C*Y^ε*primeConvolutionEnergy S w := by
  obtain ⟨C,hC,hbound⟩ := primary_orderedConvolution_energy (ι := ι) hε
  refine ⟨C,hC,?_⟩
  intro S w hS Y hY hprod χ hχ
  apply le_trans _ (hbound S w hS Y hY hprod)
  apply Finset.sum_le_sum
  intro b hb
  rw [norm_mul]
  exact pow_le_pow_left₀ (mul_nonneg (_root_.norm_nonneg _) (_root_.norm_nonneg _))
    (mul_le_of_le_one_right (_root_.norm_nonneg _) (hχ b hb)) 2

/-- The actual independent primary-element product has the unrestricted
cubic moment with the proved divisor-power energy loss. -/
theorem primaryConvolution_cubic_moment {ε δ : ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ), (∀ i, ∀ a ∈ S i, primary a) →
      ∀ (P : Finset Eisenstein) (N Y : ℝ), 1 ≤ N → 1 ≤ Y →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y) →
      (∑ a ∈ P, ‖primeCubicProductPolynomial S w a‖^2) ≤
        C*(N*Y)^ε*(N*Y^(1/3:ℝ)+(N*Y)^(2/3:ℝ)+Y^(4/3:ℝ)+Y)*
          (Y^δ*primeConvolutionEnergy S w) := by
  obtain ⟨C,hC,hbound⟩ := unrestricted_cubic_sieve hε hε₁
  obtain ⟨D,hD,henergy⟩ := primary_orderedConvolution_energy (ι := ι) hδ
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro S w hS P N Y hN hY hP hprod
  have hH : ∀ b ∈ orderedConvolutionSupport S, b ≠ 0 ∧ norm b ≤ Y := by
    intro b hb
    refine ⟨primary_ne_zero (orderedPrimarySupport_primary S hS hb),?_⟩
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
    exact hprod f hf
  have he : (∑ a ∈ P, ‖primeCubicProductPolynomial S w a‖^2) =
      ∑ a ∈ P, ‖∑ b ∈ orderedConvolutionSupport S,
        orderedConvolution S w b*cubicSymbol a b‖^2 := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [primeCubicProductPolynomial_eq S w (hP a ha).1]
  rw [he]
  apply (hbound P (orderedConvolutionSupport S) N Y hN hY hP hH
    (orderedConvolution S w)).trans
  have h := mul_le_mul_of_nonneg_left (henergy S w hS Y hY hprod)
    (show 0 ≤ C*(N*Y)^ε*(N*Y^(1/3:ℝ)+(N*Y)^(2/3:ℝ)+Y^(4/3:ℝ)+Y) by positivity)
  convert h using 1
  ring

/-- The corresponding ordinary mixed-character moment for actual
independent primary factors. Huxley's additive large sieve is the only
published analytic assumption. -/
theorem primaryConvolution_mixed_moment (hHuxley : HuxleyAdditiveLargeSieve)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ), (∀ i, ∀ a ∈ S i, primary a) →
      ∀ (P : Finset (Eisenstein × Eisenstein)) (Q Y : ℝ), 1 ≤ Q → 1 ≤ Y →
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y) →
      (∑ p ∈ P, ‖∏ i, ∑ a ∈ S i, w i a*mixedCubic p.1 p.2 a‖^2) ≤
        C*Q^ε*(Q^2+Y)*(Y^δ*primeConvolutionEnergy S w) := by
  obtain ⟨C,hC,hbound⟩ := ordinary_mixed_cubic_sieve_finite hHuxley hε
  obtain ⟨D,hD,henergy⟩ := primary_orderedConvolution_energy (ι := ι) hδ
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro S w hS P Q Y hQ hY hP hprod
  have hH : ∀ b ∈ orderedConvolutionSupport S, b ≠ 0 ∧ norm b ≤ Y := by
    intro b hb
    refine ⟨primary_ne_zero (orderedPrimarySupport_primary S hS hb),?_⟩
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
    exact hprod f hf
  have he : (∑ p ∈ P, ‖∏ i, ∑ a ∈ S i, w i a*mixedCubic p.1 p.2 a‖^2) =
      ∑ p ∈ P, ‖∑ b ∈ orderedConvolutionSupport S,
        orderedConvolution S w b*mixedCubic p.1 p.2 b‖^2 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [orderedConvolution_mixedCubic S w (hP p hp).1.1 (hP p hp).1.2.1]
  rw [he]
  apply (hbound Q Y hQ hY P (orderedConvolutionSupport S) hP hH
    (orderedConvolution S w)).trans
  have h := mul_le_mul_of_nonneg_left (henergy S w hS Y hY hprod)
    (show 0 ≤ C*Q^ε*(Q^2+Y) by positivity)
  convert h using 1
  ring

end CubicFirstMoment

end

end OAI
