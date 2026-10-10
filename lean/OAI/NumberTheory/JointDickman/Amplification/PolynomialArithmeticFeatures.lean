import OAI.NumberTheory.JointDickman.Amplification.SchwartzArithmeticFeatures
import OAI.NumberTheory.JointDickman.Arithmetic.SmoothArithmeticTensor

namespace OAI

/-! # The finite polynomial smooth weight has a finite prime-site kernel -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap

noncomputable def polynomialTermKernel (P : MvPolynomial (Fin 4) ℝ)
    (d : Fin 4 →₀ ℕ) (m B j : ℕ) (c : ℕ → ℝ) (H : ℕ)
    (T t : ℝ) (S : Finset ℤ) (s : ℤ → ℝ) :
    (auxiliaryPrimes B → Bool) → (auxiliaryPrimes B → Bool) → ℝ :=
  primeCoarseKernel m B
    (geometricWindowKernel m B t (Real.log (1/4)) (Real.log (17/4)) S
      (endpointSpatialWeight m B t (T/j)
        (fun k => (P.coeff d*(s k)^(d 3))*
          coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B))
        (tensorPowerFactor (d 0)) (tensorPowerFactor (d 1)) (tensorPowerFactor (d 2))))

noncomputable def polynomialPrimeKernel (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B j : ℕ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (H : (Fin 4 →₀ ℕ) → ℕ) (T t : ℝ) (S : Finset ℤ) (s : ℤ → ℝ)
    (x y : auxiliaryPrimes B → Bool) : ℝ :=
  ∑ d ∈ P.support, polynomialTermKernel P d (m d) B j (c d) (H d) T t S s x y

theorem polynomialPrimeKernel_test (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B j : ℕ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (H : (Fin 4 →₀ ℕ) → ℕ) (T t : ℝ) (S : Finset ℤ) (s : ℤ → ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    (∑ x, ∑ y, fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*
      g x*h y*polynomialPrimeKernel P m B j c H T t S s x y) =
    ∑ d ∈ P.support, ∑ x, ∑ y,
      fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*
        g x*h y*polynomialTermKernel P d (m d) B j (c d) (H d) T t S s x y := by
  classical
  simp only [polynomialPrimeKernel,mul_sum]
  conv_lhs => arg 2; ext x; rw [sum_comm]
  rw [sum_comm]

theorem polynomial_arithmetic_feature_comparison
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) {t η : ℝ} (ht : 0 < t) (hη : 0 < η) :
    ∃ c : (Fin 4 →₀ ℕ) → ℕ → ℝ,
      (∀ d, c d 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c d 0) ∧
      ∃ H : (Fin 4 →₀ ℕ) → ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ δ : ℝ, 0 < δ → ∃ m : (Fin 4 →₀ ℕ) → ℕ, (∀ d, 0 < m d) ∧ ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B → (B : ℝ)^(2/5 : ℝ) ≤ Q →
      ∀ T : ℝ, 0 < T → η*T ≤ j → ∀ S : Finset ℤ,
      (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
      (∀ k ∈ S, Real.log (Real.exp ((k : ℝ)*t)/T) ∈
        Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B)) →
      ∀ s : ℤ → ℝ, (∀ k ∈ S, |s k| ≤ 3) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      T*|geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S
        (fun k x y z => MvPolynomial.eval ![x,y,z,s k] P*
          tensorBoxBump x*tensorBoxBump y*tensorBoxBump z) g h-
        (singularSeries j/(j : ℝ))*(∑ x, ∑ y,
          fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*
            g x*h y*polynomialPrimeKernel P m B j c H T t S s x y)| ≤
        ε B+δ*(T/j)*singularSeries j := by
  classical
  let R := fun d : Fin 4 →₀ ℕ => |P.coeff d| *(3 : ℝ)^(d 3)
  have hex (d : Fin 4 →₀ ℕ) := schwartz_arithmetic_feature_comparison hSD hSW hM hMP
    (by norm_num : (0 : ℝ) < 1/4) (by norm_num : (1/4 : ℝ) ≤ 17/4)
    (by norm_num : (0 : ℝ) < 1/4) (by norm_num : (1/4 : ℝ) ≤ 17/4) ht hη
    (show 0 ≤ R d by positivity) (tensorPowerFactor (d 0)) (tensorPowerFactor (d 1))
    (tensorPowerFactor (d 2)) (tensorPowerFactor_support _) (tensorPowerFactor_support _)
    (tensorPowerFactor_support _)
  choose c hc hcpos H e he hcompare using hex
  refine ⟨c,fun d => ⟨hc d,hcpos d⟩,H,fun B => ∑ d ∈ P.support, e d B,?_,?_⟩
  · simpa using tendsto_finsetSum P.support (fun d _ => he d)
  intro δ hδ
  let δ₀ := δ/((P.support.card : ℝ)+1)
  have hδ₀ : 0 < δ₀ := div_pos hδ (by positivity)
  choose m hm hB using fun d => hcompare d δ₀ hδ₀
  refine ⟨m,hm,?_⟩
  filter_upwards [(eventually_all_finset P.support).mpr (fun d _ => hB d)] with B hB
  intro j _ Q hQ hscale hcut T hT hlag S hbox hlog s hs g h hg hh
  let A := fun d : Fin 4 →₀ ℕ => weightedGeometricArithmeticSum B j (1/4) (17/4) (1/4) (17/4)
    T t S (fun k => P.coeff d*(s k)^(d 3)) g h
    (tensorPowerFactor (d 0)) (tensorPowerFactor (d 1)) (tensorPowerFactor (d 2))
  let K := fun d : Fin 4 →₀ ℕ => ∑ x, ∑ y,
    fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*
      g x*h y*polynomialTermKernel P d (m d) B j (c d) (H d) T t S s x y
  have hlocal : ∀ d ∈ P.support,
      T*|A d-(singularSeries j/(j : ℝ))*K d| ≤ e d B+δ₀*(T/j)*singularSeries j := by
    intro d hd
    apply hB d hd j Q hQ hscale hcut T hT hlag S hbox hlog
      (fun k => P.coeff d*(s k)^(d 3)) _ g h hg hh
    intro k hk
    rw [abs_mul,abs_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hs k hk) _) (abs_nonneg _)
  rw [geometricSmoothArithmeticSum_tensor,polynomialPrimeKernel_test, mul_sum,← sum_sub_distrib]
  calc
    _ ≤ T*(∑ d ∈ P.support, |A d-(singularSeries j/(j : ℝ))*K d|) :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) hT.le
    _ = ∑ d ∈ P.support, T*|A d-(singularSeries j/(j : ℝ))*K d| := mul_sum _ _ _
    _ ≤ ∑ d ∈ P.support, (e d B+δ₀*(T/j)*singularSeries j) := sum_le_sum hlocal
    _ = (∑ d ∈ P.support, e d B)+(P.support.card : ℝ)*δ₀*(T/j)*singularSeries j := by
      rw [sum_add_distrib,sum_const,nsmul_eq_mul]
      ring
    _ ≤ _ := by
      have hcδ : (P.support.card : ℝ)*δ₀ ≤ δ := by
        change (P.support.card : ℝ)*(δ/((P.support.card : ℝ)+1)) ≤ δ
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < (P.support.card : ℝ)+1)).mpr
        nlinarith
      have hSp := (singularSeries_bounds hMP j).1
      have hm := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcδ (show 0 ≤ T/(j : ℝ) by positivity)) hSp
      linarith

end JointDickman

end OAI
