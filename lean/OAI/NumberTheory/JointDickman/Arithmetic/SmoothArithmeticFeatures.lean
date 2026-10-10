import OAI.NumberTheory.JointDickman.Probability.PolynomialKernelBounds
import OAI.NumberTheory.JointDickman.Arithmetic.SmoothArithmeticMassBound

namespace OAI

/-! # Compact smooth arithmetic weights have finite prime-site approximations -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem smooth_arithmetic_feature_comparison
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (F : (Fin 4 → ℝ) → ℝ) (hF : ContinuousOn F tensorParameterBox)
    {t η : ℝ} (ht : 0 < t) (hη : 0 < η) :
    ∀ δ : ℝ, 0 < δ → ∃ P : MvPolynomial (Fin 4) ℝ,
      ∃ c : (Fin 4 →₀ ℕ) → ℕ → ℝ,
      (∀ d, c d 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c d 0) ∧
      ∃ H m : (Fin 4 →₀ ℕ) → ℕ, (∀ d, 0 < m d) ∧
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B → (B : ℝ)^(2/5 : ℝ) ≤ Q →
      ∀ T : ℝ, 0 < T → η*T ≤ j → ∀ S : Finset ℤ,
      (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
      (∀ k ∈ S, Real.log (Real.exp ((k : ℝ)*t)/T) ∈
        Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B)) →
      ∀ s : ℤ → ℝ, (∀ k ∈ S, |s k| ≤ 3) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      T*|geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S
        (fun k x y z => F ![x,y,z,s k]*tensorCutoff x y z) g h-
        (singularSeries j/(j : ℝ))*(∑ x, ∑ y,
          fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*
            g x*h y*polynomialPrimeKernel P m B j c H T t S s x y)| ≤
        ε B+δ*(T/j)*singularSeries j ∧
        ∀ x y, |polynomialPrimeKernel P m B j c H T t S s x y| ≤ C₀ := by
  obtain ⟨C,hC,ε₀,hε₀,hmass⟩ := smooth_arithmetic_mass_bound hSD hSW hM hMP ht hη
  intro δ hδ
  let α := δ/(2*(C+1))
  have hα : 0 < α := div_pos hδ (by positivity)
  obtain ⟨P,hP⟩ := smooth_arithmetic_tensor_approximation F hF hα
  obtain ⟨c,hc,H,ε₁,hε₁,hpoly⟩ := polynomial_arithmetic_feature_comparison
    hSD hSW hM hMP P ht hη
  obtain ⟨m,hm,hpolyB⟩ := hpoly (δ/2) (by positivity)
  obtain ⟨C₀,hC₀,hbounded⟩ := polynomialPrimeKernel_bounded hM hMP P m hm c
    (fun d => (hc d).1) H ht
  refine ⟨P,c,hc,H,m,hm,C₀,hC₀,fun B => α*ε₀ B+ε₁ B,?_,?_⟩
  · simpa using (hε₀.const_mul α).add hε₁
  filter_upwards [hmass,hpolyB,hbounded] with B hmassB hpolyB hkb
  intro j _ Q hQ hscale hcut T hT hlag S hbox hlog s hs g h hg hh
  let A := geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S
    (fun k x y z => F ![x,y,z,s k]*tensorCutoff x y z) g h
  let Aₚ := geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S
    (fun k x y z => MvPolynomial.eval ![x,y,z,s k] P*tensorCutoff x y z) g h
  let V := geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S
    (fun _ x y z => tensorCutoff x y z) (fun _ => 1) (fun _ => 1)
  let K := (singularSeries j/(j : ℝ))*(∑ x, ∑ y,
    fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*
      g x*h y*polynomialPrimeKernel P m B j c H T t S s x y)
  have hap : |A-Aₚ| ≤ α*V := hP B j _ _ _ _ T t S s hs g h hg hh
  have hvol : T*V ≤ ε₀ B+C*(T/j)*singularSeries j :=
    hmassB j Q hQ hscale hcut T hT hlag S hbox hlog
  have hp : T*|Aₚ-K| ≤ ε₁ B+(δ/2)*(T/j)*singularSeries j := by
    simpa only [Aₚ,K,tensorCutoff,mul_assoc] using
      hpolyB j Q hQ hscale hcut T hT hlag S hbox hlog s hs g h hg hh
  have happrox : T*|A-Aₚ| ≤ α*(ε₀ B+C*(T/j)*singularSeries j) := by
    calc
      _ ≤ T*(α*V) := mul_le_mul_of_nonneg_left hap hT.le
      _ = α*(T*V) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hvol hα.le
  have hbudget : α*C+δ/2 ≤ δ := by
    have haC : α*C ≤ δ/2 := calc
      α*C ≤ α*(C+1) := mul_le_mul_of_nonneg_left (by linarith) hα.le
      _ = δ/2 := by dsimp [α]; field_simp
    linarith
  have hSp := (singularSeries_bounds hMP j).1
  have hbudget' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hbudget (show 0 ≤ T/(j : ℝ) by positivity)) hSp
  constructor
  · change T*|A-K| ≤ _
    have htri := mul_le_mul_of_nonneg_left (abs_sub_le A Aₚ K) hT.le
    nlinarith
  · exact hkb j T S (fun k hk => (hlog k hk).1) s hs

end JointDickman

end OAI
