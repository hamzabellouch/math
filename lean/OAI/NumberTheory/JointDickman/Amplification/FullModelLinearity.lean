import OAI.NumberTheory.JointDickman.Amplification.GeometricPeriodLaw

namespace OAI

/-! # Linearity in the scalar weight of each geometric box -/

namespace JointDickman
open Finset MeasureTheory
open scoped SchwartzMap

 theorem fullSmallMajorArcModel_mul (B j : ℕ) [NeZero j] (X : ℝ) (Q : ℕ)
    (F W : ℝ → ℂ) (a : ℕ+ → ℂ) (r : ℂ) :
    fullSmallMajorArcModel B j X Q F (fun ξ => r*W ξ) a =
      r*fullSmallMajorArcModel B j X Q F W a := by
  classical
  unfold fullSmallMajorArcModel
  have hi (q : ℕ+) (h : ZMod (j*(q : ℕ))) :
      (∫ ξ : ℝ, F ((h.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X))*(r*W ξ)) =
      r*∫ ξ : ℝ, F ((h.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X))*W ξ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ξ => by ring)
  simp_rw [hi]
  rw [mul_left_comm r]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro q _
  split_ifs
  · rw [mul_sum]
    apply sum_congr rfl
    intro h _
    split_ifs <;> ring
  · ring

noncomputable def weightedGeometricPeriodSum (B j : ℕ) (a b T t : ℝ)
    (S : Finset ℤ) (r : ℤ → ℝ) (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (w₁ w₂ w : ℝ → ℝ) : ℂ :=
  (B : ℂ)*∑ k ∈ S, (r k : ℂ)*(∫ θ in (0 : ℝ)..1,
    geometricBoxIntegrand B j a b T t g h w₁ w₂ w k θ)

noncomputable def weightedGeometricSmallArcSum (B j Q : ℕ) (a b T t : ℝ)
    (S : Finset ℤ) (r : ℤ → ℝ) (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (w₁ w₂ w : ℝ → ℝ) : ℂ :=
  (B : ℂ)*∑ k ∈ S, (r k : ℂ)*(∫ θ in smallMajorArcRegion B j (Real.exp ((k : ℝ)*t)/T) Q,
    geometricBoxIntegrand B j a b T t g h w₁ w₂ w k θ)

theorem weightedGeometricSmallArcSum_sub_model (B j Q : ℕ) [NeZero j] (a b T t : ℝ)
    (S : Finset ℤ) (r d : ℤ → ℝ) (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (w₁ w₂ : ℝ → ℝ) (w : 𝓢(ℝ,ℝ)) :
    weightedGeometricSmallArcSum B j Q a b T t S r g h w₁ w₂ w-
      geometricFullArcSum B j Q a b T t S (fun k => r k*d k) g h w₁ w₂ w =
      ∑ k ∈ S, (r k : ℂ)*((B : ℂ)*
        ((∫ θ in smallMajorArcRegion B j (Real.exp ((k : ℝ)*t)/T) Q,
          geometricBoxIntegrand B j a b T t g h w₁ w₂ w k θ)-
        fullSmallMajorArcModel B j (Real.exp ((k : ℝ)*t)/T) Q
          (fun θ => endpointFourierSum B a b (Real.exp ((k : ℝ)*t))
              (subsetSiteTest (auxiliaryPrimes B) g) w₁ θ*
            endpointFourierSum B a b (Real.exp ((k : ℝ)*t))
              (subsetSiteTest (auxiliaryPrimes B) h) w₂ (-θ))
          (fun ξ => (d k : ℂ)*testFourierTransform w ξ)
          (fun q => (ArithmeticFunction.moebius (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ)))) := by
  unfold weightedGeometricSmallArcSum geometricFullArcSum
  simp only [Complex.ofReal_mul,← mul_assoc,fullSmallMajorArcModel_mul]
  rw [← mul_sub,← sum_sub_distrib,mul_sum]
  apply sum_congr rfl
  intro k _
  ring

end JointDickman

end OAI
