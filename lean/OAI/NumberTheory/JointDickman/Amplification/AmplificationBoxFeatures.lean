import OAI.NumberTheory.JointDickman.Probability.AmplificationTensorProfile

namespace OAI

/-! # Finite prime-site approximation for the actual smooth amplification box weight -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem amplification_box_feature_comparison
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
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
        (fun k x y z => amplificationBoxWeight B (s k) x y z) g h-
        (singularSeries j/(j : ℝ))*(∑ x, ∑ y,
          fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*
            g x*h y*polynomialPrimeKernel P m B j c H T t S s x y)| ≤
        ε B+δ*(T/j)*singularSeries j ∧
        ∀ x y, |polynomialPrimeKernel P m B j c H T t S s x y| ≤ C₀ := by
  obtain ⟨C,hC,hfreeze⟩ := amplificationBoxWeight_freezing
  obtain ⟨D,hD,ε₀,hε₀,hmass⟩ := smooth_arithmetic_mass_bound hSD hSW hM hMP ht hη
  have hrate : Tendsto (fun B : ℕ => C/(B : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
  intro δ hδ
  obtain ⟨P,c,hc,H,m,hm,C₀,hC₀,ε₁,hε₁,hcompare⟩ := smooth_arithmetic_feature_comparison
    hSD hSW hM hMP amplificationTensorProfile amplificationTensorProfile_continuous ht hη
    (δ/2) (by positivity)
  have hbudget : ∀ᶠ B : ℕ in atTop, (C/(B : ℝ))*D ≤ δ/2 :=
    (hrate.mul_const D).eventually_le_const (by simpa using half_pos hδ)
  refine ⟨P,c,hc,H,m,hm,C₀,hC₀,fun B => ε₁ B+(C/(B : ℝ))*ε₀ B,?_,?_⟩
  · simpa using hε₁.add (hrate.mul hε₀)
  filter_upwards [hcompare,hmass,hbudget,eventually_gt_atTop 0] with B hb hmassB hbud hB
  intro j _ Q hQ hscale hcut T hT hlag S hbox hlog s hs g h hg hh
  obtain ⟨hcomp,hbound⟩ := hb j Q hQ hscale hcut T hT hlag S hbox hlog s hs g h hg hh
  refine ⟨?_,hbound⟩
  let A := geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S
    (fun k x y z => amplificationBoxWeight B (s k) x y z) g h
  let A₀ := geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S
    (fun k x y z => amplificationTensorProfile ![x,y,z,s k]*tensorCutoff x y z) g h
  let V := geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S
    (fun _ x y z => tensorCutoff x y z) (fun _ => 1) (fun _ => 1)
  let K := (singularSeries j/(j : ℝ))*(∑ x, ∑ y,
    fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*g x*h y*
      polynomialPrimeKernel P m B j c H T t S s x y)
  have hdiff : |A-A₀| ≤ (C/(B : ℝ))*V := by
    change |geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S _ g h-
      geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S _ g h| ≤ _
    rw [← geometricSmoothArithmeticSum_sub,← geometricSmoothArithmeticSum_smul]
    apply geometricSmoothArithmeticSum_abs_le _ _ _ _ _ _ _ _ _ _ _ g h hg hh
    intro k _ x y z
    rw [amplificationTensorProfile_cutoff]
    exact hfreeze B hB (s k) x y z
  have hV : T*V ≤ ε₀ B+D*(T/j)*singularSeries j :=
    hmassB j Q hQ hscale hcut T hT hlag S hbox hlog
  have hdiff' : T*|A-A₀| ≤ (C/(B : ℝ))*(ε₀ B+D*(T/j)*singularSeries j) := by
    calc
      _ ≤ T*((C/(B : ℝ))*V) := mul_le_mul_of_nonneg_left hdiff hT.le
      _ = (C/(B : ℝ))*(T*V) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hV (div_nonneg hC (Nat.cast_nonneg B))
  have hSp := (singularSeries_bounds hMP j).1
  have hbud' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hbud (show 0 ≤ T/(j : ℝ) by positivity)) hSp
  have hcomp' : T*|A₀-K| ≤ ε₁ B+(δ/2)*(T/j)*singularSeries j := hcomp
  change T*|A-K| ≤ _
  have htri := mul_le_mul_of_nonneg_left (abs_sub_le A A₀ K) hT.le
  nlinarith

end JointDickman

end OAI
