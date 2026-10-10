import OAI.NumberTheory.CubicMoment.Estimates.PoissonProfileBudget
import OAI.NumberTheory.CubicMoment.Estimates.OuterPoissonAnnulus
import OAI.NumberTheory.CubicMoment.Estimates.NonzeroOuterBound

namespace OAI
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment.ProfileControl

theorem wideCoprimeRadialForm_rapidDecay (P : PoissonProfileBudget) :
    ∀ (S H U : Finset Eisenstein),
      (∀ a ∈ S, primary a ∧ Squarefree a) →
      (∀ p ∈ U, primaryPrime p) →
      (∀ a ∈ S, primaryPrimeFactors a ⊆ U) →
      ∀ (v w phase : Eisenstein → ℂ), (∀ h ∈ H, ‖phase h‖ ≤ 1) →
      ∀ (x y : Eisenstein → ℝ),
      (∀ h ∈ H, 0 < x h) →
      (∀ a ∈ S, 0 < y a) →
      (∀ h ∈ H, ∀ a ∈ S, ∀ b ∈ S, |Real.log (x h)-Real.log (y a*y b)| ≤ poissonProfileLogWidth) →
      ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^3 * ‖coprimeRadialForm S H v w phase x y P.V ρ‖ ≤
        P.cost * coprimeNormMajorant S H U v w := by
  have hc := P.wide
  intro S H U hS hU hSU v w phase hphase x y hx hy hlog ρ hρ
  calc
    _ ≤ (1+ρ)^3 * ((∫ t : ℝ, ‖wideGramMellinCoefficient poissonProfileLogWidth poissonProfileLogWidth_pos P.V P.compact P.smooth ρ t‖) *
        coprimeNormMajorant S H U v w) :=
      mul_le_mul_of_nonneg_left
        (wideCoprimeRadialForm_norm_le poissonProfileLogWidth poissonProfileLogWidth_pos S H U hS hU hSU v w phase hphase x y hx hy hlog P.V P.compact P.smooth hρ)
        (by positivity)
    _ = ((1+ρ)^3 * (∫ t : ℝ, ‖wideGramMellinCoefficient poissonProfileLogWidth poissonProfileLogWidth_pos P.V P.compact P.smooth ρ t‖)) *
        coprimeNormMajorant S H U v w := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hc ρ hρ) (coprimeNormMajorant_nonneg _ _ _ _ _)



theorem wide_coprimePoissonDyad_norm_recurrence :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : PoissonProfileBudget) (S H : Finset Eisenstein),
      (∀ a ∈ S, primary a ∧ Squarefree a) →
      ∀ (u : Eisenstein → ℂ) (Z J N : ℝ), 0 ≤ Z → 0 < J → 0 < N →
      (∀ a ∈ S, N ≤ norm a) →
      (∀ h ∈ H, 0 < norm h) →
      (∀ h ∈ H, ∀ a ∈ S, ∀ b ∈ S,
        |Real.log (norm h/J)-Real.log ((norm a/N)*(norm b/N))| ≤ poissonProfileLogWidth) →
      (1+Z*J/(27*N^2))^3 * ‖coprimePoissonDyad S H u P.V Z‖ ≤
        (C*P.cost)*(Z/N)*finiteCubicBound S H *
          ∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖u a‖^2 := by
  refine ⟨1/9, by norm_num, ?_⟩
  intro P S H hS u Z J N hZ hJ hN hSN hHJ hlog
  let C := P.cost
  have hC : 0 < C := P.cost_pos
  have hbound := wideCoprimeRadialForm_rapidDecay P
  let U := sievePrimeSet S
  have hU : ∀ p ∈ U, primaryPrime p := sievePrimeSet_primary S (fun a ha => (hS a ha).1)
  have hu : ∀ a ∈ S, primaryPrimeFactors a ⊆ U := fun a ha => factors_subset_sievePrimeSet ha
  have hx : ∀ h ∈ H, 0 < norm h/J := fun h hh => div_pos (hHJ h hh) hJ
  have hy : ∀ a ∈ S, 0 < norm a/N := fun a ha => div_pos (hN.trans_le (hSN a ha)) hN
  have hi := hbound S H U hS hU hu (gaussRowCoefficient u) (gaussRowCoefficient u)
    (fun h => (Real.fourierChar (tracePair (h : ℂ) (1 / (3*traceLambda))) : ℂ))
    (fun h hh => by simp only [Circle.norm_coe, le_refl])
    (fun h => norm h/J) (fun a => norm a/N) hx hy hlog (Z*J/(27*N^2)) (by positivity)
  have hmajor : coprimeNormMajorant S H U (gaussRowCoefficient u) (gaussRowCoefficient u) ≤
      finiteCubicBound S H *
        ((∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖u a‖^2)/N) := by
    calc
      _ ≤ finiteCubicBound S H *
          ∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖gaussRowCoefficient u a‖^2 := by
        convert coprimeNormMajorant_le_divisorEnergy S H U (fun a ha => (hS a ha).1)
          hU (gaussRowCoefficient u) (gaussRowCoefficient u) using 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (gaussRowCoefficient_divisor_energy S hS u hN hSN)
        (finiteCubicBound_nonneg _ _)
  rw [coprimePoissonDyad_separated S H u P.V hZ (ne_of_gt hJ) (ne_of_gt hN),
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ = (Z/9) * ((1+Z*J/(27*N^2))^3 * ‖coprimeRadialForm S H
        (gaussRowCoefficient u) (gaussRowCoefficient u)
        (fun h => (Real.fourierChar (tracePair (h : ℂ) (1 / (3*traceLambda))) : ℂ))
        (fun h => norm h/J) (fun a => norm a/N) P.V (Z*J/(27*N^2))‖) := by ring
    _ ≤ (Z/9) * (C*(finiteCubicBound S H *
        ((∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖u a‖^2)/N))) :=
      mul_le_mul_of_nonneg_left (hi.trans (mul_le_mul_of_nonneg_left hmajor hC.le)) (by positivity)
    _ = _ := by dsimp [C]; ring



theorem coprime_poisson_outer_annulus {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : PoissonProfileBudget) (S : Finset Eisenstein) (u : Eisenstein → ℂ) (Z N : ℝ) (j : ℕ),
      0 < Z → 1 ≤ N →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ N ≤ norm a ∧ norm a ≤ (2:ℝ)*N) →
      (1+Z*2^j/(27*N^2))^3 * ‖coprimePoissonDyad S (frequencyDyad j) u P.V Z‖ ≤
        (C*P.cost)*(Z/N)*(4*2^j*((2:ℝ)*N))^ε*
          (2*2^j+(2*2^j*((2:ℝ)*N))^(2/3:ℝ)+(2*2^j)^(1/3:ℝ)*((2:ℝ)*N))*
            ∑ a ∈ S, (2:ℝ)^(primaryPrimeFactors a).card*‖u a‖^2 := by
  obtain ⟨C₀,hC₀,hrec₀⟩ := wide_coprimePoissonDyad_norm_recurrence
  obtain ⟨C₂,hC₂,houter⟩ := all_frequency_cubic_operator_bound hε
  refine ⟨C₀*C₂,mul_pos hC₀ hC₂,?_⟩
  intro P S u Z N j hZ hN hS
  let C₁ := C₀*P.cost
  have hC₁ : 0 < C₁ := mul_pos hC₀ P.cost_pos
  have hrec := hrec₀ P
  have hR : (1:ℝ) ≤ 2 := by norm_num
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hJ : (1:ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
  have hs : ∀ a ∈ S, primary a ∧ Squarefree a :=
    fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩
  have hlog : ∀ h ∈ frequencyDyad j, ∀ a ∈ S, ∀ b ∈ S,
      |Real.log (norm h/2^j)-Real.log ((norm a/N)*(norm b/N))| ≤ 1+2*Real.log (2:ℝ) := by
    intro h hh a ha b hb
    apply compact_norm_log_ratio hR
    · exact ⟨(le_div_iff₀ (by positivity : (0:ℝ) < 2^j)).mpr
        (by simpa only [one_mul] using (frequencyDyad_norm hh).1),
        (div_le_iff₀ (by positivity : (0:ℝ) < 2^j)).mpr (frequencyDyad_norm hh).2⟩
    · exact ⟨(le_div_iff₀ hNp).mpr (by simpa only [one_mul] using (hS a ha).2.2.1),
        (div_le_iff₀ hNp).mpr (hS a ha).2.2.2⟩
    · exact ⟨(le_div_iff₀ hNp).mpr (by simpa only [one_mul] using (hS b hb).2.2.1),
        (div_le_iff₀ hNp).mpr (hS b hb).2.2.2⟩
  have hr := hrec S (frequencyDyad j) hs u Z (2^j) N hZ.le (by positivity) hNp
    (fun a ha => (hS a ha).2.2.1)
    (fun h hh => (by positivity : (0:ℝ) < 2^j).trans_le (frequencyDyad_norm hh).1) hlog
  have hb := houter S (frequencyDyad j) (2*2^j) ((2:ℝ)*N) (by nlinarith) (by nlinarith)
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1,(hS a ha).2.2.2⟩)
    (fun h hh => ⟨(mem_frequencyDyad.mp hh).1,(frequencyDyad_norm hh).2⟩)
  apply hr.trans
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb
    (by positivity : 0 ≤ C₁*(Z/N))) (Finset.sum_nonneg (fun _ _ => by positivity))).trans_eq
  congr 1
  rw [show 2*(2*2^j)*((2:ℝ)*N) = 4*2^j*((2:ℝ)*N) by ring]
  dsimp [C₁]
  ring


theorem coprimeGramForm_outer_dual_bound {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : PoissonProfileBudget) (S : Finset Eisenstein) (u : Eisenstein → ℂ) (Z N : ℝ),
      0 < Z → 1 ≤ N →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ N ≤ norm a ∧ norm a ≤ (2:ℝ)*N) →
      ‖coprimeGramForm S u P.V Z-coprimePoissonDyad S {0} u P.V Z‖ ≤
        (2*(C*P.cost)*(Z/N)*(4*((2:ℝ)*N))^ε)*outerDyadicBound ε ((2:ℝ)*N) (Z/(27*N^2))*
          ∑ a ∈ S, (2:ℝ)^(primaryPrimeFactors a).card*‖u a‖^2 := by
  obtain ⟨C₀,hC₀,hbound₀⟩ := coprime_poisson_outer_annulus hε
  refine ⟨C₀,hC₀,?_⟩
  intro P S u Z N hZ hN hS
  let C := C₀*P.cost
  have hC : 0 < C := mul_pos hC₀ P.cost_pos
  have hbound := hbound₀ P
  have hR : (1:ℝ) ≤ 2 := by norm_num
  let E := ∑ a ∈ S, (2:ℝ)^(primaryPrimeFactors a).card*‖u a‖^2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => by positivity)
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hR0 : 0 ≤ (2:ℝ)*N := mul_nonneg (zero_le_one.trans hR) hNp.le
  have hfinite (I : Finset ℕ) :
      ‖∑ j ∈ I, coprimePoissonDyad S (frequencyDyad j) u P.V Z‖ ≤
        (2*C*(Z/N)*(4*((2:ℝ)*N))^ε)*outerDyadicBound ε ((2:ℝ)*N) (Z/(27*N^2))*E := by
    have hf (j : ℕ) (_ : j ∈ I) := hbound S u Z N j hZ hN hS
    have hh := finite_outer_poisson_sum I
      (fun j => coprimePoissonDyad S (frequencyDyad j) u P.V Z)
      (C := C*E) (T := (2:ℝ)*N) (ε := ε) (mul_nonneg hC.le hE) hZ hNp hR0 hε hε1
      (fun j hj => (hf j hj).trans_eq (by dsimp only [E]; ring))
    exact hh.trans_eq (by ring)
  have hs := hasSum_coprimePoissonDyad_with_zero S
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩) u P.V P.compact P.smooth hZ
  exact le_of_tendsto hs.norm (Eventually.of_forall hfinite)


theorem coprimeGramForm_outer_nonzero {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : PoissonProfileBudget) (S : Finset Eisenstein) (u : Eisenstein → ℂ) (Z N : ℝ),
      0 < Z → 1 ≤ N →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ N ≤ norm a ∧ norm a ≤ (2:ℝ)*N) →
      ‖coprimeGramForm S u P.V Z-coprimePoissonDyad S {0} u P.V Z‖ ≤
        (C*P.cost)*(N^3/Z)^ε*(N+Z^(1/3:ℝ)*N+Z^(2/3:ℝ)*N^(2/3:ℝ))*
          ∑ a ∈ S, (2:ℝ)^(primaryPrimeFactors a).card*‖u a‖^2 := by
  obtain ⟨C₀,hC₀,hbound₀⟩ := coprimeGramForm_outer_dual_bound hε hε1
  have hRp : 0 < (2:ℝ) := by norm_num
  refine ⟨C₀*outerPowerConstant ε (2:ℝ),mul_pos hC₀ (outerPowerConstant_pos hε hε1 hRp),?_⟩
  intro P S u Z N hZ hN hS
  let C := C₀*P.cost
  have hC : 0 < C := mul_pos hC₀ P.cost_pos
  have hbound := hbound₀ P
  convert (hbound S u Z N hZ hN hS).trans
    (mul_le_mul_of_nonneg_right
      (outer_primal_scale_bound hZ (zero_lt_one.trans_le hN) hRp hC.le hε hε1)
      (Finset.sum_nonneg (fun _ _ => by positivity))) using 1
  ring


end CubicFirstMoment.ProfileControl

end

end OAI
