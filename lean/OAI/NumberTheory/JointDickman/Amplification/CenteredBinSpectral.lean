import OAI.NumberTheory.JointDickman.Amplification.BinAwaySpectral
import OAI.NumberTheory.JointDickman.Amplification.BinDyadicLowFrequency
import OAI.NumberTheory.JointDickman.Analysis.MellinEnergyAlgebra
import OAI.NumberTheory.JointDickman.Analysis.MellinFrequencyTail

namespace OAI

/-! # Full spectral bounds for the centered principal coefficient -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Classical Topology

lemma centeredWeightedBinCoefficient_sub {J : ℕ} (ζ : Fin (J-1) → ℂ)
    (μ : ℂ) (E : Finset ℕ) (w : ℕ → ℝ) (x : ℝ) :
    (centeredWeightedBinCoefficient J ζ μ E w x : ℕ → ℂ) = fun n =>
      finiteWeightedCoefficient (binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ) E w n-
      μ*finiteWeightedCoefficient
        (binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) (fun _ => (1:ℂ))) E w n := by
  funext n
  by_cases hn : n=0
  · subst n
    simp
  · simp only [centeredWeightedBinCoefficient,finiteWeightedCoefficient,ArithmeticFunction.coe_mk,
      binLabel_apply hn,one_pow,prod_const_one]
    ring

theorem centered_bin_spectral {J : ℕ} (hJ : 0<J)
    (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖≤1) (μ : ℂ) (hμ : ‖μ‖≤1)
    (hmean : ∀ D : ℝ, 0<D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0)) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ H : ℝ in atTop,
    ∀ (E : Finset ℕ), (∀ p∈E, p.Prime) → ∀ w : ℕ → ℝ,
    (∀ p∈E, 0≤w p ∧ w p≤1) → ∀ A : ℝ, 0<A →
    ∀ᶠ x : ℝ in atTop, ∀ N : ℕ, (A/2)*x≤N → (N:ℝ)≤(2*A)*x →
    ∀ T : ℝ, 1≤T →
      (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N))
        (centeredWeightedBinCoefficient J ζ μ E w x) t‖^2) ≤
        17/H+4*canonicalAffineBase C H+(4*canonicalAffineSlope C H+128*Real.exp 1)*T/N := by
  obtain ⟨C,hC,haw⟩ := bin_away_spectral hJ
  refine ⟨C,hC,?_⟩
  filter_upwards [haw,canonical_affine_nonneg hC.le,eventually_gt_atTop (0:ℝ)] with H haw hpos hH
  intro E hE w hw A hA
  obtain ⟨U,hU,haw⟩ := haw E hE (2*A) (by positivity)
  obtain ⟨M,hM⟩ := eventually_atTop.mp (haw.and (eventually_gt_atTop (0:ℕ)))
  have hlo := centered_weighted_bin_dyadic_low hJ ζ hζ μ hμ hmean E hE w hw
    (show 0<A/2 by positivity) (show 0<2*A by positivity) hU (show 0<(1:ℝ)/H by positivity)
  filter_upwards [hlo,eventually_ge_atTop ((M:ℝ)/(A/2)),eventually_gt_atTop (0:ℝ)]
    with x hlo hx hx0
  intro N hNx hxN
  have hMN : M≤N := by
    have hh := (div_le_iff₀ (show 0<A/2 by positivity)).mp hx
    have hh' : (M:ℝ)≤N := hh.trans (by nlinarith only [hNx])
    exact_mod_cast hh'
  obtain ⟨haw,hN⟩ := hM N hMN
  have hbound : (N:ℝ)/(2*A)≤x := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hxN])
  let f := centeredWeightedBinCoefficient J ζ μ E w x
  have hfn : ∀ n, ‖f n‖≤2 := centeredWeightedBinCoefficient_norm ζ hζ hμ w hw x
  suffices hall : ∀ T : ℝ, 1≤T →
      (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) f t‖^2) ≤
        17/H+4*canonicalAffineBase C H+
        (4*canonicalAffineSlope C H+32*Real.exp 1*(2:ℝ)^2)*T/N by
    intro T hT
    have hh := hall T hT
    dsimp only [f] at hh
    convert hh using 1; ring
  apply (angularMellin_extend_affine f (by norm_num : (0:ℝ)≤2) hfn
    (add_nonneg (by positivity) (mul_nonneg (by norm_num) hpos.1))
    (mul_nonneg (by norm_num) hpos.2) hN ?_)
  intro T hT hTN
  let S := Set.Ioc (-T) T \ Set.Ioc (-U) U
  have hSm : MeasurableSet S := measurableSet_Ioc.diff measurableSet_Ioc
  have hST : ∀ t∈S, U≤|t| := by
    intro t ht
    by_contra hh
    have ha := abs_lt.mp (lt_of_not_ge hh)
    exact ht.2 ⟨ha.1,ha.2.le⟩
  have he (z : Fin (J-1) → ℂ) (hz : ∀ i, ‖z i‖≤1) :=
    haw x hbound z hz w hw S hSm T (by linarith) hTN Set.sdiff_subset hST
  have hc := angularMellin_centered_energy (Ioc N (2*N))
    (finiteWeightedCoefficient (binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ) E w)
    (finiteWeightedCoefficient (binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) (fun _ => (1:ℂ))) E w)
    hμ (show 0≤T by linarith) (Set.sdiff_subset : S ⊆ Set.Ioc (-T) T)
  rw [←centeredWeightedBinCoefficient_sub ζ μ E w x] at hc
  have hs := angularMellin_frequency_split (Ioc N (2*N)) f (show 0≤T by linarith) hU.le
  have hl := hlo N hNx hxN
  have h1 := he ζ hζ
  have h2 := he (fun _ => 1) (by intro i; simp)
  change (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) f t‖^2) ≤ _
  dsimp only [f,S] at hs ⊢
  linear_combination hs + hc + hl + 2*h1 + 2*h2

end JointDickman

end OAI
