import OAI.NumberTheory.JointDickman.Arithmetic.PrimeFeatureShortError
import OAI.NumberTheory.JointDickman.Counting.PrescribedCenterShort

namespace OAI

/-! # Finite Laplace combinations have centered short averages -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem measurable_unitProgressionBinAverage {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} (r : (ZMod q)ˣ) (H : ℝ) :
    Measurable (unitProgressionBinAverage E ζ μ w r H) := by
  let f : ArithmeticFunction ℂ := ⟨fun n => if (n : ZMod q) = r then
    (binLabel E ζ n-μ)*(w n : ℂ) else 0,by split_ifs <;> simp⟩
  exact measurable_complexShortAverage f H

theorem unit_laplace_combination {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (Q : Finset ℕ)
    (B : ℝ) (V : Finset ℕ) (a : ℕ → ℝ) {q : ℕ} (r : (ZMod q)ˣ) (H z : ℝ) :
    unitProgressionBinAverage E ζ μ
      (primeSiteWeight Q (fun x => ∑ v ∈ V, a v*primeLaplaceFeature Q B v x)) r H z =
    ∑ v ∈ V, (a v : ℂ)*unitProgressionBinAverage E ζ μ
      (finitePrimeWeight Q (fun p => (1+(p : ℝ)^(-(v : ℝ)/B))/2)) r H z := by
  unfold unitProgressionBinAverage
  simp only [primeSiteWeight_laplace,Complex.ofReal_sum,Complex.ofReal_mul,← mul_div_assoc]
  rw [← sum_div]
  congr 1
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  by_cases hk : (k : ZMod q) = r
  · simp only [hk,ite_true]
    apply sum_congr rfl
    intro v _
    ring
  · simp [hk]

theorem finite_complex_sum_energy {ι : Type*} (V : Finset ι) (a : ι → ℂ)
    (g : ι → ℝ → ℂ) {X : ℝ} (hX : 0 < X)
    (hg : ∀ v ∈ V, IntervalIntegrable (fun z => ‖g v z‖^2) volume X (2*X))
    (hgm : ∀ v ∈ V, AEStronglyMeasurable (g v) (volume.restrict (Set.uIoc X (2*X)))) :
    (1/X)*(∫ z in X..2*X, ‖∑ v ∈ V, a v*g v z‖^2) ≤
      (∑ v ∈ V, ‖a v‖^2)*∑ v ∈ V, (1/X)*(∫ z in X..2*X, ‖g v z‖^2) := by
  have hK : 0 ≤ ∑ v ∈ V, ‖a v‖^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hb z : ‖∑ v ∈ V, a v*g v z‖^2 ≤
      (∑ v ∈ V, ‖a v‖^2)*(∑ v ∈ V, ‖g v z‖^2) := by
    have hn : ‖∑ v ∈ V, a v*g v z‖ ≤ ∑ v ∈ V, ‖a v‖*‖g v z‖ := by
      simpa only [norm_mul] using norm_sum_le V (fun v => a v*g v z)
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
      (sum_mul_sq_le_sq_mul_sq V (fun v => ‖a v‖) (fun v => ‖g v z‖))
  have hi : IntervalIntegrable (fun z => (∑ v ∈ V, ‖a v‖^2)*∑ v ∈ V, ‖g v z‖^2)
      volume X (2*X) := by
    simpa only [Finset.sum_apply] using (IntervalIntegrable.sum V hg).const_mul (∑ v ∈ V, ‖a v‖^2)
  have hs : IntervalIntegrable (fun z => ‖∑ v ∈ V, a v*g v z‖^2) volume X (2*X) := by
    apply hi.mono_fun'
    · convert ((Finset.aestronglyMeasurable_sum V (fun v hv => (hgm v hv).const_mul (a v))).norm.pow 2) using 1
      ext z
      simp only [Pi.pow_apply,Finset.sum_apply]
    · exact Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs,abs_pow,abs_norm] using hb z)
  have he := intervalIntegral.integral_mono (by linarith : X ≤ 2*X) hs hi hb
  have hh := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 1/X)
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_finsetSum hg] at hh
  simpa only [mul_sum,mul_assoc,mul_left_comm (1/X)] using hh


theorem unit_laplace_short_with_center
    (hMR : RealShortIntervalInput) (hMRT : ComplexShortIntervalInput)
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (μ : ℂ)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    (Q : ℕ → Finset ℕ) (hQ : ∀ B p, p ∈ Q B → p.Prime)
    (V : Finset ℕ) (a : ℕ → ℝ)
    {q : ℕ} [NeZero q] (A scale H : ℕ → ℝ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hH : Tendsto H atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop, ∀ r : (ZMod q)ˣ,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖unitProgressionBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
          (primeSiteWeight (Q B) (fun x => ∑ v ∈ V, a v*primeLaplaceFeature (Q B) B v x))
          r (H B) z‖^2) < ε := by
  intro ε hε
  let K := ∑ v ∈ V, |a v|^2
  have hK : 0 ≤ K := sum_nonneg (fun _ _ => sq_nonneg _)
  let δ := ε/(K*(V.card : ℝ)+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hsmall v (_ : v ∈ V) := unit_progressions_short_with_center hMR hMRT hKMT hM hJ ζ μ hmean
    Q hQ (fun B p => (1+(p : ℝ)^(-(v : ℝ)/(B : ℝ)))/2)
    (fun B p hp => primeLaplaceWeight_bounds (hQ B) (Nat.cast_nonneg B) (Nat.cast_nonneg v) p hp)
    (q := q) A scale H hA hscale hH δ hδ
  filter_upwards [(eventually_all_finset V).mpr hsmall,hH.eventually_gt_atTop 0] with B hB hHB
  have hX := hscale.const_mul_atTop (hA B)
  filter_upwards [(eventually_all_finset V).mpr hB,hX.eventually_gt_atTop 0] with n hn hXn
  intro r
  let E := fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)
  let w := fun v => finitePrimeWeight (Q B) (fun p => (1+(p : ℝ)^(-(v : ℝ)/(B : ℝ)))/2)
  have he := finite_complex_sum_energy V (fun v => (a v : ℂ))
    (fun v z => unitProgressionBinAverage E ζ μ (w v) r (H B) z) hXn
    (fun v _ => unitProgressionBinAverage_sq_integrable E ζ μ (w v) r hHB _ _)
    (fun v _ => (measurable_unitProgressionBinAverage E ζ μ (w v) r (H B)).aestronglyMeasurable)
  simp only [Complex.norm_real,Real.norm_eq_abs] at he
  have hs := sum_le_sum (s := V) (fun v hv => (hn v hv r).le)
  have hb := he.trans (mul_le_mul_of_nonneg_left hs hK)
  simp only [sum_const,nsmul_eq_mul] at hb
  have hδid : (K*(V.card : ℝ)+1)*δ = ε := by dsimp [δ]; field_simp
  have hfinal : K*((V.card : ℝ)*δ) < ε := by nlinarith
  simp_rw [unit_laplace_combination]
  exact hb.trans_lt hfinal

end JointDickman

end OAI
