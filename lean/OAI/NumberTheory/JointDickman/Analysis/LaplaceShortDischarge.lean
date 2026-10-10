import OAI.NumberTheory.JointDickman.Analysis.LaplaceBinShort
import OAI.NumberTheory.JointDickman.Counting.PrescribedShortDischarge

namespace OAI

/-! # Application consequences of the proved short-average estimates -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem unit_laplace_short_with_center_proved
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖≤1) (μ : ℂ) (hμ : ‖μ‖≤1)
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
  have hsmall v (_ : v ∈ V) := unit_progressions_short_with_center_proved hKMT hM hJ ζ hζ μ hμ hmean
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
