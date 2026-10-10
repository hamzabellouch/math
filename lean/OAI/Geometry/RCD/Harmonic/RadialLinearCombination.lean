import OAI.Geometry.RCD.Harmonic.RadialDerivativeError
import OAI.Geometry.RCD.Harmonic.ColumnRepresentatives

namespace OAI

/-! # Radial pairings and harmonic corrections in every constant direction -/

open Set MeasureTheory
open scoped NNReal ENNReal BigOperators InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

private theorem gamma_sum_right {ι : Type*} (s : Finset ι)
    (u : ι → SobolevSpace μ hQ) (g : SobolevSpace μ hQ) :
    localGamma μ hQ g (∑ i ∈ s, u i) =ᵐ[μ]
      fun x => ∑ i ∈ s, localGamma μ hQ g (u i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, zero_smul, zero_mul] using
      localGamma_smul_right μ hQ 0 g (0 : SobolevSpace μ hQ)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [localGamma_add_right μ hQ g (u i) (∑ j ∈ s, u j), ih] with x hx hh
    rw [hx, hh]

/-- The radial derivative is linear in the actual coordinate direction. -/
theorem localGamma_column_right {n : ℕ} (q : SobolevSpace μ hQ)
    (u : Fin n → SobolevSpace μ hQ) (b : Euclidean n) :
    localGamma μ hQ q (sobolevColumnMap μ hQ u b) =ᵐ[μ]
      fun x => ∑ j, b j * localGamma μ hQ q (u j) x := by
  have hs := gamma_sum_right μ hQ Finset.univ (fun j => b j • u j) q
  have hc := (Filter.eventually_all_finset (Finset.univ : Finset (Fin n))).mpr
    (fun j _ => localGamma_smul_right μ hQ (b j) q (u j))
  filter_upwards [hs, hc] with x hx hc
  rw [sobolevColumnMap_apply]
  rw [hx]
  exact Finset.sum_congr rfl fun j hj => hc j hj

omit [BorelSpace X] [ProperSpace X] in
private theorem column_value {n : ℕ} (u : Fin n → SobolevSpace μ hQ) (b : Euclidean n) :
    SobolevSpace.toLp μ hQ (sobolevColumnMap μ hQ u b) =ᵐ[μ]
      fun x => ∑ j, b j * SobolevSpace.toLp μ hQ (u j) x := by
  have hrep := sobolevColumnMap_representative μ hQ u Set.univ
    (fun x => WithLp.toLp 2 (fun j => SobolevSpace.toLp μ hQ (u j) x))
    (fun _ => Filter.Eventually.of_forall fun _ => rfl) b
  rw [Measure.restrict_univ] at hrep
  simpa only [PiLp.inner_apply, Real.inner_apply, mul_comm] using hrep

/-- Componentwise harmonic corrections give one correction in every
constant direction, with the finite-dimensional Cauchy--Schwarz loss. -/
theorem radial_linear_harmonic_correction {n : ℕ} {Ω : Set X}
    (q : SobolevSpace μ hQ) (u h : Fin n → SobolevSpace μ hQ)
    (hh : ∀ j, IsSobolevHarmonicOn μ hQ Ω (h j))
    (hm : ∀ j, MemLp (fun x => localGamma μ hQ q (u j) x -
      SobolevSpace.toLp μ hQ (h j) x) 2 (μ.restrict Ω))
    {E : ℝ}
    (he : ∀ j, (∫ x in Ω, (localGamma μ hQ q (u j) x -
      SobolevSpace.toLp μ hQ (h j) x) ^ 2 ∂μ) ≤ E)
    (b : Euclidean n) :
    IsSobolevHarmonicOn μ hQ Ω (sobolevColumnMap μ hQ h b) ∧
    (∫ x in Ω, (localGamma μ hQ q (sobolevColumnMap μ hQ u b) x -
      SobolevSpace.toLp μ hQ (sobolevColumnMap μ hQ h b) x) ^ 2 ∂μ) ≤
        (n : ℝ) * E * ‖b‖ ^ 2 := by
  refine ⟨IsSobolevHarmonicOn.linearCombination μ hQ hh b, ?_⟩
  let e : Fin n → X → ℝ := fun j x => localGamma μ hQ q (u j) x - SobolevSpace.toLp μ hQ (h j) x
  have hpoint : (fun x => localGamma μ hQ q (sobolevColumnMap μ hQ u b) x -
      SobolevSpace.toLp μ hQ (sobolevColumnMap μ hQ h b) x) =ᵐ[μ.restrict Ω]
      fun x => ∑ j, b j * e j x := by
    filter_upwards [ae_restrict_of_ae (localGamma_column_right μ hQ q u b),
      ae_restrict_of_ae (column_value μ hQ h b)] with x hx hy
    rw [hx, hy]
    simp only [e, mul_sub, Finset.sum_sub_distrib]
  have hsum := memLp_finsetSum Finset.univ (fun j _ => (hm j).const_mul (b j))
  have hbound : (∫ x in Ω, (∑ j, b j * e j x) ^ 2 ∂μ) ≤
      ‖b‖ ^ 2 * ∑ j, ∫ x in Ω, (e j x) ^ 2 ∂μ := by
    have hcs := integral_mono_ae hsum.integrable_sq
      ((integrable_finsetSum Finset.univ (fun j _ => (hm j).integrable_sq)).const_mul (‖b‖ ^ 2))
      (Filter.Eventually.of_forall fun x => by
        simpa only [← EuclideanSpace.real_norm_sq_eq] using
          Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => b j) (fun j => e j x))
    rw [integral_const_mul, integral_finsetSum Finset.univ (fun j _ => (hm j).integrable_sq)] at hcs
    exact hcs
  have hp2 : (fun x => (localGamma μ hQ q (sobolevColumnMap μ hQ u b) x -
      SobolevSpace.toLp μ hQ (sobolevColumnMap μ hQ h b) x) ^ 2) =ᵐ[μ.restrict Ω]
      fun x => (∑ j, b j * e j x) ^ 2 := by
    filter_upwards [hpoint] with x hx
    rw [hx]
  rw [integral_congr_ae hp2]
  apply hbound.trans
  have he' := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => he j)
  have ht := mul_le_mul_of_nonneg_left he' (sq_nonneg ‖b‖)
  calc
    _ ≤ ‖b‖ ^ 2 * ((n : ℝ) * E) := by
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using ht
    _ = _ := by ring

end RegularPointCoordinates

end

end OAI
