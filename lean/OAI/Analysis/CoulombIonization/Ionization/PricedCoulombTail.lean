import Mathlib
import OAI.Analysis.CoulombIonization.Localization.ObservedAnnularCountBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.CoulombTailNumerics

namespace OAI

open MeasureTheory Filter Set
open scoped BigOperators
noncomputable section
namespace CoulombAtom
open CoulombObservation CoulombBarrier

lemma truncated_tail_moment_bound {N : ℕ} {psi : FormVector N} (hpsi : SobolevVector psi)
    {h D C : ℝ} (hh : 0 < h) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hcounts : ∀ u : ℝ, 0 < u → rawAnnularMoment psi u (4*u) ≤ C*(annularOffsetMass D u)^2)
    (K : ℕ) : rawWeightedMoment psi (truncatedTailWeight h K) ≤ 12*C*(1/h^8+1/h^2+D/h) := by
  let H := 1/h^8+1/h^2+D/h
  have hH : 0 ≤ H := by dsimp [H]; positivity
  let : IsFiniteMeasure (formRawLaw psi) := formRawLaw_finite hpsi
  let B := fun k (x : Configuration N) => rawAnnularCount (tailRadius h k) (4*tailRadius h k) x/tailRadius h k
  have hi (k : ℕ) : Integrable (fun x : Configuration N => (B k x)^2/tailWeight k) (formRawLaw psi) := by
    simp only [B,div_pow]
    exact ((rawAnnularCount_sq_integrable _ _ _).div_const _).div_const _
  have he (k : ℕ) : (∫ x, (B k x)^2/tailWeight k ∂formRawLaw psi) ≤ 3*C*tailWeight k*H := by
    simp only [B,div_pow,integral_div,←rawAnnularMoment_eq_integral hpsi]
    have hu := tailRadius_pos hh k
    have hw := tailWeight_pos k
    calc
      _ ≤ (C*(annularOffsetMass D (tailRadius h k))^2)/(tailRadius h k)^2/tailWeight k :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (hcounts _ hu) (sq_nonneg _)) hw.le
      _ ≤ (C*(3*(1/(tailRadius h k)^6+1+D*tailRadius h k)))/(tailRadius h k)^2/tailWeight k :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (annularOffsetMass_sq_le hD hu) hC) (sq_nonneg _)) hw.le
      _ = 3*C*((1/(tailRadius h k)^6+1+D*tailRadius h k)/((tailRadius h k)^2*tailWeight k)) := by ring
      _ ≤ 3*C*(tailWeight k*H) := mul_le_mul_of_nonneg_left (tail_annular_scale hD hh k) (by positivity)
      _ = _ := by ring
  have hhCount (x : Configuration N) := pow_le_pow_left₀
    (rawWeightedCount_nonneg (truncatedTailWeight_nonneg h K) x) (raw_truncated_tail_le_shells hh K x) 2
  rw [rawWeightedMoment_eq_integral hpsi (truncatedTailWeight_measurable h K)
    (truncatedTailWeight_nonneg h K) (fun a => (truncatedTailWeight_le h K a).trans (coulombTailWeight_le hh a))]
  calc
    _ ≤ ∫ x, 2*∑ k ∈ Finset.range K, (B k x)^2/tailWeight k ∂formRawLaw psi :=
      integral_mono (rawWeightedCount_sq_integrable (truncatedTailWeight_measurable h K)
        (truncatedTailWeight_nonneg h K) (fun a => (truncatedTailWeight_le h K a).trans (coulombTailWeight_le hh a)) _)
        ((integrable_finsetSum _ (fun k _ => hi k)).const_mul 2)
        (fun x => (hhCount x).trans (finite_tail_cauchy K (fun k => B k x)))
    _ = 2*∑ k ∈ Finset.range K, (∫ x, (B k x)^2/tailWeight k ∂formRawLaw psi) := by
      rw [integral_const_mul,integral_finsetSum _ (fun k _ => hi k)]
    _ ≤ 2*∑ k ∈ Finset.range K, 3*C*tailWeight k*H := by gcongr with k hk; exact he k
    _ = 6*C*H*(∑ k ∈ Finset.range K, tailWeight k) := by
      rw [Finset.mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ 6*C*H*2 := mul_le_mul_of_nonneg_left (sum_tailWeight_le K) (by positivity)
    _ = _ := by dsimp [H]; ring

theorem coulomb_tail_moment_bound {N : ℕ} {psi : FormVector N} (hpsi : SobolevVector psi)
    {h D C : ℝ} (hh : 0 < h) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hcounts : ∀ u : ℝ, 0 < u → rawAnnularMoment psi u (4*u) ≤ C*(annularOffsetMass D u)^2) :
    rawWeightedMoment psi (coulombTailWeight h) ≤ 12*C*(1/h^8+1/h^2+D/h) := by
  exact le_of_tendsto (truncated_tail_moment_tendsto hpsi hh)
    (Filter.Eventually.of_forall (fun K => truncated_tail_moment_bound hpsi hh hD hC hcounts K))

theorem exists_priced_coulomb_tail_constant :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Z lam : ℝ) (N : ℕ) (psi : FormVector N), SobolevFermion psi →
      formMass psi = 1 → 0 ≤ Z → 0 < lam → ∀ (D h : ℝ), 0 ≤ D → 0 < h →
      max (corePriceExcess Z lam psi) 0 ≤ D →
      rawWeightedMoment psi (coulombTailWeight h) ≤ C*(1/h^8+1/h^2+D/h) := by
  obtain ⟨C,hC,hb⟩ := exists_priced_annular_count_constant (beta := 4) (by norm_num : (0:ℝ)<1)
  refine ⟨12*C,by linarith,?_⟩
  intro Z lam N psi hpsi hm hZ hlam D h hD hh he
  exact coulomb_tail_moment_bound hpsi.sobolevVector hh hD (zero_le_one.trans hC)
    (fun u hu => by simpa only [one_mul] using hb Z lam N psi hpsi hm hZ hlam D u hD hu he)

end CoulombAtom

end

end OAI
