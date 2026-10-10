import OAI.NumberTheory.JointDickman.Counting.PrescribedCenterShort
import OAI.NumberTheory.JointDickman.Counting.PrincipalBinShortDischarge
import OAI.NumberTheory.JointDickman.Counting.NonprincipalShortDischarge

namespace OAI

/-! # Application consequences of the proved short-average estimates -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem all_characters_short_with_center_proved
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖≤1) (μ : ℂ) (hμ : ‖μ‖≤1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    (P : ℕ → Finset ℕ) (hP : ∀ B p, p ∈ P B → p.Prime)
    (t : ℕ → ℕ → ℝ) (ht : ∀ B p, p ∈ P B → 0 ≤ t B p ∧ t B p ≤ 1)
    {q : ℕ} [NeZero q] (A scale H : ℕ → ℝ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hH : Tendsto H atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      ∀ χ : DirichletCharacter ℂ q,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖twistedWeightedBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
          (finitePrimeWeight (P B) (t B)) χ (H B) z‖^2) < ε := by
  have hp B p (h : p ∈ P B ∪ q.primeFactors) : p.Prime := by
    rcases mem_union.mp h with h | h
    · exact hP B p h
    · exact (Nat.mem_primeFactors.mp h).1
  have hb B p (h : p ∈ P B ∪ q.primeFactors) :
      0 ≤ (if p ∈ q.primeFactors then 0 else t B p) ∧ (if p ∈ q.primeFactors then 0 else t B p) ≤ (1 : ℝ) := by
    by_cases hh : p ∈ q.primeFactors
    · simp [hh]
    · simpa only [ite_eq_right hh] using ht B p ((mem_union.mp h).resolve_right hh)
  have hprincipal := finitePrimeWeight_short_with_center_proved hJ ζ hζ μ hμ hmean
    (fun B => P B ∪ q.primeFactors) hp (fun B p => if p ∈ q.primeFactors then 0 else t B p) hb
    A H scale hA hH hscale
  intro ε hε
  have hc (χ : DirichletCharacter ℂ q) : ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖twistedWeightedBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
          (finitePrimeWeight (P B) (t B)) χ (H B) z‖^2) < ε := by
    by_cases he : χ = 1
    · subst χ
      simpa only [principal_twistedWeightedBinAverage,coprimePrimeWeight] using hprincipal ε hε
    · exact nonprincipal_weightedBinAverage_short_proved hKMT hM J hJ
        (fun i : Fin (J-1) => i.val+1) (fun _ => by omega) ζ μ P hP t ht χ he
        A scale H hA hscale hH ε hε
  filter_upwards [eventually_all.mpr hc] with B hb
  exact eventually_all.mpr hb

theorem unit_progressions_short_with_center_proved
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖≤1) (μ : ℂ) (hμ : ‖μ‖≤1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    (P : ℕ → Finset ℕ) (hP : ∀ B p, p ∈ P B → p.Prime)
    (t : ℕ → ℕ → ℝ) (ht : ∀ B p, p ∈ P B → 0 ≤ t B p ∧ t B p ≤ 1)
    {q : ℕ} [NeZero q] (A scale H : ℕ → ℝ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hH : Tendsto H atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      ∀ r : (ZMod q)ˣ,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖unitProgressionBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
          (finitePrimeWeight (P B) (t B)) r (H B) z‖^2) < ε := by
  have hb := all_characters_short_with_center_proved hKMT hM hJ ζ hζ μ hμ hmean
    P hP t ht (q := q) A scale H hA hscale hH
  intro ε hε
  filter_upwards [hb (ε/2) (half_pos hε),hH.eventually_gt_atTop 0] with B hb hHB
  have hX : Tendsto (fun n => A B*scale n) atTop atTop := hscale.const_mul_atTop (hA B)
  filter_upwards [hb,hX.eventually_gt_atTop 0] with n hb hXn
  intro r
  have he := unitProgressionBinAverage_energy_le
    (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
    (finitePrimeWeight (P B) (t B)) r hHB hXn
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hc : (Fintype.card (DirichletCharacter ℂ q) : ℝ) = q.totient := by
    rw [← Nat.card_eq_fintype_card,DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  have hs := sum_le_sum (s := univ) (fun χ _ => (hb χ).le)
  have hh := he.trans (mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 1/(q.totient : ℝ)))
  simp only [sum_const,card_univ,nsmul_eq_mul,hc] at hh
  have hid : (1/(q.totient : ℝ))*((q.totient : ℝ)*(ε/2)) = ε/2 := by field_simp
  rw [hid] at hh
  exact hh.trans_lt (by linarith)

end JointDickman

end OAI
