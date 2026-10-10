import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ShellGridScales
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.CharacterModulation

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace SourcePrimeFactor
open OrdinaryCorrelations OrdinaryDirichletMeanSquare OrdinarySmoothRough Finset Filter

def dyadicCofactorMellin (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Finset ℕ) (M : ℕ) (τ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc M (2*M),
    (OrdinaryArchimedeanTwist.twist (characterModulation f χ) τ n /
      (primeCount P n+1:ℂ)) / (n:ℂ)

def primeMellin (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Finset ℕ) (τ : ℝ) : ℂ :=
  polynomial P (fun p => characterModulation f χ p/(p:ℂ)) (fun p => Real.log p) τ

lemma prime_coefficient_norm {f : ℕ → ℂ} (hf : OneBounded f)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (p : ℕ) :
    ‖characterModulation f χ p/(p:ℂ)‖ ≤ (p:ℝ)⁻¹ := by
  rw [norm_div,Complex.norm_natCast]
  simpa only [one_div] using
    div_le_div_of_nonneg_right (characterModulation_bound hf χ p) (Nat.cast_nonneg p)

lemma norm_primeMellin {f : ℕ → ℂ} (hf : OneBounded f)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (P : Finset ℕ) (τ : ℝ) :
    ‖primeMellin f χ P τ‖ ≤ ∑ p ∈ P, (p:ℝ)⁻¹ := by
  unfold primeMellin polynomial
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro p hp
  rw [norm_mul,norm_phase,mul_one]
  exact prime_coefficient_norm hf χ p

lemma dyadicCofactorMellin_eq (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Finset ℕ) (H : ℕ) (t : ℝ) :
    dyadicCofactorMellin f χ P (2*H) t =
      ∑ n ∈ Ioc (2*H) (4*H), cofactorTerm (characterModulation f χ) P n t := by
  unfold dyadicCofactorMellin
  rw [show 2*(2*H)=4*H by omega]
  apply sum_congr rfl
  intro n hn
  unfold OrdinaryArchimedeanTwist.twist cofactorTerm OrdinaryLogIntegral.logPhase
  ring

theorem terminal_cofactor_sparse {f : ℕ → ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℕ, 0 < r ∧ ∀ᶠ H : ℕ in atTop, ∀ T : Finset ℝ,
      (T : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|) →
      (∀ t∈T, |t| ≤ (H:ℝ)) → T.card^r ≤ H →
      (∑ t ∈ T, ‖dyadicCofactorMellin f χ P (2*H) t‖^2) < ε := by
  obtain ⟨d,r,hd,hr,hall⟩ := OrdinarySparseShell.sparse_cofactor_all_lengths
    (characterModulation_bound hf χ) (characterModulation_multiplicative hm χ)
    (characterModulation_nonpretentious hNP hq χ) hε
  refine ⟨r,hr,?_⟩
  have hprimes : ∀ᶠ H : ℕ in atTop, ∀ p∈P, p^r ≤ H^d := by
    apply (eventually_all_finset P).mpr
    intro p hp
    filter_upwards [eventually_ge_atTop (p^r)] with H hH
    exact hH.trans (Nat.le_self_pow (by omega) H)
  filter_upwards [hall,hprimes] with H hH hbound
  intro T hsep hheight hcard
  have hh := hH P (fun p hp => ⟨hP p hp,hbound p hp⟩) T hsep hheight hcard
  simpa only [cofactorEnergy, ←dyadicCofactorMellin_eq] using hh

theorem terminal_product_sparse {f : ℕ → ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℕ, 0 < r ∧ ∀ᶠ H : ℕ in atTop, ∀ T : Finset ℝ,
      (T : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|) →
      (∀ t∈T, |t| ≤ (H:ℝ)) → T.card^r ≤ H →
      (∑ t ∈ T, ‖primeMellin f χ P t * dyadicCofactorMellin f χ P (2*H) t‖^2) < ε := by
  let L : ℝ := ∑ p ∈ P, (p:ℝ)⁻¹
  have hL : 0 ≤ L := sum_nonneg (fun p hp => inv_nonneg.mpr (Nat.cast_nonneg p))
  have hden : 0 < 1+L^2 := by positivity
  obtain ⟨r,hr,hevent⟩ := terminal_cofactor_sparse hf hm hNP hq χ P hP
    (show 0 < ε/(1+L^2) by positivity)
  refine ⟨r,hr,?_⟩
  filter_upwards [hevent] with H hH
  intro T hsep hheight hcard
  have hh := hH T hsep hheight hcard
  calc
    _ ≤ (1+L^2)*(∑ t ∈ T, ‖dyadicCofactorMellin f χ P (2*H) t‖^2) := by
      rw [mul_sum]
      apply sum_le_sum
      intro t ht
      rw [norm_mul,mul_pow]
      exact mul_le_mul_of_nonneg_right
        ((pow_le_pow_left₀ (norm_nonneg _) (norm_primeMellin hf χ P t) 2).trans (by dsimp [L]; linarith))
        (sq_nonneg _)
    _ < (1+L^2)*(ε/(1+L^2)) := mul_lt_mul_of_pos_left hh hden
    _ = ε := by field_simp

end SourcePrimeFactor

end

end OAI
