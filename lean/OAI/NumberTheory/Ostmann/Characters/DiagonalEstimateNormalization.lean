import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateMass
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateNormalizationCounts
import OAI.NumberTheory.Ostmann.Characters.PivotProductNormalizationCells
import OAI.NumberTheory.Ostmann.Characters.SourceTemplateShells

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.DiagonalEstimate
open Template HigherBiasSource HigherBiasSource.SourceTemplate HigherBiasSourceWord Preliminaries
attribute [local instance] Classical.propDecidable

def actualCopiedShells {k Q : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (bulk top E : Finset (PrimeUpTo Q)) :
    CopiedConstituent (schedule k j) j (sourceWidth cfg m) → Finset (PrimeUpTo Q) :=
  fun i => scheduledPrimeShells k (sourceWidth cfg m)
    (configurationPrimeShells cfg m bulk top E) j
    (copiedConstituentOld (schedule k j) j (sourceWidth cfg m) i)

theorem copied_word_normalization {k Q : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (bulk top E : Finset (PrimeUpTo Q))
    (i : {i : (schedule k j).Slot // (schedule k j).IsCopied j i})
    (hi : (schedule k j).role i.val = .word) :
    (∏ a : Fin (sourceWidth cfg m ((schedule k j).role i.val)),
      (primeShellMass (actualCopiedShells cfg m j bulk top E ⟨i,a⟩))⁻¹) =
        ((primeShellMass bulk)⁻¹)^m * (primeShellMass top)⁻¹ := by
  have hw : sourceWidth cfg m ((schedule k j).role i.val) = m+1 := by rw [hi]; rfl
  calc
    _ = ∏ a : Fin (sourceWidth cfg m ((schedule k j).role i.val)),
        (primeShellMass (roleShells bulk top m (finCongr hw a)))⁻¹ := by
      apply Finset.prod_congr rfl
      intro a ha
      exact congrArg (fun F => (primeShellMass F)⁻¹)
        (scheduledPrimeShells_word cfg m j bulk top E i.val hi a)
    _ = ∏ a : Fin (m+1), (primeShellMass (roleShells bulk top m a))⁻¹ :=
      Equiv.prod_comp (finCongr hw) (fun a => (primeShellMass (roleShells bulk top m a))⁻¹)
    _ = _ := by
      unfold roleShells
      rw [Fin.prod_univ_add]
      simp

lemma exp_word_cost {b t : ℝ} (hb : 0 < b) (ht : 0 < t) (m : ℕ) :
    Real.exp (-(m:ℝ)*Real.log b-Real.log t) = b⁻¹^m*t⁻¹ := by
  rw [sub_eq_add_neg,Real.exp_add]
  have he : -(m:ℝ)*Real.log b = (m:ℝ)*(-Real.log b) := by ring
  rw [he,Real.exp_nat_mul]
  simp only [Real.exp_neg,Real.exp_log hb,Real.exp_log ht]

theorem copied_atom_normalization_le {k Q : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (bulk top E : Finset (PrimeUpTo Q)) {ρ c₀ H L : ℝ}
    (hρL : 0 < ρ*L) (hc₀ : 0 < c₀)
    (hbulk : ρ*L ≤ primeShellMass bulk) (htop : c₀ ≤ primeShellMass top)
    (hcell : ∀ a, Real.exp (-H) ≤ primeShellMass (configurationCells E cfg a))
    (i : {i : (schedule k j).Slot // (schedule k j).IsCopied j i}) :
    (∏ a : Fin (sourceWidth cfg m ((schedule k j).role i.val)),
      (primeShellMass (actualCopiedShells cfg m j bulk top E ⟨i,a⟩))⁻¹) ≤
      Real.exp (if (schedule k j).role i.val = .word then
        -(m:ℝ)*Real.log (ρ*L)-Real.log c₀
        else H*(sourceWidth cfg m ((schedule k j).role i.val):ℝ)) := by
  by_cases hi : (schedule k j).role i.val = .word
  · rw [ite_eq_left hi,copied_word_normalization cfg m j bulk top E i hi,
      exp_word_cost hρL hc₀]
    exact mul_le_mul
      (pow_le_pow_left₀ (inv_nonneg.mpr (hρL.trans_le hbulk).le) (inv_anti₀ hρL hbulk) m)
      (inv_anti₀ hc₀ htop) (inv_nonneg.mpr (hc₀.trans_le htop).le) (by positivity)
  · rw [ite_eq_right hi]
    have hz (a : Fin (sourceWidth cfg m ((schedule k j).role i.val))) :
        Real.exp (-H) ≤ primeShellMass (actualCopiedShells cfg m j bulk top E ⟨i,a⟩) :=
      scheduledPrimeShells_nonword_mass cfg m j bulk top E _ hcell ⟨i.val,a⟩ hi
    have hh := PivotProductNormalization.normalization_le_exp
      (fun a => actualCopiedShells cfg m j bulk top E ⟨i,a⟩) (fun _ => H) hz
    simpa only [PivotProductFibers.normalization,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,mul_comm] using hh

theorem copied_cost_sum {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) (W H : ℝ) :
    (∑ i : {i : (schedule k j).Slot // (schedule k j).IsCopied j i},
      if (schedule k j).role i.val = .word then W
      else H*(sourceWidth cfg m ((schedule k j).role i.val):ℝ)) =
    (2^j:ℕ)*W + H*(∑ i : {i : (schedule k j).Slot // (schedule k j).IsCopied j i},
      nonwordWeight cfg m ((schedule k j).role i.val) : ℕ) := by
  let I := {i : (schedule k j).Slot // (schedule k j).IsCopied j i}
  have hc : Fintype.card {i : I // (schedule k j).role i.val = .word} = 2^j :=
    (Fintype.card_congr (copiedWordEquiv k j)).trans (active_word_card k j)
  have hs : (∑ i : I, if (schedule k j).role i.val = .word then (1:ℕ) else 0) = 2^j := by
    have hh := sum_subtype_nat_eq_ite (fun i : I => (schedule k j).role i.val = .word) (fun _ => 1)
    have hh' : (∑ i : I, if (schedule k j).role i.val = .word then (1:ℕ) else 0) =
        Fintype.card {i : I // (schedule k j).role i.val = .word} := by simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using hh.symm
    exact hh'.trans hc
  have hsR : (∑ i : I, if (schedule k j).role i.val = .word then (1:ℝ) else 0) = (2^j:ℕ) := by
    exact_mod_cast hs
  calc
    _ = (∑ i : I, (if (schedule k j).role i.val = .word then (1:ℝ) else 0)*W) +
        ∑ i : I, H*(nonwordWeight cfg m ((schedule k j).role i.val):ℝ) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : (schedule k j).role i.val = .word <;> simp [h,nonwordWeight]
    _ = _ := by rw [← Finset.sum_mul,hsR,← Finset.mul_sum,Nat.cast_sum]

theorem actualCopiedNormalization_le_exp {k Q : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (bulk top E : Finset (PrimeUpTo Q)) {ρ c₀ H L : ℝ}
    (hρL : 0 < ρ*L) (hc₀ : 0 < c₀) (hH : 0 ≤ H)
    (hbulk : ρ*L ≤ primeShellMass bulk) (htop : c₀ ≤ primeShellMass top)
    (hcell : ∀ a, Real.exp (-H) ≤ primeShellMass (configurationCells E cfg a)) :
    copiedNormalization (actualCopiedShells cfg m j bulk top E) ≤
      Real.exp ((2^j:ℕ)*(-(m:ℝ)*Real.log (ρ*L)-Real.log c₀) +
        H*((2^j:ℕ)*(2*configCellCount cfg):ℕ)) := by
  classical
  change (∏ i : CopiedConstituent (schedule k j) j (sourceWidth cfg m),
    (primeShellMass (actualCopiedShells cfg m j bulk top E i))⁻¹) ≤ _
  rw [Fintype.prod_sigma]
  calc
    _ ≤ ∏ i : {i : (schedule k j).Slot // (schedule k j).IsCopied j i},
        Real.exp (if (schedule k j).role i.val = .word then
          -(m:ℝ)*Real.log (ρ*L)-Real.log c₀
          else H*(sourceWidth cfg m ((schedule k j).role i.val):ℝ)) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        apply Finset.prod_nonneg
        intro a ha
        unfold primeShellMass
        positivity
      · intro i hi
        exact copied_atom_normalization_le cfg m j bulk top E hρL hc₀ hbulk htop hcell i
    _ = Real.exp ((2^j:ℕ)*(-(m:ℝ)*Real.log (ρ*L)-Real.log c₀) +
        H*(∑ i : {i : (schedule k j).Slot // (schedule k j).IsCopied j i},
          nonwordWeight cfg m ((schedule k j).role i.val):ℕ)) := by
      rw [← Real.exp_sum,copied_cost_sum]
    _ ≤ _ := by
      have hh : ((∑ i : {i : (schedule k j).Slot // (schedule k j).IsCopied j i},
          nonwordWeight cfg m ((schedule k j).role i.val):ℕ):ℝ) ≤
          ((2^j * (2*configCellCount cfg):ℕ):ℝ) := by
        exact_mod_cast copied_nonword_weight_le cfg m j
      exact Real.exp_le_exp.mpr (add_le_add le_rfl (mul_le_mul_of_nonneg_left hh hH))

end Ostmann.Characters.DiagonalEstimate

end

end OAI
