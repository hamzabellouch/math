import OAI.NumberTheory.Ostmann.QuadraticCenter.HighWeight
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergyMean

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators Topology ComplexConjugate
open Filter

def quadraticHighWeightIndices (S L : ℕ) (u K : ℝ) : Finset ℕ :=
  (Finset.Ico S (2*S)).filter (fun s =>
    Squarefree s ∧ s.Coprime L ∧ Real.exp (K / 200) < u ^ s.primeFactors.card)

theorem sum_weight_mul_residue_le {L : ℕ} [NeZero L] (T : Finset ℕ)
    (weight : ℕ → ℝ) (f : ZMod L → ℝ) (W : ℝ)
    (hf : ∀ a, 0 ≤ f a)
    (hW : ∀ a : ZMod L, (∑ n ∈ T.filter (fun n : ℕ => (n : ZMod L) = a), weight n) ≤ W) :
    (∑ n ∈ T, weight n * f (n : ZMod L)) ≤ W * ∑ a, f a := by
  classical
  rw [← Finset.sum_fiberwise T (fun n : ℕ => (n : ZMod L))
    (fun n => weight n * f (n : ZMod L)), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  calc
    _ = ∑ n ∈ T.filter (fun n : ℕ => (n : ZMod L) = a), weight n * f a := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [(Finset.mem_filter.mp hn).2]
    _ = (∑ n ∈ T.filter (fun n : ℕ => (n : ZMod L) = a), weight n) * f a :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (hW a) (hf a)

theorem quadraticHighWeightIndices_residue {S L : ℕ} [NeZero L]
    (u K : ℝ) (a : ZMod L) :
    (quadraticHighWeightIndices S L u K).filter (fun n : ℕ => (n : ZMod L) = a) =
      highWeightResidueSet S L a.val u K := by
  classical
  have hres (n : ℕ) : ((n : ZMod L) = a) ↔ Nat.ModEq L n a.val := by
    rw [← ZMod.natCast_zmod_val a, ZMod.natCast_eq_natCast_iff]
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (ZMod.val_lt a)]
  ext n
  simp only [quadraticHighWeightIndices, highWeightResidueSet, Finset.mem_filter, hres]
  tauto

theorem high_weight_periodic_l1_eventually :
    ∀ᶠ T : ℝ in atTop, ∀ (S L : ℕ) [NeZero L] (u K : ℝ) (f : ZMod L → ℝ),
      2 * L ^ 2 ≤ S → (S : ℝ) ≤ Real.exp (T ^ 2) →
      1 < u → u ≤ T ^ ((1 : ℝ) / 100000) → T ^ ((3 : ℝ) / 4) ≤ K →
      (∀ a, 0 ≤ f a) → (∑ a, f a) ≤ L →
      (∑ s ∈ quadraticHighWeightIndices S L u K, u ^ s.primeFactors.card * f (s : ZMod L)) ≤
        (S : ℝ) * Real.exp (-10 * K) := by
  filter_upwards [high_weight_residue_mass_eventually] with T hT
  intro S L inst u K f hS hSupper hu huupper hK hf hmean
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_neZero L
  calc
    _ ≤ ((S : ℝ) / L * Real.exp (-10 * K)) * ∑ a, f a := by
      apply sum_weight_mul_residue_le _ _ _ _ hf
      intro a
      rw [quadraticHighWeightIndices_residue]
      exact hT S L a.val u K (Nat.pos_of_neZero L) hS hSupper hu huupper hK
    _ ≤ ((S : ℝ) / L * Real.exp (-10 * K)) * L :=
      mul_le_mul_of_nonneg_left hmean (by positivity)
    _ = _ := by field_simp

theorem high_weight_transform_product_eventually :
    ∀ᶠ T : ℝ in atTop,
    ∀ {ι κ : Type} [Fintype ι] [Fintype κ]
      (p : ι → ℕ) (r : κ → ℕ) [∀ i, NeZero (p i)] [∀ j, NeZero (r j)]
      [NeZero (∏ i, p i)] [NeZero (∏ j, r j)]
      (_hp : ∀ i, (p i).Prime) (_hr : ∀ j, (r j).Prime)
      (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
      (hcor : Pairwise (fun i j => (r i).Coprime (r j)))
      (A : ∀ i, Finset (ZMod (p i))) (B : ∀ j, Finset (ZMod (r j)))
      (c : ZMod (∏ i, p i)) (c' : ZMod (∏ j, r j))
      (S L : ℕ) [NeZero L] (_hd : (∏ i, p i) ∣ L) (_he : (∏ j, r j) ∣ L) (u K : ℝ),
      2 * L ^ 2 ≤ S → (S : ℝ) ≤ Real.exp (T ^ 2) →
      1 < u → u ≤ T ^ ((1 : ℝ) / 100000) → T ^ ((3 : ℝ) / 4) ≤ K →
      (∑ s ∈ quadraticHighWeightIndices S L u K, u ^ s.primeFactors.card *
        ‖centeredProductTransform p hcop A (c * (s : ZMod (∏ i, p i))) *
          conj (centeredProductTransform r hcor B (c' * (s : ZMod (∏ j, r j))))‖) ≤
        (S : ℝ) * Real.exp (-10 * K) := by
  filter_upwards [high_weight_periodic_l1_eventually] with T hT
  intro ι κ instι instκ p r instp instr instD instE hp hr hcop hcor A B c c' S L instL hd he u K
    hS hSupper hu huupper hK
  have h := hT S L u K
    (fun z => ‖centeredProductTransform p hcop A (c * ZMod.castHom hd (ZMod (∏ i, p i)) z) *
      conj (centeredProductTransform r hcor B (c' * ZMod.castHom he (ZMod (∏ j, r j)) z))‖)
    hS hSupper hu huupper hK (fun _ => norm_nonneg _)
    (centered_transform_product_period_l1_le p r hp hr hcop hcor A B c c' hd he)
  simpa only [map_natCast] using h

end Ostmann.QuadraticCenter

end

end OAI
