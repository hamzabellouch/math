import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleScaleGeometry
import OAI.NumberTheory.CubicMoment.Estimates.OrdinaryGroupRange

namespace OAI

/-! The compactness grouping is converted to fixed smooth-box lengths.
All constant support ratios are retained before the eventual power gap
is used. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma largePrimeTuplePiece_log_pos {i j N : ℕ} {ℓ : ℤ} {ξ : ℝ}
    {Ct : ℕ} {H X : ℝ} (hX : 1 ≤ X) (hlog : 200 ≤ Real.log X)
    (k : (Fin i ⊕ Fin j) → Fin N)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hne : largePrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0) :
    0 < norm (largePrimeTupleProduct q) ∧ 0 < Real.log (norm (largePrimeTupleProduct q)) := by
  have hXp := zero_lt_one.trans_le hX
  have hn := (largePrimeTupleTerm_product_range hXp (mul_ne_zero_iff.mp hne).1).1
  change X/2 ≤ norm (largePrimeTupleProduct q) at hn
  have hnp := (by positivity : (0:ℝ) < X/2).trans_le hn
  have hl := Real.log_le_log (by positivity : (0:ℝ) < X/2) hn
  rw [Real.log_div hXp.ne' (by norm_num)] at hl
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  exact ⟨hnp,by linarith⟩

theorem largePrimeTuplePiece_ordinary_group (i j : ℕ) {ξ δ : ℝ}
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (ℓ : ℤ) (Ct : ℕ) (H X : ℝ),
      1 ≤ X → 200 ≤ Real.log X → ∀ {N : ℕ}
      (k : (Fin i ⊕ Fin j) → Fin N),
      ∀ q ∈ largePrimeTupleBox i j X,
        largePrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0 →
        ¬largePrimeTupleExceptional δ q →
        ∃ s : Finset (Fin i ⊕ Fin j),
          norm (largePrimeTupleProduct q)^(1/3+ε:ℝ)/2^(i+j) ≤
            largeTupleSubsetScale (fun a => (k a).val) s ∧
          largeTupleSubsetScale (fun a => (k a).val) s ≤
            norm (largePrimeTupleProduct q)^(1/2:ℝ) := by
  obtain ⟨ε,hε,hgroup⟩ := largePrimeTuple_grouping_gap i j hξ hξz hδ
  refine ⟨ε,hε,?_⟩
  intro ℓ Ct H X hX hlog N k q hq hne hex
  obtain ⟨ht,hw⟩ := mul_ne_zero_iff.mp hne
  obtain ⟨hn,hln⟩ := largePrimeTuplePiece_log_pos hX hlog k hne
  obtain ⟨s,hl,hu⟩ := hgroup ℓ Ct H X hX hlog q hq ht hex
  obtain ⟨s,hl,hu⟩ := largePrimeTuple_short_subset (largePrimeTupleExponent_sum hq hln.ne') hl hu
  obtain ⟨hsl,hsu⟩ := largePrimeTuplePiece_group_scale k hq hw hn hln s hl hu
  refine ⟨s,?_,hsu⟩
  apply le_trans _ hsl
  apply div_le_div_of_nonneg_left (Real.rpow_nonneg hn.le _) (by positivity)
  exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2)
    (by simpa using Finset.card_le_univ s)

end CubicFirstMoment

end

end OAI
