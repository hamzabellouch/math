import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleSmoothIdentity
import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleGrouping

namespace OAI

/-! A nonzero smooth box fixes independent coordinate lengths. The
same lengths work for every tuple in the box, so a grouping chosen at
one surviving tuple does not introduce a new coupled coefficient. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def largeTupleSubsetScale {i j : ℕ} (k : (Fin i ⊕ Fin j) → ℕ)
    (s : Finset (Fin i ⊕ Fin j)) : ℝ := ∏ a ∈ s, largeTupleNormScale k a

lemma largeTupleSubsetScale_pos {i j : ℕ} (k : (Fin i ⊕ Fin j) → ℕ)
    (s : Finset (Fin i ⊕ Fin j)) : 0 < largeTupleSubsetScale k s :=
  Finset.prod_pos (fun a _ => largeTupleNormScale_pos k a)

lemma largeTupleSubsetScale_complement {i j : ℕ} (k : (Fin i ⊕ Fin j) → ℕ)
    (s : Finset (Fin i ⊕ Fin j)) :
    largeTupleSubsetScale k s*largeTupleSubsetScale k (Finset.univ\s) =
      largeTupleSubsetScale k Finset.univ := by
  exact Finset.prod_mul_prod_compl s (largeTupleNormScale k)

lemma largePrimeTuplePiece_coordinate_range {i j N : ℕ}
    (k : (Fin i ⊕ Fin j) → Fin N)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hw : normTupleWeight k (largePrimeTupleNorm q) ≠ 0) (a : Fin i ⊕ Fin j) :
    largeTupleNormScale (fun a => (k a).val) a ≤ largePrimeTupleNorm q a ∧
      largePrimeTupleNorm q a ≤ 2*largeTupleNormScale (fun a => (k a).val) a := by
  have hi := Finset.prod_ne_zero_iff.mp hw a (Finset.mem_univ a)
  obtain ⟨hu,hl⟩ := normPartitionWeight_nonzero_scale hi
  change (4/3:ℝ)^(k a).val/2 ≤ largePrimeTupleNorm q a ∧
    largePrimeTupleNorm q a ≤ 2*((4/3:ℝ)^(k a).val/2)
  constructor <;> linarith

lemma largePrimeTuplePiece_subset_range {i j N : ℕ}
    (k : (Fin i ⊕ Fin j) → Fin N)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hw : normTupleWeight k (largePrimeTupleNorm q) ≠ 0)
    (s : Finset (Fin i ⊕ Fin j)) :
    largeTupleSubsetScale (fun a => (k a).val) s ≤ ∏ a ∈ s, largePrimeTupleNorm q a ∧
      (∏ a ∈ s, largePrimeTupleNorm q a) ≤
        2^s.card*largeTupleSubsetScale (fun a => (k a).val) s := by
  constructor
  · exact Finset.prod_le_prod₀ (fun a _ => (largeTupleNormScale_pos _ a).le)
      (fun a _ => (largePrimeTuplePiece_coordinate_range k hw a).1)
  · calc
      _ ≤ ∏ a ∈ s, 2*largeTupleNormScale (fun a => (k a).val) a :=
        Finset.prod_le_prod₀ (fun a _ =>
          (largeTupleNormScale_pos _ a).le.trans (largePrimeTuplePiece_coordinate_range k hw a).1)
          (fun a _ => (largePrimeTuplePiece_coordinate_range k hw a).2)
      _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const]; rfl

lemma largePrimeTuplePiece_scale_product {i j N : ℕ} {ℓ : ℤ} {ξ : ℝ}
    {Ct : ℕ} {H X : ℝ} (hX : 0 < X)
    (k : (Fin i ⊕ Fin j) → Fin N)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hne : largePrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0) :
    X/(2*2^(i+j)) ≤ largeTupleSubsetScale (fun a => (k a).val) Finset.univ ∧
      largeTupleSubsetScale (fun a => (k a).val) Finset.univ ≤ 3*X := by
  obtain ⟨ht,hw⟩ := mul_ne_zero_iff.mp hne
  obtain ⟨hlo,hhi⟩ := largePrimeTupleTerm_product_range hX ht
  change X/2 ≤ norm (largePrimeTupleProduct q) at hlo
  obtain ⟨hl,hu⟩ := largePrimeTuplePiece_subset_range k hw Finset.univ
  rw [largePrimeTupleNorm_prod] at hl hu
  simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin] at hu
  refine ⟨?_,hl.trans hhi⟩
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*2^(i+j))).mpr
  nlinarith

lemma largePrimeTuplePiece_group_scale {i j N : ℕ} {X : ℝ}
    (k : (Fin i ⊕ Fin j) → Fin N)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X)
    (hw : normTupleWeight k (largePrimeTupleNorm q) ≠ 0)
    (hn : 0 < norm (largePrimeTupleProduct q))
    (hln : 0 < Real.log (norm (largePrimeTupleProduct q)))
    (s : Finset (Fin i ⊕ Fin j)) {l u : ℝ}
    (hl : l ≤ ∑ a ∈ s, largePrimeTupleExponent q a)
    (hu : (∑ a ∈ s, largePrimeTupleExponent q a) ≤ u) :
    norm (largePrimeTupleProduct q)^l/2^s.card ≤ largeTupleSubsetScale (fun a => (k a).val) s ∧
      largeTupleSubsetScale (fun a => (k a).val) s ≤ norm (largePrimeTupleProduct q)^u := by
  obtain ⟨hpl,hpu⟩ := largePrimeTuple_subset_norm_bounds hq hn hln s hl hu
  obtain ⟨hsl,hsu⟩ := largePrimeTuplePiece_subset_range k hw s
  refine ⟨(div_le_iff₀ (by positivity : (0:ℝ) < 2^s.card)).mpr ?_,hsl.trans hpu⟩
  simpa only [mul_comm] using hpl.trans hsu

end CubicFirstMoment

end

end OAI
