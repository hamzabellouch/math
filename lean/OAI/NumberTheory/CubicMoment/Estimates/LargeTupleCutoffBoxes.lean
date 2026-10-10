import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleScaleGeometry

namespace OAI

/-! The sharp distinguished-product condition is automatic on high
boxes and kills low boxes. The remaining boxes are explicitly confined
to a fixed-ratio neighborhood of the original cutoff. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def largeTupleDistinguishedScale {i j : ℕ} (k : (Fin i ⊕ Fin j) → ℕ) : ℝ :=
  ∏ a : Fin i, largeTupleNormScale k (.inl a)

lemma largePrimeTuplePiece_distinguished_range {i j N : ℕ}
    (k : (Fin i ⊕ Fin j) → Fin N)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hw : normTupleWeight k (largePrimeTupleNorm q) ≠ 0) :
    largeTupleDistinguishedScale (fun a => (k a).val) ≤ norm (∏ a, q.1 a) ∧
      norm (∏ a, q.1 a) ≤ 2^i*largeTupleDistinguishedScale (fun a => (k a).val) := by
  rw [norm_finset_prod]
  constructor
  · exact Finset.prod_le_prod₀ (fun a _ => (largeTupleNormScale_pos _ _).le)
      (fun a _ => (largePrimeTuplePiece_coordinate_range k hw (.inl a)).1)
  · calc
      _ ≤ ∏ a : Fin i, 2*largeTupleNormScale (fun a => (k a).val) (.inl a) :=
        Finset.prod_le_prod₀ (fun a _ => norm_nonneg _)
          (fun a _ => (largePrimeTuplePiece_coordinate_range k hw (.inl a)).2)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp [largeTupleDistinguishedScale]

lemma largePrimeTupleTerm_high_box {i j N : ℕ} (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ)
    (H : ℝ) {X : ℝ} (hX : 0 < X) (k : (Fin i ⊕ Fin j) → Fin N)
    (hhigh : X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (k a).val))
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X) :
    largePrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight k (largePrimeTupleNorm q) =
      (∏ a, largeTupleCoordinateWeight ξ X (fun a => (k a).val) a
        (largePrimeTupleNorm q a/largeTupleNormScale (fun a => (k a).val) a))*
        centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct)
          X X (largePrimeTupleProduct q) := by
  by_cases hw : normTupleWeight k (largePrimeTupleNorm q) = 0
  · rw [hw,mul_zero,largeTupleCoordinateWeight_product,hw,mul_zero,zero_mul]
  · have hh : ¬norm (∏ a, q.1 a) < X^(38/100:ℝ) :=
      not_lt.mpr (hhigh.trans (largePrimeTuplePiece_distinguished_range k hw).1)
    rw [largePrimeTupleTerm_smoothed ℓ ξ Ct H hX k hq,ite_eq_left hh]
    rfl

lemma largePrimeTupleTerm_low_box {i j N : ℕ} (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ)
    (H : ℝ) {X : ℝ} (hX : 0 < X) (k : (Fin i ⊕ Fin j) → Fin N)
    (hlow : 2^i*largeTupleDistinguishedScale (fun a => (k a).val) < X^(38/100:ℝ))
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X) :
    largePrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight k (largePrimeTupleNorm q) = 0 := by
  by_cases hw : normTupleWeight k (largePrimeTupleNorm q) = 0
  · rw [hw,mul_zero]
  · have hh : norm (∏ a, q.1 a) < X^(38/100:ℝ) :=
      (largePrimeTuplePiece_distinguished_range k hw).2.trans_lt hlow
    rw [largePrimeTupleTerm_smoothed ℓ ξ Ct H hX k hq,ite_eq_right (not_not.mpr hh)]

lemma largeTuple_cutoff_boundary {i j N : ℕ} {X : ℝ}
    (k : (Fin i ⊕ Fin j) → Fin N)
    (hhigh : ¬X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (k a).val))
    (hlow : ¬2^i*largeTupleDistinguishedScale (fun a => (k a).val) < X^(38/100:ℝ)) :
    X^(38/100:ℝ)/2^i ≤ largeTupleDistinguishedScale (fun a => (k a).val) ∧
      largeTupleDistinguishedScale (fun a => (k a).val) < X^(38/100:ℝ) := by
  exact ⟨(div_le_iff₀ (by positivity : (0:ℝ) < 2^i)).mpr
    (by simpa only [mul_comm] using not_lt.mp hlow),not_le.mp hhigh⟩

end CubicFirstMoment

end

end OAI
