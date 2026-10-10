import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedPrimeTuples
import OAI.NumberTheory.CubicMoment.Estimates.SmoothTuplePartition
import OAI.NumberTheory.CubicMoment.Estimates.SmoothPartitionCount

namespace OAI

/-! Finite smooth norm partition of the literal large-row prime tuples.
Every original support condition stays inside each summand. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def largePrimeTupleBox (i j : ℕ) (X : ℝ) :
    Finset ((Fin i → Eisenstein) × (Fin j → Eisenstein)) :=
  (Fintype.piFinset (fun _ : Fin i => primeCutoff (Real.exp primeProductWeights.radius*X))).product
    (Fintype.piFinset (fun _ : Fin j => primeCutoff (Real.exp primeProductWeights.radius*X)))

def largePrimeTupleTerm (i j : ℕ) (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ)
    (q : (Fin i → Eisenstein) × (Fin j → Eisenstein)) : ℂ :=
  if (∏ a, q.1 a) ∈ (centralPrimaryFactors X).filter
      (fun r => ¬norm r < X^(38/100:ℝ)) then
    if (∏ b, q.2 b) ∈ primaryProductSlice (centralProductEnvelope X)
        (Real.exp primeProductWeights.radius*X) (∏ a, q.1 a) then
      (∏ a, distinguishedPrimeWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) (q.1 a))*
        (∏ b, (1-(primeDetectorCutoff (norm (q.2 b)/(X^ξ)):ℂ)))*
        centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct)
          X X ((∏ a, q.1 a)*(∏ b, q.2 b))
    else 0
  else 0

def largePrimeTupleNorm {i j : ℕ}
    (q : (Fin i → Eisenstein) × (Fin j → Eisenstein)) : (Fin i ⊕ Fin j) → ℝ :=
  Sum.elim (fun a => norm (q.1 a)) (fun b => norm (q.2 b))

lemma largePrimeTupleNorm_bounds {i j : ℕ} {X : ℝ}
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X) (a : Fin i ⊕ Fin j) :
    1 ≤ largePrimeTupleNorm q a ∧
      largePrimeTupleNorm q a ≤ Real.exp primeProductWeights.radius*X := by
  obtain ⟨hf,hg⟩ := Finset.mem_product.mp hq
  rcases a with a | b
  · have hp := mem_primeCutoff.mp (Fintype.mem_piFinset.mp hf a)
    exact ⟨one_le_norm hp.1.2.ne_zero,hp.2⟩
  · have hp := mem_primeCutoff.mp (Fintype.mem_piFinset.mp hg b)
    exact ⟨one_le_norm hp.1.2.ne_zero,hp.2⟩

lemma distinguishedPrimeTupleLow_eq_sum (i j : ℕ) (ℓ : ℤ) (ξ : ℝ)
    (Ct : ℕ) (H X : ℝ) :
    distinguishedPrimeTupleLow i j ℓ ξ Ct H X =
      ((i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹)*
        ∑ q ∈ largePrimeTupleBox i j X, largePrimeTupleTerm i j ℓ ξ Ct H X q := by
  simp only [distinguishedPrimeTupleLow,largePrimeTupleBox,Finset.product_eq_sprod,Finset.sum_product,
    largePrimeTupleTerm]

def largePrimeTuplePiece (i j : ℕ) (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ)
    (k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ((i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹)*
    ∑ q ∈ largePrimeTupleBox i j X,
      largePrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight k (largePrimeTupleNorm q)

theorem distinguishedPrimeTupleLow_partition (i j : ℕ) (ℓ : ℤ) (ξ : ℝ)
    (Ct : ℕ) (H : ℝ) {X : ℝ} (hX : 1 ≤ Real.exp primeProductWeights.radius*X) :
    distinguishedPrimeTupleLow i j ℓ ξ Ct H X =
      ∑ k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
        largePrimeTuplePiece i j ℓ ξ Ct H X k := by
  rw [distinguishedPrimeTupleLow_eq_sum]
  rw [finite_sum_normTupleWeight (largePrimeTupleBox i j X)
    (largePrimeTupleTerm i j ℓ ξ Ct H X) largePrimeTupleNorm
    (fun _ hq a => (largePrimeTupleNorm_bounds hq a).1)
    (fun _ hq a => (largePrimeTupleNorm_bounds hq a).2)
    (normPartitionCount_covers hX)]
  rw [Finset.mul_sum]
  rfl

end CubicFirstMoment

end

end OAI
