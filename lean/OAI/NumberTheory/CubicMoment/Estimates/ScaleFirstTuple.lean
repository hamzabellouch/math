import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedScaleRows
import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleFullSupport

namespace OAI

/-! Full tuple pieces for the scale-first branch. The smooth total
product kernel enforces the squarefree envelope; no lower cutoff on the
actual distinguished product is inserted. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def uncutPrimeTupleTerm (i j : ℕ) (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ)
    (q : (Fin i → Eisenstein) × (Fin j → Eisenstein)) : ℂ :=
  (∏ a, distinguishedPrimeWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) (q.1 a))*
    (∏ b, (1-(primeDetectorCutoff (norm (q.2 b)/(X^ξ)):ℂ)))*
    centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct)
      X X (largePrimeTupleProduct q)

def scaleFirstPrimeTuplePiece (i j : ℕ) (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ)
    (k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ((i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹)*
    ∑ q ∈ largePrimeTupleBox i j X,
      uncutPrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight k (largePrimeTupleNorm q)

lemma uncutPrimeTupleTerm_envelope {i j : ℕ} (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ)
    (H : ℝ) {X : ℝ} (hX : 0 < X)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X) :
    (if (∏ a, q.1 a) ∈ centralPrimaryFactors X then
      if (∏ b, q.2 b) ∈ primaryProductSlice (centralProductEnvelope X)
          (Real.exp primeProductWeights.radius*X) (∏ a, q.1 a) then
        uncutPrimeTupleTerm i j ℓ ξ Ct H X q else 0 else 0) =
      uncutPrimeTupleTerm i j ℓ ξ Ct H X q := by
  obtain ⟨hf,hg⟩ := Finset.mem_product.mp hq
  have hr : primary (∏ a, q.1 a) := primary_finset_prod _ _
    (fun a _ => (mem_primeCutoff.mp (Fintype.mem_piFinset.mp hf a)).1.1)
  have hu : primary (∏ b, q.2 b) := primary_finset_prod _ _
    (fun b _ => (mem_primeCutoff.mp (Fintype.mem_piFinset.mp hg b)).1.1)
  have hn := primary_mul hr hu
  by_cases hp : largePrimeTupleProduct q ∈ centralProductEnvelope X
  · have hrB : (∏ a, q.1 a) ∈ centralPrimaryFactors X := by
      apply mem_primaryElementBall.mpr
      exact ⟨hr,(norm_le_of_dvd (primary_ne_zero hn) (dvd_mul_right _ _)).trans
        (centralProductEnvelope_spec hp).2.2⟩
    have huS : (∏ b, q.2 b) ∈ primaryProductSlice (centralProductEnvelope X)
        (Real.exp primeProductWeights.radius*X) (∏ a, q.1 a) :=
      (mem_primaryProductSlice_iff _ _ (fun _ hn => centralProductEnvelope_spec hn) _ hu).mpr hp
    rw [ite_eq_left hrB,ite_eq_left huS]
  · have he := centeredHeightKernel_envelope ℓ primeProductEnvelope hX
      (fun x hx => primeProductWeights.upper_support () x hx) H ((1+Real.log X)^Ct) X hn
    change (if largePrimeTupleProduct q ∈ centralProductEnvelope X then
      centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct)
        X X (largePrimeTupleProduct q) else 0) = _ at he
    rw [ite_eq_right hp] at he
    have hz : uncutPrimeTupleTerm i j ℓ ξ Ct H X q = 0 := by
      simp only [uncutPrimeTupleTerm,largePrimeTupleProduct,he.symm,mul_zero]
    simp only [hz,ite_self]

lemma uncutPrimeTupleTerm_smoothed {i j N : ℕ} (ℓ : ℤ) (ξ : ℝ)
    (Ct : ℕ) (H X : ℝ) (k : (Fin i ⊕ Fin j) → Fin N)
    (q : (Fin i → Eisenstein) × (Fin j → Eisenstein)) :
    uncutPrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight k (largePrimeTupleNorm q) =
      (∏ a, largeTupleCoordinateWeight ξ X (fun a => (k a).val) a
        (largePrimeTupleNorm q a/largeTupleNormScale (fun a => (k a).val) a))*
        centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct)
          X X (largePrimeTupleProduct q) := by
  rw [largeTupleCoordinateWeight_product]
  unfold uncutPrimeTupleTerm
  ring

lemma scaleFirstPrimeTuplePiece_full (i j : ℕ) (ℓ : ℤ) (ξ : ℝ)
    (Ct : ℕ) (H X : ℝ)
    (k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (hb : ∀ a, 2*largeTupleNormScale (fun a => (k a).val) a ≤ Real.exp primeProductWeights.radius*X) :
    scaleFirstPrimeTuplePiece i j ℓ ξ Ct H X k =
      ((i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹)*
        largeTupleIndependentSum i j ℓ ξ Ct H X (fun a => (k a).val) := by
  unfold scaleFirstPrimeTuplePiece largeTupleIndependentSum
  congr 1
  have he := independent_tuple_sum_sum_type
    (fun _ : Fin i ⊕ Fin j => primeCutoff (Real.exp primeProductWeights.radius*X))
    (fun q => (∏ a, largeTupleCoordinateWeight ξ X (fun a => (k a).val) a
      (norm (largeTupleVector q a)/largeTupleNormScale (fun a => (k a).val) a))*
      centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (∏ a, largeTupleVector q a))
  simp_rw [largeTupleVector_split] at he
  rw [independent_tuple_sum_support
    (fun _ : Fin i ⊕ Fin j => primeCutoff (Real.exp primeProductWeights.radius*X))
    (fullPrimeSupport 2 (largeTupleCoordinateWeight ξ X (fun a => (k a).val))
      (largeTupleNormScale (fun a => (k a).val)))
    (fun a p => largeTupleCoordinateWeight ξ X (fun a => (k a).val) a
      (norm p/largeTupleNormScale (fun a => (k a).val) a))
    (fun f => centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (∏ a, f a))
    (largeTuple_coordinate_support ξ X (fun a => (k a).val) hb)] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro q _
  rw [uncutPrimeTupleTerm_smoothed]
  simp only [largeTupleVector_norm,largeTupleVector_prod]

end CubicFirstMoment

end

end OAI
