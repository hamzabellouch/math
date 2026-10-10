import OAI.NumberTheory.CubicMoment.Estimates.TailPrimeRegroup
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstArity
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstTailDecompositionRows

namespace OAI

/-! Exact bounded-arity expansion of the remaining Gauss height rows.
The original total-product envelope is retained before independent regrouping. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma tailPrimeTupleTerm_envelope {i j : ℕ} (ℓ : ℤ) (ξ H U : ℝ)
    {X : ℝ} (hX : 0 < X)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X) :
    (if (∏ a, q.1 a) ∈ centralPrimaryFactors X then
      if (∏ b, q.2 b) ∈ primaryProductSlice (centralProductEnvelope X)
          (Real.exp primeProductWeights.radius*X) (∏ a, q.1 a) then
        tailPrimeTupleTerm i j ℓ ξ H U X q else 0 else 0) =
      tailPrimeTupleTerm i j ℓ ξ H U X q := by
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
  · have he := productGaussHeightWindowKernel_envelope ℓ primeProductEnvelope hX
      (fun x hx => primeProductWeights.upper_support () x hx) H U X hn
    change (if largePrimeTupleProduct q ∈ centralProductEnvelope X then
      productGaussHeightWindowKernel ℓ primeProductEnvelope H U X X
        (largePrimeTupleProduct q) else 0) = _ at he
    rw [ite_eq_right hp] at he
    have hz : tailPrimeTupleTerm i j ℓ ξ H U X q = 0 := by
      simp only [tailPrimeTupleTerm,largePrimeTupleProduct,he.symm,mul_zero]
    simp only [hz,ite_self]

def tailScaleDoubleRow (i j : ℕ) (ℓ : ℤ) (ξ : ℝ) (H U X : ℝ)
    (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ∑ r ∈ centralPrimaryFactors X, distinguishedScaleCoefficient i ξ X k r *
    ∑ u ∈ primaryProductSlice (centralProductEnvelope X)
      (Real.exp primeProductWeights.radius*X) r,
      roughTupleCoefficient j (Real.exp primeProductWeights.radius*X)
        primeDetectorCutoff (X^ξ) u *
        productGaussHeightWindowKernel ℓ primeProductEnvelope H U X X (r*u)

theorem tailScaleRow_remainder_arity {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ m : ℕ, ∀ᶠ X : ℝ in atTop, ∀ (i : ℕ) (ℓ : ℤ) (H U : ℝ)
      (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))),
      scaleFirstTailScaleRow i ℓ ξ H U X k =
        ∑ j ∈ Finset.range m, tailScaleDoubleRow i j ℓ ξ H U X k := by
  obtain ⟨m,hm⟩ := rough_slice_by_arity hξ (Real.exp_pos primeProductWeights.radius)
    (fun _ _ hx => primeDetectorCutoff_one hx)
  refine ⟨m,?_⟩
  filter_upwards [hm] with X hm
  intro i ℓ H U k
  unfold scaleFirstTailScaleRow tailScaleDoubleRow
  change (∑ r ∈ centralPrimaryFactors X, distinguishedScaleCoefficient i ξ X k r *
    ∑ u ∈ primaryProductSlice (centralProductEnvelope X)
      (Real.exp primeProductWeights.radius*X) r,
      (roughProduct primeDetectorCutoff (X^ξ) u:ℂ)*
        productGaussHeightWindowKernel ℓ primeProductEnvelope H U X X (r*u)) = _
  simp_rw [hm (centralProductEnvelope X) _ _ (fun _ hn => centralProductEnvelope_spec hn),
    Finset.mul_sum]
  rw [Finset.sum_comm]

lemma tailScaleDoubleRow_eq_tuples (i j : ℕ) (ℓ : ℤ) (ξ : ℝ)
    (H U : ℝ) {X : ℝ} (hX : 0 < X)
    (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
    tailScaleDoubleRow i j ℓ ξ H U X k =
      ((i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹) *
        ∑ q ∈ largePrimeTupleBox i j X,
          tailPrimeTupleTerm i j ℓ ξ H U X q * normTupleWeight k (fun a => norm (q.1 a)) := by
  let S := fun _ : Fin i => primeCutoff (Real.exp primeProductWeights.radius*X)
  let T := fun _ : Fin j => primeCutoff (Real.exp primeProductWeights.radius*X)
  let v := fun a p => normPartitionWeight (2*norm p/(4/3:ℝ)^(k a).val) *
    distinguishedPrimeWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) p
  let w := fun _ : Fin j => fun p => 1-(primeDetectorCutoff (norm p/(X^ξ)):ℂ)
  let Q := primaryProductSlice (centralProductEnvelope X) (Real.exp primeProductWeights.radius*X)
  let K := fun r u => productGaussHeightWindowKernel ℓ primeProductEnvelope H U X X (r*u)
  let c := (i.factorial:ℂ)⁻¹
  let d := (j.factorial:ℂ)⁻¹
  have he : tailScaleDoubleRow i j ℓ ξ H U X k =
      (c*d)*∑ r ∈ centralPrimaryFactors X, orderedConvolution S v r *
        ∑ u ∈ Q r, orderedConvolution T w u*K r u := by
    unfold tailScaleDoubleRow distinguishedScaleCoefficient
      distinguishedTupleCoefficient roughTupleCoefficient
    simp only [Fintype.card_fin]
    change (∑ r ∈ centralPrimaryFactors X, (c*orderedConvolution S v r)*
      ∑ u ∈ Q r, (d*orderedConvolution T w u)*K r u) = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    have hu : (∑ u ∈ Q r, (d*orderedConvolution T w u)*K r u) =
        d*∑ u ∈ Q r, orderedConvolution T w u*K r u := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    rw [hu]
    ring
  rw [he,orderedConvolution_double_restrict]
  congr 1
  rw [show largePrimeTupleBox i j X = (Fintype.piFinset S).product (Fintype.piFinset T) from rfl,
    Finset.product_eq_sprod,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro g hg
  have hq : (f,g) ∈ largePrimeTupleBox i j X := Finset.mem_product.mpr ⟨hf,hg⟩
  have henv := tailPrimeTupleTerm_envelope ℓ ξ H U hX hq
  have hwprod : (∏ a, v a (f a))*(∏ b, w b (g b))*K (∏ a, f a) (∏ b, g b) =
      tailPrimeTupleTerm i j ℓ ξ H U X (f,g)*normTupleWeight k (fun a => norm (f a)) := by
    simp only [v,w,K,tailPrimeTupleTerm,largePrimeTupleProduct,normTupleWeight,
      Finset.prod_mul_distrib]
    ring
  by_cases hr : (∏ a, f a) ∈ centralPrimaryFactors X
  · by_cases hu : (∏ b, g b) ∈ Q (∏ a, f a)
    · simp only [hr,hu,ite_true]
      exact hwprod
    · dsimp only [Q] at hu
      have hz : tailPrimeTupleTerm i j ℓ ξ H U X (f,g) = 0 := by
        simpa only [hr,hu,ite_true,ite_false] using henv.symm
      simp only [Q,hr,hu,ite_true,ite_false,hz,zero_mul]
  · have hz : tailPrimeTupleTerm i j ℓ ξ H U X (f,g) = 0 := by
      simpa only [hr,ite_false] using henv.symm
    simp only [hr,ite_false,hz,zero_mul]

lemma tailScaleDoubleRow_partition (i j : ℕ) (ℓ : ℤ) (ξ : ℝ)
    (H U : ℝ) {X : ℝ} (hX : 1 ≤ Real.exp primeProductWeights.radius*X)
    (hXp : 0 < X)
    (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
    tailScaleDoubleRow i j ℓ ξ H U X k =
      ∑ l : Fin j → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
        tailPrimeTuplePiece i j ℓ ξ H U X (Sum.elim k l) := by
  rw [tailScaleDoubleRow_eq_tuples i j ℓ ξ H U hXp]
  rw [finite_sum_normTupleWeight (largePrimeTupleBox i j X)
    (fun q => tailPrimeTupleTerm i j ℓ ξ H U X q * normTupleWeight k (fun a => norm (q.1 a)))
    (fun q b => norm (q.2 b))
    (fun q hq b => (largePrimeTupleNorm_bounds hq (.inr b)).1)
    (fun q hq b => (largePrimeTupleNorm_bounds hq (.inr b)).2)
    (normPartitionCount_covers hX),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  unfold tailPrimeTuplePiece
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  rw [normTupleWeight_sum_elim]
  ring

end CubicFirstMoment

end

end OAI
