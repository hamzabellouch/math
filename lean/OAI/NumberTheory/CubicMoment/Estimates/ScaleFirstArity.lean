import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstTuple

namespace OAI

/-! Expand the rough remainder only after fixing the distinguished
smooth scales. All tuple and product supports remain exact. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def distinguishedScaleDoubleRow (i j : ℕ) (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ)
    (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ∑ r ∈ centralPrimaryFactors X, distinguishedScaleCoefficient i ξ X k r *
    ∑ u ∈ primaryProductSlice (centralProductEnvelope X)
      (Real.exp primeProductWeights.radius*X) r,
      roughTupleCoefficient j (Real.exp primeProductWeights.radius*X)
        primeDetectorCutoff (X^ξ) u *
        centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (r*u)

theorem distinguishedScaleRow_remainder_arity {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ m : ℕ, ∀ᶠ X : ℝ in atTop, ∀ (i : ℕ) (ℓ : ℤ) (Ct : ℕ) (H : ℝ)
      (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))),
      distinguishedScaleRow i ℓ ξ Ct H X k =
        ∑ j ∈ Finset.range m, distinguishedScaleDoubleRow i j ℓ ξ Ct H X k := by
  obtain ⟨m,hm⟩ := rough_slice_by_arity hξ (Real.exp_pos primeProductWeights.radius)
    (fun _ _ hx => primeDetectorCutoff_one hx)
  refine ⟨m,?_⟩
  filter_upwards [hm] with X hm
  intro i ℓ Ct H k
  unfold distinguishedScaleRow distinguishedScaleDoubleRow
  simp_rw [hm (centralProductEnvelope X) _ _ (fun _ hn => centralProductEnvelope_spec hn),
    Finset.mul_sum]
  rw [Finset.sum_comm]

lemma distinguishedScaleDoubleRow_eq_tuples (i j : ℕ) (ℓ : ℤ) (ξ : ℝ)
    (Ct : ℕ) (H : ℝ) {X : ℝ} (hX : 0 < X)
    (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
    distinguishedScaleDoubleRow i j ℓ ξ Ct H X k =
      ((i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹) *
        ∑ q ∈ largePrimeTupleBox i j X,
          uncutPrimeTupleTerm i j ℓ ξ Ct H X q * normTupleWeight k (fun a => norm (q.1 a)) := by
  let S := fun _ : Fin i => primeCutoff (Real.exp primeProductWeights.radius*X)
  let T := fun _ : Fin j => primeCutoff (Real.exp primeProductWeights.radius*X)
  let v := fun a p => normPartitionWeight (2*norm p/(4/3:ℝ)^(k a).val) *
    distinguishedPrimeWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) p
  let w := fun _ : Fin j => fun p => 1-(primeDetectorCutoff (norm p/(X^ξ)):ℂ)
  let U := primaryProductSlice (centralProductEnvelope X) (Real.exp primeProductWeights.radius*X)
  let K := fun r u => centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (r*u)
  let c := (i.factorial:ℂ)⁻¹
  let d := (j.factorial:ℂ)⁻¹
  have he : distinguishedScaleDoubleRow i j ℓ ξ Ct H X k =
      (c*d)*∑ r ∈ centralPrimaryFactors X, orderedConvolution S v r *
        ∑ u ∈ U r, orderedConvolution T w u*K r u := by
    unfold distinguishedScaleDoubleRow distinguishedScaleCoefficient
      distinguishedTupleCoefficient roughTupleCoefficient
    simp only [Fintype.card_fin]
    change (∑ r ∈ centralPrimaryFactors X, (c*orderedConvolution S v r)*
      ∑ u ∈ U r, (d*orderedConvolution T w u)*K r u) = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    have hu : (∑ u ∈ U r, (d*orderedConvolution T w u)*K r u) =
        d*∑ u ∈ U r, orderedConvolution T w u*K r u := by
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
  have henv := uncutPrimeTupleTerm_envelope ℓ ξ Ct H hX hq
  have hwprod : (∏ a, v a (f a))*(∏ b, w b (g b))*K (∏ a, f a) (∏ b, g b) =
      uncutPrimeTupleTerm i j ℓ ξ Ct H X (f,g)*normTupleWeight k (fun a => norm (f a)) := by
    simp only [v,w,K,uncutPrimeTupleTerm,largePrimeTupleProduct,normTupleWeight,
      Finset.prod_mul_distrib]
    ring
  by_cases hr : (∏ a, f a) ∈ centralPrimaryFactors X
  · by_cases hu : (∏ b, g b) ∈ U (∏ a, f a)
    · simp only [hr,hu,ite_true]
      exact hwprod
    · dsimp only [U] at hu
      have hz : uncutPrimeTupleTerm i j ℓ ξ Ct H X (f,g) = 0 := by
        simpa only [hr,hu,ite_true,ite_false] using henv.symm
      simp only [U,hr,hu,ite_true,ite_false,hz,zero_mul]
  · have hz : uncutPrimeTupleTerm i j ℓ ξ Ct H X (f,g) = 0 := by
      simpa only [hr,ite_false] using henv.symm
    simp only [hr,ite_false,hz,zero_mul]

lemma normTupleWeight_sum_elim {i j N : ℕ} (k : Fin i → Fin N) (l : Fin j → Fin N)
    (q : (Fin i → Eisenstein) × (Fin j → Eisenstein)) :
    normTupleWeight (Sum.elim k l) (largePrimeTupleNorm q) =
      normTupleWeight k (fun a => norm (q.1 a)) *
        normTupleWeight l (fun b => norm (q.2 b)) := by
  unfold normTupleWeight
  rw [Fintype.prod_sum_type]
  rfl

lemma distinguishedScaleDoubleRow_partition (i j : ℕ) (ℓ : ℤ) (ξ : ℝ)
    (Ct : ℕ) (H : ℝ) {X : ℝ} (hX : 1 ≤ Real.exp primeProductWeights.radius*X)
    (hXp : 0 < X)
    (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
    distinguishedScaleDoubleRow i j ℓ ξ Ct H X k =
      ∑ l : Fin j → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
        scaleFirstPrimeTuplePiece i j ℓ ξ Ct H X (Sum.elim k l) := by
  rw [distinguishedScaleDoubleRow_eq_tuples i j ℓ ξ Ct H hXp]
  rw [finite_sum_normTupleWeight (largePrimeTupleBox i j X)
    (fun q => uncutPrimeTupleTerm i j ℓ ξ Ct H X q * normTupleWeight k (fun a => norm (q.1 a)))
    (fun q b => norm (q.2 b))
    (fun q hq b => (largePrimeTupleNorm_bounds hq (.inr b)).1)
    (fun q hq b => (largePrimeTupleNorm_bounds hq (.inr b)).2)
    (normPartitionCount_covers hX),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  unfold scaleFirstPrimeTuplePiece
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  rw [normTupleWeight_sum_elim]
  ring

end CubicFirstMoment

end

end OAI
