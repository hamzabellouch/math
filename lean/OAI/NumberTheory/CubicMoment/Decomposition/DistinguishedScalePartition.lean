import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleCutoffBoxes
import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedArityRows

namespace OAI

/-! The manuscript partitions the distinguished prime scales before
splitting the rough remainder. This exact finite partition introduces no
partial-product cutoff in a high-scale coefficient. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def distinguishedScaleLength {i N : ℕ} (k : Fin i → Fin N) : ℝ :=
  ∏ a, (4/3:ℝ)^(k a).val/2

def distinguishedScaleCoefficient (i : ℕ) (ξ X : ℝ)
    (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (r : Eisenstein) : ℂ :=
  distinguishedTupleCoefficient
    (fun _ : Fin i => primeCutoff (Real.exp primeProductWeights.radius*X))
    (fun a p => normPartitionWeight (2*norm p/(4/3:ℝ)^(k a).val))
    primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) r

lemma distinguishedScaleCoefficient_partition (i : ℕ) (ξ : ℝ) {X : ℝ}
    (hX : 1 ≤ Real.exp primeProductWeights.radius*X) (r : Eisenstein) :
    distinguishedTupleCoefficient
      (fun _ : Fin i => primeCutoff (Real.exp primeProductWeights.radius*X))
      (fun _ _ => 1) primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) r =
      ∑ k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
        distinguishedScaleCoefficient i ξ X k r := by
  unfold distinguishedScaleCoefficient distinguishedTupleCoefficient orderedConvolution
  simp only [one_mul]
  rw [←Finset.mul_sum]
  congr 1
  let S := (Fintype.piFinset (fun _ : Fin i =>
    primeCutoff (Real.exp primeProductWeights.radius*X))).filter (fun f => (∏ a, f a) = r)
  have hb (f : Fin i → Eisenstein) (hf : f ∈ S) (a : Fin i) :
      1 ≤ norm (f a) ∧ norm (f a) ≤ Real.exp primeProductWeights.radius*X := by
    have hp := mem_primeCutoff.mp
      (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf).1 a)
    exact ⟨one_le_norm hp.1.2.ne_zero,hp.2⟩
  have he := finite_sum_normTupleWeight S
    (fun f => ∏ a, distinguishedPrimeWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) (f a))
    (fun f a => norm (f a)) (fun f hf a => (hb f hf a).1)
    (fun f hf a => (hb f hf a).2) (normPartitionCount_covers hX)
  rw [he]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro f _
  simp only [normTupleWeight,Finset.prod_mul_distrib]
  ring

lemma distinguishedScaleCoefficient_range (i : ℕ) (ξ X : ℝ)
    (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    {r : Eisenstein} (hne : distinguishedScaleCoefficient i ξ X k r ≠ 0) :
    distinguishedScaleLength k ≤ norm r ∧ norm r ≤ 2^i*distinguishedScaleLength k := by
  have hn : ∃ f ∈ (Fintype.piFinset (fun _ : Fin i =>
        primeCutoff (Real.exp primeProductWeights.radius*X))).filter (fun f => (∏ a, f a) = r),
      (∏ a, normPartitionWeight (2*norm (f a)/(4/3:ℝ)^(k a).val)*
        distinguishedPrimeWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) (f a)) ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    unfold distinguishedScaleCoefficient distinguishedTupleCoefficient orderedConvolution
    rw [Finset.sum_eq_zero h,mul_zero]
  obtain ⟨f,hf,hw⟩ := hn
  have he := (Finset.mem_filter.mp hf).2
  have hcoord (a : Fin i) := normPartitionWeight_nonzero_scale
    (mul_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp hw a (Finset.mem_univ a))).1
  rw [←he,norm_finset_prod]
  constructor
  · apply Finset.prod_le_prod₀
      (fun a _ => by positivity)
    intro a _
    have hh := (hcoord a).2
    linarith
  · calc
      _ ≤ ∏ a : Fin i, (4/3:ℝ)^(k a).val :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun a _ => (hcoord a).1)
      _ = 2^i*distinguishedScaleLength k := by
        simp only [distinguishedScaleLength,Finset.prod_div_distrib,Finset.prod_const,
          Finset.card_univ,Fintype.card_fin]
        field_simp

lemma distinguishedScaleCoefficient_norm (i : ℕ) (ξ X : ℝ)
    (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (r : Eisenstein) :
    ‖distinguishedScaleCoefficient i ξ X k r‖ ≤ ‖(i.factorial:ℂ)⁻¹‖*(i^i:ℕ) := by
  simpa only [Fintype.card_fin,distinguishedScaleCoefficient] using distinguishedTupleCoefficient_norm (ι := Fin i) _
    (fun _ _ hp => (mem_primeCutoff.mp hp).1) _
    (fun _ p _ => normPartitionWeight_norm _)
    (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩) _ _ r

lemma eventually_distinguishedScale_low_initial (i : ℕ) (ξ : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ k : Fin i →
      Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
      distinguishedScaleLength k < X^(69/200:ℝ) → ∀ r : Eisenstein,
      distinguishedScaleCoefficient i ξ X k r ≠ 0 → norm r < X^(9/25:ℝ) := by
  filter_upwards [eventually_const_mul_rpow_le
    (by norm_num : (69/200:ℝ) < 9/25) (2^i)] with X hX
  intro k hk r hr
  exact (distinguishedScaleCoefficient_range i ξ X k hr).2.trans_lt
    ((mul_lt_mul_of_pos_left hk (by positivity)).trans_le hX)

end CubicFirstMoment

end

end OAI
