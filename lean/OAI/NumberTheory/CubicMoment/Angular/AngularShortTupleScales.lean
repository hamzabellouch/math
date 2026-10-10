import OAI.NumberTheory.CubicMoment.Estimates.SmoothNormPartition
import OAI.NumberTheory.CubicMoment.Angular.AngularShortTupleMellin
import OAI.NumberTheory.CubicMoment.Estimates.ShortTupleScales

namespace OAI

/-! A nonzero smooth convolution piece automatically has comparable total
length. Thus the moment hypotheses need not be imposed on empty pieces. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable (ℓ : ℤ)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem primaryAngularShortTupleSum_nonzero_scales (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (V : ℝ → ℂ) {Z : ℝ} (hX : ∀ i, 0 < X i) (hZ : 0 < Z)
    (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (h : primaryAngularShortTupleSum ℓ X A a b q η (fun _ => normPartitionWeight) t V Z ≠ 0) :
    Z ≤ ∏ i, X i ∧ (∏ i, X i) ≤ (2:ℝ)^(Fintype.card ι+1)*Z := by
  unfold primaryAngularShortTupleSum at h
  obtain ⟨n,_,hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hp := (mul_ne_zero_iff.mp hn).1
  have hv := (mul_ne_zero_iff.mp hn).2
  have hi (i : ι) : norm (n i:Eisenstein) ≤ X i ∧ X i ≤ 2*norm (n i:Eisenstein) := by
    apply normPartitionWeight_nonzero_length (hX i)
    exact (mul_ne_zero_iff.mp ((Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i))).2
  have hlo : 1 ≤ (∏ i, norm (n i:Eisenstein))/Z := by
    by_contra hlt
    exact hv (hVlo _ (lt_of_not_ge hlt))
  have hhi : (∏ i, norm (n i:Eisenstein))/Z ≤ 2 := by
    by_contra hgt
    exact hv (hVhi _ (lt_of_not_ge hgt))
  constructor
  · simpa only [one_mul] using ((le_div_iff₀ hZ).mp hlo).trans
      (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => (hi i).1))
  · calc
      _ ≤ ∏ i, 2*norm (n i:Eisenstein) := Finset.prod_le_prod₀
        (fun i _ => (hX i).le) (fun i _ => (hi i).2)
      _ = (2:ℝ)^(Fintype.card ι)*(∏ i, norm (n i:Eisenstein)) := by
        rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
      _ ≤ (2:ℝ)^(Fintype.card ι)*(2*Z) :=
        mul_le_mul_of_nonneg_left ((div_le_iff₀ hZ).mp hhi) (by positivity)
      _ = _ := by rw [pow_succ]; ring

theorem primaryAngularShortTupleSum_zero_outside_scales (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (V : ℝ → ℂ) {Z : ℝ} (hX : ∀ i, 0 < X i) (hZ : 0 < Z)
    (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hscale : ¬(Z ≤ ∏ i, X i ∧ (∏ i, X i) ≤ (2:ℝ)^(Fintype.card ι+1)*Z)) :
    primaryAngularShortTupleSum ℓ X A a b q η (fun _ => normPartitionWeight) t V Z = 0 := by
  by_contra h
  exact hscale (primaryAngularShortTupleSum_nonzero_scales ℓ X A a b q η t V hX hZ hVlo hVhi h)

end CubicFirstMoment

end

end OAI
