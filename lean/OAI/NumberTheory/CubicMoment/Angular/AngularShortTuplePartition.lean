import OAI.NumberTheory.CubicMoment.Angular.AngularShortTupleScales
import OAI.NumberTheory.CubicMoment.Estimates.ShortTuplePartition
import OAI.NumberTheory.CubicMoment.Estimates.SmoothPartitionCount

namespace OAI

/-! Exact reconstruction of the original finite convolution from smooth
norm pieces. The common ball is forced by the global product cutoff. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primaryAngularTupleCore (A : ι → EisensteinArithmeticFunction) (a b : Eisenstein)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (t : ι → ℝ) (V : ℝ → ℂ) (Z : ℝ) (n : ι → Eisenstein) : ℂ :=
  (∏ i, ((MvPowerSeries.coeff (idealExponentOf (n i)) (A i):ℝ):ℂ)*
    (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*theta ℓ (n i)*
      mellinPhase (t i) (norm (n i))))*V ((∏ i, norm (n i))/Z)

lemma primaryAngularShortTupleSum_eq_core (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (V : ℝ → ℂ) (Z : ℝ) :
    primaryAngularShortTupleSum ℓ X A a b q η (fun _ => normPartitionWeight) t V Z =
      ∑ n ∈ Fintype.piFinset (fun i => primaryElementBall (X i)),
        primaryAngularTupleCore ℓ A a b q η t V Z n*
          ∏ i, normPartitionWeight (norm (n i)/(X i/2)) := by
  unfold primaryAngularShortTupleSum
  calc
    _ = ∑ n : (i : ι) → primaryElementBall (X i),
        primaryAngularTupleCore ℓ A a b q η t V Z (fun i => n i)*
          ∏ i, normPartitionWeight (norm (n i)/(X i/2)) := by
      apply Finset.sum_congr rfl
      intro n _
      unfold primaryAngularTupleCore
      rw [Finset.prod_mul_distrib]
      ring
    _ = _ := sum_primary_pi X (fun n => primaryAngularTupleCore ℓ A a b q η t V Z n*
      ∏ i, normPartitionWeight (norm (n i)/(X i/2)))

omit [DecidableEq ι] in
lemma primaryAngularTupleCore_support (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (V : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (hV : ∀ x, 2 < x → V x = 0)
    (n : ι → Eisenstein) (hn : ∀ i, primary (n i))
    (h : primaryAngularTupleCore ℓ A a b q η t V Z n ≠ 0) (i : ι) : norm (n i) ≤ 2*Z := by
  have hv := (mul_ne_zero_iff.mp h).2
  have hp : (∏ j, norm (n j))/Z ≤ 2 := by
    by_contra hgt
    exact hv (hV _ (lt_of_not_ge hgt))
  have hni : norm (n i) ≤ ∏ j, norm (n j) := by
    calc
      _ = ∏ j ∈ ({i} : Finset ι), norm (n j) := by simp
      _ ≤ _ := Finset.prod_le_prod_of_subset_of_one_le₀ (by simp)
        (fun j _ => norm_nonneg _) (fun j _ _ => one_le_norm (primary_ne_zero (hn j)))
  exact hni.trans ((div_le_iff₀ hZ).mp hp)

lemma primaryAngularShortTupleSum_common_ball (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (V : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (hV : ∀ x, 2 < x → V x = 0)
    (hX : ∀ i, 0 < X i) :
    primaryAngularShortTupleSum ℓ X A a b q η (fun _ => normPartitionWeight) t V Z =
      ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Z)),
        primaryAngularTupleCore ℓ A a b q η t V Z n*
          ∏ i, normPartitionWeight (norm (n i)/(X i/2)) := by
  rw [primaryAngularShortTupleSum_eq_core ℓ]
  apply Finset.sum_bij_ne_zero (fun n _ _ => n)
  · intro n hn h
    have hc := (mul_ne_zero_iff.mp h).1
    exact Fintype.mem_piFinset.mpr (fun i => mem_primaryElementBall.mpr
      ⟨(mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hn) i)).1,
        primaryAngularTupleCore_support ℓ A a b q η t V hZ hV n
          (fun j => (mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hn) j)).1) hc i⟩)
  · intro n _ _ m _ _ h
    exact h
  · intro n hn h
    refine ⟨n,Fintype.mem_piFinset.mpr (fun i => ?_),h,rfl⟩
    have hw := (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp h).2) i (Finset.mem_univ i)
    exact mem_primaryElementBall.mpr
      ⟨(mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hn) i)).1,
        (normPartitionWeight_nonzero_length (hX i) hw).1⟩
  · intro n _ _
    rfl

/-- The unsplit finite tuple sum is exactly the sum of its explicit smooth
pieces. No decomposition hypothesis is assumed. -/
theorem primaryAngularShortTupleSum_partition (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (V : ℝ → ℂ) {Z : ℝ} (hZ : 1 ≤ Z) (hV : ∀ x, 2 < x → V x = 0) :
    (∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Z)),
      primaryAngularTupleCore ℓ A a b q η t V Z n) =
      ∑ k : ι → Fin (normPartitionCount (2*Z)),
        primaryAngularShortTupleSum ℓ (fun i => (4/3:ℝ)^(k i).val) A a b q η
          (fun _ => normPartitionWeight) t V Z := by
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  rw [finite_sum_normTupleWeight (Fintype.piFinset (fun _ : ι => primaryElementBall (2*Z)))
    (primaryAngularTupleCore ℓ A a b q η t V Z) (fun n i => norm (n i))
    (fun n hn i => one_le_norm (primary_ne_zero
      (mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hn) i)).1))
    (fun n hn i => (mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hn) i)).2)
    (normPartitionCount_covers (by linarith : 1 ≤ 2*Z))]
  apply Finset.sum_congr rfl
  intro k _
  rw [primaryAngularShortTupleSum_common_ball ℓ _ A a b q η t V hZp hV
    (fun i => pow_pos (by norm_num) _)]
  apply Finset.sum_congr rfl
  intro n _
  unfold normTupleWeight
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  field_simp

end CubicFirstMoment

end

end OAI
