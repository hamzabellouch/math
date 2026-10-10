import Mathlib
import OAI.Analysis.IrrationalRotation.Model.ProductCharacters

namespace OAI

namespace InvariantProjection.ProductRotation

open scoped BigOperators ComplexConjugate
open Set Algebra Submodule

variable {ι : Type*}

@[simp] theorem characterPhase_zero (x : ι → UnitAddCircle) :
    characterPhase (0 : ι →₀ ℤ) x = 0 := by
  simp [characterPhase]

theorem characterPhase_add (v : ι →₀ ℤ) (x y : ι → UnitAddCircle) :
    characterPhase v (x + y) = characterPhase v x + characterPhase v y := by
  simp [characterPhase, Finsupp.sum_add]

theorem characterPhase_add_index (v w : ι →₀ ℤ) (x : ι → UnitAddCircle) :
    characterPhase (v + w) x = characterPhase v x + characterPhase w x := by
  classical
  simp [characterPhase, Finsupp.sum_add_index, add_zsmul]

@[simp] theorem characterPhase_single (i : ι) (n : ℤ) (x : ι → UnitAddCircle) :
    characterPhase (Finsupp.single i n) x = n • x i := by
  simp [characterPhase]

@[simp] theorem productCharacter_zero : productCharacter (0 : ι →₀ ℤ) = 1 := by
  ext x
  simp [productCharacter]

theorem productCharacter_add (v : ι →₀ ℤ) (x y : ι → UnitAddCircle) :
    productCharacter v (x + y) = productCharacter v x * productCharacter v y := by
  simp [productCharacter, characterPhase_add, AddCircle.toCircle_add]

theorem productCharacter_add_index (v w : ι →₀ ℤ) :
    productCharacter (v + w) = productCharacter v * productCharacter w := by
  ext x
  simp [productCharacter, characterPhase_add_index, AddCircle.toCircle_add]

@[simp] theorem productCharacter_single_one (i : ι) (x : ι → UnitAddCircle) :
    productCharacter (Finsupp.single i 1) x = (AddCircle.toCircle (x i) : ℂ) := by
  simp [productCharacter]

theorem productCharacter_neg (v : ι →₀ ℤ) :
    productCharacter (-v) = star (productCharacter v) := by
  ext x
  simp [productCharacter, characterPhase, Finsupp.sum_neg_index,
    Finsupp.sum_neg, AddCircle.toCircle_neg]
  exact Circle.coe_inv_eq_conj _

theorem productFourierAlgebra_separatesPoints :
    (productFourierAlgebra ι).SeparatesPoints := by
  classical
  intro x y hxy
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  refine ⟨_, ⟨productCharacter (Finsupp.single i 1),
    StarAlgebra.subset_adjoin ℂ _ ⟨Finsupp.single i 1, rfl⟩, rfl⟩, ?_⟩
  intro heq
  apply hi
  apply AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero
  apply Subtype.coe_injective
  simpa only [productCharacter_single_one] using heq

theorem productFourierAlgebra_closure_eq_top :
    (productFourierAlgebra ι).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    productFourierAlgebra_separatesPoints

theorem productFourierAlgebra_toSubmodule :
    (productFourierAlgebra ι).toSubalgebra.toSubmodule =
      Submodule.span ℂ (Set.range (productCharacter (ι := ι))) := by
  classical
  rw [productFourierAlgebra, StarAlgebra.adjoin_eq_span]
  congr 1
  apply Set.Subset.antisymm
  · intro f hf
    induction hf using Submonoid.closure_induction with
    | mem f hf =>
      rcases hf with hf | hf
      · exact hf
      · obtain ⟨v, hv⟩ := hf
        exact ⟨-v, by rw [productCharacter_neg, hv, star_star]⟩
    | one => exact ⟨0, productCharacter_zero⟩
    | mul f g hf hg ihf ihg =>
      obtain ⟨v, rfl⟩ := ihf
      obtain ⟨w, rfl⟩ := ihg
      exact ⟨v + w, productCharacter_add_index v w⟩
  · intro f hf
    exact Submonoid.subset_closure (Or.inl hf)

theorem span_productCharacter_closure_eq_top :
    (Submodule.span ℂ (Set.range (productCharacter (ι := ι)))).topologicalClosure = ⊤ := by
  rw [← productFourierAlgebra_toSubmodule]
  exact congr_arg (fun A : StarSubalgebra ℂ C((ι → UnitAddCircle), ℂ) =>
    A.toSubalgebra.toSubmodule) productFourierAlgebra_closure_eq_top

theorem mul_sum_ne_int (θ : ι → ℝ)
    (hθ : ∀ (v : ι →₀ ℤ) (k : ℤ),
      v.sum (fun i z => (z : ℝ) * θ i) = k → v = 0)
    {v : ι →₀ ℤ} (hv : v ≠ 0) {q : ℤ} (hq : q ≠ 0) (k : ℤ) :
    (q : ℝ) * v.sum (fun i z => (z : ℝ) * θ i) ≠ (k : ℝ) := by
  intro heq
  have hz : q • v = 0 := hθ (q • v) k (by
    rw [Finsupp.sum_smul_index (fun _ => by simp)]
    simpa only [Int.cast_mul, mul_assoc, Finsupp.sum, Finset.mul_sum] using heq)
  exact (smul_ne_zero hq hv) hz

theorem characterPhase_coe (v : ι →₀ ℤ) (θ : ι → ℝ) :
    characterPhase v (fun i => (θ i : UnitAddCircle)) =
      ((v.sum (fun i z => (z : ℝ) * θ i) : ℝ) : UnitAddCircle) := by
  change v.sum (fun i n => n • (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) (θ i)) =
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
      (v.sum (fun i z => (z : ℝ) * θ i))
  rw [map_finsuppSum]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [zsmul_eq_mul] using
    (map_zsmul (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) (v i) (θ i)).symm

theorem productCharacter_ne_one (θ : ι → ℝ)
    (hθ : ∀ (v : ι →₀ ℤ) (k : ℤ),
      v.sum (fun i z => (z : ℝ) * θ i) = k → v = 0)
    {v : ι →₀ ℤ} (hv : v ≠ 0) {q : ℤ} (hq : q ≠ 0) :
    productCharacter v (fun i => (((q : ℝ) * θ i : ℝ) : UnitAddCircle)) ≠ 1 := by
  intro heq
  have hphase : characterPhase v (fun i => (((q : ℝ) * θ i : ℝ) : UnitAddCircle)) = 0 := by
    apply AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero
    apply Subtype.coe_injective
    simpa [productCharacter] using heq
  rw [characterPhase_coe, AddCircle.coe_eq_zero_iff] at hphase
  obtain ⟨k, hk⟩ := hphase
  apply mul_sum_ne_int θ hθ hv hq k
  simpa only [Finsupp.sum, Finset.mul_sum, zsmul_eq_mul, mul_one,
    mul_left_comm, mul_assoc] using hk.symm

theorem product_rotation_free [Nonempty ι] (θ : ι → ℝ)
    (hθ : ∀ (v : ι →₀ ℤ) (k : ℤ),
      v.sum (fun i z => (z : ℝ) * θ i) = k → v = 0)
    {q : ℤ} (hq : q ≠ 0) (x : ι → UnitAddCircle) :
    (fun i => x i + (((q : ℝ) * θ i : ℝ) : UnitAddCircle)) ≠ x := by
  classical
  intro heq
  have ha : (fun i => (((q : ℝ) * θ i : ℝ) : UnitAddCircle)) = 0 := by
    funext i
    apply add_left_cancel (a := x i)
    simpa only [add_zero, Pi.zero_apply] using congrFun heq i
  let i : ι := Classical.choice inferInstance
  have hv : (Finsupp.single i (1 : ℤ)) ≠ 0 := by simp
  apply productCharacter_ne_one θ hθ hv hq
  rw [ha]
  simp [productCharacter, characterPhase]

theorem productCharacter_translation (v : ι →₀ ℤ) (θ : ι → ℝ) (q : ℤ)
    (x : ι → UnitAddCircle) :
    productCharacter v (fun i => x i + (((q : ℝ) * θ i : ℝ) : UnitAddCircle)) =
      productCharacter v (fun i => (((q : ℝ) * θ i : ℝ) : UnitAddCircle)) *
        productCharacter v x := by
  rw [mul_comm, ← productCharacter_add]
  congr 1

end InvariantProjection.ProductRotation

end OAI
