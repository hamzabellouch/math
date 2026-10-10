import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.CorrectionOperator
import OAI.Algebra.AlgebraicObstruction.TaylorRemainder

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries Matrix
open scoped Classical
variable {R α ι σ : Type*} [CommRing R] [Fintype α] [Fintype ι] [Finite σ]

def shiftedGraph (x : (α ⊕ ι) → MvPowerSeries σ R) (δ : ι → MvPowerSeries σ R) :
    (α ⊕ ι) → MvPowerSeries σ R :=
  Sum.elim (fun a => x (.inl a)) (fun i => x (.inr i) + δ i)

omit [Fintype α] [Fintype ι] [Finite σ] in
theorem extended_centered [Fintype α] [Fintype ι] [Finite σ]
    (x : (α ⊕ ι) → MvPowerSeries σ R) (δ : ι → MvPowerSeries σ R)
    (hx : ∀ i, constantCoeff (x i) = 0) (hδ : ∀ i, constantCoeff (δ i) = 0) :
    ∀ j, constantCoeff (Sum.elim x δ j) = 0 := by
  intro j; cases j with
  | inl j => exact hx j
  | inr j => exact hδ j

omit [Fintype α] [Fintype ι] [Finite σ] in
theorem shiftedGraph_centered [Fintype α] [Fintype ι] [Finite σ]
    (x : (α ⊕ ι) → MvPowerSeries σ R) (δ : ι → MvPowerSeries σ R)
    (hx : ∀ i, constantCoeff (x i) = 0) (hδ : ∀ i, constantCoeff (δ i) = 0) :
    ∀ j, constantCoeff (shiftedGraph x δ j) = 0 := by
  intro j; cases j <;> simp [shiftedGraph, hx, hδ]

theorem subst_extended_base (x : (α ⊕ ι) → MvPowerSeries σ R) (δ : ι → MvPowerSeries σ R)
    (hx : ∀ i, constantCoeff (x i) = 0) (hδ : ∀ i, constantCoeff (δ i) = 0)
    (f : MvPowerSeries (α ⊕ ι) R) :
    subst (Sum.elim x δ) (subst (baseArguments (R := R)) f) = subst x f := by
  let hs := hasSubst_of_constantCoeff_zero (extended_centered x δ hx hδ)
  rw [subst_comp_subst_apply (R := R) (hasSubst_of_constantCoeff_zero (baseArguments_centered (R := R) (α := α) (ι := ι))) hs]
  simp only [baseArguments, subst_X hs, Sum.elim_inl]

theorem subst_extended_shifted (x : (α ⊕ ι) → MvPowerSeries σ R) (δ : ι → MvPowerSeries σ R)
    (hx : ∀ i, constantCoeff (x i) = 0) (hδ : ∀ i, constantCoeff (δ i) = 0)
    (f : MvPowerSeries (α ⊕ ι) R) :
    subst (Sum.elim x δ) (subst (shiftedArguments (R := R)) f) = subst (shiftedGraph x δ) f := by
  let hs := hasSubst_of_constantCoeff_zero (extended_centered x δ hx hδ)
  rw [subst_comp_subst_apply (R := R) (hasSubst_of_constantCoeff_zero (shiftedArguments_centered (R := R) (α := α) (ι := ι))) hs]
  congr 1
  funext i
  cases i <;> simp only [shiftedArguments, shiftedGraph, Sum.elim_inl, Sum.elim_inr,
    subst_add hs, subst_X hs]

def gradientValue (f : MvPowerSeries (α ⊕ ι) R) (x : (α ⊕ ι) → MvPowerSeries σ R) :
    ι → MvPowerSeries σ R := fun i => subst x (MvPowerSeries.pderiv (R := R) (Sum.inr i) f)

theorem gradientValue_vanishes (f : MvPowerSeries (α ⊕ ι) R) (hf : Vanishes 3 f)
    (x : (α ⊕ ι) → MvPowerSeries σ R) (hx : ∀ i, constantCoeff (x i) = 0) :
    ∀ i, Vanishes 2 (gradientValue f x i) := by
  intro i
  exact (hf.pderiv _).subst x hx

theorem evaluated_remainder (f : MvPowerSeries (α ⊕ ι) R)
    (H : Matrix ι ι (MvPowerSeries (Extended (α := α)) R))
    (hH : subst shiftedArguments f = subst baseArguments f +
        (∑ i, X (Sum.inr i) * subst baseArguments (MvPowerSeries.pderiv (R := R) (Sum.inr i) f)) +
        ∑ i, ∑ j, X (Sum.inr i) * H i j * X (Sum.inr j))
    (x : (α ⊕ ι) → MvPowerSeries σ R) (δ : ι → MvPowerSeries σ R)
    (hx : ∀ i, constantCoeff (x i) = 0) (hδ : ∀ i, constantCoeff (δ i) = 0) :
    subst (shiftedGraph x δ) f = subst x f + dotProduct (gradientValue f x) δ +
      dotProduct δ ((fun i j => subst (Sum.elim x δ) (H i j)) *ᵥ δ) := by
  let hs := hasSubst_of_constantCoeff_zero (extended_centered x δ hx hδ)
  have hh := congrArg (substAlgHom hs) hH
  simp only [map_add, map_sum, map_mul, substAlgHom_apply, subst_X hs,
    Sum.elim_inr, subst_extended_shifted x δ hx hδ, subst_extended_base x δ hx hδ] at hh
  rw [hh]
  congr 2
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem evaluated_first_remainder (f : MvPowerSeries (α ⊕ ι) R)
    (x : (α ⊕ ι) → MvPowerSeries σ R) (δ : ι → MvPowerSeries σ R)
    (hx : ∀ i, constantCoeff (x i) = 0) (hδ : ∀ i, constantCoeff (δ i) = 0) :
    ∃ q : ι → MvPowerSeries σ R,
      subst (shiftedGraph x δ) f - subst x f = dotProduct q δ := by
  obtain ⟨q,_,hq⟩ := exists_first_remainder f
  let hs := hasSubst_of_constantCoeff_zero (extended_centered x δ hx hδ)
  refine ⟨fun i => subst (Sum.elim x δ) (q i), ?_⟩
  have hh := congrArg (substAlgHom hs) hq
  simpa only [map_sub, map_sum, map_mul, substAlgHom_apply, subst_X hs,
    Sum.elim_inr, subst_extended_shifted x δ hx hδ, subst_extended_base x δ hx hδ,
    dotProduct] using hh

end BoundaryOnly.FormalObstruction.FormalCorrection

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries Matrix
open scoped Classical
variable {R α ι σ : Type*} [CommRing R] [Fintype α] [Fintype ι] [Finite σ]

omit [Finite σ] in
theorem mulVec_vanishes [Finite σ] {n : ℕ} (B : Matrix ι ι (MvPowerSeries σ R))
    (v : ι → MvPowerSeries σ R) (hv : ∀ i, Vanishes n (v i)) :
    ∀ i, Vanishes n ((B *ᵥ v) i) := by
  intro i
  exact Vanishes.sum Finset.univ _ (fun j _ => (hv j).mul_left (B i j))

omit [Finite σ] in
theorem quadratic_transpose [Finite σ] (B H : Matrix ι ι (MvPowerSeries σ R))
    (v : ι → MvPowerSeries σ R) :
    dotProduct (B *ᵥ v) (H *ᵥ (B *ᵥ v)) =
      dotProduct v ((B.transpose * H * B) *ᵥ v) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_transpose_mulVec, dotProduct_comm]

omit [Fintype α] [Fintype ι] [Finite σ] in
theorem shiftedGraph_jet [Fintype α] [Fintype ι] [Finite σ]
    {n : ℕ} (x : (α ⊕ ι) → MvPowerSeries σ R)
    (δ : ι → MvPowerSeries σ R) (hδ : ∀ i, Vanishes n (δ i)) :
    ∀ i, Jet n (shiftedGraph x δ i) (x i) := by
  intro i
  cases i with
  | inl a => exact Jet.refl _ _
  | inr i =>
    change Vanishes n ((x (.inr i) + δ i) - x (.inr i))
    simpa only [add_sub_cancel_left] using hδ i

theorem exists_zero_correction (f : MvPowerSeries (α ⊕ ι) R) (hf : Vanishes 3 f)
    (x : (α ⊕ ι) → MvPowerSeries σ R) (hx : ∀ i, constantCoeff (x i) = 0)
    (b : Matrix ι ι (MvPowerSeries σ R))
    (hg : subst x f = dotProduct (gradientValue f x) (b *ᵥ gradientValue f x)) :
    ∃ B : Matrix ι ι (MvPowerSeries σ R),
      subst (shiftedGraph x (B *ᵥ gradientValue f x)) f = 0 ∧
      (∀ i, Jet 2 (shiftedGraph x (B *ᵥ gradientValue f x) i) (x i)) := by
  obtain ⟨H,hH,hTaylor⟩ := exists_taylor_remainder f hf
  let v := gradientValue f x
  have hv : ∀ i, Vanishes 2 (v i) := gradientValue_vanishes f hf x hx
  obtain ⟨B,hB⟩ := exists_correction_matrix b H x v hH hx hv
  have hδ := mulVec_vanishes B v hv
  have hδ0 : ∀ i, constantCoeff ((B *ᵥ v) i) = 0 :=
    fun i => Vanishes.one_iff.mp ((hδ i).mono (by omega))
  refine ⟨B, ?_, shiftedGraph_jet x _ hδ⟩
  have ht := evaluated_remainder f H hTaylor x (B *ᵥ v) hx hδ0
  change subst (shiftedGraph x (B *ᵥ v)) f = _ at ht ⊢
  have heval : (fun i j => subst (Sum.elim x (B *ᵥ v)) (H i j)) = remainderValue H x v B := by
    funext i j
    unfold remainderValue
    congr 1
    funext k
    cases k <;> rfl
  rw [heval, quadratic_transpose B, hg] at ht
  have hz : b + B + B.transpose * remainderValue H x v B * B = 0 := by
    change B = -b - B.transpose * remainderValue H x v B * B at hB
    calc
      _ = b + (-b - B.transpose * remainderValue H x v B * B) +
        B.transpose * remainderValue H x v B * B := congrArg (fun A => b+A+B.transpose * remainderValue H x v B * B) hB
      _ = 0 := by abel
  rw [ht]
  change dotProduct v (b *ᵥ v) + dotProduct v (B *ᵥ v) +
    dotProduct v ((B.transpose * remainderValue H x v B * B) *ᵥ v) = 0
  rw [← dotProduct_add, ← add_mulVec, ← dotProduct_add, ← add_mulVec, hz]
  simp

end BoundaryOnly.FormalObstruction.FormalCorrection

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries Matrix
open scoped Classical
variable {R α ι σ : Type*} [CommRing R] [Fintype α] [Fintype ι] [Finite σ]

theorem evaluated_gradient_remainder (f : MvPowerSeries (α ⊕ ι) R) (hf : Vanishes 3 f)
    (x : (α ⊕ ι) → MvPowerSeries σ R) (δ : ι → MvPowerSeries σ R)
    (hx : ∀ i, constantCoeff (x i) = 0) (hδ : ∀ i, constantCoeff (δ i) = 0) :
    ∃ G : Matrix ι ι (MvPowerSeries σ R), (∀ i j, Vanishes 1 (G i j)) ∧
      gradientValue f (shiftedGraph x δ) = gradientValue f x + G *ᵥ δ := by
  obtain ⟨G,hG,hgrad⟩ := exists_gradient_remainder f hf
  let hs := hasSubst_of_constantCoeff_zero (extended_centered x δ hx hδ)
  refine ⟨fun i j => subst (Sum.elim x δ) (G i j), ?_, ?_⟩
  · intro i j
    exact (hG i j).subst _ (extended_centered x δ hx hδ)
  · funext i
    have hh := congrArg (substAlgHom hs) (hgrad i)
    simp only [map_sub, map_sum, map_mul, substAlgHom_apply, subst_X hs,
      Sum.elim_inr, subst_extended_shifted x δ hx hδ, subst_extended_base x δ hx hδ] at hh
    change gradientValue f (shiftedGraph x δ) i = gradientValue f x i + _
    change gradientValue f (shiftedGraph x δ) i - gradientValue f x i = _ at hh
    exact sub_eq_iff_eq_add.mp hh |>.trans (add_comm _ _)

omit [Finite σ] in
theorem matrix_one_add_isUnit [Finite σ] (M : Matrix ι ι (MvPowerSeries σ R))
    (hM : ∀ i j, Vanishes 1 (M i j)) : IsUnit (1 + M) := by
  have hc : (1 + M).map (constantCoeff (σ := σ) (R := R)) = 1 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, map_add, Vanishes.one_iff.mp (hM i j), add_zero]
    simp only [Matrix.one_apply, apply_ite, map_one, map_zero]
    split_ifs <;> rfl
  apply ((1+M).isUnit_iff_isUnit_det).mpr
  apply MvPowerSeries.isUnit_iff_constantCoeff.mpr
  rw [RingHom.map_det]
  change IsUnit (((1+M).map (constantCoeff (σ := σ) (R := R))).det)
  rw [hc, Matrix.det_one]
  exact isUnit_one

theorem gradient_transport (f : MvPowerSeries (α ⊕ ι) R) (hf : Vanishes 3 f)
    (x : (α ⊕ ι) → MvPowerSeries σ R) (hx : ∀ i, constantCoeff (x i) = 0)
    (B : Matrix ι ι (MvPowerSeries σ R)) :
    ∃ A : Matrix ι ι (MvPowerSeries σ R), IsUnit A ∧
      gradientValue f (shiftedGraph x (B *ᵥ gradientValue f x)) = A *ᵥ gradientValue f x := by
  let v := gradientValue f x
  have hv : ∀ i, Vanishes 2 (v i) := gradientValue_vanishes f hf x hx
  have hδ := mulVec_vanishes B v hv
  have hδ0 : ∀ i, constantCoeff ((B *ᵥ v) i) = 0 :=
    fun i => Vanishes.one_iff.mp ((hδ i).mono (by omega))
  obtain ⟨G,hG,hgrad⟩ := evaluated_gradient_remainder f hf x (B *ᵥ v) hx hδ0
  have hM : ∀ i j, Vanishes 1 ((G*B) i j) := by
    intro i j
    exact Vanishes.sum Finset.univ _ (fun k _ => (hG i k).mul_right (B k j))
  refine ⟨1+G*B, matrix_one_add_isUnit _ hM, ?_⟩
  rw [hgrad, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]

def vectorIdeal (v : ι → MvPowerSeries σ R) : Ideal (MvPowerSeries σ R) :=
  Ideal.span (Set.range v)

omit [Fintype ι] [Finite σ] in
theorem vector_mem_vectorIdeal [Fintype ι] [Finite σ]
    (v : ι → MvPowerSeries σ R) (i : ι) :
    v i ∈ vectorIdeal v := Ideal.subset_span ⟨i,rfl⟩

theorem mulVec_mem_vectorIdeal (A : Matrix ι ι (MvPowerSeries σ R))
    (v : ι → MvPowerSeries σ R) (i : ι) : (A *ᵥ v) i ∈ vectorIdeal v := by
  apply Ideal.sum_mem
  intro j _
  exact Ideal.mul_mem_left _ _ (vector_mem_vectorIdeal v j)

theorem vectorIdeal_mulVec_le (A : Matrix ι ι (MvPowerSeries σ R))
    (v : ι → MvPowerSeries σ R) : vectorIdeal (A *ᵥ v) ≤ vectorIdeal v := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact mulVec_mem_vectorIdeal A v i

theorem vectorIdeal_unit_mulVec (A : Matrix ι ι (MvPowerSeries σ R))
    (hA : IsUnit A) (v : ι → MvPowerSeries σ R) : vectorIdeal (A *ᵥ v) = vectorIdeal v := by
  obtain ⟨u,rfl⟩ := hA
  apply le_antisymm (vectorIdeal_mulVec_le _ v)
  have h := vectorIdeal_mulVec_le (↑(u⁻¹) : Matrix ι ι (MvPowerSeries σ R)) ((↑u) *ᵥ v)
  simpa only [mulVec_mulVec, Units.inv_mul, one_mulVec] using h

theorem gradient_ideal_transport (f : MvPowerSeries (α ⊕ ι) R) (hf : Vanishes 3 f)
    (x : (α ⊕ ι) → MvPowerSeries σ R) (hx : ∀ i, constantCoeff (x i) = 0)
    (B : Matrix ι ι (MvPowerSeries σ R)) :
    vectorIdeal (gradientValue f (shiftedGraph x (B *ᵥ gradientValue f x))) =
      vectorIdeal (gradientValue f x) := by
  obtain ⟨A,hA,h⟩ := gradient_transport f hf x hx B
  rw [h]
  exact vectorIdeal_unit_mulVec A hA _

theorem scalar_transport_mem (g : MvPowerSeries (α ⊕ ι) R)
    (x : (α ⊕ ι) → MvPowerSeries σ R) (hx : ∀ i, constantCoeff (x i) = 0)
    (v : ι → MvPowerSeries σ R) (hv : ∀ i, Vanishes 2 (v i))
    (B : Matrix ι ι (MvPowerSeries σ R)) :
    subst (shiftedGraph x (B *ᵥ v)) g - subst x g ∈ vectorIdeal v := by
  have hδ := mulVec_vanishes B v hv
  have hδ0 : ∀ i, constantCoeff ((B *ᵥ v) i) = 0 :=
    fun i => Vanishes.one_iff.mp ((hδ i).mono (by omega))
  obtain ⟨q,hq⟩ := evaluated_first_remainder g x (B *ᵥ v) hx hδ0
  rw [hq]
  apply Ideal.sum_mem
  intro i _
  exact Ideal.mul_mem_left _ _ (mulVec_mem_vectorIdeal B v i)

end BoundaryOnly.FormalObstruction.FormalCorrection

end

end OAI
