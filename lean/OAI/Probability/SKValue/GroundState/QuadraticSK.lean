import Mathlib
import OAI.Probability.SKValue.GroundState.AdaptiveColumns
import OAI.Probability.SKValue.GroundState.GramSchmidtLimit
import OAI.Probability.SKValue.GroundState.EmpiricalVectors

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG

noncomputable def spinVector (n : ℕ) (s : Fin n → Bool) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ spin (s i))

lemma spinVector_inner (n : ℕ) (s t : Fin n → Bool) :
    ⟪spinVector n s,spinVector n t⟫=∑ i,spin (s i)*spin (t i) := euclidean_inner_sum _ _

lemma spinVector_sqNorm (n : ℕ) (s : Fin n → Bool) : ‖spinVector n s‖^2=(n : ℝ) := by
  rw [←real_inner_self_eq_norm_sq,spinVector_inner]
  simp only [←sq,spin_sq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]

lemma spinVector_norm (n : ℕ) (s : Fin n → Bool) : ‖spinVector n s‖=Real.sqrt (n : ℝ) := by
  rw [←spinVector_sqNorm n s,Real.sqrt_sq (norm_nonneg _)]

lemma finiteMaximum_mul_nonneg {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) {c : ℝ} (hc : 0≤c) :
    finiteMaximum (fun i ↦ c*f i)=c*finiteMaximum f := by
  obtain ⟨i,hi⟩ := exists_finiteMaximum f
  apply le_antisymm
  · obtain ⟨j,hj⟩ := exists_finiteMaximum (fun i ↦ c*f i)
    rw [←hj]
    exact mul_le_mul_of_nonneg_left (le_finiteMaximum f j) hc
  · rw [←hi]
    exact le_finiteMaximum (fun i ↦ c*f i) i

lemma scaled_linearProcess {ι κ : Type*} [Fintype κ] (a : ι → κ → ℝ) (c : ℝ)
    (z : κ → ℝ) (i : ι) : linearProcess (fun i k ↦ c*a i k) z i=c*linearProcess a z i := by
  simp only [linearProcess,Finset.mul_sum,mul_assoc]

lemma quadratic_spin_distance {n : ℕ} (hn : 0<n) (s t : Fin n → Bool) :
    (∑ k,(quadraticCoeff (spinVector n s) k-quadraticCoeff (spinVector n t) k)^2)=
      ∑ k,(Real.sqrt (n : ℝ)*hamCoeff n s k-Real.sqrt (n : ℝ)*hamCoeff n t k)^2 := by
  have hs0 : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
  have hq (s : Fin n → Bool) :
      (∑ k,(quadraticCoeff (spinVector n s) k)^2)=(n : ℝ)^2/2 := by
    simp only [sq]
    rw [quadraticCoeff_inner,real_inner_self_eq_norm_sq,spinVector_sqNorm]
    ring
  rw [sq_distance_sum,hq,hq,quadraticCoeff_inner,spinVector_inner]
  have hs : (∑ k,(Real.sqrt (n : ℝ)*hamCoeff n s k-Real.sqrt (n : ℝ)*hamCoeff n t k)^2)=
      (n : ℝ)*(∑ k,(hamCoeff n s k-hamCoeff n t k)^2) := by
    simp only [←mul_sub,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n),Finset.mul_sum]
  rw [hs,hamCoeff_distance hn]
  field_simp
  ring

theorem quadraticValue_spin {n : ℕ} (hn : 0<n) :
    quadraticValue (spinVector n) (fun _ ↦ 0)=Real.sqrt (n : ℝ)*expectedMaximum n := by
  have he : (∫ z,finiteMaximum (fun s ↦ linearProcess (fun s ↦ quadraticCoeff (spinVector n s)) z s+0)
      ∂gaussianProduct (Fin n×Fin n))=
      ∫ z,finiteMaximum (fun s ↦ linearProcess (fun s k ↦ Real.sqrt (n : ℝ)*hamCoeff n s k) z s+0)
      ∂gaussianProduct (Fin n×Fin n) := by
    apply le_antisymm
    · exact expected_affine_max_le _ _ (fun _ ↦ 0) (fun s t ↦ (quadratic_spin_distance hn s t).le)
    · exact expected_affine_max_le _ _ (fun _ ↦ 0) (fun s t ↦ (quadratic_spin_distance hn s t).ge)
  unfold quadraticValue
  rw [he]
  simp only [add_zero,scaled_linearProcess,finiteMaximum_mul_nonneg _ (Real.sqrt_nonneg _)]
  rw [integral_const_mul]
  rfl

theorem finite_adaptive_SK_lower {n : ℕ} (hn : 0<n)
    (v : (j : ℕ) → ColumnHistory (Fin n) j → EuclideanSpace ℝ (Fin n))
    (hv : ∀ j,Measurable (v j)) (hu : ∀ j h,v j h=0 ∨ ⟪v j h,v j h⟫=1)
    (K : ℕ) (s : ColumnHistory (Fin n) K → (Fin n → Bool))
    (hs : Measurable (fun h ↦ adaptiveOffset (spinVector n) v K h (s h))) :
    (∫ h,adaptiveOffset (spinVector n) v K h (s h) ∂columnHistoryLaw (Fin n) K)/
      ((n : ℝ)*Real.sqrt (n : ℝ))≤groundStateSequence n := by
  have hh := adaptive_spin_lower (spinVector n) v hv hu (Real.sqrt (n : ℝ))
    (fun s ↦ (spinVector_norm n s).le) K s hs
  rw [quadraticValue_spin hn] at hh
  have hn' : (0 : ℝ)<n := by exact_mod_cast hn
  have pro : (0 : ℝ)<(n : ℝ)*Real.sqrt (n : ℝ) := mul_pos hn' (Real.sqrt_pos.mpr hn')
  apply (div_le_div_of_nonneg_right hh pro.le).trans_eq
  rw [groundStateSequence_eq]
  field_simp

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG

lemma orthogonalRemainder_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ℕ → E) (w : E) (j : ℕ) (c : ℝ) :
    orthogonalRemainder v (c • w) j=c • orthogonalRemainder v w j := by
  simp only [orthogonalRemainder,smul_sub,Finset.smul_sum,real_inner_smul_right,smul_smul]

lemma columnVector_smul {κ : Type*} [Fintype κ]
    (v w : EuclideanSpace ℝ κ) (c : ℝ) : columnVector v (c • w)=c^2 • columnVector v w := by
  simp only [columnVector,columnResidual,real_inner_smul_right,smul_sub,smul_add,smul_smul]
  module

lemma empiricalVector_scale {Ω : Type*} (f : Ω → ℝ) (x : ℕ → Ω) {n : ℕ} (hn : 0<n) :
    Real.sqrt (n : ℝ) • empiricalVector f x n=WithLp.toLp 2 (fun i : Fin n ↦ f (x i)) := by
  rw [empiricalVector,smul_smul,mul_inv_cancel₀,one_smul]
  exact Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn)

variable (K n : ℕ) (f : ℕ → (Fin (K+1) → ℝ) → ℝ)
  (ha : ∀ l x y,(∀ i : Fin (K+1),i.val≤l → x i=y i) → f l x=f l y)
  (x : ℕ → (Fin (K+1) → ℝ))

include ha in
lemma predictableResidual_rows {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → EuclideanSpace ℝ (Fin n)) (j : ℕ) (s : ι) :
    adaptiveResidual w (predictableDirection K n f) (j+1)
      (rowHistory K n (fun i ↦ x i) (j+1)) s=
    orthogonalRemainder (gramSchmidtNormed ℝ (fun l ↦ empiricalVector (f l) x n)) (w s) j := by
  induction j with
  | zero => simp [adaptiveResidual,predictableDirection,columnResidual,orthogonalRemainder]
  | succ j ih =>
    change columnResidual (predictableDirection K n f (j+1)
      (rowHistory K n (fun i ↦ x i) (j+1)))
      (adaptiveResidual w (predictableDirection K n f) (j+1)
        (rowHistory K n (fun i ↦ x i) (j+1)) s)=_
    rw [predictableDirection_rows K n f ha x j,ih]
    apply columnResidual_orthogonalRemainder
    intro i hi
    exact gramSchmidtNormed_pairwise_orthogonal _ (Ne.symm (Nat.ne_of_lt hi))

include ha in
lemma predictableOffset_rows {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → EuclideanSpace ℝ (Fin n)) (J : ℕ) (s : ι) :
    adaptiveOffset w (predictableDirection K n f) (J+1)
      (rowHistory K n (fun i ↦ x i) (J+1)) s=
      ∑ j∈Finset.range J,
        ⟪columnVector (gramSchmidtNormed ℝ (fun l ↦ empiricalVector (f l) x n) j)
          (orthogonalRemainder (gramSchmidtNormed ℝ (fun l ↦ empiricalVector (f l) x n)) (w s) j),
          WithLp.toLp 2 (rowColumn K n (fun i ↦ x i) (j+1))⟫ := by
  induction J with
  | zero => simp [adaptiveOffset,predictableDirection,columnVector,columnResidual,linearProcess]
  | succ J ih =>
    change adaptiveOffset w (predictableDirection K n f) (J+1)
      (rowHistory K n (fun i ↦ x i) (J+1)) s+
      linearProcess (fun i k ↦ columnVector
        (predictableDirection K n f (J+1) (rowHistory K n (fun i ↦ x i) (J+1)))
        (adaptiveResidual w (predictableDirection K n f) (J+1)
          (rowHistory K n (fun i ↦ x i) (J+1)) i) k)
        (rowColumn K n (fun i ↦ x i) (J+1)) s=_
    rw [ih,Finset.sum_range_succ,predictableDirection_rows K n f ha x J]
    congr 1
    unfold linearProcess
    dsimp only
    rw [predictableResidual_rows K n f ha x w J s]
    rw [euclidean_inner_sum]

noncomputable def empiricalColumnEnergy (F : (Fin (K+1) → ℝ) → ℝ) (j : ℕ) : ℝ :=
  ⟪columnVector (gramSchmidtNormed ℝ (fun l ↦ empiricalVector (f l) x n) j)
      (orthogonalRemainder (gramSchmidtNormed ℝ (fun l ↦ empiricalVector (f l) x n))
        (empiricalVector F x n) j),
    empiricalVector (fun y ↦ if hj : j+1<K+1 then y ⟨j+1,hj⟩ else 0) x n⟫

include ha in
lemma normalizedOffset_rows (hn : 0<n) (F : (Fin (K+1) → ℝ) → Bool) :
    adaptiveOffset (spinVector n) (predictableDirection K n f) (K+1)
      (rowHistory K n (fun i ↦ x i) (K+1)) (fun i ↦ F (x i))/
      ((n : ℝ)*Real.sqrt (n : ℝ))=
      ∑ j∈Finset.range K,empiricalColumnEnergy K n f x (fun y ↦ spin (F y)) j := by
  rw [predictableOffset_rows K n f ha x (spinVector n) K]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hw : spinVector n (fun i ↦ F (x i))=
      Real.sqrt (n : ℝ) • empiricalVector (fun y ↦ spin (F y)) x n :=
    (empiricalVector_scale (fun y ↦ spin (F y)) x hn).symm
  have hz : WithLp.toLp 2 (rowColumn K n (fun i ↦ x i) (j+1))=
      Real.sqrt (n : ℝ) • empiricalVector
        (fun y ↦ if hj : j+1<K+1 then y ⟨j+1,hj⟩ else 0) x n :=
    by
    change (WithLp.toLp 2 (fun i : Fin n ↦ if hj : j+1<K+1 then x i ⟨j+1,hj⟩ else 0)) = _
    exact (empiricalVector_scale (fun y : Fin (K+1) → ℝ ↦ if hj : j+1<K+1 then y ⟨j+1,hj⟩ else 0) x hn).symm
  rw [hw,hz,orthogonalRemainder_smul,columnVector_smul,real_inner_smul_left,real_inner_smul_right,
    Real.sq_sqrt (Nat.cast_nonneg n)]
  unfold empiricalColumnEnergy
  have hn' : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
  have hs : Real.sqrt (n : ℝ)≠0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn)
  field_simp

end SKValueG

end

end OAI
