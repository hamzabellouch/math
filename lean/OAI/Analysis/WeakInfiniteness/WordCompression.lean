import Mathlib
import OAI.Analysis.WeakInfiniteness.TensorCompression

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint

namespace WeakPureInfiniteness

section Words

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def wordEval (T : ι → E →L[ℂ] E) : List ι → E →L[ℂ] E
  | [] => ContinuousLinearMap.id ℂ E
  | i :: w => (T i).comp (wordEval T w)

lemma norm_wordEval_le_one (T : ι → E →L[ℂ] E) (hT : ∀ i, ‖T i‖ ≤ 1)
    (w : List ι) : ‖wordEval T w‖ ≤ 1 := by
  induction w with
  | nil => exact ContinuousLinearMap.norm_id_le
  | cons i w ih =>
    calc
      ‖wordEval T (i :: w)‖ ≤ ‖T i‖ * ‖wordEval T w‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul (hT i) ih (norm_nonneg _) (by positivity)
      _ = 1 := one_mul _

lemma norm_wordEval_intertwining_le
    (T : ι → F →L[ℂ] F) (D : ι → E →L[ℂ] E) (J : E →L[ℂ] F)
    (hT : ∀ i, ‖T i‖ ≤ 1) (hD : ∀ i, ‖D i‖ ≤ 1)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hJ : ∀ i, ‖(T i).comp J - J.comp (D i)‖ ≤ θ)
    (w : List ι) :
    ‖(wordEval T w).comp J - J.comp (wordEval D w)‖ ≤ w.length * θ := by
  induction w with
  | nil => simp [wordEval]
  | cons i w ih =>
    have hid :
        (wordEval T (i :: w)).comp J - J.comp (wordEval D (i :: w)) =
          (T i).comp ((wordEval T w).comp J - J.comp (wordEval D w)) +
          ((T i).comp J - J.comp (D i)).comp (wordEval D w) := by
      simp only [wordEval, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
        ContinuousLinearMap.comp_assoc]
      abel
    rw [hid]
    calc
      _ ≤ ‖(T i).comp ((wordEval T w).comp J - J.comp (wordEval D w))‖ +
          ‖((T i).comp J - J.comp (D i)).comp (wordEval D w)‖ := norm_add_le _ _
      _ ≤ ‖T i‖ * ‖(wordEval T w).comp J - J.comp (wordEval D w)‖ +
          ‖(T i).comp J - J.comp (D i)‖ * ‖wordEval D w‖ := by
        exact add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
          (ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ 1 * (w.length * θ) + θ * 1 := by
        apply add_le_add
        · exact mul_le_mul (hT i) ih (norm_nonneg _) (by positivity)
        · exact mul_le_mul (hJ i) (norm_wordEval_le_one D hD w) (norm_nonneg _) hθ
      _ = (i :: w).length * θ := by simp [Nat.cast_add, add_mul]

end Words

section FiniteCompression

variable {ι S H : Type*} [Finite ι] [Finite S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def wordSpace (T : ι → H →L[ℂ] H) (ξ : S → H) : ℕ → Submodule ℂ H
  | 0 => Submodule.span ℂ (Set.range ξ)
  | m + 1 => wordSpace T ξ m ⊔ ⨆ i, (wordSpace T ξ m).map (T i).toLinearMap

instance wordSpace_finiteDimensional (T : ι → H →L[ℂ] H) (ξ : S → H) (m : ℕ) :
    FiniteDimensional ℂ (wordSpace T ξ m) := by
  induction m with
  | zero => exact FiniteDimensional.span_of_finite ℂ (Set.finite_range ξ)
  | succ m ih =>
    change FiniteDimensional ℂ
      ↥(wordSpace T ξ m ⊔ ⨆ i, (wordSpace T ξ m).map (T i).toLinearMap)
    let := ih
    infer_instance

omit [Finite ι] [Finite S] in
lemma wordSpace_mono (T : ι → H →L[ℂ] H) (ξ : S → H) : Monotone (wordSpace T ξ) := by
  apply monotone_nat_of_le_succ
  intro m
  exact le_sup_left

omit [Finite ι] [Finite S] in
lemma wordEval_mem_wordSpace (T : ι → H →L[ℂ] H) (ξ : S → H) (w : List ι) (j : S) :
    wordEval T w (ξ j) ∈ wordSpace T ξ w.length := by
  induction w with
  | nil => exact Submodule.subset_span (Set.mem_range_self j)
  | cons i w ih =>
    apply (show (⨆ i, (wordSpace T ξ w.length).map (T i).toLinearMap) ≤
      wordSpace T ξ (i :: w).length from le_sup_right)
    apply (le_iSup (fun i => (wordSpace T ξ w.length).map (T i).toLinearMap) i)
    exact Submodule.mem_map.mpr ⟨_, ih, rfl⟩

omit [Finite ι] [Finite S] in
lemma wordEval_mem_wordSpace_of_length_le (T : ι → H →L[ℂ] H) (ξ : S → H)
    (w : List ι) (j : S) {m : ℕ} (hw : w.length ≤ m) :
    wordEval T w (ξ j) ∈ wordSpace T ξ m :=
  wordSpace_mono T ξ hw (wordEval_mem_wordSpace T ξ w j)

omit [Finite ι] [Finite S] in
lemma testVector_mem_wordSpace (T : ι → H →L[ℂ] H) (ξ : S → H) (m : ℕ) (j : S) :
    ξ j ∈ wordSpace T ξ m :=
  wordEval_mem_wordSpace_of_length_le T ξ [] j (Nat.zero_le m)

omit [Finite ι] [Finite S] in
lemma adjoint_compress [CompleteSpace H] (K : Submodule ℂ H) [CompleteSpace K]
    (T : H →L[ℂ] H) :
    (compress K T).adjoint = compress K T.adjoint := by
  simp only [compress, ContinuousLinearMap.adjoint_comp, Submodule.adjoint_subtypeL,
    Submodule.adjoint_orthogonalProjectionOnto, ContinuousLinearMap.comp_assoc]

omit [Finite ι] [Finite S] in
lemma compressed_wordEval (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (T : ι → H →L[ℂ] H) (ξ : H) (hξ : ξ ∈ K) (w : List ι)
    (hmem : ∀ u : List ι, u.length ≤ w.length → wordEval T u ξ ∈ K) :
    (wordEval (fun i => compress K (T i)) w ⟨ξ, hξ⟩ : H) = wordEval T w ξ := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (K.orthogonalProjectionOnto
      (T i (wordEval (fun i => compress K (T i)) w ⟨ξ, hξ⟩ : H)) : H) = _
    rw [ih (fun u hu => hmem u (by simpa using Nat.le_succ_of_le hu))]
    exact Submodule.starProjection_eq_self_iff.mpr (hmem (i :: w) le_rfl)

lemma wordSpace_compression_exact (T : ι → H →L[ℂ] H) (ξ : S → H) (m : ℕ)
    (w : List ι) (hw : w.length ≤ m) (j : S) :
    (wordEval (fun i => compress (wordSpace T ξ m) (T i)) w
      ⟨ξ j, testVector_mem_wordSpace T ξ m j⟩ : H) = wordEval T w (ξ j) := by
  apply compressed_wordEval
  intro u hu
  exact wordEval_mem_wordSpace_of_length_le T ξ u j (hu.trans hw)

end FiniteCompression

section Amplification

open scoped TensorProduct

variable {ι K E F : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

noncomputable def amplifiedPolynomial (s : Finset (List ι))
    (B : List ι → K →L[ℂ] K) (T : ι → E →L[ℂ] E) :
    (K ⊗[ℂ] E) →L[ℂ] (K ⊗[ℂ] E) :=
  ∑ w ∈ s, TensorProduct.mapL (B w) (wordEval T w)

lemma amplifiedPolynomial_intertwining
    (s : Finset (List ι)) (B : List ι → K →L[ℂ] K)
    (T : ι → F →L[ℂ] F) (D : ι → E →L[ℂ] E) (J : E →L[ℂ] F) :
    (amplifiedPolynomial s B T).comp (J.lTensor K) -
      (J.lTensor K).comp (amplifiedPolynomial s B D) =
      ∑ w ∈ s, TensorProduct.mapL (B w)
        ((wordEval T w).comp J - J.comp (wordEval D w)) := by
  simp only [amplifiedPolynomial, ContinuousLinearMap.finsetSum_comp, ContinuousLinearMap.comp_finsetSum,
    ContinuousLinearMap.mapL_comp_lTensor, ContinuousLinearMap.lTensor_comp_mapL,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  simp only [TensorProduct.mapL, ContinuousLinearMap.lTensor_sub, ContinuousLinearMap.comp_sub]

lemma norm_amplifiedPolynomial_intertwining_le
    (s : Finset (List ι)) (B : List ι → K →L[ℂ] K)
    (T : ι → F →L[ℂ] F) (D : ι → E →L[ℂ] E) (J : E →L[ℂ] F)
    (hT : ∀ i, ‖T i‖ ≤ 1) (hD : ∀ i, ‖D i‖ ≤ 1)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hJ : ∀ i, ‖(T i).comp J - J.comp (D i)‖ ≤ θ) :
    ‖(amplifiedPolynomial s B T).comp (J.lTensor K) -
      (J.lTensor K).comp (amplifiedPolynomial s B D)‖ ≤
      (∑ w ∈ s, ‖B w‖ * w.length) * θ := by
  rw [amplifiedPolynomial_intertwining]
  calc
    _ ≤ ∑ w ∈ s, ‖TensorProduct.mapL (B w)
        ((wordEval T w).comp J - J.comp (wordEval D w))‖ := by
      have hs := norm_sum_le s (fun w => TensorProduct.mapL (B w)
        ((wordEval T w).comp J - J.comp (wordEval D w)))
      exact hs
    _ ≤ ∑ w ∈ s, ‖B w‖ * (w.length * θ) := by
      apply Finset.sum_le_sum
      intro w hw
      have hm := TensorProduct.norm_mapL_le (B w)
        ((wordEval T w).comp J - J.comp (wordEval D w))
      have hw := norm_wordEval_intertwining_le T D J hT hD hθ hJ w
      exact hm.trans (mul_le_mul_of_nonneg_left hw (norm_nonneg (B w)))
    _ = _ := by simp only [← mul_assoc, Finset.sum_mul]

lemma norm_amplifiedPolynomial_le
    (s : Finset (List ι)) (B : List ι → K →L[ℂ] K)
    (T : ι → F →L[ℂ] F) (D : ι → E →L[ℂ] E) (J : E →ₗᵢ[ℂ] F)
    (hT : ∀ i, ‖T i‖ ≤ 1) (hD : ∀ i, ‖D i‖ ≤ 1)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hJ : ∀ i, ‖(T i).comp J.toContinuousLinearMap -
        J.toContinuousLinearMap.comp (D i)‖ ≤ θ) :
    ‖amplifiedPolynomial s B D‖ ≤ ‖amplifiedPolynomial s B T‖ +
      (∑ w ∈ s, ‖B w‖ * w.length) * θ := by
  let Q := (J.lTensor K).toContinuousLinearMap
  have hQ : ‖Q‖ ≤ 1 := (J.lTensor K).norm_toContinuousLinearMap_le
  have herr : ‖(amplifiedPolynomial s B T).comp Q -
      Q.comp (amplifiedPolynomial s B D)‖ ≤ (∑ w ∈ s, ‖B w‖ * w.length) * θ :=
    by
      simpa only [Q, LinearIsometry.toContinuousLinearMap_lTensor] using
        norm_amplifiedPolynomial_intertwining_le s B T D J.toContinuousLinearMap hT hD hθ hJ
  calc
    _ = ‖Q.comp (amplifiedPolynomial s B D)‖ :=
      ((J.lTensor K).norm_toContinuousLinearMap_comp).symm
    _ ≤ ‖(amplifiedPolynomial s B T).comp Q‖ +
        ‖(amplifiedPolynomial s B T).comp Q - Q.comp (amplifiedPolynomial s B D)‖ :=
      by
        rw [norm_sub_rev ((amplifiedPolynomial s B T).comp Q)]
        exact norm_le_norm_add_norm_sub' (Q.comp (amplifiedPolynomial s B D))
          ((amplifiedPolynomial s B T).comp Q)
    _ ≤ ‖amplifiedPolynomial s B T‖ * ‖Q‖ +
        (∑ w ∈ s, ‖B w‖ * w.length) * θ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) herr
    _ ≤ _ := add_le_add
      (mul_le_of_le_one_right (norm_nonneg (amplifiedPolynomial s B T)) hQ) le_rfl

end Amplification

section FiniteAmplificationTests

open scoped TensorProduct

variable {ι S K H : Type*} [Finite ι] [Fintype S]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [Finite ι] [Fintype S] in
lemma amplifiedPolynomial_tmul (s : Finset (List ι))
    (B : List ι → K →L[ℂ] K) (T : ι → H →L[ℂ] H) (κ : K) (ξ : H) :
    amplifiedPolynomial s B T (κ ⊗ₜ[ℂ] ξ) =
      ∑ w ∈ s, B w κ ⊗ₜ[ℂ] wordEval T w ξ := by
  simp only [amplifiedPolynomial, sum_apply, TensorProduct.mapL_tmul]

lemma amplifiedPolynomial_compression_exact
    (s : Finset (List ι)) (B : List ι → K →L[ℂ] K)
    (T : ι → H →L[ℂ] H) (κ : S → K) (ξ : S → H) {m : ℕ}
    (hm : ∀ w ∈ s, w.length ≤ m) :
    let L := wordSpace T ξ m
    let v : K ⊗[ℂ] L := ∑ j, κ j ⊗ₜ[ℂ] ⟨ξ j, testVector_mem_wordSpace T ξ m j⟩
    (L.subtypeₗᵢ.lTensor K) (amplifiedPolynomial s B (fun i => compress L (T i)) v) =
      amplifiedPolynomial s B T (∑ j, κ j ⊗ₜ[ℂ] ξ j) := by
  dsimp only
  simp only [map_sum, amplifiedPolynomial_tmul, LinearIsometry.lTensor_apply, LinearMap.lTensor_tmul]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro w hw
  congr 1
  exact wordSpace_compression_exact T ξ m w (hm w hw) j

omit [Fintype S] in
lemma norm_amplifiedPolynomial_le_of_finite_compressions
    (s : Finset (List ι)) (B : List ι → K →L[ℂ] K) (T : ι → H →L[ℂ] H)
    {M : ℝ} (hM : 0 ≤ M)
    (htest : ∀ (L : Submodule ℂ H) [FiniteDimensional ℂ L],
      ‖amplifiedPolynomial s B (fun i => compress L (T i))‖ ≤ M) :
    ‖amplifiedPolynomial s B T‖ ≤ M := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro x
  obtain ⟨k, κ, ξ, rfl⟩ := TensorProduct.exists_sum_tmul_eq x
  let m := s.sup List.length
  have hm : ∀ w ∈ s, w.length ≤ m := fun w hw => Finset.le_sup hw
  let L := wordSpace T ξ m
  let v : K ⊗[ℂ] L := ∑ j, κ j ⊗ₜ[ℂ] ⟨ξ j, testVector_mem_wordSpace T ξ m j⟩
  let Q : (K ⊗[ℂ] L) →ₗᵢ[ℂ] (K ⊗[ℂ] H) := L.subtypeₗᵢ.lTensor K
  have hv : Q v = ∑ j, κ j ⊗ₜ[ℂ] ξ j := by
    simp only [Q, v, LinearIsometry.lTensor_apply, map_sum, LinearMap.lTensor_tmul]
    rfl
  have hp : Q (amplifiedPolynomial s B (fun i => compress L (T i)) v) =
      amplifiedPolynomial s B T (∑ j, κ j ⊗ₜ[ℂ] ξ j) :=
    amplifiedPolynomial_compression_exact s B T κ ξ hm
  rw [← hp, Q.norm_map, ← hv, Q.norm_map]
  exact (ContinuousLinearMap.le_opNorm _ v).trans
    (mul_le_mul_of_nonneg_right (htest L) (norm_nonneg v))

end FiniteAmplificationTests

end WeakPureInfiniteness
end

end OAI
