import OAI.Analysis.KadisonSimilarity.Tracial.TracialMatrixRealization

namespace OAI

/-!
# Actual matrix-conjugation actions on tracial tensor words

The conjugation action is constructed from the represented unitary and the
tracial conjugation. Its action on completed tensor words is obtained by genuine
tensor-product isometries.
-/

noncomputable section
namespace KadisonSimilarity
open scoped TensorProduct

universe u v
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The tensor power of an actual Hilbert-space isometry. -/
def algebraicTensorWordIsometry (g : F →ₗᵢ[ℂ] F) :
    (n : ℕ) → TensorWord F n →ₗᵢ[ℂ] TensorWord F n
  | 0 => LinearIsometry.id
  | n + 1 => TensorProduct.mapIsometry g (algebraicTensorWordIsometry g n)

theorem algebraicTensorWordIsometry_apply (g : F →ₗᵢ[ℂ] F) {n : ℕ} (x : Fin n → F) :
    algebraicTensorWordIsometry g n (tensorWord x) = tensorWord (fun i => g (x i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change g (x 0) ⊗ₜ[ℂ] algebraicTensorWordIsometry g n (tensorWord (Fin.tail x)) = _
    rw [ih]
    rfl

def completedTensorWordIsometry (g : F →ₗᵢ[ℂ] F) (n : ℕ) :
    CompletedTensorWord F n →ₗᵢ[ℂ] CompletedTensorWord F n :=
  (algebraicTensorWordIsometry g n).completion

@[simp] theorem completedTensorWordIsometry_apply (g : F →ₗᵢ[ℂ] F) {n : ℕ}
    (x : Fin n → F) :
    completedTensorWordIsometry g n (completedTensorWord x) =
      completedTensorWord (fun i => g (x i)) := by
  change (algebraicTensorWordIsometry g n).completion (tensorWord x) = _
  rw [LinearIsometry.completion_apply_coe, algebraicTensorWordIsometry_apply]
  rfl

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def endpointTensorIsometry (p : E →ₗᵢ[ℂ] E) (g : F →ₗᵢ[ℂ] F) (n : ℕ) :
    EndpointTensor E F n →ₗᵢ[ℂ] EndpointTensor E F n :=
  (TensorProduct.mapIsometry p (completedTensorWordIsometry g n)).completion

@[simp] theorem endpointTensorIsometry_apply (p : E →ₗᵢ[ℂ] E) (g : F →ₗᵢ[ℂ] F)
    {n : ℕ} (d : E) (x : Fin n → F) :
    endpointTensorIsometry p g n (endpointWord d x) =
      endpointWord (p d) (fun i => g (x i)) := by
  change (TensorProduct.mapIsometry p (completedTensorWordIsometry g n)).completion
    ((d ⊗ₜ[ℂ] completedTensorWord x : E ⊗[ℂ] CompletedTensorWord F n) :
      UniformSpace.Completion (E ⊗[ℂ] CompletedTensorWord F n)) =
    ((p d ⊗ₜ[ℂ] completedTensorWord (fun i => g (x i)) :
      E ⊗[ℂ] CompletedTensorWord F n) :
      UniformSpace.Completion (E ⊗[ℂ] CompletedTensorWord F n))
  rw [LinearIsometry.completion_apply_coe]
  simp only [TensorProduct.mapIsometry_apply, TensorProduct.map_tmul]
  change ((p d ⊗ₜ[ℂ] completedTensorWordIsometry g n (completedTensorWord x) :
    E ⊗[ℂ] CompletedTensorWord F n) :
    UniformSpace.Completion (E ⊗[ℂ] CompletedTensorWord F n)) = _
  rw [completedTensorWordIsometry_apply]

variable {R : Type v} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  [CompleteSpace E] {α : Type*} [Fintype α] [DecidableEq α]
  (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E) (L : R →⋆ₐ[ℂ] (E →L[ℂ] E))
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] R)
  (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
  (hleft : ∀ a b, L a (V b) = V (a * b))
  (htrace : ∀ a b, τ (a * b) = τ (b * a)) (hdense : DenseRange V)

/-- A matrix unitary acts isometrically through the actual left representation. -/
def representedMatrixUnitary (u : Matrix.unitaryGroup α ℂ) : E →ₗᵢ[ℂ] E :=
  (Unitary.linearIsometryEquiv
    ⟨L (ι (u : Matrix α α ℂ)), Unitary.map_mem (L.comp ι) u.property⟩).toLinearIsometry

omit [StarModule ℂ R] in
@[simp] theorem representedMatrixUnitary_apply (u : Matrix.unitaryGroup α ℂ) (x : E) :
    representedMatrixUnitary L ι u x = L (ι (u : Matrix α α ℂ)) x := rfl

/-- Left multiplication followed by the conjugate right multiplication gives
the actual trace-preserving matrix-conjugation isometry. -/
def tracialUnitaryConjugation (u : Matrix.unitaryGroup α ℂ) : E →ₗᵢ[ℂ] E where
  toLinearMap :=
    (((representedMatrixUnitary L ι u).toContinuousLinearMap.comp
      (tracialConjugation τ V hinner htrace hdense).toContinuousLinearMap).comp
      ((representedMatrixUnitary L ι u).toContinuousLinearMap.comp
      (tracialConjugation τ V hinner htrace hdense).toContinuousLinearMap)).toLinearMap
  norm_map' x := by
    change ‖representedMatrixUnitary L ι u
      (tracialConjugation τ V hinner htrace hdense
      (representedMatrixUnitary L ι u (tracialConjugation τ V hinner htrace hdense x)))‖ = _
    simp only [LinearIsometry.norm_map]

include hleft in
@[simp] theorem tracialUnitaryConjugation_apply_vector
    (u : Matrix.unitaryGroup α ℂ) (a : R) :
    tracialUnitaryConjugation τ V L ι hinner htrace hdense u (V a) =
      V (ι (u : Matrix α α ℂ) * a * star (ι (u : Matrix α α ℂ))) := by
  change L (ι (u : Matrix α α ℂ))
    (tracialConjugation τ V hinner htrace hdense
      (L (ι (u : Matrix α α ℂ)) (tracialConjugation τ V hinner htrace hdense (V a)))) = _
  rw [tracialConjugation_apply_vector, hleft, tracialConjugation_apply_vector,
    hleft, star_mul, star_star, mul_assoc]

include hleft in
@[simp] theorem tracialUnitaryConjugation_traceVector (u : Matrix.unitaryGroup α ℂ) :
    tracialUnitaryConjugation τ V L ι hinner htrace hdense u (V 1) = V 1 := by
  have hu : (u : Matrix α α ℂ) * star (u : Matrix α α ℂ) = 1 := u.property.2
  rw [tracialUnitaryConjugation_apply_vector τ V L ι hinner hleft htrace hdense,
    mul_one, ← map_star ι, ← map_mul ι, hu, map_one]

include hleft in
theorem tracialUnitaryConjugation_mem_centered (u : Matrix.unitaryGroup α ℂ)
    (x : centeredSubspace (V 1)) :
    tracialUnitaryConjugation τ V L ι hinner htrace hdense u x ∈ centeredSubspace (V 1) := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  calc
    inner ℂ (V 1) (tracialUnitaryConjugation τ V L ι hinner htrace hdense u (x : E)) =
        inner ℂ (V 1) (x : E) := by
      simpa only [tracialUnitaryConjugation_traceVector τ V L ι hinner hleft htrace hdense] using
        (tracialUnitaryConjugation τ V L ι hinner htrace hdense u).inner_map_map (V 1) (x : E)
    _ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property

def centeredUnitaryConjugation (u : Matrix.unitaryGroup α ℂ) :
    centeredSubspace (V 1) →ₗᵢ[ℂ] centeredSubspace (V 1) where
  toFun x := ⟨tracialUnitaryConjugation τ V L ι hinner htrace hdense u x,
    tracialUnitaryConjugation_mem_centered τ V L ι hinner hleft htrace hdense u x⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add (tracialUnitaryConjugation τ V L ι hinner htrace hdense u) (x : E) (y : E)
  map_smul' c x := by
    apply Subtype.ext
    exact (tracialUnitaryConjugation τ V L ι hinner htrace hdense u).map_smul c (x : E)
  norm_map' x := (tracialUnitaryConjugation τ V L ι hinner htrace hdense u).norm_map x

include hleft in
theorem tracialUnitaryConjugation_commutes (u : Matrix.unitaryGroup α ℂ) (x : E) :
    tracialConjugation τ V hinner htrace hdense
      (tracialUnitaryConjugation τ V L ι hinner htrace hdense u x) =
    tracialUnitaryConjugation τ V L ι hinner htrace hdense u
      (tracialConjugation τ V hinner htrace hdense x) := by
  refine hdense.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  simp only [tracialUnitaryConjugation_apply_vector τ V L ι hinner hleft htrace hdense,
    tracialConjugation_apply_vector, star_mul, star_star, mul_assoc]

include htrace in
omit [StarModule ℂ R] in
theorem trace_matrix_conjugation (u : Matrix.unitaryGroup α ℂ) (a : R) :
    τ (ι (u : Matrix α α ℂ) * a * star (ι (u : Matrix α α ℂ))) = τ a := by
  rw [htrace, ← mul_assoc, ← map_star ι, ← map_mul ι,
    Unitary.coe_star_mul_self, map_one, one_mul]

theorem centeredUnitaryConjugation_commutes (u : Matrix.unitaryGroup α ℂ)
    (x : centeredSubspace (V 1)) :
    centeredTracialConjugation τ V hinner htrace hdense
      (centeredUnitaryConjugation τ V L ι hinner hleft htrace hdense u x) =
    centeredUnitaryConjugation τ V L ι hinner hleft htrace hdense u
      (centeredTracialConjugation τ V hinner htrace hdense x) := by
  apply Subtype.ext
  exact tracialUnitaryConjugation_commutes τ V L ι hinner hleft htrace hdense u x

/-- The constructed conjugation action carries actual centered matrix vectors
to the centered vectors of their matrix conjugates. -/
theorem centeredUnitaryConjugation_center (hτ : τ 1 = 1) (u : Matrix.unitaryGroup α ℂ)
    (a : Matrix α α ℂ) :
    centeredUnitaryConjugation τ V L ι hinner hleft htrace hdense u
      (tracialCenter V (ι a)) =
      tracialCenter V (ι ((u : Matrix α α ℂ) * a * star (u : Matrix α α ℂ))) := by
  apply Subtype.ext
  change tracialUnitaryConjugation τ V L ι hinner htrace hdense u
    (tracialCenter V (ι a) : E) = _
  rw [coe_tracialCenter τ V hinner hτ, coe_tracialCenter τ V hinner hτ]
  rw [map_sub, map_smul,
    tracialUnitaryConjugation_apply_vector τ V L ι hinner hleft htrace hdense,
    tracialUnitaryConjugation_traceVector τ V L ι hinner hleft htrace hdense]
  simp only [map_mul, map_star]
  rw [trace_matrix_conjugation τ ι htrace]

include hleft in
theorem tracialUnitaryConjugation_star_matrix (u : Matrix.unitaryGroup α ℂ)
    (a : Matrix α α ℂ) :
    tracialUnitaryConjugation τ V L ι hinner htrace hdense u (V (ι (star a))) =
      V (ι (star ((u : Matrix α α ℂ) * a * star (u : Matrix α α ℂ)))) := by
  rw [tracialUnitaryConjugation_apply_vector τ V L ι hinner hleft htrace hdense]
  simp only [map_star, map_mul, star_mul, star_star, mul_assoc]

/-- The genuine completed endpoint tensor action of a matrix unitary. -/
def tracialMatrixWordAction (u : Matrix.unitaryGroup α ℂ) (n : ℕ) :
    EndpointTensor E (centeredSubspace (V 1)) n →ₗᵢ[ℂ]
      EndpointTensor E (centeredSubspace (V 1)) n :=
  endpointTensorIsometry (tracialUnitaryConjugation τ V L ι hinner htrace hdense u)
    (centeredUnitaryConjugation τ V L ι hinner hleft htrace hdense u) n

/-- Actual matrix-unitary intertwining supplies the word covariance used by the
finite invariant theory. The source and test word formulas are proved here. -/
def tracialMatrixWordCovariance (hτ : τ 1 = 1)
    (hι : ∀ a, τ (ι a) = (Fintype.card α : ℂ)⁻¹ * Matrix.trace a)
    {k l : ℕ} (Y : EndpointTensor E (centeredSubspace (V 1)) k →L[ℂ]
      EndpointTensor E (centeredSubspace (V 1)) l)
    (hY : ∀ u, Y.comp
      (tracialMatrixWordAction τ V L ι hinner hleft htrace hdense u k).toContinuousLinearMap =
      (tracialMatrixWordAction τ V L ι hinner hleft htrace hdense u l).toContinuousLinearMap.comp Y) :
    MatrixWordCovariance (tracialMatrixStage τ V L ι hinner hleft hι)
      (centeredTracialConjugation τ V hinner htrace hdense) (V 1) Y where
  sourceAction u := tracialMatrixWordAction τ V L ι hinner hleft htrace hdense u k
  testAction u := tracialMatrixWordAction τ V L ι hinner hleft htrace hdense u l
  intertwine := hY
  source_covariance u v := by
    change endpointWord (V 1) (fun i => tracialCenter V
      (ι ((u : Matrix α α ℂ) * v (some (Sum.inl i)) * star (u : Matrix α α ℂ)))) = _
    rw [tracialMatrixWordAction, endpointTensorIsometry_apply,
      tracialUnitaryConjugation_traceVector τ V L ι hinner hleft htrace hdense]
    apply congrArg (endpointWord (V 1))
    funext i
    exact (centeredUnitaryConjugation_center τ V L ι hinner hleft htrace hdense hτ u _).symm
  test_covariance u v := by
    change endpointWord
      (V (ι (star ((u : Matrix α α ℂ) * v none * star (u : Matrix α α ℂ)))))
      (fun j => centeredTracialConjugation τ V hinner htrace hdense (tracialCenter V
        (ι ((u : Matrix α α ℂ) * v (some (Sum.inr j)) * star (u : Matrix α α ℂ))))) = _
    rw [tracialMatrixWordAction, endpointTensorIsometry_apply]
    apply congrArg₂ (fun d (x : Fin l → centeredSubspace (V 1)) => endpointWord d x)
    · exact (tracialUnitaryConjugation_star_matrix τ V L ι hinner hleft htrace hdense u _).symm
    · funext j
      rw [← centeredUnitaryConjugation_center τ V L ι hinner hleft htrace hdense hτ]
      exact centeredUnitaryConjugation_commutes τ V L ι hinner hleft htrace hdense u _

end KadisonSimilarity

end

end OAI
