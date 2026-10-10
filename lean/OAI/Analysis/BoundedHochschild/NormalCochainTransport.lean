import OAI.Analysis.BoundedHochschild.FiniteGroupCochainAverages

namespace OAI

/-! Unitary transport and finite cochain averaging preserve separate
normality. Normalizing an input also commutes with unitary transport. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
lemma cochainUnitaryTuple_update {n : ℕ} (u : Fin (n + 2) → unitary M)
    (x : Fin (n + 1) → M) (i : Fin (n + 1)) (a : M) :
    cochainUnitaryTuple u (Function.update x i a) =
      Function.update (cochainUnitaryTuple u x) i
        ((u i.castSucc : M) * a * star (u i.succ : M)) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [cochainUnitaryTuple]
  · simp [cochainUnitaryTuple, hji]

private def inputTransport {n : ℕ} (u : Fin (n + 2) → unitary M) (i : Fin (n + 1)) :
    M →L[ℂ] M :=
  ((ContinuousLinearMap.mul ℂ M).flip (star (u i.succ : M))).comp
    (ContinuousLinearMap.mul ℂ M (u i.castSucc : M))

private def outputTransport {n : ℕ} (u : Fin (n + 2) → unitary M) : M →L[ℂ] M :=
  ((ContinuousLinearMap.mul ℂ M).flip (u (Fin.last (n + 1)) : M)).comp
    (ContinuousLinearMap.mul ℂ M (star (u 0 : M)))

private lemma inputTransport_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {n : ℕ} (u : Fin (n + 2) → unitary M) (i : Fin (n + 1)) :
    HasPreadjoint e (inputTransport u i) :=
  ((HochschildSakai.abstract_multiplication_normal e).2 _).comp e
    ((HochschildSakai.abstract_multiplication_normal e).1 _)

private lemma outputTransport_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {n : ℕ} (u : Fin (n + 2) → unitary M) : HasPreadjoint e (outputTransport u) :=
  ((HochschildSakai.abstract_multiplication_normal e).2 _).comp e
    ((HochschildSakai.abstract_multiplication_normal e).1 _)

private lemma transport_updateSlice {n : ℕ} (u : Fin (n + 2) → unitary M)
    (f : Cochain M (n + 1)) (i : Fin (n + 1)) (x : Fin (n + 1) → M) :
    updateSlice (cochainUnitaryTransport u f) i x =
      (outputTransport u).comp ((updateSlice f i (cochainUnitaryTuple u x)).comp (inputTransport u i)) := by
  ext a
  simp only [updateSlice_apply, cochainUnitaryTransport_apply, cochainUnitaryTuple_update,
    ContinuousLinearMap.comp_apply, inputTransport, outputTransport,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply']

lemma cochainUnitaryTransport_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {n : ℕ} (u : Fin (n + 2) → unitary M) (f : Cochain M (n + 1))
    (hf : SeparatelyNormal e f) : SeparatelyNormal e (cochainUnitaryTransport u f) := by
  intro i x z
  have hn : HasPreadjoint e (updateSlice (cochainUnitaryTransport u f) i x) := by
    rw [transport_updateSlice]
    exact (outputTransport_normal e u).comp e
      ((updateSlice_normal e f hf i _).comp e (inputTransport_normal e u i))
  obtain ⟨w, hw⟩ := hn z
  exact ⟨w, fun a => by simpa only [updateSlice_apply] using hw a⟩

omit [CompleteSpace X] in
lemma separatelyNormal_smul (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {n : ℕ} (z : ℂ) (f : Cochain M (n + 1)) (hf : SeparatelyNormal e f) :
    SeparatelyNormal e (z • f) := by
  intro i x w
  have he : updateSlice (z • f) i x = z • updateSlice f i x := by
    ext a
    simp only [updateSlice_apply, smul_apply]
  have hn : HasPreadjoint e (updateSlice (z • f) i x) := by
    rw [he]
    exact (updateSlice_normal e f hf i x).smul e z
  obtain ⟨w', hw'⟩ := hn w
  exact ⟨w', fun a => by simpa only [updateSlice_apply] using hw' a⟩

omit [CompleteSpace X] in
lemma separatelyNormal_sum (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {I : Type v} (s : Finset I) {n : ℕ} (f : I → Cochain M (n + 1))
    (hf : ∀ j ∈ s, SeparatelyNormal e (f j)) : SeparatelyNormal e (∑ j ∈ s, f j) := by
  intro i x w
  have he : updateSlice (∑ j ∈ s, f j) i x = ∑ j ∈ s, updateSlice (f j) i x := by
    ext a
    simp only [updateSlice_apply, sum_apply]
  have hn : HasPreadjoint e (updateSlice (∑ j ∈ s, f j) i x) := by
    rw [he]
    exact HasPreadjoint.sum e s _ (fun j hj => updateSlice_normal e (f j) (hf j hj) i x)
  obtain ⟨w', hw'⟩ := hn w
  exact ⟨w', fun a => by simpa only [updateSlice_apply] using hw' a⟩

lemma finiteGroupCochainAverage_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {G : Type v} [Group G] [Fintype G] (ρ : G →* unitary M)
    {n : ℕ} (f : Cochain M (n + 1)) (hf : SeparatelyNormal e f) :
    SeparatelyNormal e (finiteGroupCochainAverage ρ f) := by
  unfold finiteGroupCochainAverage
  apply separatelyNormal_smul e
  apply separatelyNormal_sum e
  intro g _
  exact cochainUnitaryTransport_normal e _ f hf

end BoundedHochschild.KadisonRingrose

end

end OAI
