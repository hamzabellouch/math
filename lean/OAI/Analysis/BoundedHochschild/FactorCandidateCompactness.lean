import OAI.Analysis.BoundedHochschild.WeakRepresentationAverages

namespace OAI

/-! Compact sets of factorization operators whose coefficient maps take
values in the original algebra. The range condition is retained explicitly. -/

noncomputable section

open Topology
open scoped InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H K : Type*} [CStarAlgebra M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def representationWeakBall (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (C : ℝ) :
    Set (H →WOT[ℂ] H) :=
  {A | ∃ a : M, ‖a‖ ≤ C ∧ ContinuousLinearMapWOT.ofCLM (σ a) = A}

def factorCandidates (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H))
    (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K) (D : ℝ) : Set (H →WOT[ℂ] K) :=
  rectangularWeakBall D ∩ {W | ∀ a, weakFactorValue π L a W ∈
    representationWeakBall σ (‖L‖ * D * ‖a‖)}

lemma factorCandidates_isClosed (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hσ : ∀ C, IsClosed (representationWeakBall σ C))
    (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K) (D : ℝ) :
    IsClosed (factorCandidates σ π L D) := by
  apply (rectangularWeakBall_isClosed D).inter
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun a =>
    (hσ (‖L‖ * D * ‖a‖)).preimage (weakFactorValue_continuous π L a)

theorem factorCandidates_isCompact (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hσ : ∀ C, IsClosed (representationWeakBall σ C))
    (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K) (D : ℝ) :
    IsCompact (factorCandidates σ π L D) :=
  (rectangularWeakBall_isCompact D).of_isClosed_subset
    (factorCandidates_isClosed σ hσ π L D) (fun _ h => h.1)

lemma weakFactorValue_norm_le (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K)
    (a : M) (W : H →WOT[ℂ] K) :
    ‖(weakFactorValue π L a W).toCLM‖ ≤ ‖L‖ * ‖a‖ * ‖W.toCLM‖ := by
  change ‖L.adjoint.comp ((π a).comp W.toCLM)‖ ≤ _
  calc
    _ ≤ ‖L.adjoint‖ * (‖π a‖ * ‖W.toCLM‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ = ‖L‖ * (‖π a‖ * ‖W.toCLM‖) := by rw [LinearIsometryEquiv.norm_map]
    _ ≤ ‖L‖ * (‖a‖ * ‖W.toCLM‖) := by
      gcongr
      exact NonUnitalStarAlgHom.norm_apply_le π a
    _ = _ := by ring

lemma mem_factorCandidates_of_range (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hσ : Function.Injective σ) (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (L : H →L[ℂ] K) {D : ℝ} {W : H →WOT[ℂ] K}
    (hW : ‖W.toCLM‖ ≤ D)
    (hrange : ∀ a, ∃ x : M, σ x = (weakFactorValue π L a W).toCLM) :
    W ∈ factorCandidates σ π L D := by
  refine ⟨hW, fun a => ?_⟩
  obtain ⟨x, hx⟩ := hrange a
  refine ⟨x, ?_, congrArg ContinuousLinearMapWOT.ofCLM hx⟩
  calc
    ‖x‖ = ‖σ x‖ := (NonUnitalStarAlgHom.norm_map σ hσ x).symm
    _ = ‖(weakFactorValue π L a W).toCLM‖ := congrArg norm hx
    _ ≤ ‖L‖ * ‖a‖ * ‖W.toCLM‖ := weakFactorValue_norm_le π L a W
    _ ≤ ‖L‖ * ‖a‖ * D := mul_le_mul_of_nonneg_left hW (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ‖L‖ * D * ‖a‖ := by ring

theorem factorCandidates_realize (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hσ : Function.Injective σ) (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (L : H →L[ℂ] K) {D : ℝ} (hD : 0 ≤ D) {W : H →WOT[ℂ] K}
    (hW : W ∈ factorCandidates σ π L D) :
    ∃ T : M →L[ℂ] M, ‖T‖ ≤ ‖L‖ * D ∧
      ∀ a, σ (T a) = L.adjoint.comp ((π a).comp W.toCLM) := by
  choose t ht he using hW.2
  have he' (a : M) : σ (t a) = L.adjoint.comp ((π a).comp W.toCLM) :=
    congrArg ContinuousLinearMapWOT.toCLM (he a)
  have hadd (a b : M) : t (a + b) = t a + t b := by
    apply hσ
    rw [map_add, he', he', he']
    apply ContinuousLinearMap.ext
    intro ξ
    simp only [ContinuousLinearMap.comp_apply, add_apply, map_add]
  have hsmul (z : ℂ) (a : M) : t (z • a) = z • t a := by
    apply hσ
    rw [map_smul, he', he']
    apply ContinuousLinearMap.ext
    intro ξ
    simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul]
  let tlin : M →ₗ[ℂ] M := { toFun := t, map_add' := hadd, map_smul' := hsmul }
  let T := tlin.mkContinuous (‖L‖ * D) ht
  exact ⟨T, tlin.mkContinuous_norm_le (mul_nonneg (norm_nonneg _) hD) ht, he'⟩

theorem factorCandidates_invariant (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hσ : Function.Injective σ) (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (L : H →L[ℂ] K) {D : ℝ} (hD : 0 ≤ D) {I : Type*} [Fintype I]
    (m : I → M) (hm : ∑ i, m i * star (m i) = 1) :
    Set.MapsTo (weakRepresentedRightAverage π σ m)
      (factorCandidates σ π L D) (factorCandidates σ π L D) := by
  intro W hW
  obtain ⟨T, _, hT⟩ := factorCandidates_realize σ hσ π L hD hW
  apply mem_factorCandidates_of_range σ hσ π L
  · exact (representedRightAverage_norm_le π σ m hm W.toCLM).trans hW.1
  · intro a
    exact ⟨finiteRightAverage m T a, representedRightAverage_factorization π σ T L W.toCLM hT m a⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
