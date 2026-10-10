import OAI.Analysis.BoundedHochschild.MultimodularEndFaces
import OAI.Analysis.TracialCohomology.NormalReduction

namespace OAI

/-! The established normal-cocycle reduction retains multimodularity.
This is preparatory support for the properly infinite application; it
assumes no complete bound on the initial cocycle. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma MultimodularAt.sub {n : ℕ} {f g : Cochain M (n + 1)} {r : M}
    (hf : MultimodularAt f r) (hg : MultimodularAt g r) : MultimodularAt (f - g) r := by
  simpa only [neg_one_smul, ← sub_eq_add_neg] using hf.add (hg.smul (-1))

lemma multimodularOver_iff_at {n : ℕ} (R : StarSubalgebra ℂ M) (f : Cochain M (n + 1)) :
    MultimodularOver R f ↔ ∀ r ∈ R, MultimodularAt f r := by
  constructor
  · intro h r hr
    exact ⟨h.left r hr, h.right r hr, h.balance r hr⟩
  · intro h
    exact ⟨fun r hr => (h r hr).left, fun r hr => (h r hr).right,
      fun r hr => (h r hr).balance⟩

lemma normalFirst_eq_normalAt_zero (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {n : ℕ} (f : Cochain M (n + 1)) : normalFirst e f = normalAt e f 0 := by
  ext x
  rw [← Fin.cons_self_tail x, normalFirst_cons]
  have h := normalAt_insert e f 0 (Fin.tail x) (x 0)
  simp only [Fin.insertNth_zero'] at h
  rw [h]
  have hs : firstSliceN f (Fin.tail x) = sliceAt f 0 (Fin.tail x) := by
    ext a
    simp only [sliceAt_apply, Fin.insertNth_zero', firstSliceN_apply]
  rw [hs]

lemma multimodularAt_firstNormalCorrection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {n : ℕ} (f : Cochain M (n + 2)) (r : M) (hf : MultimodularAt f r) :
    MultimodularAt (firstNormalCorrectionN e f) r := by
  have hn : MultimodularAt (normalFirst e f) r := by
    rw [normalFirst_eq_normalAt_zero]
    exact normalAt_multimodularAt e f 0 r hf
  have he : firstNormalCorrectionN e f = (normalFirst e f).curryMid 0 1 := by
    ext x
    change normalFirst e f (Fin.cons 1 x) = normalFirst e f ((0 : Fin (n + 2)).insertNth 1 x)
    rw [Fin.insertNth_zero']
  rw [he]
  exact multimodularAt_curryMid_one _ r hn 0

lemma multimodularAt_firstNormalRemainder (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {n : ℕ} (f : Cochain M (n + 2)) (r : M) (hf : MultimodularAt f r) :
    MultimodularAt (firstNormalRemainderN e f) r := by
  exact hf.sub (multimodularAt_differential _ r (multimodularAt_firstNormalCorrection e f r hf))

lemma multimodularAt_slotInsertion (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {n : ℕ} (f : Cochain M (n + 2)) (i : Fin (n + 2)) (r : M)
    (hf : MultimodularAt f r) : MultimodularAt (slotInsertion e f i) r :=
  multimodularAt_curryMid_one _ r (normalAt_multimodularAt e f i r hf) i

lemma multimodularAt_slotRemainder (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {n : ℕ} (f : Cochain M (n + 2)) (i : Fin (n + 2)) (r : M)
    (hf : MultimodularAt f r) : MultimodularAt (slotRemainder e f i) r :=
  hf.sub ((multimodularAt_differential _ r (multimodularAt_slotInsertion e f i r hf)).smul _)

lemma multimodularOver_firstNormalRemainder (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {n : ℕ} (R : StarSubalgebra ℂ M) (f : Cochain M (n + 2)) (hf : MultimodularOver R f) :
    MultimodularOver R (firstNormalRemainderN e f) := by
  rw [multimodularOver_iff_at] at hf ⊢
  exact fun r hr => multimodularAt_firstNormalRemainder e f r (hf r hr)

lemma multimodularOver_slotRemainder (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {n : ℕ} (R : StarSubalgebra ℂ M) (f : Cochain M (n + 2)) (i : Fin (n + 2))
    (hf : MultimodularOver R f) : MultimodularOver R (slotRemainder e f i) := by
  rw [multimodularOver_iff_at] at hf ⊢
  exact fun r hr => multimodularAt_slotRemainder e f i r (hf r hr)

lemma normal_before_multimodular (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hP : BilinearNormalPartPreservation e) {n : ℕ} (R : StarSubalgebra ℂ M)
    (f : Cochain M (n + 2)) (hf : ∀ x, differentialValue f x = 0)
    (hM : MultimodularOver R f) (r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n + 1) :
    ∃ (F : Cochain M (n + 2)) (b : Cochain M (n + 1)),
      (∀ x, differentialValue F x = 0) ∧ (∀ x, f x = F x + differentialValue b x) ∧
      NormalBefore e F r ∧ UnitZeroBefore F r ∧ MultimodularOver R F := by
  induction r with
  | zero => omega
  | succ r ih =>
      by_cases hz : r = 0
      · subst r
        exact ⟨firstNormalRemainderN e f, firstNormalCorrectionN e f,
          firstNormalRemainderN_cocycle e f hf, firstNormalRemainderN_identity e f,
          firstRemainder_before_normal e f hf, firstRemainder_before_unitZero e f hf,
          multimodularOver_firstNormalRemainder e R f hM⟩
      · obtain ⟨F, b, hFc, hid, hFN, hFU, hFM⟩ := ih (by omega) (by omega)
        let i : Fin (n + 1) := ⟨r, by omega⟩
        have hi : 0 < i.val := by dsimp [i]; omega
        have hNN := normalAt_before_normal_of_preservation e hP F i.castSucc hFN
        refine ⟨slotRemainder e F i.castSucc, b + slotCorrection e F i.castSucc,
          slotRemainder_cocycle e F i.castSucc hFc, ?_,
          slotRemainder_normal e F i hi hFc hFN hFU hNN,
          slotRemainder_unitZero e F i hi hFc hFN hFU,
          multimodularOver_slotRemainder e R F i.castSucc hFM⟩
        intro x
        rw [hid x, slotRemainder_identity e F i.castSucc x, differentialValue_add]
        abel

theorem normal_reduction_multimodular (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {n : ℕ} (R : StarSubalgebra ℂ M) (f : Cochain M (n + 2))
    (hf : ∀ x, differentialValue f x = 0) (hM : MultimodularOver R f) :
    ∃ (F : Cochain M (n + 2)) (b : Cochain M (n + 1)),
      SeparatelyNormal e F ∧ MultimodularOver R F ∧
      (∀ x, differentialValue F x = 0) ∧ (∀ x, f x = F x + differentialValue b x) := by
  have hP : BilinearNormalPartPreservation e :=
    (bilinear_preservation_iff e).mpr (HochschildNormalPart.operator_bilinear_normal_preservation e)
  obtain ⟨F, b, hFc, hid, hFN, _, hFM⟩ :=
    normal_before_multimodular e hP R f hf hM (n + 1) (by omega) le_rfl
  exact ⟨F, b, (separatelyNormal_iff_slices e F).mpr
    (all_normal_of_before_penultimate e F hFc hFN), hFM, hFc, hid⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
