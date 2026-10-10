import OAI.Analysis.KadisonKastler.SupportSpanNorm
import OAI.Analysis.KadisonKastler.LocalizedFactorNorm

namespace OAI

/-! Compactness assembles the finite support rows into the localized norm
bound used by Paulsen's minimal-family argument. No normality of the auxiliary
representation is needed: the finite sums are on the original space. -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H}

theorem representationRowAverage_reindex
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (r : κ → Algebra M) (R : H →L[ℂ] K) :
    representationRowAverage π (r ∘ e) R = representationRowAverage π r R := by
  exact Equiv.sum_comp e (fun i => (π (r i)).comp (R.comp (star (r i) : H →L[ℂ] H)))

omit [CompleteSpace K] in
theorem norm_comp_finiteSupportSum_mono (A : H →L[ℂ] K)
    (s t : Finset (PartialIsometry M))
    (ho : ∀ v ∈ t, ∀ w ∈ t, v ≠ w → v.support.val * w.support.val = 0)
    (hst : s ⊆ t) :
    ‖A.comp (finiteSupportSum s : H →L[ℂ] H)‖ ≤
      ‖A.comp (finiteSupportSum t : H →L[ℂ] H)‖ := by
  have he : (finiteSupportSum t : H →L[ℂ] H).comp
      (finiteSupportSum s : H →L[ℂ] H) = (finiteSupportSum s : H →L[ℂ] H) :=
    congrArg Subtype.val (finiteSupportSum_mul_of_subset s t ho hst)
  have hp := (finiteSupportSum_projection s
    (fun v hv w hw => ho v (hst hv) w (hst hw))).map M.toStarSubalgebra.subtype
  calc
    _ = ‖(A.comp (finiteSupportSum t : H →L[ℂ] H)).comp
        (finiteSupportSum s : H →L[ℂ] H)‖ := by rw [ContinuousLinearMap.comp_assoc, he]
    _ ≤ _ := ((A.comp (finiteSupportSum t : H →L[ℂ] H)).opNorm_comp_le _).trans
      ((mul_le_mul_of_nonneg_left hp.norm_le (norm_nonneg _)).trans_eq (mul_one _))

theorem exists_central_localized_norm_le
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (R : X → H →L[ℂ] K)
    (hR : Continuous (fun F => ContinuousLinearMapWOT.ofCLM (R F)))
    (hrows : ∀ (F : X) (n : ℕ) (r : Fin n → Algebra M)
      (_hr : ∑ i, r i * star (r i) = 1),
      ∃ G : X, R G = representationRowAverage π r (R F))
    (e : AlgebraProjection M) (F : X) :
    ∃ G : X, ‖(R G).comp ((centralSupport e).val : H →L[ℂ] H)‖ ≤
      ‖(π e.val).comp ((R F).comp (e.val : H →L[ℂ] H))‖ := by
  classical
  obtain ⟨S, hS, hcover⟩ := exists_centralSupportCover e
  let I := {s : Finset (PartialIsometry M) // (↑s : Set (PartialIsometry M)) ⊆ S}
  let d := ‖(π e.val).comp ((R F).comp (e.val : H →L[ℂ] H))‖
  let D : I → Set X := fun s => {G | ‖(R G).comp (finiteSupportSum s.val : H →L[ℂ] H)‖ ≤ d}
  let : Nonempty I := ⟨⟨∅, by simp⟩⟩
  have ho (s : I) : ∀ v ∈ s.val, ∀ w ∈ s.val, v ≠ w →
      v.support.val * w.support.val = 0 := fun v hv w hw => hS.2 (s.property hv) (s.property hw)
  have hd (s : I) : IsClosed (D s) :=
    isClosed_localized_factor_norm R hR (finiteSupportSum s.val : H →L[ℂ] H) d
  have hn (s : I) : (D s).Nonempty := by
    let r := finiteSupportRow s.val
    let f := (Fintype.equivFin (Option s.val)).symm
    have hr : ∑ i, (r ∘ f) i * star ((r ∘ f) i) = 1 := by
      change (∑ i, r (f i) * star (r (f i))) = 1
      rw [Equiv.sum_comp f (fun j => r j * star (r j))]
      exact finiteSupportRow_normalized s.val (ho s)
    obtain ⟨G, hG⟩ := hrows F _ (r ∘ f) hr
    refine ⟨G, ?_⟩
    change ‖(R G).comp (finiteSupportSum s.val : H →L[ℂ] H)‖ ≤ d
    rw [hG, representationRowAverage_reindex]
    exact finiteSupportRow_localized_norm_le e s.val (ho s)
      (fun v hv => (hS.1 v (s.property hv)).1) π (R F)
  have hdir : Directed (· ⊇ ·) D := by
    intro s t
    let u : I := ⟨s.val ∪ t.val, by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact s.property hv
      · exact t.property hv⟩
    refine ⟨u, ?_, ?_⟩
    · intro G hG
      exact (norm_comp_finiteSupportSum_mono (R G) s.val u.val (ho u)
        Finset.subset_union_left).trans hG
    · intro G hG
      exact (norm_comp_finiteSupportSum_mono (R G) t.val u.val (ho u)
        Finset.subset_union_right).trans hG
  obtain ⟨G, hG⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    D hdir hn (fun s => (hd s).isCompact) hd
  refine ⟨G, ?_⟩
  rw [← hcover]
  exact norm_comp_partialSupportProjection_le S hS.2 (R G) (norm_nonneg _) (fun s hs =>
    Set.mem_iInter.mp hG ⟨s, hs⟩)

end

end KadisonKastler

end OAI
