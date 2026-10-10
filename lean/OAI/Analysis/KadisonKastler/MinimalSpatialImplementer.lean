import OAI.Analysis.KadisonKastler.SelfAdjointVectorCompactness
import Mathlib.Topology.Semicontinuity.Basic

namespace OAI

/-! # Minimum distance for bounded self-adjoint spatial implementers

The bounded family of self-adjoint implementers of the same derivation is
weak-operator compact. Its distance from the self-adjoint part of the
algebra is attained. This is the compactness step of Sakai's spatial
splitting argument (Ann. Math. 83 (1966), Lemma 2, p.274).
-/

namespace KadisonKastler

noncomputable section

open ContinuousLinearMapWOT Generator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem wot_isSelfAdjoint_isClosed :
    IsClosed {T : H →WOT[ℂ] H | IsSelfAdjoint T.toCLM} := by
  have he : {T : H →WOT[ℂ] H | IsSelfAdjoint T.toCLM} = {T | star T = T} := by
    ext T
    constructor
    · intro h
      exact DFunLike.ext _ _ (fun x => congrArg (fun A : H →L[ℂ] H => A x) h.star_eq)
    · intro h
      exact ContinuousLinearMap.ext (fun x => congrArg (fun A : H →WOT[ℂ] H => A x) h)
  rw [he]
  exact isClosed_eq continuous_star continuous_id

theorem wot_norm_lowerSemicontinuous :
    LowerSemicontinuous (fun T : H →WOT[ℂ] H => ‖T.toCLM‖) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro r
  exact (wotNormBall_compact r).isClosed

theorem wot_vonNeumann_isClosed (M : VonNeumannAlgebra H) :
    IsClosed {T : H →WOT[ℂ] H | T.toCLM ∈ M} := by
  have he : {T : H →WOT[ℂ] H | T.toCLM ∈ M} =
      {T | ∀ a : M.commutant.toStarSubalgebra, ∀ x y : H,
        inner ℂ (a.val.adjoint y) (T x) = inner ℂ y (T (a.val x))} := by
    ext T
    constructor
    · intro h a x y
      rw [ContinuousLinearMap.adjoint_inner_left]
      exact congrArg (inner ℂ y) (congrArg (fun R : H →L[ℂ] H => R x)
        (VonNeumannAlgebra.mem_commutant_iff.mp a.property T.toCLM h).symm)
    · intro h
      rw [← VonNeumannAlgebra.commutant_commutant M]
      apply VonNeumannAlgebra.mem_commutant_iff.mpr
      intro a ha
      ext x
      apply ext_inner_left ℂ
      intro y
      simpa only [mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMapWOT.toCLM_apply] using
        h ⟨a, ha⟩ x y
  rw [he]
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun a => isClosed_iInter (fun x => isClosed_iInter (fun y =>
    isClosed_eq (continuous_inner_apply continuous_id x (a.val.adjoint y))
      (continuous_inner_apply continuous_id (a.val x) y))))

def boundedSelfAdjointImplementers (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) :
    Set (H →WOT[ℂ] H) :=
  {S | IsSelfAdjoint S.toCLM ∧ ‖S.toCLM‖ ≤ ‖T‖ ∧ S.toCLM - T ∈ M.commutant}

theorem boundedSelfAdjointImplementers_compact (M : VonNeumannAlgebra H)
    (T : H →L[ℂ] H) : IsCompact (boundedSelfAdjointImplementers M T) := by
  have hc : IsClosed {S : H →WOT[ℂ] H | S.toCLM - T ∈ M.commutant} :=
    (wot_vonNeumann_isClosed M.commutant).preimage
      (continuous_id.sub continuous_const)
  have he : boundedSelfAdjointImplementers M T =
      wotNormBall ‖T‖ ∩ {S | IsSelfAdjoint S.toCLM} ∩
        {S | S.toCLM - T ∈ M.commutant} := by
    ext S
    simp only [boundedSelfAdjointImplementers, wotNormBall, Set.mem_ofPred_eq,
      Set.mem_inter_iff]
    tauto
  rw [he]
  exact ((wotNormBall_compact ‖T‖).inter_right wot_isSelfAdjoint_isClosed).inter_right hc

theorem exists_minimal_selfAdjoint_spatial_implementer
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    ∃ X S : H →L[ℂ] H, X ∈ M ∧ IsSelfAdjoint X ∧ IsSelfAdjoint S ∧
      ‖S‖ ≤ ‖T‖ ∧ S - T ∈ M.commutant ∧
      ∀ Y V : H →L[ℂ] H, Y ∈ M → IsSelfAdjoint Y → IsSelfAdjoint V →
        ‖V‖ ≤ ‖T‖ → V - T ∈ M.commutant → ‖X - S‖ ≤ ‖Y - V‖ := by
  let A : Set (H →WOT[ℂ] H) :=
    Generator.Tracial.weakOperatorBall M (2 * ‖T‖) ∩
      {X | IsSelfAdjoint X.toCLM}
  let K := boundedSelfAdjointImplementers M T
  have hA : IsCompact A :=
    (Generator.Tracial.weakOperatorBall_isCompact M _).inter_right
      wot_isSelfAdjoint_isClosed
  have hK : IsCompact K := boundedSelfAdjointImplementers_compact M T
  have hz : (0 : H →WOT[ℂ] H) ∈ A := by
    exact ⟨⟨M.zero_mem, by simp⟩, IsSelfAdjoint.zero _⟩
  have ht : ofCLM T ∈ K := by
    exact ⟨hT, le_rfl, by simp only [sub_self]; exact M.commutant.zero_mem⟩
  have hl : LowerSemicontinuous
      (fun p : (H →WOT[ℂ] H) × (H →WOT[ℂ] H) => ‖p.1.toCLM - p.2.toCLM‖) :=
    wot_norm_lowerSemicontinuous.comp (continuous_fst.sub continuous_snd)
  obtain ⟨p, hp, hmin⟩ := (hl.lowerSemicontinuousOn (A ×ˢ K)).exists_isMinOn
    (Set.prod_nonempty_iff.mpr ⟨⟨0, hz⟩, ⟨ofCLM T, ht⟩⟩) (hA.prod hK)
  have hmin' := isMinOn_iff.mp hmin
  have hbound : ‖p.1.toCLM - p.2.toCLM‖ ≤ ‖T‖ := by
    simpa only [ofCLM_toCLM, toCLM_zero, zero_sub, norm_neg] using
      hmin' (0, ofCLM T) (show (0, ofCLM T) ∈ A ×ˢ K from ⟨hz, ht⟩)
  refine ⟨p.1.toCLM, p.2.toCLM, hp.1.1.1, hp.1.2, hp.2.1, hp.2.2.1,
    hp.2.2.2, ?_⟩
  intro Y V hYM hY hV hnV hVT
  by_cases hnY : ‖Y‖ ≤ 2 * ‖T‖
  · exact hmin' (ofCLM Y, ofCLM V) (show (ofCLM Y, ofCLM V) ∈ A ×ˢ K from
      ⟨⟨⟨hYM, hnY⟩, hY⟩, ⟨hV, hnV, hVT⟩⟩)
  · have hn := norm_sub_norm_le Y V
    exact hbound.trans (by linarith)

end

end KadisonKastler

end OAI
