import OAI.Analysis.PureInfiniteness.UltrapowerGramCuts

namespace OAI

/-! Reindex the finite cut Gram row to a product of copy and spectral indices. -/

noncomputable section

namespace WeakPureInfiniteness

variable {D J : Type*} [NonUnitalCStarAlgebra D] [Fintype J] [DecidableEq J]

local instance reindexGramOrder : PartialOrder D := CStarAlgebra.spectralOrder D
local instance reindexGramStarOrder : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D

lemma reindex_cut_gram_row {n : ℕ} (e : J ≃ Fin n) (f : J → D)
    (hf : ∀ j, 0 ≤ f j) (hfn : ∀ j, ‖f j‖ ≤ 1)
    (δ C : ℝ) (hδ : 0 ≤ δ) (d : Fin n → D) (hd : ∀ j, ‖d j‖ ≤ C)
    (H : CStarMatrix (Fin 1) (Fin n) D)
    (hentry : ∀ j, H 0 j = CFC.sqrt (f (e.symm j)) * d j)
    (hgram : H.conjTranspose * H =
      NonunitalGamma.diagonalHom (fun j => MainGap.cut (f (e.symm j)) δ)) :
    ∃ d' : J → D, (∀ j, ‖d' j‖ ≤ C) ∧
      ∃ H' : CStarMatrix (Fin 1) J D,
        (∀ j, H' 0 j = CFC.sqrt (f j) * d' j) ∧ ‖H'‖ ≤ 1 ∧
        H'.conjTranspose * H' = NonunitalGamma.diagonalHom (fun j => MainGap.cut (f j) δ) := by
  let H' : CStarMatrix (Fin 1) J D := CStarMatrix.ofMatrix (fun _ j => H 0 (e j))
  have hgram' : H'.conjTranspose * H' =
      NonunitalGamma.diagonalHom (fun j => MainGap.cut (f j) δ) := by
    apply CStarMatrix.ext
    intro i j
    have he := congrArg (fun M => M (e i) (e j)) hgram
    change (∑ k : Fin 1, star (H k (e i)) * H k (e j)) =
      (if e i = e j then MainGap.cut (f (e.symm (e i))) δ else 0) at he
    change (∑ k : Fin 1, star (H' k i) * H' k j) =
      (if i = j then MainGap.cut (f i) δ else 0)
    simp only [Fin.sum_univ_one] at he ⊢
    change star (H 0 (e i)) * H 0 (e j) = _
    simpa only [Equiv.symm_apply_apply, e.injective.eq_iff] using he
  refine ⟨fun j => d (e j), fun j => hd (e j), H', ?_, ?_, hgram'⟩
  · intro j
    change H 0 (e j) = _
    simpa only [Equiv.symm_apply_apply] using hentry (e j)
  · have hn : ‖H'‖ ^ 2 ≤ 1 := by
      rw [← rectangular_norm_initial, hgram']
      exact NonunitalGamma.diagonalHom_norm_le_one _ fun j =>
        (MainGap.norm_cut_le (hf j) hδ).trans (hfn j)
    nlinarith [norm_nonneg H']

end WeakPureInfiniteness

end

end OAI
