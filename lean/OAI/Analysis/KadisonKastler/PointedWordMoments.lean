import OAI.Analysis.KadisonKastler.PointedWordReduction

namespace OAI

/-! # Vacuum moments of arbitrary matrix-site words

Distinct-site product moments determine repeated words as well. The
algebraic reduction is shared across representations and site reindexings.
-/

namespace KadisonKastler

noncomputable section

namespace MatrixSiteWord

variable {I J : Type*}

private def letterAt (w : MatrixSiteWord I) (i : I) : MatrixSiteLetter I := by
  classical
  exact if h : ∃ a ∈ w, a.1 = i then Classical.choose h else (i, 0, 0)

private theorem letterAt_eq (w : MatrixSiteWord I) (hw : (indices w).Nodup)
    (a : MatrixSiteLetter I) (ha : a ∈ w) : letterAt w a.1 = a := by
  classical
  have hex : ∃ b ∈ w, b.1 = a.1 := ⟨a, ha, rfl⟩
  simp only [letterAt, dite_eq_left hex]
  have hb := Classical.choose_spec hex
  exact List.inj_on_of_nodup_map hw hb.1 ha hb.2

def weight (ν : I → ℝ) (w : MatrixSiteWord I) : ℂ :=
  (w.map fun a => if a.2.1 = a.2.2 then (twoSiteWeight (ν a.1) a.2.1 : ℂ) else 0).prod

theorem weight_reindex (ν : I → ℝ) (η : J → ℝ) (e : I ≃ J)
    (h : ∀ i, η (e i) = ν i) (w : MatrixSiteWord I) :
    weight η (reindex e w) = weight ν w := by
  simp only [weight, reindex, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro a ha
  simp only [h]

theorem indices_reindex (e : I ≃ J) (w : MatrixSiteWord I) :
    indices (reindex e w) = (indices w).map e := by
  simp only [indices, reindex, List.map_map, Function.comp_def]

theorem nodup_indices_reindex (e : I ≃ J) (w : MatrixSiteWord I)
    (h : (indices w).Nodup) : (indices (reindex e w)).Nodup := by
  rw [indices_reindex]
  exact h.map e.injective

end MatrixSiteWord

namespace PointedMatrixSites

variable {H K I J : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
variable {Ω : H} {ξ : K} {ν : I → ℝ} {η : J → ℝ}

/-- The finite-site moment axiom applied to a word with distinct indices. -/
theorem word_moment_of_nodup (S : PointedMatrixSites M Ω ν)
    (w : MatrixSiteWord I) (hw : (MatrixSiteWord.indices w).Nodup) :
    inner ℂ Ω (S.wordVector w) = MatrixSiteWord.weight ν w := by
  classical
  let r : I → Fin 2 := fun i => (MatrixSiteWord.letterAt w i).2.1
  let c : I → Fin 2 := fun i => (MatrixSiteWord.letterAt w i).2.2
  have heval : ((MatrixSiteWord.indices w).map
      (fun i => (S.site i).entry (r i) (c i))).prod = S.wordOperator w := by
    unfold MatrixSiteWord.indices wordOperator MatrixSiteWord.eval
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha
    simp only [Function.comp_apply, r, c, MatrixSiteWord.letterAt_eq w hw a ha]
  have hweight : ((MatrixSiteWord.indices w).map
      (fun i => if r i = c i then (twoSiteWeight (ν i) (r i) : ℂ) else 0)).prod =
      MatrixSiteWord.weight ν w := by
    unfold MatrixSiteWord.indices MatrixSiteWord.weight
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha
    simp only [Function.comp_apply, r, c, MatrixSiteWord.letterAt_eq w hw a ha]
  have h := S.moments (MatrixSiteWord.indices w) hw r c
  rw [heval, hweight] at h
  exact h

/-- All vacuum word moments agree after a weight-preserving site bijection,
including words that visit the same site repeatedly. -/
theorem word_moment_eq_of_reindex (S : PointedMatrixSites M Ω ν)
    (T : PointedMatrixSites N ξ η) (e : I ≃ J) (hweight : ∀ i, η (e i) = ν i)
    (w : MatrixSiteWord I) :
    inner ℂ Ω (S.wordVector w) = inner ℂ ξ (T.wordVector (MatrixSiteWord.reindex e w)) := by
  classical
  have hT : ∀ i j, i ≠ j → ∀ a b c d,
      Commute ((T.site (e i)).entry a b) ((T.site (e j)).entry c d) := by
    intro i j hij
    exact T.commuting (e i) (e j) (fun h => hij (e.injective h))
  have hS := MatrixSiteWord.evalOption_reduce S.site S.commuting w
  have hT' := MatrixSiteWord.evalOption_reduce (T.site ∘ e) hT w
  cases hred : MatrixSiteWord.reduce w with
  | none =>
    simp only [hred, MatrixSiteWord.evalOption, Option.elim_none] at hS hT'
    change inner ℂ Ω (MatrixSiteWord.eval S.site w Ω) =
      inner ℂ ξ (MatrixSiteWord.eval T.site (MatrixSiteWord.reindex e w) ξ)
    rw [MatrixSiteWord.eval_reindex, ← hS, ← hT']
    simp
  | some v =>
    simp only [hred, MatrixSiteWord.evalOption, Option.elim_some] at hS hT'
    have hv := MatrixSiteWord.indices_reduce_nodup w v hred
    have hs : S.wordVector w = S.wordVector v := congrArg (fun a : H →L[ℂ] H => a Ω) hS.symm
    have ht : T.wordVector (MatrixSiteWord.reindex e w) =
        T.wordVector (MatrixSiteWord.reindex e v) := by
      change MatrixSiteWord.eval T.site (MatrixSiteWord.reindex e w) ξ =
        MatrixSiteWord.eval T.site (MatrixSiteWord.reindex e v) ξ
      rw [MatrixSiteWord.eval_reindex, MatrixSiteWord.eval_reindex, hT']
    rw [hs, ht, S.word_moment_of_nodup v hv,
      T.word_moment_of_nodup _ (MatrixSiteWord.nodup_indices_reindex e v hv),
      MatrixSiteWord.weight_reindex ν η e hweight]

/-- The shared word Gram matrix is determined by the product moments. -/
theorem word_inner_eq_of_reindex (S : PointedMatrixSites M Ω ν)
    (T : PointedMatrixSites N ξ η) (e : I ≃ J) (hweight : ∀ i, η (e i) = ν i)
    (w v : MatrixSiteWord I) :
    inner ℂ (S.wordVector w) (S.wordVector v) =
      inner ℂ (T.wordVector (MatrixSiteWord.reindex e w))
        (T.wordVector (MatrixSiteWord.reindex e v)) := by
  have hs : inner ℂ (S.wordVector w) (S.wordVector v) =
      inner ℂ Ω (S.wordVector (MatrixSiteWord.star w ++ v)) := by
    change inner ℂ (S.wordOperator w Ω) (S.wordOperator v Ω) = _
    rw [← ContinuousLinearMap.adjoint_inner_right]
    simp only [wordVector, wordOperator_append, wordOperator_star,
      ContinuousLinearMap.star_eq_adjoint, mul_apply_eq_comp]
  have ht : inner ℂ (T.wordVector (MatrixSiteWord.reindex e w))
      (T.wordVector (MatrixSiteWord.reindex e v)) =
      inner ℂ ξ (T.wordVector (MatrixSiteWord.reindex e (MatrixSiteWord.star w ++ v))) := by
    have he : MatrixSiteWord.reindex e (MatrixSiteWord.star w ++ v) =
        MatrixSiteWord.star (MatrixSiteWord.reindex e w) ++ MatrixSiteWord.reindex e v := by
      simp only [MatrixSiteWord.reindex, MatrixSiteWord.star, List.map_append,
        List.map_reverse, List.map_map, Function.comp_def]
    rw [he]
    change inner ℂ (T.wordOperator (MatrixSiteWord.reindex e w) ξ)
      (T.wordOperator (MatrixSiteWord.reindex e v) ξ) = _
    rw [← ContinuousLinearMap.adjoint_inner_right]
    simp only [wordVector, wordOperator_append, wordOperator_star,
      ContinuousLinearMap.star_eq_adjoint, mul_apply_eq_comp]
  rw [hs, ht]
  exact S.word_moment_eq_of_reindex T e hweight _

end PointedMatrixSites

end

end KadisonKastler

end OAI
