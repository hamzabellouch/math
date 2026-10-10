import OAI.Analysis.CircleDomains.Topology.CountablePathTimes

namespace OAI

/-! Actual countable path concatenation, including the new limiting endpoint.
The shrinking-tail hypothesis is the one supplied by nested dust collars. -/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X]

def collarPieceIndex (t : PathTime) : ℕ :=
  if h : ⊥ < t then Classical.choose (exists_collarTime_cell h) else 0

theorem collarPieceIndex_spec {t : PathTime} (ht : ⊥ < t) :
    collarTime (collarPieceIndex t + 1) < t ∧ t ≤ collarTime (collarPieceIndex t) := by
  simp only [collarPieceIndex, dite_eq_left ht]
  exact Classical.choose_spec (exists_collarTime_cell ht)

def collarPiece (γ : ℕ → C(PathTime, X)) (n : ℕ) : C(PathTime, X) :=
  (γ n).comp (rescalePathTime (collarTime (n + 1)) (collarTime n))

theorem collarPiece_lower (γ : ℕ → C(PathTime, X)) (n : ℕ) :
    collarPiece γ n (collarTime (n + 1)) = γ n ⊥ := by
  have h := rescale_affinePathTime (collarTime_strictAnti (Nat.lt_succ_self n)) ⊥
  rw [affinePathTime_zero] at h
  change γ n _ = γ n ⊥
  rw [h]

theorem collarPiece_upper (γ : ℕ → C(PathTime, X)) (n : ℕ) :
    collarPiece γ n (collarTime n) = γ n ⊤ := by
  have h := rescale_affinePathTime (collarTime_strictAnti (Nat.lt_succ_self n)) ⊤
  rw [affinePathTime_one] at h
  change γ n _ = γ n ⊤
  rw [h]

theorem collarPieces_agree (γ : ℕ → C(PathTime, X))
    (hjoin : ∀ n, γ (n + 1) ⊤ = γ n ⊥) {i j : ℕ} {t : PathTime}
    (hi : t ∈ collarCell i) (hj : t ∈ collarCell j) :
    collarPiece γ i t = collarPiece γ j t := by
  wlog hij : i ≤ j generalizing i j
  · exact (this hj hi (Nat.le_of_not_ge hij)).symm
  rcases hij.eq_or_lt with rfl | hij
  · rfl
  have hji : j ≤ i + 1 := by
    by_contra hn
    have hb := collarTime_strictAnti (Nat.lt_of_not_ge hn)
    exact (hj.2.trans_lt hb).not_ge hi.1
  have heq : j = i + 1 := le_antisymm hji (Nat.succ_le_of_lt hij)
  subst j
  have ht : t = collarTime (i + 1) := le_antisymm hj.2 hi.1
  rw [ht, collarPiece_lower, collarPiece_upper, hjoin]

def collarConcatenationFun (p : X) (γ : ℕ → C(PathTime, X)) (t : PathTime) : X :=
  if t = ⊥ then p else collarPiece γ (collarPieceIndex t) t

theorem collarConcatenation_on_cell (p : X) (γ : ℕ → C(PathTime, X))
    (hjoin : ∀ n, γ (n + 1) ⊤ = γ n ⊥) (n : ℕ) {t : PathTime}
    (ht : t ∈ collarCell n) :
    collarConcatenationFun p γ t = collarPiece γ n t := by
  have hpos : ⊥ < t := (collarTime_pos (n + 1)).trans_le ht.1
  rw [collarConcatenationFun, ite_eq_right (ne_of_gt hpos)]
  exact collarPieces_agree γ hjoin
    ⟨(collarPieceIndex_spec hpos).1.le, (collarPieceIndex_spec hpos).2⟩ ht

theorem collarConcatenation_continuous_positive (p : X) (γ : ℕ → C(PathTime, X))
    (hjoin : ∀ n, γ (n + 1) ⊤ = γ n ⊥) :
    Continuous (fun t : PositivePathTime => collarConcatenationFun p γ t) := by
  apply collarCells_locallyFinite.continuous collarCells_cover_positive
  · intro n
    exact isClosed_Icc.preimage continuous_subtype_val
  · intro n
    apply ((collarPiece γ n).continuous.comp continuous_subtype_val).continuousOn.congr
    intro t ht
    exact collarConcatenation_on_cell p γ hjoin n ht

theorem collarConcatenation_continuous (p : X) (γ : ℕ → C(PathTime, X))
    (hjoin : ∀ n, γ (n + 1) ⊤ = γ n ⊥)
    (htail : ∀ V ∈ 𝓝 p, ∃ N : ℕ, ∀ n ≥ N, ∀ s, γ n s ∈ V) :
    Continuous (collarConcatenationFun p γ) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t = ⊥
  · subst t
    change Tendsto _ _ (𝓝 (collarConcatenationFun p γ ⊥))
    have heq : collarConcatenationFun p γ ⊥ = p := by
      simp [collarConcatenationFun]
    rw [heq]
    apply tendsto_def.mpr
    intro V hV
    obtain ⟨N, hN⟩ := htail V hV
    filter_upwards [gt_mem_nhds (collarTime_pos N)] with t ht
    change collarConcatenationFun p γ t ∈ V
    by_cases ht0 : t = ⊥
    · simpa only [collarConcatenationFun, ite_eq_left ht0] using mem_of_mem_nhds hV
    · have hpos : ⊥ < t := bot_lt_iff_ne_bot.mpr ht0
      have hidx : N ≤ collarPieceIndex t := by
        by_contra hn
        have hb := collarTime_strictAnti.antitone
          (Nat.succ_le_of_lt (Nat.lt_of_not_ge hn))
        exact (ht.trans_le hb).not_ge (collarPieceIndex_spec hpos).1.le
      simp only [collarConcatenationFun, ite_eq_right ht0, collarPiece, ContinuousMap.comp_apply]
      exact hN _ hidx _
  · have hpos : t ∈ Ioi (⊥ : PathTime) := bot_lt_iff_ne_bot.mpr ht
    have hcont : ContinuousOn (collarConcatenationFun p γ) (Ioi ⊥) :=
      continuousOn_iff_continuous_domRestrict.mpr
        (collarConcatenation_continuous_positive p γ hjoin)
    exact (hcont t hpos).continuousAt (isOpen_Ioi.mem_nhds hpos)

def collarConcatenation (p : X) (γ : ℕ → C(PathTime, X))
    (hjoin : ∀ n, γ (n + 1) ⊤ = γ n ⊥)
    (htail : ∀ V ∈ 𝓝 p, ∃ N : ℕ, ∀ n ≥ N, ∀ s, γ n s ∈ V) : C(PathTime, X) :=
  ⟨collarConcatenationFun p γ, collarConcatenation_continuous p γ hjoin htail⟩

theorem collarConcatenation_zero (p : X) (γ : ℕ → C(PathTime, X)) hjoin htail :
    collarConcatenation p γ hjoin htail ⊥ = p := by
  simp [collarConcatenation, collarConcatenationFun]

theorem collarConcatenation_affine (p : X) (γ : ℕ → C(PathTime, X)) hjoin htail
    (n : ℕ) (s : PathTime) :
    collarConcatenation p γ hjoin htail
      (affinePathTime (collarTime (n + 1)) (collarTime n) s) = γ n s := by
  change collarConcatenationFun p γ _ = _
  rw [collarConcatenation_on_cell p γ hjoin n
    (affinePathTime_mem_Icc (collarTime_strictAnti (Nat.lt_succ_self n)).le s)]
  change γ n _ = γ n s
  rw [rescale_affinePathTime (collarTime_strictAnti (Nat.lt_succ_self n))]

theorem collarConcatenation_one (p : X) (γ : ℕ → C(PathTime, X)) hjoin htail :
    collarConcatenation p γ hjoin htail ⊤ = γ 0 ⊤ := by
  have h := collarConcatenation_affine p γ hjoin htail 0 ⊤
  rwa [affinePathTime_one, collarTime_zero] at h

end CircleDomainRigidity

end

end OAI
