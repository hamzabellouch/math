import OAI.Probability.MatroidProphet.Density.Basic

namespace OAI

namespace MatroidProphet
open Set

variable {α : Type*} [Fintype α]

private lemma densityPath_prefix (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D : Set α) (P : ℕ → Set α) (hP : Monotone P) (N : ℕ) :
    ∃ J : ℕ → Set α, Monotone J ∧ (∀ k, J k ⊆ D) ∧
      (∀ k ≤ N, M.closure (P k ∪ J k) = densityExpansion M hE κ D (P k)) ∧
      κ * (J N).ncard ≤ (D ∩ densityExpansion M hE κ D (P N)).ncard ∧
      (∀ k, N ≤ k → J k = J N) := by
  induction N with
  | zero =>
    have hPQ : M.closure (P 0) ⊆ densityExpansion M hE κ D (P 0) := by
      exact (M.closure_subset_closure (densityExpansion_extensive M hE κ D (P 0))).trans_eq
        (densityExpansion_flat M hE κ D (P 0)).closure
    obtain ⟨K, hK, hgen, hcard⟩ := densityExpansion_generator_step M hE κ hκ D (P 0)
      (M.closure (P 0)) (Matroid.isFlat_closure (M := M) _)
      (M.subset_closure _ (by simp [hE])) hPQ
    refine ⟨fun _ => K, fun _ _ _ => Subset.rfl, ?_, ?_, ?_, ?_⟩
    · exact fun _ _ he => (hK he).1.1
    · intro k hk
      have hk0 : k = 0 := by omega
      subst k
      simpa only [M.closure_union_closure_left_eq] using hgen
    · dsimp only
      omega
    · exact fun _ _ => rfl
  | succ N ih =>
    obtain ⟨J, hJmono, hJD, hJgen, hJcard, hJsat⟩ := ih
    let Q := densityExpansion M hE κ D (P N)
    let Q' := densityExpansion M hE κ D (P (N + 1))
    let R := M.closure (P (N + 1) ∪ Q)
    have hQQ' : Q ⊆ Q' := densityExpansion_mono M hE κ D (hP (Nat.le_succ N))
    have hRflat : M.IsFlat R := Matroid.isFlat_closure (M := M) _
    have hPR : P (N + 1) ⊆ R :=
      subset_union_left.trans (M.subset_closure _ (by simp [hE]))
    have hQR : Q ⊆ R := subset_union_right.trans (M.subset_closure _ (by simp [hE]))
    have hRQ' : R ⊆ Q' := by
      exact (M.closure_subset_closure
        (union_subset (densityExpansion_extensive M hE κ D _) hQQ')).trans_eq
        (densityExpansion_flat M hE κ D _).closure
    obtain ⟨K, hK, hKgen, hKcard⟩ :=
      densityExpansion_generator_step M hE κ hκ D (P (N + 1)) R hRflat hPR hRQ'
    have hJNQ : J N ⊆ Q := by
      change J N ⊆ densityExpansion M hE κ D (P N)
      rw [← hJgen N le_rfl]
      exact subset_union_right.trans (M.subset_closure _ (by simp [hE]))
    have hJNR : J N ⊆ R := hJNQ.trans hQR
    have hdisj : Disjoint (J N) K := by
      rw [Set.disjoint_left]
      intro e heJ heK
      exact (hK heK).2 (hJNR heJ)
    have hRgen : M.closure (P (N + 1) ∪ J N) = R := by
      apply Subset.antisymm
      · exact M.closure_subset_closure (union_subset_union Subset.rfl hJNQ)
      · apply Matroid.closure_subset_closure_of_subset_closure
        apply union_subset
        · exact subset_union_left.trans (M.subset_closure _ (by simp [hE]))
        · change densityExpansion M hE κ D (P N) ⊆ _
          rw [← hJgen N le_rfl]
          exact M.closure_subset_closure (union_subset_union (hP (Nat.le_succ N)) Subset.rfl)
    have hnewgen : M.closure (P (N + 1) ∪ (J N ∪ K)) = Q' := by
      calc
        M.closure (P (N + 1) ∪ (J N ∪ K)) =
            M.closure ((P (N + 1) ∪ J N) ∪ K) := by rw [union_assoc]
        _ = M.closure (M.closure (P (N + 1) ∪ J N) ∪ K) :=
          (M.closure_union_closure_left_eq _ _).symm
        _ = M.closure (R ∪ K) := by rw [hRgen]
        _ = Q' := hKgen
    have hnewcard : κ * (J N ∪ K).ncard ≤ (D ∩ Q').ncard := by
      rw [Set.ncard_union_eq hdisj, Nat.mul_add]
      have hm := Set.ncard_mono (inter_subset_inter_right D hQR)
      change κ * K.ncard + (D ∩ R).ncard ≤ (D ∩ Q').ncard at hKcard
      change κ * (J N).ncard ≤ (D ∩ Q).ncard at hJcard
      omega
    let J' : ℕ → Set α := fun k => if k ≤ N then J k else J N ∪ K
    have hJ'last : J' (N + 1) = J N ∪ K := by simp [J']
    refine ⟨J', ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      by_cases hi : i ≤ N
      · by_cases hj : j ≤ N
        · simpa [J', hi, hj] using hJmono hij
        · change (if i ≤ N then J i else J N ∪ K) ⊆ _
          rw [ite_eq_left hi]
          simpa only [J', ite_eq_right hj] using (hJmono hi).trans subset_union_left
      · have hj : ¬j ≤ N := by omega
        simp only [J', ite_eq_right hi, ite_eq_right hj]
        exact Subset.rfl
    · intro k e he
      by_cases hk : k ≤ N
      · exact hJD k (by simpa [J', hk] using he)
      · have he' : e ∈ J N ∪ K := by simpa [J', hk] using he
        rcases he' with heJ | heK
        · exact hJD N heJ
        · exact (hK heK).1.1
    · intro k hk
      by_cases hk' : k ≤ N
      · simpa [J', hk'] using hJgen k hk'
      · have heq : k = N + 1 := by omega
        subst k
        rw [hJ'last]
        exact hnewgen
    · rw [hJ'last]
      exact hnewcard
    · intro k hk
      have hk' : ¬ k ≤ N := by omega
      rw [hJ'last]
      simp [J', hk']

lemma densityPath_generators (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D : Set α) (P : ℕ → Set α) (hP : Monotone P) (N : ℕ) :
    ∃ Jtotal : Set α, Jtotal ⊆ D ∧ κ * Jtotal.ncard ≤ D.ncard ∧
      ∃ J : ℕ → Set α, Monotone J ∧ (∀ k ≤ N, J k ⊆ Jtotal) ∧
        (∀ k ≤ N, M.closure (P k ∪ J k) = densityExpansion M hE κ D (P k)) := by
  obtain ⟨J, hmono, hD, hgen, hcard, _⟩ := densityPath_prefix M hE κ hκ D P hP N
  refine ⟨J N, hD N, ?_, J, hmono, ?_, hgen⟩
  · exact hcard.trans (Set.ncard_mono inter_subset_left)
  · exact fun k hk => hmono hk

end MatroidProphet

end OAI
