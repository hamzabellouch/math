import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Order.Ring.Int

namespace OAI

namespace MatroidProphet
open Set

variable {α : Type*} [Fintype α]

noncomputable def natRank (M : Matroid α) (X : Set α) : ℕ :=
  (M.eRk X).toNat

lemma rank_ne_top (M : Matroid α) (X : Set α) : M.eRk X ≠ ⊤ :=
  (M.isRkFinite_set X).eRk_lt_top.ne

lemma natRank_mono (M : Matroid α) {X Y : Set α} (h : X ⊆ Y) :
    natRank M X ≤ natRank M Y :=
  ENat.toNat_le_toNat (M.eRk_mono h) (rank_ne_top M Y)

omit [Fintype α] in
@[simp] lemma natRank_closure (M : Matroid α) (X : Set α) :
    natRank M (M.closure X) = natRank M X := by
  simp [natRank]

omit [Fintype α] in
@[simp] lemma natRank_empty (M : Matroid α) : natRank M ∅ = 0 := by
  simp [natRank]

lemma natRank_submod (M : Matroid α) (X Y : Set α) :
    natRank M (X ∩ Y) + natRank M (X ∪ Y) ≤ natRank M X + natRank M Y := by
  have h := ENat.toNat_le_toNat (M.eRk_submod X Y)
    (WithTop.add_ne_top.2 ⟨rank_ne_top M X, rank_ne_top M Y⟩)
  simpa only [ENat.toNat_add (rank_ne_top M _) (rank_ne_top M _), natRank] using h

omit [Fintype α] in
lemma flat_inter (M : Matroid α) {X Y : Set α} (hX : M.IsFlat X)
    (hY : M.IsFlat Y) : M.IsFlat (X ∩ Y) := by
  apply Matroid.isFlat_iff_closure_eq.2
  apply Subset.antisymm
  · exact subset_inter ((M.closure_subset_closure inter_subset_left).trans_eq hX.closure)
      ((M.closure_subset_closure inter_subset_right).trans_eq hY.closure)
  · exact M.subset_closure _ (inter_subset_left.trans hX.subset_ground)

noncomputable def densityObjective (M : Matroid α) (κ : ℕ) (D X : Set α) : ℤ :=
  (D ∩ X).ncard - (κ : ℤ) * natRank M X

lemma densityObjective_supermod (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D X Y : Set α) :
    densityObjective M κ D X + densityObjective M κ D Y ≤
      densityObjective M κ D (X ∩ Y) + densityObjective M κ D (M.closure (X ∪ Y)) := by
  have hc := ncard_union_add_ncard_inter (D ∩ X) (D ∩ Y)
  have hm := ncard_mono (inter_subset_inter_right D
    (M.subset_closure (X ∪ Y) (by simp [hE])))
  have hr := natRank_submod M X Y
  have hu : (D ∩ X) ∪ (D ∩ Y) = D ∩ (X ∪ Y) := (Set.inter_union_distrib_left D X Y).symm
  have hi : (D ∩ X) ∩ (D ∩ Y) = D ∩ (X ∩ Y) := (Set.inter_inter_distrib_left D X Y).symm
  rw [hu, hi] at hc
  have hmul : (κ : ℤ) * (natRank M (X ∩ Y) + natRank M (X ∪ Y)) ≤
      (κ : ℤ) * (natRank M X + natRank M Y) := by
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hr) (by exact_mod_cast (Nat.zero_le κ))
  dsimp [densityObjective]
  rw [natRank_closure]
  simp only [mul_add] at hmul
  omega

def IsDensityMax (M : Matroid α) (κ : ℕ) (D P Q : Set α) : Prop :=
  M.IsFlat Q ∧ P ⊆ Q ∧ ∀ Z, M.IsFlat Z → P ⊆ Z →
    densityObjective M κ D Z ≤ densityObjective M κ D Q

lemma exists_densityMax (M : Matroid α) (κ : ℕ) (D P : Set α)
    (hP : P ⊆ M.E) : ∃ Q, IsDensityMax M κ D P Q := by
  obtain ⟨Q, hQ, hmax⟩ := Set.exists_max_image {Z | M.IsFlat Z ∧ P ⊆ Z}
    (densityObjective M κ D) (Set.toFinite _) ⟨M.E, M.ground_isFlat, hP⟩
  exact ⟨Q, hQ.1, hQ.2, fun Z hZ hPZ => hmax Z ⟨hZ, hPZ⟩⟩

lemma densityMax_union (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P : Set α) {Q Q' : Set α}
    (hQ : IsDensityMax M κ D P Q) (hQ' : IsDensityMax M κ D P Q') :
    IsDensityMax M κ D P (M.closure (Q ∪ Q')) := by
  have hPQQ' : P ⊆ Q ∩ Q' := subset_inter hQ.2.1 hQ'.2.1
  have hPc : P ⊆ M.closure (Q ∪ Q') :=
    hQ.2.1.trans ((subset_union_left).trans (M.subset_closure _ (by simp [hE])))
  refine ⟨Matroid.isFlat_closure (M := M) _, hPc, ?_⟩
  intro Z hZ hPZ
  have h1 := hQ.2.2 Z hZ hPZ
  have h2 := hQ'.2.2 (Q ∩ Q') (flat_inter M hQ.1 hQ'.1) hPQQ'
  have h3 := densityObjective_supermod M hE κ D Q Q'
  omega

lemma exists_largest_densityMax (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P : Set α) :
    ∃ Q, IsDensityMax M κ D P Q ∧ ∀ Q', IsDensityMax M κ D P Q' → Q' ⊆ Q := by
  obtain ⟨Q₀, hQ₀⟩ := exists_densityMax M κ D P (by simp [hE])
  obtain ⟨Q, hQ, hmax⟩ := Set.exists_max_image {Z | IsDensityMax M κ D P Z}
    Set.ncard (Set.toFinite _) ⟨Q₀, hQ₀⟩
  refine ⟨Q, hQ, ?_⟩
  intro Q' hQ'
  have hu := densityMax_union M hE κ D P hQ hQ'
  have hcard := hmax _ hu
  have hsub : Q ⊆ M.closure (Q ∪ Q') :=
    subset_union_left.trans (M.subset_closure _ (by simp [hE]))
  have heq : Q = M.closure (Q ∪ Q') := Set.eq_of_subset_of_ncard_le hsub hcard
  rw [heq]
  exact subset_union_right.trans (M.subset_closure _ (by simp [hE]))

noncomputable def densityExpansion (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P : Set α) : Set α :=
  (exists_largest_densityMax M hE κ D P).choose

lemma densityExpansion_spec (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P : Set α) :
    IsDensityMax M κ D P (densityExpansion M hE κ D P) ∧
      ∀ Q, IsDensityMax M κ D P Q → Q ⊆ densityExpansion M hE κ D P :=
  (exists_largest_densityMax M hE κ D P).choose_spec

lemma densityExpansion_extensive (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P : Set α) : P ⊆ densityExpansion M hE κ D P :=
  (densityExpansion_spec M hE κ D P).1.2.1

lemma densityExpansion_flat (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P : Set α) : M.IsFlat (densityExpansion M hE κ D P) :=
  (densityExpansion_spec M hE κ D P).1.1

lemma densityExpansion_mono (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D : Set α) {P P' : Set α} (hPP' : P ⊆ P') :
    densityExpansion M hE κ D P ⊆ densityExpansion M hE κ D P' := by
  let Q := densityExpansion M hE κ D P
  let Q' := densityExpansion M hE κ D P'
  have hQ : IsDensityMax M κ D P Q := (densityExpansion_spec M hE κ D P).1
  have hQ' : IsDensityMax M κ D P' Q' := (densityExpansion_spec M hE κ D P').1
  have hPint : P ⊆ Q ∩ Q' := subset_inter hQ.2.1 (hPP'.trans hQ'.2.1)
  have hP'cl : P' ⊆ M.closure (Q ∪ Q') :=
    hQ'.2.1.trans (subset_union_right.trans (M.subset_closure _ (by simp [hE])))
  have hInt := hQ.2.2 (Q ∩ Q') (flat_inter M hQ.1 hQ'.1) hPint
  have hSup := densityObjective_supermod M hE κ D Q Q'
  have hjoin : IsDensityMax M κ D P' (M.closure (Q ∪ Q')) := by
    refine ⟨Matroid.isFlat_closure (M := M) _, hP'cl, ?_⟩
    intro Z hZ hPZ
    have hm := hQ'.2.2 Z hZ hPZ
    omega
  exact (subset_union_left.trans (M.subset_closure _ (by simp [hE]))).trans
    ((densityExpansion_spec M hE κ D P').2 _ hjoin)

lemma densityExpansion_residual (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P Z : Set α) :
    let Q := densityExpansion M hE κ D P
    (D ∩ (M.closure (Q ∪ Z) \ Q)).ncard + κ * natRank M Q ≤
      κ * natRank M (Q ∪ Z) := by
  dsimp only
  let Q := densityExpansion M hE κ D P
  have hQ : IsDensityMax M κ D P Q := (densityExpansion_spec M hE κ D P).1
  have hQc : Q ⊆ M.closure (Q ∪ Z) :=
    subset_union_left.trans (M.subset_closure _ (by simp [hE]))
  have hmax := hQ.2.2 (M.closure (Q ∪ Z)) (Matroid.isFlat_closure (M := M) _) (hQ.2.1.trans hQc)
  have hc := Set.ncard_sdiff_add_ncard_of_subset (inter_subset_inter_right D hQc)
  have heq : D ∩ (M.closure (Q ∪ Z) \ Q) =
      (D ∩ M.closure (Q ∪ Z)) \ (D ∩ Q) := by ext; simp; tauto
  change (D ∩ (M.closure (Q ∪ Z) \ Q)).ncard + κ * natRank M Q ≤
    κ * natRank M (Q ∪ Z)
  rw [heq]
  dsimp [densityObjective] at hmax
  rw [natRank_closure] at hmax
  exact_mod_cast (show ((D ∩ M.closure (Q ∪ Z)) \ (D ∩ Q)).ncard +
    (κ : ℤ) * natRank M Q ≤ (κ : ℤ) * natRank M (Q ∪ Z) by omega)

omit [Fintype α] in
lemma natRank_eq_ncard_of_basis (M : Matroid α) {I X : Set α}
    (hI : M.IsBasis I X) : natRank M X = I.ncard := by
  rw [natRank, ← hI.encard_eq_eRk, Set.ncard_def]

lemma closure_eq_of_subset_of_natRank_le (M : Matroid α) {X Y : Set α}
    (hXY : X ⊆ Y) (hr : natRank M Y ≤ natRank M X) : M.closure X = M.closure Y := by
  apply (M.isRkFinite_set X).closure_eq_closure_of_subset_of_eRk_ge_eRk hXY
  have hcast : (natRank M Y : ℕ∞) ≤ (natRank M X : ℕ∞) := by exact_mod_cast hr
  simpa only [natRank, ENat.natCast_toNat (rank_ne_top M _)] using hcast

lemma densityExpansion_generated (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D P : Set α) :
    let Q := densityExpansion M hE κ D P
    M.closure (P ∪ (D ∩ Q)) = Q := by
  dsimp only
  let Q := densityExpansion M hE κ D P
  let A := M.closure (P ∪ (D ∩ Q))
  have hQ : IsDensityMax M κ D P Q := (densityExpansion_spec M hE κ D P).1
  have hAQ : A ⊆ Q := by
    exact (M.closure_subset_closure (union_subset hQ.2.1 inter_subset_right)).trans_eq hQ.1.closure
  have hPA : P ⊆ A := subset_union_left.trans (M.subset_closure _ (by simp [hE]))
  have hDA : D ∩ A = D ∩ Q := by
    apply Subset.antisymm (inter_subset_inter_right D hAQ)
    exact fun e he => ⟨he.1, M.subset_closure _ (by simp [hE]) (Or.inr he)⟩
  have hm := hQ.2.2 A (Matroid.isFlat_closure (M := M) _) hPA
  have hr : natRank M Q ≤ natRank M A := by
    dsimp [densityObjective] at hm
    rw [hDA] at hm
    have hm' : (κ : ℤ) * natRank M Q ≤ (κ : ℤ) * natRank M A := by omega
    have hk' : (0 : ℤ) < κ := by exact_mod_cast hκ
    exact_mod_cast (le_of_mul_le_mul_left hm' hk')
  have heq := closure_eq_of_subset_of_natRank_le M hAQ hr
  simpa only [A, M.closure_closure, hQ.1.closure] using heq

lemma exists_extension_generators (M : Matroid α) (hE : M.E = univ)
    (R D Q : Set α) (_hR : M.IsFlat R) (hgen : M.closure (R ∪ D) = Q) :
    ∃ K : Set α, K ⊆ D \ R ∧ M.closure (R ∪ K) = Q ∧
      K.ncard + natRank M R = natRank M Q := by
  obtain ⟨I, hI, hIR⟩ := M.exists_isBasis_union_inter_isBasis D R
    (by simp [hE]) (by simp [hE])
  refine ⟨I \ R, ?_, ?_, ?_⟩
  · intro e he
    refine ⟨?_, he.2⟩
    rcases hI.subset he.1 with hD | hr
    · exact hD
    · exact (he.2 hr).elim
  · apply Subset.antisymm
    · have hsub : R ∪ (I \ R) ⊆ R ∪ D := by
        intro e he
        rcases he with hr | hi
        · exact Or.inl hr
        · rcases hI.subset hi.1 with hd | hr
          · exact Or.inr hd
          · exact Or.inl hr
      exact (M.closure_subset_closure hsub).trans_eq hgen
    · have hIsub : I ⊆ R ∪ (I \ R) := by intro e he; by_cases hr : e ∈ R <;> simp_all
      calc
        Q = M.closure (D ∪ R) := by rw [union_comm D R, hgen]
        _ = M.closure I := hI.closure_eq_closure.symm
        _ ⊆ M.closure (R ∪ (I \ R)) := M.closure_subset_closure hIsub
  · have hiRank : natRank M Q = I.ncard := by
      rw [← hgen, natRank_closure, union_comm R D]
      exact natRank_eq_ncard_of_basis M hI
    rw [natRank_eq_ncard_of_basis M hIR, hiRank]
    simpa only [add_comm] using Set.ncard_inter_add_ncard_sdiff_eq_ncard I R

lemma densityExpansion_generator_step (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D P R : Set α) (hR : M.IsFlat R)
    (hPR : P ⊆ R) (hRQ : R ⊆ densityExpansion M hE κ D P) :
    ∃ K : Set α,
      K ⊆ (D ∩ densityExpansion M hE κ D P) \ R ∧
      M.closure (R ∪ K) = densityExpansion M hE κ D P ∧
      κ * K.ncard + (D ∩ R).ncard ≤
        (D ∩ densityExpansion M hE κ D P).ncard := by
  let Q := densityExpansion M hE κ D P
  have hQ : IsDensityMax M κ D P Q := (densityExpansion_spec M hE κ D P).1
  have hgen : M.closure (R ∪ (D ∩ Q)) = Q := by
    apply Subset.antisymm
    · exact (M.closure_subset_closure (union_subset hRQ inter_subset_right)).trans_eq hQ.1.closure
    · calc
        Q = M.closure (P ∪ (D ∩ Q)) := (densityExpansion_generated M hE κ hκ D P).symm
        _ ⊆ M.closure (R ∪ (D ∩ Q)) :=
          M.closure_subset_closure (union_subset_union hPR Subset.rfl)
  obtain ⟨K, hK, hKgen, hKcard⟩ := exists_extension_generators M hE R (D ∩ Q) Q hR hgen
  refine ⟨K, hK, hKgen, ?_⟩
  have hm := hQ.2.2 R hR hPR
  dsimp [densityObjective] at hm
  have hmul := congrArg (fun x : ℕ => κ * x) hKcard
  rw [Nat.mul_add] at hmul
  exact_mod_cast (show (κ : ℤ) * K.ncard + (D ∩ R).ncard ≤ (D ∩ Q).ncard by
    have hmul' : (κ : ℤ) * K.ncard + (κ : ℤ) * natRank M R =
        (κ : ℤ) * natRank M Q := by exact_mod_cast hmul
    omega)

end MatroidProphet

end OAI
