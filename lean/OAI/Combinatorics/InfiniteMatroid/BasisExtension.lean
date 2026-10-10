import OAI.Combinatorics.InfiniteMatroid.LocalBases

namespace OAI

section
open Set Filter
open scoped Topology symmDiff
namespace InfiniteMatroidCounterexample

lemma sameClass_compl {T X : Set E0} (h : SameClass T X) : SameClass Tᶜ Xᶜ := by
  have he : Xᶜ ∆ Tᶜ = X ∆ T := by ext x; simp only [mem_symmDiff, mem_compl_iff]; tauto
  simpa only [SameClass, he] using h

lemma sameClass_add {T X P : Set E0} (h : SameClass T X) (hP : Small P) : SameClass T (X ∪ P) := by
  apply sameClass_trans h
  apply small_subset hP
  intro x hx
  simp only [mem_symmDiff, Set.mem_union] at hx
  tauto

lemma sameClass_delete {T X P : Set E0} (h : SameClass T X) (hP : Small P) : SameClass T (X \ P) := by
  apply sameClass_trans h
  apply small_subset hP
  intro x hx
  simp only [mem_symmDiff, Set.mem_sdiff] at hx
  tauto

lemma positive_sameClass {T X : Set E0} (hT : ¬ Small T) (h : SameClass T X) : ¬ Small X := by
  intro hX
  apply hT
  apply small_subset (small_union hX h)
  intro x hx
  simp only [Set.mem_union, mem_symmDiff]
  tauto

lemma positive_pool_delete {T X G : Set E0} (hX : SameClass T X)
    (hG : ¬ Small G) (hGX : G ⊆ X) :
    ∃ P, P ⊆ G ∧ Small P ∧ Tendsto (fun n ↦ fProbe T n (X \ P)) atTop atBot := by
  obtain ⟨P,hPG,hP,ht⟩ := positive_pool_add (sameClass_compl hX) hG (by simpa using hGX)
  refine ⟨P,hPG,hP,?_⟩
  have he (n : ℕ) : fProbe T n (X \ P) = -fProbe Tᶜ n (Xᶜ ∪ P) := by
    have hc : (X \ P)ᶜ = Xᶜ ∪ P := by ext x; simp only [mem_compl_iff, Set.mem_sdiff, Set.mem_union]; tauto
    rw [← hc, fProbe_compl, neg_neg]
  simpa only [he, Function.comp_def] using (tendsto_neg_atTop_atBot.comp ht)

lemma localLower_self (T : Set E0) : T ∈ LocalLower T := by
  refine ⟨sameClass_refl _,?_⟩
  have hz (n : ℕ) : fProbe T n T = 0 := by
    have hd : dProbe T T = fun _ ↦ 0 := funext fun _ ↦ sub_self _
    have ht (n : ℕ) : tailSup (fun _ ↦ (0:ℝ)) n = 0 ∧ tailInf (fun _ ↦ (0:ℝ)) n = 0 := by
      simp [tailSup, tailInf, (nonempty_Ici (a := n)).image_const]
    simp [fProbe, pProbe, hd, (ht n).1, (ht n).2]
  simp [LowerBasis, probeLiminf, hz]

lemma localLower_swap {T B : Set E0} (hB : B ∈ LocalLower T)
    (e : E0) (he : e ∈ B) (f : E0) (hf : f ∉ B) : insert f (B \ {e}) ∈ LocalLower T := by
  have heq : B \ (B \ {e}) = {e} := by ext x; simp only [Set.mem_sdiff, Set.mem_singleton_iff]; aesop
  have hfq : insert f (B \ {e}) \ (B \ {e}) = {f} := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
    have : f ∉ B \ {e} := fun h ↦ hf h.1
    aesop
  have h1 := finite_change_eventually (T := T) (Set.sdiff_subset : B \ {e} ⊆ B)
    (show (B \ (B \ {e})).Finite by rw [heq]; exact finite_singleton e)
  have h2 := finite_change_eventually (T := T) (subset_insert f (B \ {e}))
    (show (insert f (B \ {e}) \ (B \ {e})).Finite by rw [hfq]; exact finite_singleton f)
  simp only [heq, hfq, ncard_singleton, Nat.cast_one] at h1 h2
  have hevent : ∀ᶠ n in atTop, fProbe T n (insert f (B \ {e})) = fProbe T n B + 0 := by
    filter_upwards [h1,h2] with n hn1 hn2
    rw [hn2, hn1, add_zero]
  have hlim := probeLiminf_finite_change hevent
  simp only [EReal.coe_zero, add_zero] at hlim
  refine ⟨?_,by simpa only [LowerBasis,hlim] using hB.2⟩
  have hclass := sameClass_add (sameClass_delete hB.1 (small_finite (finite_singleton e)))
    (small_finite (finite_singleton f))
  simpa only [Set.union_singleton] using hclass

lemma localLower_correct_up {T X G : Set E0} (hX : SameClass T X)
    (hG : ¬ Small G) (hGX : G ⊆ Xᶜ) (hlo : probeLiminf (fProbe T) X ≤ -1) :
    ∃ B ∈ LocalLower T, X ⊆ B ∧ B ⊆ X ∪ G := by
  obtain ⟨P,hPG,hP,ht⟩ := positive_pool_add hX hG hGX
  have hlim : probeLiminf (fProbe T) (X ∪ P) = ⊤ := (EReal.tendsto_coe_atTop.comp ht).liminf_eq
  obtain ⟨B,hXB,hBP,hBT,hB⟩ := fProbe_interpolation hX (sameClass_add hX hP)
    (Set.subset_union_left) hlo (by rw [hlim]; exact EReal.coe_lt_top 0)
  exact ⟨B,⟨hBT,hB⟩,hXB,hBP.trans (union_subset_union_right X hPG)⟩

lemma localLower_correct_down {T X G : Set E0} (hX : SameClass T X)
    (hG : ¬ Small G) (hGX : G ⊆ X) (hhi : 0 < probeLiminf (fProbe T) X) :
    ∃ B ∈ LocalLower T, X \ G ⊆ B ∧ B ⊆ X := by
  obtain ⟨P,hPG,hP,ht⟩ := positive_pool_delete hX hG hGX
  have hlim : probeLiminf (fProbe T) (X \ P) = ⊥ := (EReal.tendsto_coe_atBot.comp ht).liminf_eq
  obtain ⟨B,hPB,hBX,hBT,hB⟩ := fProbe_interpolation (sameClass_delete hX hP) hX
    sdiff_subset (by rw [hlim]; exact bot_le) hhi
  exact ⟨B,⟨hBT,hB⟩,(Set.sdiff_subset_sdiff_right hPG).trans hPB,hBX⟩

/-- Upper rule with its complement identity built into the definition. -/
def LocalUpper (T : Set E0) : Set (Set E0) := {X | Xᶜ ∈ LocalLower Tᶜ}

lemma localUpper_iff (T X : Set E0) : X ∈ LocalUpper T ↔
    SameClass T X ∧ 0 ≤ limsup (fun n ↦ (fProbe T n X : EReal)) atTop ∧
      limsup (fun n ↦ (fProbe T n X : EReal)) atTop < 1 := by
  have hc : SameClass Tᶜ Xᶜ ↔ SameClass T X :=
    ⟨fun h ↦ by simpa using sameClass_compl h, sameClass_compl⟩
  have he : probeLiminf (fProbe Tᶜ) Xᶜ = -limsup (fun n ↦ (fProbe T n X : EReal)) atTop := by
    simp only [probeLiminf, fProbe_compl, EReal.coe_neg]
    exact EReal.liminf_neg
  simp only [LocalUpper, Set.mem_ofPred_eq, LocalLower, LowerBasis, hc, he]
  simp only [EReal.neg_le_zero, EReal.lt_neg_comm, neg_neg]
  tauto

def LocalRule (upper : Bool) (T : Set E0) : Set (Set E0) :=
  if upper then LocalUpper T else LocalLower T

lemma localRule_class {s : Bool} {T X : Set E0} (h : X ∈ LocalRule s T) : SameClass T X := by
  cases s with
  | false => exact h.1
  | true =>
    change Xᶜ ∈ LocalLower Tᶜ at h
    simpa using sameClass_compl h.1

lemma localRule_self (s : Bool) (T : Set E0) : T ∈ LocalRule s T := by
  cases s with
  | false => exact localLower_self _
  | true =>
    change Tᶜ ∈ LocalLower Tᶜ
    exact localLower_self Tᶜ

lemma localRule_compl {s : Bool} {T X : Set E0} (h : X ∈ LocalRule s T) :
    Xᶜ ∈ LocalRule (!s) Tᶜ := by
  cases s with
  | false => simpa [LocalRule,LocalUpper] using h
  | true => exact h

lemma localRule_antichain (s : Bool) (T : Set E0) :
    ∀ ⦃X Y⦄, X ∈ LocalRule s T → Y ∈ LocalRule s T → X ⊆ Y → X = Y := by
  cases s with
  | false => exact localLower_antichain T
  | true =>
    intro X Y hX hY hXY
    have he := localLower_antichain Tᶜ hY hX (compl_subset_compl.mpr hXY)
    exact compl_injective he.symm

lemma localRule_swap {s : Bool} {T B : Set E0} (hB : B ∈ LocalRule s T)
    (e : E0) (he : e ∈ B) (f : E0) (hf : f ∉ B) : insert f (B \ {e}) ∈ LocalRule s T := by
  cases s with
  | false => exact localLower_swap hB e he f hf
  | true =>
    have hc : (insert f (B \ {e}))ᶜ = insert e (Bᶜ \ {f}) := by
      ext x
      simp only [mem_compl_iff, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
      have hx1 : x = e → x ∈ B := fun h ↦ h ▸ he
      have hx2 : x = f → x ∉ B := fun h ↦ h ▸ hf
      tauto
    change (insert f (B \ {e}))ᶜ ∈ LocalLower Tᶜ
    rw [hc]
    change Bᶜ ∈ LocalLower Tᶜ at hB
    exact localLower_swap hB f hf e (by simpa using he)

lemma localLower_interval {T I Y : Set E0} (hT : ¬ Small T) (hTc : ¬ Small Tᶜ)
    (hIY : I ⊆ Y) (hI : SameClass T I) (hY : SameClass T Y) :
    ∃ B ∈ LocalLower T, B ⊆ I ∨ (I ⊆ B ∧ B ⊆ Y) ∨ Y ⊆ B := by
  by_cases hlo : -1 < probeLiminf (fProbe T) I
  · by_cases hhi : probeLiminf (fProbe T) I ≤ 0
    · exact ⟨I,⟨hI,hlo,hhi⟩,Or.inl Subset.rfl⟩
    · obtain ⟨B,hB,_,hBI⟩ := localLower_correct_down hI (positive_sameClass hT hI)
        Subset.rfl (lt_of_not_ge hhi)
      exact ⟨B,hB,Or.inl hBI⟩
  · by_cases hhi : 0 < probeLiminf (fProbe T) Y
    · obtain ⟨B,hIB,hBY,hBT,hB⟩ := fProbe_interpolation hI hY hIY (le_of_not_gt hlo) hhi
      exact ⟨B,⟨hBT,hB⟩,Or.inr (Or.inl ⟨hIB,hBY⟩)⟩
    · by_cases hyl : -1 < probeLiminf (fProbe T) Y
      · exact ⟨Y,⟨hY,hyl,le_of_not_gt hhi⟩,Or.inr (Or.inr Subset.rfl)⟩
      · obtain ⟨B,hB,hYB,_⟩ := localLower_correct_up hY
          (positive_sameClass hTc (sameClass_compl hY)) Subset.rfl (le_of_not_gt hyl)
        exact ⟨B,hB,Or.inr (Or.inr hYB)⟩

lemma localLower_lower_endpoint {T I Y : Set E0} (hT : ¬ Small T)
    (hIY : I ⊆ Y) (hI : SameClass T I) (hgap : ¬ Small (Y \ I)) :
    ∃ B ∈ LocalLower T, B ⊆ I ∨ (I ⊆ B ∧ B ⊆ Y) := by
  by_cases hlo : -1 < probeLiminf (fProbe T) I
  · by_cases hhi : probeLiminf (fProbe T) I ≤ 0
    · exact ⟨I,⟨hI,hlo,hhi⟩,Or.inl Subset.rfl⟩
    · obtain ⟨B,hB,_,hBI⟩ := localLower_correct_down hI (positive_sameClass hT hI)
        Subset.rfl (lt_of_not_ge hhi)
      exact ⟨B,hB,Or.inl hBI⟩
  · obtain ⟨B,hB,hIB,hBY⟩ := localLower_correct_up hI hgap (fun _ hx ↦ hx.2) (le_of_not_gt hlo)
    exact ⟨B,hB,Or.inr ⟨hIB,hBY.trans (union_subset hIY sdiff_subset)⟩⟩

lemma localLower_upper_endpoint {T I Y : Set E0} (hTc : ¬ Small Tᶜ)
    (hIY : I ⊆ Y) (hY : SameClass T Y) (hgap : ¬ Small (Y \ I)) :
    ∃ B ∈ LocalLower T, (I ⊆ B ∧ B ⊆ Y) ∨ Y ⊆ B := by
  by_cases hhi : 0 < probeLiminf (fProbe T) Y
  · obtain ⟨B,hB,hIB,hBY⟩ := localLower_correct_down hY hgap sdiff_subset hhi
    exact ⟨B,hB,Or.inl ⟨(by intro x hx; exact hIB ⟨hIY hx,fun h ↦ h.2 hx⟩),hBY⟩⟩
  · by_cases hlo : -1 < probeLiminf (fProbe T) Y
    · exact ⟨Y,⟨hY,hlo,le_of_not_gt hhi⟩,Or.inr Subset.rfl⟩
    · obtain ⟨B,hB,hYB,_⟩ := localLower_correct_up hY
        (positive_sameClass hTc (sameClass_compl hY)) Subset.rfl (le_of_not_gt hlo)
      exact ⟨B,hB,Or.inr hYB⟩

lemma localRule_interval (s : Bool) {T I Y : Set E0} (hT : ¬ Small T) (hTc : ¬ Small Tᶜ)
    (hIY : I ⊆ Y) (hI : SameClass T I) (hY : SameClass T Y) :
    ∃ B ∈ LocalRule s T, B ⊆ I ∨ (I ⊆ B ∧ B ⊆ Y) ∨ Y ⊆ B := by
  cases s with
  | false => exact localLower_interval hT hTc hIY hI hY
  | true =>
    obtain ⟨B,hB,hBI | ⟨hIB,hBY⟩ | hYB⟩ := localLower_interval hTc (by simpa using hT)
      (compl_subset_compl.mpr hIY) (sameClass_compl hY) (sameClass_compl hI)
    · refine ⟨Bᶜ,?_,Or.inr (Or.inr ?_)⟩
      · simpa [LocalRule,LocalUpper] using hB
      · simpa using compl_subset_compl.mpr hBI
    · refine ⟨Bᶜ,?_,Or.inr (Or.inl ⟨?_,?_⟩)⟩
      · simpa [LocalRule,LocalUpper] using hB
      · simpa using compl_subset_compl.mpr hBY
      · simpa using compl_subset_compl.mpr hIB
    · refine ⟨Bᶜ,?_,Or.inl ?_⟩
      · simpa [LocalRule,LocalUpper] using hB
      · simpa using compl_subset_compl.mpr hYB

lemma localRule_lower_endpoint (s : Bool) {T I Y : Set E0} (hT : ¬ Small T) (_hTc : ¬ Small Tᶜ)
    (hIY : I ⊆ Y) (hI : SameClass T I) (hgap : ¬ Small (Y \ I)) :
    ∃ B ∈ LocalRule s T, B ⊆ I ∨ (I ⊆ B ∧ B ⊆ Y) := by
  cases s with
  | false => exact localLower_lower_endpoint hT hIY hI hgap
  | true =>
    have hg : ¬ Small (Iᶜ \ Yᶜ) := by
      have he : Iᶜ \ Yᶜ = Y \ I := by ext x; simp only [Set.mem_sdiff,mem_compl_iff]; tauto
      rwa [he]
    obtain ⟨B,hB,⟨hIB,hBY⟩ | hYB⟩ := localLower_upper_endpoint (T := Tᶜ) (I := Yᶜ) (Y := Iᶜ)
      (by simpa only [compl_compl] using hT)
      (compl_subset_compl.mpr hIY) (sameClass_compl hI) hg
    · refine ⟨Bᶜ,?_,Or.inr ⟨?_,?_⟩⟩
      · simpa [LocalRule,LocalUpper] using hB
      · simpa using compl_subset_compl.mpr hBY
      · simpa using compl_subset_compl.mpr hIB
    · refine ⟨Bᶜ,?_,Or.inl ?_⟩
      · simpa [LocalRule,LocalUpper] using hB
      · simpa using compl_subset_compl.mpr hYB

lemma localRule_upper_endpoint (s : Bool) {T I Y : Set E0} (_hT : ¬ Small T) (hTc : ¬ Small Tᶜ)
    (hIY : I ⊆ Y) (hY : SameClass T Y) (hgap : ¬ Small (Y \ I)) :
    ∃ B ∈ LocalRule s T, (I ⊆ B ∧ B ⊆ Y) ∨ Y ⊆ B := by
  cases s with
  | false => exact localLower_upper_endpoint hTc hIY hY hgap
  | true =>
    have hg : ¬ Small (Iᶜ \ Yᶜ) := by
      have he : Iᶜ \ Yᶜ = Y \ I := by ext x; simp only [Set.mem_sdiff,mem_compl_iff]; tauto
      rwa [he]
    obtain ⟨B,hB,hBI | ⟨hIB,hBY⟩⟩ := localLower_lower_endpoint hTc
      (compl_subset_compl.mpr hIY) (sameClass_compl hY) hg
    · refine ⟨Bᶜ,?_,Or.inr ?_⟩
      · simpa [LocalRule,LocalUpper] using hB
      · simpa using compl_subset_compl.mpr hBI
    · refine ⟨Bᶜ,?_,Or.inl ⟨?_,?_⟩⟩
      · simpa [LocalRule,LocalUpper] using hB
      · simpa using compl_subset_compl.mpr hBY
      · simpa using compl_subset_compl.mpr hIB

end InfiniteMatroidCounterexample
end

end OAI
