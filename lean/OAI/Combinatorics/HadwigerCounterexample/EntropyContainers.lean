import OAI.Combinatorics.HadwigerCounterexample.FiniteEntropy
import Mathlib.Data.Finset.Card

namespace OAI

/-! # Entropy Containers -/

noncomputable section
open scoped BigOperators
open Real Finset
namespace HadwigerCounterexample

variable {α : Type*} [Fintype α]

private theorem avg_reached {w f : Wgt α} (hw : IsLaw w) :
    ∃ x, 0 < w x ∧ avg w f ≤ f x := by
  by_contra! hn
  have hp := exists_of_pr_pos (p:=fun _ => True) hw.nz (by rw [pr_true, hw.total]; norm_num)
  obtain ⟨x, _, hx⟩ := hp
  have h : avg w f < avg w (fun _ => avg w f) := by
    unfold avg
    apply Finset.sum_lt_sum
    · intro y _
      by_cases h : 0 < w y
      · exact mul_le_mul_of_nonneg_left (hn y h).le h.le
      · rw [le_antisymm (le_of_not_gt h) (hw.nz _), zero_mul, zero_mul]
    · exact ⟨x, mem_univ _, mul_lt_mul_of_pos_left (hn x hx) hx⟩
  rw [hw.avg_const] at h
  exact lt_irrefl _ h

omit [Fintype α] in
theorem closed_carried (p : α → Prop) : IsClosed {w : Wgt α | carried w p} := by
  have he : {w : Wgt α | carried w p} = ⋂ (x : α) (_ : ¬ p x), {w | w x = 0} := by
    ext; simp [carried]
  rw [he]
  exact isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_eq (continuous_apply x)
    continuous_const

/-- Cover the conflict-independent sets in R by a small family of terminal sets. -/
theorem containers {ok : Set (Wgt α)} (hcomp : IsCompact ok) (hok : ∀ w ∈ ok, IsLaw w)
    (hmid : ∀ w ∈ ok, ∀ v ∈ ok, midLaw w v ∈ ok) (rel : α → α → Prop)
    {e : ℝ} (he : 0 < e) (R : Finset α)
    (hsat : ∀ w ∈ ok, carried w (· ∈ R) →
      e ≤ pr (pairW w w) (fun x => rel x.1 x.2))
    (L : ℕ) (hL : ∀ w ∈ ok, carried w (· ∈ R) →
      0 < negEnt w + L * (e * Real.log 2)) :
    ∃ C : Finset (Finset α),
      C.card ≤ (R.card + 1)^L ∧
      (∀ r ∈ C, r ⊆ R ∧ ¬∃ w ∈ ok, carried w (· ∈ r)) ∧
      ∀ I : Finset α, I ⊆ R → (∀ v ∈ I, ∀ u ∈ I, ¬rel v u) →
        ∃ r ∈ C, I ⊆ r := by
  classical
  induction R using Finset.strongInductionOn generalizing L with | _ R ih
  by_cases h : ∃ w ∈ ok, carried w (· ∈ R)
  · let T := ok ∩ {w : Wgt α | carried w (· ∈ R)}
    have hn : T.Nonempty := h
    obtain ⟨w, hw, hwmin⟩ := (hcomp.inter_right (closed_carried (· ∈ R))).exists_isMinOn hn
      negEnt_continuous.continuousOn
    have hwL := hok w hw.1
    obtain ⟨v,hv,hv'⟩ := avg_reached (w:=w) (f:=fun x => pr w (rel x)) hwL
    have hvR : v ∈ R := Classical.byContradiction (fun h => hv.ne' (hw.2 v h))
    have he' : e ≤ pr w (rel v) := by
      have h := hsat w hw.1 hw.2
      unfold pr at *
      rw [pairW_avg] at h
      exact h.trans hv'
    have hwl : 0 < negEnt w + L * (e * Real.log 2) := hL w hw.1 hw.2
    cases L with
    | zero =>
      have hnonpos := negEnt_le_zero hwL.sub
      simp [show ¬ (0 < negEnt w) from not_lt.mpr hnonpos] at hwl
    | succ L =>
      let R₁ := R.erase v
      let R₂ := R.filter (fun x => ¬rel v x)
      have hr₁ : R₁ ⊂ R := Finset.erase_ssubset hvR
      have hr₂ : R₂ ⊂ R := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
        obtain ⟨x,hx,hx'⟩ := exists_of_pr_pos hwL.nz (lt_of_lt_of_le he he')
        intro h
        have hxr : x ∈ R := Classical.byContradiction fun h => hx'.ne' (hw.2 _ h)
        rw [← h] at hxr
        exact (mem_filter.mp hxr).2 hx
      have hm {r : Finset α} (hr : r ⊂ R) {w : Wgt α}
          (h : carried w (· ∈ r)) : carried w (· ∈ R) :=
        fun x hx => h x (fun hxr => hx (subset_of_ssubset hr hxr))
      obtain ⟨C, hC, htC, hcovC⟩ := ih R₁ hr₁ (fun w hw h => hsat w hw (hm hr₁ h))
        (L+1) (fun w hw h => hL w hw (hm hr₁ h))
      obtain ⟨D, hD, htD, hcovD⟩ := ih R₂ hr₂ (fun w hw h => hsat w hw (hm hr₂ h)) L (by
        intro u hu hRu
        have hmidT : midLaw w u ∈ T := by
          refine ⟨hmid w hw.1 u hu, fun x hx => ?_⟩
          simp [midLaw, hw.2 x hx, hm hr₂ hRu x hx]
        have hle : negEnt w ≤ negEnt (midLaw w u) := hwmin hmidT
        have hh := negEnt_gap hwL.nz (hok u hu).nz (rel v) (fun x hx =>
          hRu x (fun h => (mem_filter.mp h).2 hx))
        have hy : e * Real.log 2 ≤ pr w (rel v) * Real.log 2 := by
          gcongr
        push_cast at hwl
        linarith)
      refine ⟨C ∪ D, ?_, ?_, ?_⟩
      · refine (card_union_le _ _).trans ?_
        have h₁ : C.card ≤ R.card^(L+1) :=
          hC.trans (by gcongr; exact card_lt_card hr₁)
        have h₂ : D.card ≤ R.card^L :=
          hD.trans (by gcongr; exact card_lt_card hr₂)
        refine (add_le_add h₁ h₂).trans ?_
        rw [pow_succ, pow_succ]
        calc R.card ^ L * R.card + R.card ^ L = R.card ^ L * (R.card + 1) := by ring
             _ ≤ _ := by gcongr; omega
      · intro r hr
        rcases mem_union.mp hr with hr|hr
        · exact ⟨(htC r hr).1.trans (subset_of_ssubset hr₁), (htC r hr).2⟩
        · exact ⟨(htD r hr).1.trans (subset_of_ssubset hr₂), (htD r hr).2⟩
      · intro I hIR hI
        by_cases h : v ∈ I
        · have h' : I ⊆ R₂ := fun x hx => mem_filter.mpr ⟨hIR hx,hI v h x hx⟩
          obtain ⟨r,h1,h2⟩ := hcovD I h' hI
          exact ⟨r,mem_union_right _ h1,h2⟩
        · have h' : I ⊆ R₁ := fun x hx => mem_erase.mpr ⟨fun hxv => h (hxv ▸ hx),hIR hx⟩
          obtain ⟨r,h1,h2⟩ := hcovC I h' hI
          exact ⟨r,mem_union_left _ h1,h2⟩
  · refine ⟨{R}, ?_, ?_, ?_⟩
    · rw [card_singleton]
      exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    · simpa using h
    · intro I hIR _; exact ⟨R, mem_singleton_self _, hIR⟩

end HadwigerCounterexample

end

end OAI
