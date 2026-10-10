import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ElementaryCalculus

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem elementary_evacuateHighest {a p w : ι → Space} {D η H : ℝ} {safe : Set ι}
    (ar : RationalCenters a) (pr : RationalCenters p) (wr : RationalCenters w)
    (Hr : RationalConstant H)
    (hwidth : ∀ i k, 0 < w i k)
    (hsize : ∀ i j k, w i k + w j k + 4 * η ≤ D)
    (ha : CenterSeparated a D)
    (hcross : ∀ i j, D < |a i 0 - p j 0|)
    (hp : ∀ i j, i ≠ j → D < |p i 0 - p j 0|)
    (hhigha : ∀ i, D < H - a i 1) (hhighp : ∀ i, D < H - p i 1)
    (hD : 0 ≤ D)
    (hga : (BoxLayout.mk a w).Guarded safe) (hgp : (BoxLayout.mk p w).Guarded safe)
    (S : Finset ι) (i : ι) (hi : i ∈ S) (hmax : ∀ j ∈ S, a j 1 ≤ a i 1) :
    ∃ m : BoxMotion ⟨remainingCenters a p S, w⟩ ⟨remainingCenters a p (S.erase i), w⟩ safe η,
      ElementaryMotion m := by
  let u := remainingCenters a p S
  let v₁ := Function.update (a i) 1 H
  let v₂ := Function.update (p i) 1 H
  have hui : u i = a i := by simp [u, remainingCenters, hi]
  have hu := remainingCenters_separated ha hcross hp S
  have hgu := remainingCenters_guarded hga hgp S
  have hv₁ : (BoxLayout.mk (Function.update u i v₁) w).Guarded safe :=
    guarded_update hgu i v₁ (by intro his; simpa [v₁] using hga i his)
  have hv₂ : (BoxLayout.mk (Function.update u i v₂) w).Guarded safe :=
    guarded_update hgu i v₂ (by intro his; simpa [v₂] using hgp i his)
  have hp₃ : (BoxLayout.mk (Function.update u i (p i)) w).Guarded safe :=
    guarded_update hgu i (p i) (fun his => hgp i his)
  have hfirst : ∀ r ∈ Icc (0 : ℝ) 1, ∀ j, j ≠ i →
      ∃ k, D < |(1 - r) * u i k + r * v₁ k - u j k| := by
    intro r hr j hji
    rw [hui]
    by_cases hj : j ∈ S
    · have huj : u j = a j := by simp [u, remainingCenters, hj]
      rw [huj]
      exact raising_gap (hmax j hj) (by linarith [hhigha i]) hr (ha i j (Ne.symm hji))
    · have huj : u j = p j := by simp [u, remainingCenters, hj]
      rw [huj]
      exact fixed_first_gap (by simp [v₁]) (by simpa [v₁] using hcross i j)
  have hsecond : ∀ r ∈ Icc (0 : ℝ) 1, ∀ j, j ≠ i →
      ∃ k, D < |(1 - r) * (Function.update u i v₁) i k +
        r * v₂ k - (Function.update u i v₁) j k| := by
    intro r _ j hji
    simp only [Function.update_self, Function.update_of_ne hji]
    apply high_plane_gap (H := H) (by simp [v₁]) (by simp [v₂])
    by_cases hj : j ∈ S
    · simpa [u, remainingCenters, hj] using hhigha j
    · simpa [u, remainingCenters, hj] using hhighp j
  have hthird : ∀ r ∈ Icc (0 : ℝ) 1, ∀ j, j ≠ i →
      ∃ k, D < |(1 - r) * (Function.update u i v₂) i k +
        r * p i k - (Function.update u i v₂) j k| := by
    intro r _ j hji
    simp only [Function.update_self, Function.update_of_ne hji]
    apply fixed_first_gap (by simp [v₂])
    by_cases hj : j ∈ S
    · simpa [u, remainingCenters, hj, abs_sub_comm] using hcross j i
    · simpa [u, remainingCenters, hj] using hp i j (Ne.symm hji)
  have hsep₁ := hu.update i v₁ (fun j hji => by simpa using hfirst 1 ⟨by norm_num, le_rfl⟩ j hji)
  have hsep₂ : CenterSeparated (Function.update u i v₂) D := by
    have hh := hsep₁.update i v₂ (fun j hji => by simpa using hsecond 1 ⟨by norm_num, le_rfl⟩ j hji)
    simpa [Function.update_idem] using hh
  let m₁ := singleSegmentMotion i v₁ hwidth hsize hu hfirst hgu hv₁
  let m₂ := singleSegmentMotion i v₂ hwidth hsize hsep₁ hsecond hv₁
    (by simpa [Function.update_idem] using hv₂)
  let m₃ := singleSegmentMotion i (p i) hwidth hsize hsep₂ hthird hv₂
    (by simpa [Function.update_idem] using hp₃)
  have ur : RationalCenters u := rational_remaining ar pr S
  have v₁r : ∀ k, RationalConstant (v₁ k) := rational_space_update (ar i) 1 Hr
  have v₂r : ∀ k, RationalConstant (v₂ k) := rational_space_update (pr i) 1 Hr
  have e₁ : ElementaryMotion m₁ := elementary_singleSegment ur wr i v₁ v₁r _ _ _ _ _ _
  have e₂ : ElementaryMotion m₂ := elementary_singleSegment (ur.update i v₁r) wr i v₂ v₂r _ _ _ _ _ _
  have e₃ : ElementaryMotion m₃ := elementary_singleSegment (ur.update i v₂r) wr i (p i) (pr i) _ _ _ _ _ _
  have h₂ := Exists.intro m₂ e₂
  change ∃ m : BoxMotion ⟨Function.update u i v₁, w⟩
    ⟨Function.update (Function.update u i v₁) i v₂, w⟩ safe η, ElementaryMotion m at h₂
  rw [Function.update_idem] at h₂
  have h₃ := Exists.intro m₃ e₃
  change ∃ m : BoxMotion ⟨Function.update u i v₂, w⟩
    ⟨Function.update (Function.update u i v₂) i (p i), w⟩ safe η, ElementaryMotion m at h₃
  rw [Function.update_idem] at h₃
  obtain ⟨m₂',e₂'⟩ := h₂
  obtain ⟨m₃',e₃'⟩ := h₃
  have h : ElementaryMotion ((m₁.trans m₂').trans m₃') :=
    (e₁.trans e₂' ⟨ur.update i v₁r,wr⟩).trans e₃' ⟨ur.update i v₂r,wr⟩
  rw [remainingCenters_erase hi]
  exact ⟨_,h⟩

theorem elementary_evacuateToParking {a p w : ι → Space} {D η H : ℝ} {safe : Set ι}
    (ar : RationalCenters a) (pr : RationalCenters p) (wr : RationalCenters w)
    (Hr : RationalConstant H)
    (hwidth : ∀ i k, 0 < w i k)
    (hsize : ∀ i j k, w i k + w j k + 4 * η ≤ D)
    (ha : CenterSeparated a D)
    (hcross : ∀ i j, D < |a i 0 - p j 0|)
    (hp : ∀ i j, i ≠ j → D < |p i 0 - p j 0|)
    (hhigha : ∀ i, D < H - a i 1) (hhighp : ∀ i, D < H - p i 1)
    (hD : 0 ≤ D)
    (hga : (BoxLayout.mk a w).Guarded safe) (hgp : (BoxLayout.mk p w).Guarded safe) :
    ∃ m : BoxMotion ⟨a, w⟩ ⟨p, w⟩ safe η, ElementaryMotion m := by
  have h : ∀ S : Finset ι, ∃ m : BoxMotion ⟨remainingCenters a p S, w⟩ ⟨p, w⟩ safe η,
      ElementaryMotion m := by
    intro S
    refine Finset.strongInductionOn S ?_
    intro S ih
    by_cases hS : S.Nonempty
    · obtain ⟨i, hi, hmax⟩ := S.exists_max_image (fun i => a i 1) hS
      obtain ⟨m,em⟩ := ih (S.erase i) (Finset.erase_ssubset hi)
      obtain ⟨v,ev⟩ := elementary_evacuateHighest ar pr wr Hr hwidth hsize ha hcross hp hhigha hhighp hD
        hga hgp S i hi hmax
      exact ⟨v.trans m, ev.trans em ⟨rational_remaining ar pr _,wr⟩⟩
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      have hempty : remainingCenters a p ∅ = p := by ext i k; simp [remainingCenters]
      rw [hempty]
      exact ⟨BoxMotion.stationary (A := ⟨p, w⟩) hwidth
        (separated_of_centerSeparated (fun i j hij => ⟨0, hp i j hij⟩) hsize) hgp,
        ElementaryMotion.stationary ⟨pr,wr⟩ _ _ _⟩
  have hh := h Finset.univ
  have he : remainingCenters a p Finset.univ = a := by ext i k; simp [remainingCenters]
  rw [he] at hh
  exact hh

end BalancedTransport.Effectivity
end

end OAI
