import OAI.MeasureTheory.Falconer.Incidence.CoarsePencilWeights

namespace OAI

/-! A regular coarse pencil with a lower fine-incidence count in every
retained coarse tube, obtained directly from the original fine pencils. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem regular_coarse_pencil_mul {δ Δ s K C : ℝ}
    (hΔ : 0 < Δ) (hδΔ : δ ≤ Δ) (hs : 0 ≤ s) (hK : 1 ≤ K) (hC : 0 ≤ C)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hT : ∀ x ∈ P, (T x).Nonempty)
    (q : Space 2 → Space 2)
    (hnear : ∀ x ∈ P, ∀ l ∈ T x, dist l (q l) ≤ C*Δ)
    (hball : ∀ x ∈ P, NormalizedFiniteBallBound δ s K (T x)) :
    let W := ∑ x ∈ P, (T x).card
    let J := Nat.log 2 W+1
    ∃ A ⊆ (P.biUnion T).image q, A.Nonempty ∧
      NormalizedFiniteBallBound Δ s (2*(K*(C+1)^s)*(J:ℝ)) A ∧
      ∀ a ∈ A, (W:ℝ) ≤ 2*(J:ℝ)*(A.card:ℝ)*(coarsePencilWeight P T q a:ℝ) := by
  let W := ∑ x ∈ P, (T x).card
  let J := Nat.log 2 W+1
  let V := (P.biUnion T).image q
  have hV : V.Nonempty := by
    obtain ⟨x,hx⟩ := hP
    obtain ⟨l,hl⟩ := hT x hx
    exact ⟨q l,Finset.mem_image_of_mem q (Finset.mem_biUnion.mpr ⟨x,hx,hl⟩)⟩
  have hW : ∑ a ∈ V, (coarsePencilWeight P T q a:ℝ) = (W:ℝ) := by
    exact_mod_cast sum_coarsePencilWeight_union P T q
  obtain ⟨k,A,hAV,hA,hweight,hband,hreg⟩ := weighted_dyadic_regular_subset hΔ.le
    (show 0 ≤ K*(C+1)^s by positivity) V (coarsePencilWeight P T q) hV W
    (fun a ha => ⟨coarsePencilWeight_pos P T q ha,coarsePencilWeight_le P T q a⟩)
    (coarse_pencil_weight_ball_mul hΔ hδΔ hs hK hC P T q hnear hball)
  refine ⟨A,hAV,hA,hreg,?_⟩
  intro a ha
  have hmass : (W:ℝ) ≤ (J:ℝ)*(∑ b ∈ A, (coarsePencilWeight P T q b:ℝ)) := by
    rwa [hW] at hweight
  have hbound : (∑ b ∈ A, (coarsePencilWeight P T q b:ℝ)) ≤
      2*(coarsePencilWeight P T q a:ℝ)*(A.card:ℝ) := by
    calc
      _ ≤ ∑ _b ∈ A, 2*(coarsePencilWeight P T q a:ℝ) := by
        apply Finset.sum_le_sum
        intro b hb
        have hab : coarsePencilWeight P T q b ≤ 2*coarsePencilWeight P T q a := by
          have hlo := (hband a ha).1
          have hhi := (hband b hb).2
          rw [pow_succ] at hhi
          omega
        exact_mod_cast hab
      _ = _ := by simp; ring
  calc
    _ ≤ (J:ℝ)*(∑ b ∈ A, (coarsePencilWeight P T q b:ℝ)) := hmass
    _ ≤ (J:ℝ)*(2*(coarsePencilWeight P T q a:ℝ)*(A.card:ℝ)) :=
      mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)
    _ = _ := by ring

theorem regular_coarse_pencil {δ Δ s K : ℝ}
    (hΔ : 0 < Δ) (hδΔ : δ ≤ Δ) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hT : ∀ x ∈ P, (T x).Nonempty)
    (q : Space 2 → Space 2)
    (hnear : ∀ x ∈ P, ∀ l ∈ T x, dist l (q l) ≤ Δ)
    (hball : ∀ x ∈ P, NormalizedFiniteBallBound δ s K (T x)) :
    let W := ∑ x ∈ P, (T x).card
    let J := Nat.log 2 W+1
    ∃ A ⊆ (P.biUnion T).image q, A.Nonempty ∧
      NormalizedFiniteBallBound Δ s (2*(K*(2:ℝ)^s)*(J:ℝ)) A ∧
      ∀ a ∈ A, (W:ℝ) ≤ 2*(J:ℝ)*(A.card:ℝ)*(coarsePencilWeight P T q a:ℝ) := by
  simpa only [one_add_one_eq_two,one_mul] using regular_coarse_pencil_mul
    hΔ hδΔ hs hK (C := 1) (by norm_num) P T hP hT q (by simpa only [one_mul] using hnear) hball

end Falconer

end OAI
