import OAI.MeasureTheory.Falconer.Recursion.FiniteProjectionPotential

namespace OAI

/-! At least half of the original direction labels have bounded projected
energy. No direction is replaced and the estimate is uniform over later
subsets of the planar point set. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem finite_low_half {α : Type*} (I : Finset α) (f : α → ℝ) {B : ℝ}
    (hB : 0 < B) (hf : ∀ c ∈ I, 0 ≤ f c)
    (hmean : (∑ c ∈ I, f c) ≤ B*(I.card:ℝ)) :
    (I.card:ℝ)/2 ≤ ((I.filter fun c => f c ≤ 2*B).card:ℝ) := by
  let G := I.filter fun c => f c ≤ 2*B
  let D := I.filter fun c => ¬f c ≤ 2*B
  have hbad : 2*B*(D.card:ℝ) ≤ B*(I.card:ℝ) := by
    calc
      _ = ∑ _c ∈ D, 2*B := by simp; ring
      _ ≤ ∑ c ∈ D, f c := Finset.sum_le_sum fun c hc => (lt_of_not_ge (Finset.mem_filter.mp hc).2).le
      _ ≤ ∑ c ∈ I, f c := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun c hc _ => hf c hc)
      _ ≤ _ := hmean
  have hpart : (G.card:ℝ)+(D.card:ℝ) = I.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := I) (fun c => f c ≤ 2*B)
  have hd : 2*(D.card:ℝ) ≤ I.card := by
    apply (mul_le_mul_iff_right₀ hB).1
    nlinarith only [hbad]
  change (I.card:ℝ)/2 ≤ (G.card:ℝ)
  linarith only [hpart,hd]

noncomputable def projectionEnergyBudget (N : ℕ) (s t KI KP : ℝ) : ℝ :=
  1+((2:ℝ)^s*(1+(N:ℝ)*(2:ℝ)^s)*KI*(8:ℝ)^s)*KP*planarPotentialConstant s t

theorem projectionEnergyBudget_pos (N : ℕ) {s t KI KP : ℝ}
    (hst : s < t) (hKI : 0 ≤ KI) (hKP : 0 ≤ KP) :
    0 < projectionEnergyBudget N s t KI KP := by
  have hC := planarPotentialConstant_pos hst
  unfold projectionEnergyBudget
  positivity

theorem good_projection_directions (N : ℕ) {s t KI KP : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hKI : 1 ≤ KI) (hKP : 1 ≤ KP)
    (I : Finset ℝ) (P : Finset (Space 2)) (hPne : P.Nonempty)
    (hI : ∀ c ∈ I, |c| ≤ 1) (hP : InBoundedLineChart P)
    (hIball : ∀ u r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      scalarBallMass I u r ≤ KI*r^s*(I.card:ℝ))
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t KP P) :
    ∃ J ⊆ I, (I.card:ℝ)/2 ≤ (J.card:ℝ) ∧
      ∀ c ∈ J, planarProjectionEnergy N s c P ≤
        2*projectionEnergyBudget N s t KI KP*(P.card:ℝ)^2 := by
  let B := projectionEnergyBudget N s t KI KP*(P.card:ℝ)^2
  have hPcard : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hPne.card_pos
  have hB : 0 < B := mul_pos
    (projectionEnergyBudget_pos N hst (zero_le_one.trans hKI) (zero_le_one.trans hKP))
    (sq_pos_of_pos hPcard)
  have hmean : (∑ c ∈ I, planarProjectionEnergy N s c P) ≤ B*(I.card:ℝ) := by
    have hh := finite_projection_energy_average N hs hst hKI hKP I P hI hP hIball hPball
    convert hh using 1
    dsimp [B,projectionEnergyBudget]
    ring
  refine ⟨I.filter (fun c => planarProjectionEnergy N s c P ≤ 2*B),Finset.filter_subset _ _,
    finite_low_half I _ hB (fun c _ => ?_) hmean,?_⟩
  · unfold planarProjectionEnergy
    exact Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => by positivity
  · intro c hc
    have hh := (Finset.mem_filter.mp hc).2
    convert hh using 1
    dsimp [B]
    ring

end Falconer

end OAI
