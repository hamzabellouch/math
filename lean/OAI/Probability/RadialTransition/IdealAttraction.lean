import OAI.Probability.RadialTransition.Model

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

abbrev Pressure := ℝ → ℝ → ℝ

def pressureSupport (Q : Pressure) (β h e d : ℝ) : Prop :=
  ∀ β' h', 0 < β' →
    Q β h + e * (β' - β) + d * (h' - h) ≤ Q β' h'

def attractionBranch (Q : Pressure) (a u : ℝ) : Pressure :=
  fun β h => Q β (h + β * a * u) - β * a / 2 * u ^ 2

def idealAttraction (Q : Pressure) (a : ℝ) : Pressure :=
  fun β h => sSup (Set.range fun u => attractionBranch Q a u β h)

def ActiveShift (Q : Pressure) (a β h u : ℝ) : Prop :=
  ∀ v : ℝ, attractionBranch Q a v β h ≤ attractionBranch Q a u β h

theorem active_parabola {Q : Pressure} {a β h u : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hu : ActiveShift Q a β h u) (r : ℝ) :
    Q β (h + β * a * u + r) ≤
      Q β (h + β * a * u) + u * r + r ^ 2 / (2 * β * a) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hβ0 : β ≠ 0 := ne_of_gt hβ
  have hshift : h + β * a * (u + r / (β * a)) = h + β * a * u + r := by
    field_simp
    ring
  have hc := hu (u + r / (β * a))
  dsimp [attractionBranch] at hc
  rw [hshift] at hc
  calc
    Q β (h + β * a * u + r) ≤ Q β (h + β * a * u) +
        β * a / 2 * ((u + r / (β * a)) ^ 2 - u ^ 2) := by linarith
    _ = Q β (h + β * a * u) + u * r + r ^ 2 / (2 * β * a) := by
      field_simp
      ring

theorem active_support_density {Q : Pressure} {a β h u e d : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hu : ActiveShift Q a β h u)
    (hs : pressureSupport Q β (h + β * a * u) e d) : d = u := by
  have hba : 0 < β * a := mul_pos hβ ha
  have hqa : ∀ r : ℝ, d * r ≤ u * r + r ^ 2 / (2 * β * a) := by
    intro r
    have hl := hs β (h + β * a * u + r) hβ
    have hr := active_parabola ha hβ hu r
    simp only [sub_self, mul_zero, add_zero, add_sub_cancel_left] at hl
    linarith
  have hh := hqa ((β * a) * (d - u))
  have hden : 0 < 2 * β * a := by positivity
  have hh' : (d * ((β * a) * (d - u)) - u * ((β * a) * (d - u))) *
      (2 * β * a) ≤ ((β * a) * (d - u)) ^ 2 :=
    (le_div_iff₀ hden).mp (by linarith [hh])
  have hz : (β * a) ^ 2 * (d - u) ^ 2 ≤ 0 := by nlinarith [hh']
  have hd : (d - u) ^ 2 ≤ 0 := le_of_mul_le_mul_left (by simpa only [mul_zero] using hz) (sq_pos_of_pos hba)
  nlinarith [sq_nonneg (d - u)]

theorem support_attractionBranch {Q : Pressure} {a β h u e d : ℝ}
    (hs : pressureSupport Q β (h + β * a * u) e d) :
    pressureSupport (attractionBranch Q a u) β h
      (e + a * u * d - a * u ^ 2 / 2) d := by
  intro β' h' hβ'
  have hc := hs β' (h' + β' * a * u) hβ'
  dsimp [attractionBranch]
  nlinarith [hc]

theorem idealAttraction_eq_of_active {Q : Pressure} {a β h u : ℝ}
    (hu : ActiveShift Q a β h u) :
    idealAttraction Q a β h = attractionBranch Q a u β h := by
  apply IsGreatest.csSup_eq
  exact ⟨⟨u, rfl⟩, by rintro _ ⟨v, rfl⟩; exact hu v⟩

theorem active_generator_support {Q : Pressure} {a β h u e : ℝ}
    (hfinite : ∀ β' h', 0 < β' →
      BddAbove (Set.range fun v => attractionBranch Q a v β' h'))
    (hu : ActiveShift Q a β h u)
    (hs : pressureSupport Q β (h + β * a * u) e u) :
    pressureSupport (idealAttraction Q a) β h (e + a * u ^ 2 / 2) u := by
  have hb : pressureSupport (attractionBranch Q a u) β h (e + a * u ^ 2 / 2) u := by
    convert support_attractionBranch hs using 1
    ring
  intro β' h' hβ'
  rw [idealAttraction_eq_of_active hu]
  exact (hb β' h' hβ').trans (le_csSup (hfinite β' h' hβ') ⟨u, rfl⟩)

theorem support_of_attractionBranch {Q : Pressure} {a β h u e d : ℝ}
    (hs : pressureSupport (attractionBranch Q a u) β h e d) :
    pressureSupport Q β (h + β * a * u) (e - a * u * d + a * u ^ 2 / 2) d := by
  intro β' h' hβ'
  have hc := hs β' (h' - β' * a * u) hβ'
  dsimp [attractionBranch] at hc
  rw [sub_add_cancel] at hc
  nlinarith [hc]

end RadialTransition

end

end OAI
