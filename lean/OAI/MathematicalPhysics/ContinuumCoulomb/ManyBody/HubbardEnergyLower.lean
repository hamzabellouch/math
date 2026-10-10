import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockEnergyError
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.HubbardFermionSpectrum

namespace OAI

/-! The actual half-filled Hubbard variational bottom bounds every sector
vector, including unnormalized projections of continuum states. -/

noncomputable section
open scoped BigOperators InnerProductSpace Classical
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
variable {Edge : Type*} [Fintype Edge]

theorem hubbardFermionForm_occupation (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (left right : Edge → Fin (m+1)) (t : Edge → ℝ)
    (x : Space (2*m+1)) :
    hubbardFermionForm m U V left right t x =
      (occupationInner (2*m+1) x
        ((chargePenaltyFock m U V+graphHopping m left right (fun e => (t e:ℂ))) x)).re := by
  rw [hubbardFermionForm,euclidean_real_inner,occupationInner_fockCoordinates]

theorem hubbardFermionForm_abs_bound (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (left right : Edge → Fin (m+1)) (t : Edge → ℝ)
    (x : Space (2*m+1)) :
    |hubbardFermionForm m U V left right t x| ≤
      ‖fockOperator (chargePenaltyFock m U V+graphHopping m left right (fun e => (t e:ℂ)))‖*
        fockMass x := by
  let T := chargePenaltyFock m U V+graphHopping m left right (fun e => (t e:ℂ))
  have he := occupationInner_operator_error T 0 ‖fockOperator T‖ (by simp) x
  have hm := occupationNormSq_fockCoordinates x
  rw [fockCoordinates_norm_sq] at hm
  have hz : occupationInner (2*m+1) x 0 = 0 := by simp [occupationInner]
  rw [hubbardFermionForm_occupation]
  simpa only [LinearMap.zero_apply,hz,Complex.zero_re,sub_zero,hm] using he

theorem hubbardFermionBottom_lower (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (left right : Edge → Fin (m+1)) (t : Edge → ℝ)
    (x : Space (2*m+1)) (hx : IsHalfFilled m x) :
    hubbardFermionBottom m U V left right t*fockMass x ≤
      hubbardFermionForm m U V left right t x := by
  have hb : BddBelow {e | ∃ y : Space (2*m+1), IsHalfFilled m y ∧ 0 < fockMass y ∧
      e = hubbardFermionForm m U V left right t y/fockMass y} := by
    refine ⟨-‖fockOperator (chargePenaltyFock m U V+
      graphHopping m left right (fun e => (t e:ℂ)))‖,?_⟩
    rintro e ⟨y,_hy,hpos,rfl⟩
    apply (le_div_iff₀ hpos).mpr
    have he := (abs_le.mp (hubbardFermionForm_abs_bound m U V left right t y)).1
    linarith
  have hm : 0 ≤ fockMass x := by rw [← fockCoordinates_norm_sq]; positivity
  rcases eq_or_lt_of_le hm with hz | hpos
  · have hnorm : ‖fockCoordinates (2*m+1) x‖ = 0 := by
      have h := fockCoordinates_norm_sq x
      rw [← hz] at h
      nlinarith [norm_nonneg (fockCoordinates (2*m+1) x)]
    have hzero : x=0 := (fockCoordinates (2*m+1)).injective (by simpa using norm_eq_zero.mp hnorm)
    subst x
    simp [hubbardFermionForm,fockMass]
  · exact (le_div_iff₀ hpos).mp (csInf_le hb ⟨x,hx,hpos,rfl⟩)

end ContinuumCoulomb.HubbardGlobal

end

end OAI
