import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserChargeBounds

namespace OAI

/-! A uniform four-derivative reciprocal estimate away from zero, used
only for the positive density in the Moser field. -/

noncomputable section
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

private theorem reciprocal_derivatives_bounded {rho : ℝ} (hrho : 0 < rho) :
    ∃ C : ℝ, 0 < C ∧ ∀ k ≤ 4, ∀ y ∈ Set.Icc (rho/2) (3*rho/2),
      ‖iteratedFDeriv ℝ k (fun z : ℝ => z⁻¹) y‖ ≤ C := by
  let T : Set ℝ := {0}ᶜ
  have hT : IsOpen T := isClosed_singleton.isOpen_compl
  have hg : ContDiffOn ℝ 4 (fun z : ℝ => z⁻¹) T :=
    contDiffOn_id.inv (fun z hz => hz)
  have hsub : Set.Icc (rho/2) (3*rho/2) ⊆ T := by
    intro z hz
    exact ne_of_gt (lt_of_lt_of_le (by positivity : 0 < rho/2) hz.1)
  have hb (k : Fin 5) : ∃ A : ℝ, ∀ y ∈ Set.Icc (rho/2) (3*rho/2),
      ‖iteratedFDeriv ℝ k.val (fun z : ℝ => z⁻¹) y‖ ≤ A := by
    have hc : ContinuousOn (iteratedFDeriv ℝ k.val (fun z : ℝ => z⁻¹)) T := by
      apply (hg.continuousOn_iteratedFDerivWithin (by exact_mod_cast (show k.val ≤ 4 by omega))
        hT.uniqueDiffOn).congr
      intro z hz
      exact (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun z : ℝ => z⁻¹)
        k.val hT hz).symm
    obtain ⟨A,hA⟩ := isCompact_Icc.bddAbove_image ((hc.mono hsub).norm)
    exact ⟨A, fun y hy => hA ⟨y,hy,rfl⟩⟩
  choose B hB using hb
  let C : ℝ := 1+∑ k : Fin 5, max (B k) 0
  have hn : 0 ≤ ∑ k : Fin 5, max (B k) 0 :=
    Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro k hk y hy
  let i : Fin 5 := ⟨k, by omega⟩
  have hs : max (B i) 0 ≤ ∑ j : Fin 5, max (B j) 0 :=
    Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ i)
  exact (hB i y hy).trans ((le_max_left _ _).trans (by dsimp [C]; linarith))

/-- The constant depends on the density floor and on the four-derivative
bound, not on the support or the number of wells. -/
theorem uniform_reciprocal_four_bound {rho B : ℝ} (hrho : 0 < rho) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ × Position → ℝ, ContDiff ℝ 4 f →
      ∀ x, f x ∈ Set.Icc (rho/2) (3*rho/2) →
      (∀ j ≤ 4, ‖iteratedFDeriv ℝ j f x‖ ≤ B) →
      ∀ k ≤ 4, ‖iteratedFDeriv ℝ k (fun y => (f y)⁻¹) x‖ ≤ C := by
  obtain ⟨A,hA,hAb⟩ := reciprocal_derivatives_bounded hrho
  let D : ℝ := max 1 B
  refine ⟨24*A*D^4, by dsimp [D]; positivity, ?_⟩
  intro f hf x hx hb k hk
  let U : Set (ℝ × Position) := {y | f y ≠ 0}
  let T : Set ℝ := {0}ᶜ
  have hT : IsOpen T := isClosed_singleton.isOpen_compl
  have hU : IsOpen U := isOpen_ne.preimage hf.continuous
  have hxU : x ∈ U := ne_of_gt (lt_of_lt_of_le (by positivity : 0 < rho/2) hx.1)
  have hg : ContDiffOn ℝ 4 (fun z : ℝ => z⁻¹) T :=
    contDiffOn_id.inv (fun z hz => hz)
  have hcomp := norm_iteratedFDerivWithin_comp_le hg hf.contDiffOn
    (show (k : WithTop ℕ∞) ≤ 4 by exact_mod_cast hk)
    hT.uniqueDiffOn hU.uniqueDiffOn (fun y hy => hy) hxU
    (C := A) (D := D) (fun j hj => by
      rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun z : ℝ => z⁻¹)
        j hT (show f x ∈ T from hxU)]
      exact hAb j (hj.trans hk) (f x) hx)
    (fun j hj hjk => by
      rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) j hU hxU]
      exact (hb j (hjk.trans hk)).trans ((le_max_right 1 B).trans (by
        simpa only [pow_one] using pow_le_pow_right₀ (le_max_left 1 B) hj)))
  rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
    (f := (fun z : ℝ => z⁻¹) ∘ f) k hU hxU] at hcomp
  apply hcomp.trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right (by
      exact_mod_cast (show k.factorial ≤ 24 from
        (Nat.factorial_le hk).trans (by decide))) hA.le
  · exact pow_le_pow_right₀ (le_max_left 1 B) hk
  · exact pow_nonneg (le_trans zero_le_one (le_max_left 1 B)) k
  · positivity

end ContinuumCoulomb

end

end OAI
