import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedFieldBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserUniformVelocity

namespace OAI

/-! The same integer background density and the same flow derivative
constant work for every separated manufactured well family. -/

noncomputable section
namespace ContinuumCoulomb

/-- The background density is selected before the size, sites, field scale,
or slab width. Thus the published flow input has uniform constants. -/
theorem manufactured_uniform_density_and_flow (hpublished : PublishedC4FlowInput) :
    ∃ rho : ℕ, 0 < rho ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (freq scale S : ℝ), 0 < scale → 1 ≤ S →
      ∀ (m : ℕ) (u : Fin m → PlanarPosition),
      (∀ i j, i ≠ j → 3 ≤ ‖u i-u j‖) →
      (∀ i, localizedCounterterm freq u i ≤ scale) →
      (∀ x, |manufacturedCharge (manufacturedWellField freq scale S u) x| ≤ (rho:ℝ)/2) ∧
      (∀ G : Position → ℝ → Position,
        IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G →
        ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
          ‖iteratedFDeriv ℝ k (fun y => G y t) x‖ ≤ C) := by
  let B := manufacturedFieldDerivativeConstant
  have hB : 0 < B := manufacturedFieldDerivativeConstant_positive
  obtain ⟨rho,hrho⟩ := exists_nat_gt (max (1:ℝ) (6*B/(4*Real.pi)))
  have hrhop : 0 < rho := by
    have h : (1:ℝ) < rho := (le_max_left _ _).trans_lt hrho
    exact_mod_cast (lt_trans zero_lt_one h)
  have hrhopR : (0:ℝ) < rho := by exact_mod_cast hrhop
  obtain ⟨C,hC,hCb⟩ := moserFlow_family_derivative_bound hpublished hrhopR hB.le
  refine ⟨rho,hrhop,C,hC,?_⟩
  intro freq scale S hscale hS m u hsep hcounter
  let V := manufacturedWellField freq scale S u
  have hV : ContDiff ℝ 6 V := (manufacturedWellField_C7 freq scale S u).of_le (by norm_num)
  have hb (k : ℕ) (hk : k ≤ 6) (x : Position) : ‖iteratedFDeriv ℝ k V x‖ ≤ B :=
    manufacturedWellField_derivative_bound freq hscale hS u hsep hcounter hk x
  have hc (x : Position) : |manufacturedCharge V x| ≤ (rho:ℝ)/2 := by
    have h := manufacturedCharge_derivative_bound V hV hB.le hb (k := 0) (by norm_num) x
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
    have h' : 6*B/(4*Real.pi) < rho := (le_max_right _ _).trans_lt hrho
    have he : 6*B/(4*Real.pi) = 2*(3*B/(4*Real.pi)) := by ring
    rw [he] at h'
    linarith
  exact ⟨hc, hCb V hV hb hc⟩

end ContinuumCoulomb

end

end OAI
