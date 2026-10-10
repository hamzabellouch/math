import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactRealization
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactCalibrationScale

namespace OAI

/-! Simultaneous calibration of every edge of the actual positive mediator
graph, together with whole-matrix Coulomb coercivity for its realized sites. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.ContactMediator
open MediatorIteration

theorem exists_calibrated_finalGraph_above {freq : ℝ} (hfreq : 0 < freq) (A B S : ℕ) (kmin : ℝ) :
    ∃ k : ℕ, 0 < k ∧ kmin ≤ (k : ℝ) ∧ ∀ N : ℝ, 2 ≤ N →
      5 ≤ (1 - contactLengthTolerance) * ((k : ℝ) * Real.log N) ∧
      ∀ (d : SquareLatticeHeisenberg) (W G : ℕ) (K : GlobalEdge d → ℝ),
        (Fintype.card (GlobalSite d) : ℝ) ≤ N ^ S →
        (∀ a, (N ^ A)⁻¹ ≤ K a) → (∀ a, K a ≤ N ^ A) →
        ∃ u : GlobalSite d → PlanarPosition,
          (∀ a, N ^ k * planarHopping ‖u ((finalGraph d.bonds W G).left a) -
              u ((finalGraph d.bonds W G).right a)‖ =
            coulombHoppingTarget freq (N ^ B)⁻¹ (K a)
              ‖u ((finalGraph d.bonds W G).left a) - u ((finalGraph d.bonds W G).right a)‖) ∧
          (∀ x y, x ≠ y → (1 - contactLengthTolerance) * ((k : ℝ) * Real.log N) ≤
            ‖u x - u y‖) ∧
          (∀ x y, x ≠ y → Nonedge d W G x y →
            (6 / 5) * ((k : ℝ) * Real.log N) < ‖u x - u y‖) ∧
          (∀ c : GlobalSite d → ℝ, localizedGramConstant freq * ∑ i, c i ^ 2 ≤
            ∑ i, ∑ j, localizedCoulombCoeff freq (u i) (u j) * c i * c j) ∧
          Function.Injective u ∧
          (∀ M : ℝ, (∀ j i, |(contactGridAxis (d.coordinate j) i : ℝ)| ≤ M) →
            ∀ x i, |u x i| ≤ ((k : ℝ) * Real.log N) * (17 * M + 17)) := by
  obtain ⟨L, _, hrange⟩ := exists_coulomb_target_polynomial_bounds hfreq A B
  obtain ⟨k, hk, hminimum, hcal⟩ := exists_uniform_coulomb_calibration_above
    (ε := contactLengthTolerance) hfreq
    (by norm_num [contactLengthTolerance]) (by norm_num [contactLengthTolerance]) (B + A + L) S kmin
  refine ⟨k, hk, hminimum, fun N hN => ⟨(hcal N hN).1, ?_⟩⟩
  intro d W G K hcount hlo hhi
  have hNpos : 0 < N := by linarith
  let D : ℝ := (k : ℝ) * Real.log N
  have hD : 0 < D := mul_pos (by exact_mod_cast hk) (Real.log_pos (by linarith))
  have htarget (a : GlobalEdge d) :
      ∃ t ∈ Set.Icc ((1 - contactLengthTolerance) * D) ((1 + contactLengthTolerance) * D),
        N ^ k * planarHopping t = coulombHoppingTarget freq (N ^ B)⁻¹ (K a) t := by
    obtain ⟨hl, hh⟩ := hrange N hN (K a) (hlo a) (hhi a)
    exact (hcal N hN).2.2.1 (N ^ B)⁻¹ (K a) (by positivity)
      ((inv_nonneg.mpr (pow_nonneg hNpos.le A)).trans (hlo a)) hl hh
  choose t ht using htarget
  let ℓ : GlobalEdge d → ℝ := fun a => t a / D
  have hℓ (a : GlobalEdge d) : ℓ a ∈
      Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance) := by
    constructor
    · exact (le_div_iff₀ hD).mpr (ht a).1.1
    · exact (div_le_iff₀ hD).mpr (ht a).1.2
  obtain ⟨u, hlen, hnon, hsep, hinj, hext⟩ := exists_scaled_finalGraph_realization d W G D hD ℓ hℓ
  have hdist (a : GlobalEdge d) :
      ‖u ((finalGraph d.bonds W G).left a) - u ((finalGraph d.bonds W G).right a)‖ = t a := by
    rw [← dist_eq_norm, hlen]
    dsimp only [ℓ]
    field_simp [hD.ne']
  refine ⟨u, ?_, ?_, ?_, ?_, hinj, hext⟩
  · intro a
    rw [hdist]
    exact (ht a).2
  · intro x y hxy
    simpa only [dist_eq_norm, D] using hsep x y hxy
  · intro x y hxy hn
    simpa only [dist_eq_norm, D] using hnon x y hxy hn
  · intro c
    apply (hcal N hN).2.2.2 _ (by simpa only [Fintype.card_fin] using hcount) u
    intro x y hxy
    simpa only [dist_eq_norm, D] using hsep x y hxy

theorem exists_calibrated_finalGraph {freq : ℝ} (hfreq : 0 < freq) (A B S : ℕ) :
    ∃ k : ℕ, 0 < k ∧ ∀ N : ℝ, 2 ≤ N →
      5 ≤ (1 - contactLengthTolerance) * ((k : ℝ) * Real.log N) ∧
      ∀ (d : SquareLatticeHeisenberg) (W G : ℕ) (K : GlobalEdge d → ℝ),
        (Fintype.card (GlobalSite d) : ℝ) ≤ N ^ S →
        (∀ a, (N ^ A)⁻¹ ≤ K a) → (∀ a, K a ≤ N ^ A) →
        ∃ u : GlobalSite d → PlanarPosition,
          (∀ a, N ^ k * planarHopping ‖u ((finalGraph d.bonds W G).left a) -
              u ((finalGraph d.bonds W G).right a)‖ =
            coulombHoppingTarget freq (N ^ B)⁻¹ (K a)
              ‖u ((finalGraph d.bonds W G).left a) - u ((finalGraph d.bonds W G).right a)‖) ∧
          (∀ x y, x ≠ y → (1 - contactLengthTolerance) * ((k : ℝ) * Real.log N) ≤
            ‖u x - u y‖) ∧
          (∀ x y, x ≠ y → Nonedge d W G x y →
            (6 / 5) * ((k : ℝ) * Real.log N) < ‖u x - u y‖) ∧
          (∀ c : GlobalSite d → ℝ, localizedGramConstant freq * ∑ i, c i ^ 2 ≤
            ∑ i, ∑ j, localizedCoulombCoeff freq (u i) (u j) * c i * c j) ∧
          Function.Injective u ∧
          (∀ M : ℝ, (∀ j i, |(contactGridAxis (d.coordinate j) i : ℝ)| ≤ M) →
            ∀ x i, |u x i| ≤ ((k : ℝ) * Real.log N) * (17 * M + 17)) := by
  obtain ⟨k, hk, _, hcal⟩ := exists_calibrated_finalGraph_above hfreq A B S 0
  exact ⟨k, hk, hcal⟩

end ContinuumCoulomb.ContactMediator

end

end OAI
