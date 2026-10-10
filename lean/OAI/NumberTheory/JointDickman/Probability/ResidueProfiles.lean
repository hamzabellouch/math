import OAI.NumberTheory.JointDickman.Probability.ResidueHilbert

namespace OAI

/-! # Compatible finite residue profiles

A profile records the conditional averages on every finite residue space.
Compatibility is tested against all functions on a coarser residue space.
The energy identity below is the finite conditional-expectation identity.
-/

namespace JointDickman
open Finset

structure ResidueProfile where
  value : (q : ℕ+) → ZMod (q : ℕ) → ℂ
  compatible : ∀ (d q : ℕ+) (_ : (d : ℕ) ∣ (q : ℕ)) (g : ZMod (d : ℕ) → ℂ),
    residueMean (fun a => value q a * residueLift g a) =
      residueMean (fun a => value d a * g a)
  energy_bounded : BddAbove (Set.range fun q => residueEnergy (value q))

theorem residueMean_re {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (residueMean f).re = (∑ a, (f a).re) / (q : ℝ) := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  simp [residueMean, Complex.div_re, Complex.normSq]
  field_simp

theorem residueMean_self_conj_re {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (residueMean (fun a => f a * star (f a))).re = residueEnergy f := by
  rw [residueMean_re]
  unfold residueEnergy
  congr 1
  apply sum_congr rfl
  intro a _
  simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re]

theorem residueEnergy_sub {q : ℕ} [NeZero q] (f g : ZMod q → ℂ) :
    residueEnergy (fun a => f a - g a) = residueEnergy f + residueEnergy g -
      2 * (residueMean (fun a => f a * star (g a))).re := by
  have he (z w : ℂ) : ‖z-w‖^2 = ‖z‖^2 + ‖w‖^2 - 2*(z * star w).re := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  simp only [residueEnergy, residueMean_re, he, sum_sub_distrib, sum_add_distrib]
  rw [← mul_sum]
  ring

namespace ResidueProfile

theorem refinement_energy (W : ResidueProfile) {d q : ℕ+} (hd : (d : ℕ) ∣ (q : ℕ)) :
    residueEnergy (fun a => W.value q a - residueLift (W.value d) a) =
      residueEnergy (W.value q) - residueEnergy (W.value d) := by
  rw [residueEnergy_sub, residueEnergy_lift hd]
  have hc := W.compatible d q hd (fun a => star (W.value d a))
  have he : residueMean (fun a : ZMod (q : ℕ) =>
      W.value q a * star (residueLift (W.value d) a)) =
      residueMean (fun a => W.value d a * star (W.value d a)) := hc
  rw [he, residueMean_self_conj_re]
  ring

theorem energy_mono (W : ResidueProfile) {d q : ℕ+} (hd : (d : ℕ) ∣ (q : ℕ)) :
    residueEnergy (W.value d) ≤ residueEnergy (W.value q) := by
  have h := residueEnergy_nonneg (fun a => W.value q a - residueLift (W.value d) a)
  rw [W.refinement_energy hd] at h
  linarith

/-- One finite residue coordinate approximates every refinement in mean square. -/
theorem exists_approximation (W : ResidueProfile) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℕ+, ∀ q : ℕ+, (d : ℕ) ∣ (q : ℕ) →
      residueEnergy (fun a => W.value q a - residueLift (W.value d) a) < ε := by
  have hn : (Set.range fun q => residueEnergy (W.value q)).Nonempty :=
    Set.range_nonempty _
  obtain ⟨x, hx, hclose⟩ := exists_lt_of_lt_csSup hn
    (sub_lt_self (sSup (Set.range fun q => residueEnergy (W.value q))) hε)
  obtain ⟨d, rfl⟩ := hx
  refine ⟨d, fun q hd => ?_⟩
  rw [W.refinement_energy hd]
  have hq := le_csSup W.energy_bounded (Set.mem_range_self q)
  linarith

end ResidueProfile
end JointDickman

end OAI
