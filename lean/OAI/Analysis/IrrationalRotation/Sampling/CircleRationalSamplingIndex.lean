import OAI.Analysis.IrrationalRotation.Rotation.CircleRationalGraphCaps

namespace OAI

noncomputable section
namespace Invariant233

private theorem exists_nat_rational_representative (d : ℕ) (hd : 0 < d) (z : ℤ) :
    ∃ r : ℕ, r < d ∧
      (((z : ℝ) / (d : ℝ) : ℝ) : Circle) =
        (((r : ℝ) / (d : ℝ) : ℝ) : Circle) := by
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  have hn : 0 ≤ z % (d : ℤ) := Int.emod_nonneg z hdZ.ne'
  refine ⟨(z % (d : ℤ)).toNat, (Int.toNat_lt hn).mpr (Int.emod_lt_of_pos z hdZ), ?_⟩
  apply sub_eq_zero.mp
  rw [← AddCircle.coe_sub]
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  refine ⟨z / (d : ℤ), ?_⟩
  have hcast : (((z % (d : ℤ)).toNat : ℕ) : ℝ) = (z % (d : ℤ) : ℤ) := by
    exact_mod_cast Int.toNat_of_nonneg hn
  have hdiv := congrArg (fun n : ℤ => (n : ℝ))
    (Int.emod_add_mul_ediv z (d : ℤ))
  push_cast at hdiv
  rw [hcast, zsmul_eq_mul, mul_one]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp
  nlinarith

namespace CircleParameterLaws
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem rational_shift_later_denominator {A a : ℕ} (hAa : A ≤ a) (r : ℤ) :
    ∃ s : ℕ, s < p.q a ∧
      (((r : ℝ) / (p.q A : ℝ) : ℝ) : Circle) =
        (((s : ℝ) / (p.q a : ℝ) : ℝ) : Circle) := by
  obtain ⟨d, hd⟩ := hp.trimming_frequency_dvd_of_le hAa
  have hqa : (p.q A : ℝ) ≠ 0 := by exact_mod_cast (hp.q_pos A).ne'
  have hqb : (p.q a : ℝ) ≠ 0 := by exact_mod_cast (hp.q_pos a).ne'
  have he : ((r * (d : ℤ) : ℤ) : ℝ) / (p.q a : ℝ) =
      (r : ℝ) / (p.q A : ℝ) := by
    have hdR : (p.q a : ℝ) = (p.q A : ℝ) * d := by exact_mod_cast hd
    push_cast
    field_simp
    rw [hdR]
    ring
  obtain ⟨s, hs, heq⟩ := exists_nat_rational_representative (p.q a) (hp.q_pos a)
    (r * (d : ℤ))
  refine ⟨s, hs, ?_⟩
  rwa [he] at heq

theorem exists_rational_sampling_index {A j : ℕ}
    (hAj : A ≤ p.blockEnd (j - 1)) (r : ℤ) :
    ∃ s : ℕ, s < p.q (p.blockEnd (j - 1)) ∧
      (((r : ℝ) / (p.q A : ℝ) : ℝ) : Circle) = (p.shift j s : Circle) := by
  exact hp.rational_shift_later_denominator hAj r

theorem exists_rational_sampling_index_of_late {A j : ℕ}
    (hAj : A + 1 ≤ j) (r : ℤ) :
    ∃ s : ℕ, s < p.q (p.blockEnd (j - 1)) ∧
      (((r : ℝ) / (p.q A : ℝ) : ℝ) : Circle) = (p.shift j s : Circle) := by
  apply hp.exists_rational_sampling_index
  exact (show A ≤ j - 1 by omega).trans (p.blockEnd_ge_index hp.m_pos (j - 1))

end CircleParameterLaws
end Invariant233

end

end OAI
