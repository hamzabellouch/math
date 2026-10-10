import OAI.NumberTheory.JointDickman.Amplification.AuxiliaryPowerDensity

namespace OAI

/-! # Missing auxiliary factors in the actual dyadic interval -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

lemma uniformFiniteLaw_shifted_count (A N : ℕ) [NeZero N] (E : ℕ → Prop) :
    (uniformFiniteLaw (Fin N)).probability (fun j => E (A+j.val)) =
      (((Ico A (A+N)).filter E).card:ℝ)/N := by
  rw [uniformFiniteLaw_nat_count N (fun n => E (A+n))]
  have he : (((range N).filter (fun n => E (A+n))).image (fun n => A+n)) =
      (Ico A (A+N)).filter E := by
    ext n
    simp only [mem_image,mem_filter,mem_range,mem_Ico]
    constructor
    · rintro ⟨k,⟨hk,hEk⟩,rfl⟩
      exact ⟨⟨by omega,by omega⟩,hEk⟩
    · rintro ⟨⟨hlo,hhi⟩,hEn⟩
      refine ⟨n-A,⟨by omega,?_⟩,by omega⟩
      simpa only [Nat.add_sub_of_le hlo] using hEn
  rw [← he,card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h)]

lemma uniformFiniteLaw_dyadic_count (N : ℕ) [NeZero N] (E : ℕ → Prop) :
    (uniformFiniteLaw (Fin N)).probability (fun j => E (N+1+j.val)) =
      (((Ioc N (2*N)).filter E).card:ℝ)/N := by
  rw [uniformFiniteLaw_shifted_count]
  have he : Ico (N+1) (N+1+N)=Ioc N (2*N) := by
    ext n
    simp only [mem_Ico,mem_Ioc]
    omega
  rw [he]

theorem auxiliary_power_missing_count : ∃ C M : ℝ, 0 < C ∧ 0 ≤ M ∧
    ∀ R β : ℝ, 1 ≤ R → 0 < β → ∀ r : ℕ, β*(4*r:ℕ)<1 →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (((Ioc N (2*N)).filter fun n =>
        mrtPrimeAvoids (mrtPrimeBand ((N:ℝ)^(β/R)) ((N:ℝ)^β)) n).card:ℝ)/N ≤
        C/R+Real.exp (2*(Real.log R+M))/(2:ℝ)^(2*r+1)+ε := by
  obtain ⟨C,M,hC,hM,hbound⟩ := auxiliary_power_missing
  refine ⟨C,M,hC,hM,?_⟩
  intro R β hR hβ r hsmall ε hε
  have hh := (hbound R β hR hβ r hsmall ε hε).filter_mono tendsto_natCast_atTop_atTop
  filter_upwards [hh,eventually_gt_atTop (0:ℕ)] with N hN hN0
  let : NeZero N := ⟨hN0.ne'⟩
  have hb := hN (N+1) N le_rfl
  rwa [uniformFiniteLaw_dyadic_count] at hb

end JointDickman

end OAI
