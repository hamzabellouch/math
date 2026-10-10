import OAI.Analysis.Laughlin.Charge.Model

namespace OAI

namespace Laughlin.Charge
open scoped BigOperators

def LNWYRecursionInput : Prop :=
  ∀ Q n : ℕ, 2 ≤ n → groundEnergy Q n = 0 →
    ∀ x : Hilbert Q, x ∈ unitSector Q (n+1) →
      ((n : ℝ)-1)*energy Q x ≥ ((n : ℝ)+1)*groundEnergy Q n +
        neutralGap Q n * ((n : ℝ)+1-groundOverlap Q n x)

def LNWYRankOneInput : Prop :=
  ∀ Q n : ℕ, Module.finrank ℂ (groundKernel Q n) = 1 →
    ∀ x : Hilbert Q, x ∈ unitSector Q (n+1) → groundOverlap Q n x ≤ 1

def LaughlinChargeGroundInput : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    groundEnergy (3*(n-1)) n = 0 ∧ groundEnergy (3*(n-1)) (n-1) = 0 ∧
      Module.finrank ℂ (groundKernel (3*(n-1)) n) = 1

theorem charge_neutral_of_published (hrec : LNWYRecursionInput)
    (hrank : LNWYRankOneInput) (hground : LaughlinChargeGroundInput)
    (n : ℕ) (hn : 2 ≤ n) :
    chargeGap (3*(n-1)) n = groundEnergy (3*(n-1)) (n+1) ∧
      ((n : ℝ)*neutralGap (3*(n-1)) n)/((n : ℝ)-1) ≤ chargeGap (3*(n-1)) n := by
  obtain ⟨hzero,hlower,hline⟩ := hground n hn
  have hcharge : chargeGap (3*(n-1)) n = groundEnergy (3*(n-1)) (n+1) := by
    simp [chargeGap,hzero,hlower]
  refine ⟨hcharge,?_⟩
  rw [hcharge]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (0 : ℝ) < (n : ℝ)-1 := by linarith
  apply le_csInf
  · exact (unitSector_nonempty (3*(n-1)) (n+1) (by omega)).image _
  · rintro t ⟨x,hx,rfl⟩
    have hr := hrec (3*(n-1)) n hn hzero x hx
    have ho := hrank (3*(n-1)) n hline x hx
    have hg := neutralGap_nonneg (3*(n-1)) n
    have hprod := mul_nonneg hg (sub_nonneg.mpr ho)
    apply (div_le_iff₀ hd).mpr
    rw [hzero] at hr
    nlinarith

theorem charge_uniform_of_published (hrec : LNWYRecursionInput)
    (hrank : LNWYRankOneInput) (hground : LaughlinChargeGroundInput)
    (n : ℕ) (hn : 2 ≤ n) (hgap : (1/25 : ℝ) ≤ neutralGap (3*(n-1)) n) :
    (n : ℝ)/(25*((n : ℝ)-1)) ≤ chargeGap (3*(n-1)) n := by
  have h := (charge_neutral_of_published hrec hrank hground n hn).2
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (0 : ℝ) < (n : ℝ)-1 := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  apply le_trans _ h
  apply (le_div_iff₀ hd).mpr
  have hm := mul_le_mul_of_nonneg_left hgap hn0
  field_simp
  nlinarith

end Laughlin.Charge

end OAI
