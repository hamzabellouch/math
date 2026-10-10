import OAI.NumberTheory.TotientAsymptotic.FordStateIteration
import OAI.NumberTheory.TotientAsymptotic.FordTerminalMass

namespace OAI

/-! Combining the proved initial, band, and terminal counting inequalities. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ford_initial_scalar {A y B L d V : ℝ} (hB : B ≠ 0) (hL : L ≠ 0) :
    (A*(y/d)*B^2/(L/(6*B))^3)*(L/V)=
      (216*A)*(y/d)*B^5/L^2/V := by
  field_simp
  ring

theorem ford_raw_count : ∃ A C M D₀ : ℝ,
    0 < A ∧ 0 < C ∧ 0 < M ∧ 0 < D₀ ∧
    ∀ (b D r : ℕ) (y S : ℝ) (Y U : ℕ → ℝ),Real.exp 2 ≤ y → 1 ≤ B y → 2 ≤ b →
    FordComparisonParameters b y S D r Y U → D₀ ≤ Real.sqrt (B S*B y) →
    ∀ T : Finset (ShiftedPair b),(∀ t ∈ T,FordComparisonConditions b y S D r Y U t) →
    (T.card:ℝ) ≤
      ((216*A)*(y/(D*r:ℕ))*(B y)^5/(Real.log y)^2/Real.log (Y 1))*
      (∏ k ∈ Finset.Icc 2 b,fordBandCost C k y S Y U)*
      (M*(b+1:ℝ)^D.primeFactorsList.length*
        (Real.log (Y b))^(20*(b:ℝ)*Real.log b+1)) := by
  classical
  obtain ⟨A,hA,hinit⟩ := ford_initial_count
  obtain ⟨C,D₀,hC,hD₀,hiter⟩ := ford_state_iteration
  obtain ⟨M,hM,hterm⟩ := ford_terminal_mass
  refine ⟨A,C,M,D₀,hA,hC,hM,hD₀,?_⟩
  intro b D r y S Y U hy hBy hb hp hroot T hT
  have hy0 : 0 < y := (Real.exp_pos 2).trans_le hy
  have hy1 : 1 < y := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ) < 2)).trans_le hy
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  have hY1 : 0 < Real.log (Y 1) := Real.log_pos (by linarith [ford_cutoff_two_le hp hp.1])
  have hI : 0 ≤ (A*(y/(D*r:ℕ))*(B y)^2/(Real.log y/(6*B y))^3)*
      (Real.log y/Real.log (Y 1)) := by positivity
  have hP : 0 ≤ ∏ k ∈ Finset.Icc 2 b,fordBandCost C k y S Y U :=
    Finset.prod_nonneg (fun k _ => fordBandCost_nonneg hC.le k y S Y U)
  have hcut (k : ℕ) (hk : k ∈ Finset.Icc 2 b) : 2 ≤ Y k ∧ 1 < U (k-1) := by
    obtain ⟨hk2,hkb⟩ := Finset.mem_Icc.mp hk
    have hh := hp.2.2.2.2.1 (k-1) (Finset.mem_range.mpr (by omega))
    have hlow : Y k < U (k-1) := by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hh.1
    exact ⟨ford_cutoff_two_le hp hkb,lt_of_le_of_lt (by linarith [ford_cutoff_two_le hp hkb]) hlow⟩
  have hi := hinit b D r y S Y U hy hBy (ford_cutoff_two_le hp hp.1) hp T hT
  have hm := hiter b D r y S Y U hy hBy hp hcut hroot T hT
  have ht := hterm b D r y S Y U hb hp T hT
  calc
    _ ≤ (A*(y/(D*r:ℕ))*(B y)^2/(Real.log y/(6*B y))^3)*
        (Real.log y/Real.log (Y 1))*fordStateMass T Y 1 := hi
    _ ≤ (A*(y/(D*r:ℕ))*(B y)^2/(Real.log y/(6*B y))^3)*
        (Real.log y/Real.log (Y 1))*
        ((∏ k ∈ Finset.Icc 2 b,fordBandCost C k y S Y U)*
          (M*(b+1:ℝ)^D.primeFactorsList.length*
            (Real.log (Y b))^(20*(b:ℝ)*Real.log b+1))) :=
      mul_le_mul_of_nonneg_left (hm.trans (mul_le_mul_of_nonneg_left ht hP)) hI
    _ = _ := by
      rw [ford_initial_scalar (by linarith : B y ≠ 0) (Real.log_pos hy1).ne']
      ring

theorem ford_raw_count_one : ∃ A M : ℝ,0 < A ∧ 0 < M ∧
    ∀ (D r : ℕ) (y S : ℝ) (Y U : ℕ → ℝ),Real.exp 2 ≤ y → 1 ≤ B y →
    FordComparisonParameters 1 y S D r Y U →
    ∀ T : Finset (ShiftedPair 1),(∀ t ∈ T,FordComparisonConditions 1 y S D r Y U t) →
    (T.card:ℝ) ≤
      ((216*A)*(y/(D*r:ℕ))*(B y)^5/(Real.log y)^2/Real.log (Y 1))*
        (M*(2:ℝ)^D.primeFactorsList.length*(Real.log (Y 1))^2) := by
  obtain ⟨A,hA,hinit⟩ := ford_initial_count
  obtain ⟨M,hM,hterm⟩ := ford_terminal_mass_one
  refine ⟨A,M,hA,hM,?_⟩
  intro D r y S Y U hy hBy hp T hT
  have hy0 : 0 < y := (Real.exp_pos 2).trans_le hy
  have hy1 : 1 < y := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ) < 2)).trans_le hy
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  have hY1 : 0 < Real.log (Y 1) := Real.log_pos (by linarith [ford_cutoff_two_le hp hp.1])
  have hI : 0 ≤ (A*(y/(D*r:ℕ))*(B y)^2/(Real.log y/(6*B y))^3)*
      (Real.log y/Real.log (Y 1)) := by positivity
  have hh := (hinit 1 D r y S Y U hy hBy (ford_cutoff_two_le hp hp.1) hp T hT).trans
    (mul_le_mul_of_nonneg_left (hterm D r y S Y U hp T hT) hI)
  rwa [ford_initial_scalar (by linarith : B y ≠ 0) (Real.log_pos hy1).ne'] at hh

end TotientAsymptotic

end

end OAI
