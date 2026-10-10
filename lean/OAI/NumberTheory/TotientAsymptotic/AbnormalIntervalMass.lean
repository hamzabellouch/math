import OAI.NumberTheory.TotientAsymptotic.NormalityGridReduction
import OAI.NumberTheory.TotientAsymptotic.NormalityGridEnvelope
import OAI.NumberTheory.TotientAsymptotic.NormalityGridMass

namespace OAI

/-! Reciprocal cofactor mass for all failed interval normality conditions. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem abnormal_interval_mass : ∃ C : ℝ, 0 < C ∧ ∀ S x : ℝ,
    1 < S → 4 ≤ B S → Real.exp 1 ≤ x → 1 ≤ B x → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,0 < n ∧ (n:ℝ) ≤ x ∧ ∃ U T : ℝ, S ≤ U ∧ U < T ∧ T ≤ x ∧
      Real.sqrt (B S*B T)-1 ≤ |(omegaIn n U T:ℝ)-(B T-B U)|) →
    (∑ n ∈ Q,(n:ℝ)⁻¹)  ≤  C*(B x)^2*Real.log x*(Real.log S)^(-1/6:ℝ) := by
  classical
  obtain ⟨C,hC,hgrid⟩ := normality_grid_mass
  refine ⟨9*C*(Real.exp 1+1)*Real.exp (1/3),by positivity,?_⟩
  intro S x hS hBS hx hBx Q hQ
  let M := ⌊B x⌋₊+1
  let N := normalityGridEnvelope x
  have hen := normalityGridEnvelope_bounds hx
  have hB0 : 0 ≤ B x := by linarith
  have hA : 0 < B S-2 := by linarith
  have hQ' : ∀ n ∈ Q,0 < n ∧ n ≤ N ∧ ∃ i j : ℕ,
      1 ≤ i ∧ i < j ∧ j ≤ M ∧ B S-2 ≤ (j:ℝ)-1 ∧
      Real.sqrt ((B S-2)*((j:ℝ)-1))-4 ≤ 
        |(omegaIn n (normalityGridPoint i) (normalityGridPoint j):ℝ)-((j:ℝ)-i)| := by
    intro n hn
    obtain ⟨hn0,hnx,U,T,hSU,hUT,hTx,hbad⟩ := hQ n hn
    have hnN : n ≤ N := by exact_mod_cast hnx.trans hen.1
    exact ⟨hn0,hnN,normality_grid_reduction n hS hBS hSU hUT hTx hbad⟩
  have hg := hgrid N M hen.2.1 hen.2.2.1 (B S-2) hA Q hQ'
  have hM : ((M+1:ℕ):ℝ) ≤ 3*B x := by
    dsimp [M]
    push_cast
    have hh := Nat.floor_le hB0
    linarith
  have hsq : (((M+1:ℕ):ℝ))^2 ≤ (3*B x)^2 := pow_le_pow_left₀ (by positivity) hM 2
  have he : Real.exp (-(B S-2)/6)=Real.exp (1/3)*((Real.log S)^(-1/6:ℝ)) := by
    rw [Real.rpow_def_of_pos (Real.log_pos hS),← Real.exp_add]
    unfold B
    congr 1
    ring
  have hlogx : 0 ≤ Real.log x := by
    have h0 := (Real.exp_pos 1).trans_le hx
    have hh := (Real.le_log_iff_exp_le h0).mpr hx
    linarith
  calc
    _  ≤  C*(((M+1:ℕ):ℝ))^2*Real.log N*Real.exp (-(B S-2)/6) := by
      exact_mod_cast hg
    _  ≤  C*(3*B x)^2*((Real.exp 1+1)*Real.log x)*Real.exp (-(B S-2)/6) := by
      gcongr
      exact hen.2.2.2
    _ = _ := by rw [he]; ring

end TotientAsymptotic

end

end OAI
