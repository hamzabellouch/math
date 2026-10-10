import Mathlib
import OAI.Analysis.Commutator.PositiveCauchySchwarz
import OAI.Analysis.Commutator.PositiveWOT

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma units_inverse_mem (M : VonNeumannAlgebra H) (A : (H →L[ℂ] H)ˣ)
    (hA : (A:H →L[ℂ] H)∈M) : (↑A⁻¹:H →L[ℂ] H)∈M := by
  change (↑A⁻¹:H →L[ℂ] H)∈M.carrier
  rw [←M.centralizer_centralizer']
  intro T hT
  exact (show Commute (A:H →L[ℂ] H) T from hT _ hA).units_inv_left.eq.symm

theorem exists_injective_inverse_limit (M : VonNeumannAlgebra H)
    (S : ℕ → H →L[ℂ] H) (hSM : ∀ n,S n∈M) (hone : ∀ n,1≤S n)
    (hmono : Monotone S) (v : J → H) (hdense : DenseRange v)
    (hbounded : ∀ j,∃ C : ℝ,∀ n,(inner ℂ (S n (v j)) (v j)).re≤C) :
    ∃ B : H →L[ℂ] H,B∈M ∧ 0≤B ∧ B≤1 ∧ Function.Injective B ∧
      (∀ n,B≤Ring.inverse (S n)) ∧
      (∀ x,Tendsto (fun n => Ring.inverse (S n) x) atTop (𝓝 (B x))) := by
  let U (n : ℕ) : (H →L[ℂ] H)ˣ := (CStarAlgebra.isUnit_of_le 1 (hone n)).unit
  have hu (n : ℕ) : (U n:H →L[ℂ] H)=S n := IsUnit.unit_spec _
  have hp (n : ℕ) : 0≤(U n:H →L[ℂ] H) := by rw [hu]; exact zero_le_one.trans (hone n)
  let P (n : ℕ) : H →L[ℂ] H := (↑(U n)⁻¹:H →L[ℂ] H)
  have hPeq (n : ℕ) : P n=Ring.inverse (S n) := by rw [←hu,Ring.inverse_unit]
  have hPM (n : ℕ) : P n∈M := units_inverse_mem M (U n) (by rw [hu]; exact hSM n)
  have hPpos (n : ℕ) : 0≤P n := CFC.inv_nonneg_of_nonneg (U n) (hp n)
  have hPone (n : ℕ) : P n≤1 := CStarAlgebra.inv_le_one (by change (1:H →L[ℂ] H)≤(U n:H →L[ℂ] H); rw [hu]; exact hone n)
  have hPmono : Antitone P := by
    intro n m hnm
    exact CStarAlgebra.inv_le_inv (hp n) (by rw [hu,hu]; exact hmono hnm)
  obtain ⟨B,hBM,hBpos,hB1,hBP,hlim⟩ := exists_strong_inf M P hPM hPpos hPone hPmono
  have hker : ∀ x,B x=0 → x=0 := by
    intro x hx
    have hin (j : J) : inner ℂ x (v j)=0 := by
      obtain ⟨C,hC⟩ := hbounded j
      have hh (n : ℕ) : ‖inner ℂ x (v j)‖^2≤(inner ℂ (P n x) x).re*C := by
        have hcs := inverse_cauchySchwarz (U n) (hp n) x (v j)
        rw [hu] at hcs
        exact hcs.trans (mul_le_mul_of_nonneg_left (hC n)
          ((ContinuousLinearMap.nonneg_iff_isPositive.mp (hPpos n)).re_inner_nonneg_left x))
      have ht : Tendsto (fun n => (inner ℂ (P n x) x).re*C) atTop (𝓝 0) := by
        have hh := (Complex.continuous_re.tendsto _ |>.comp
          ((hlim x).inner (tendsto_const_nhds (x:=x)))).mul_const C
        simpa only [hx,inner_zero_left,Complex.zero_re,zero_mul,Function.comp_apply] using hh
      have hz : ‖inner ℂ x (v j)‖^2≤0 := ge_of_tendsto ht (Eventually.of_forall hh)
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg (inner ℂ x (v j))])
    apply (inner_self_eq_zero (𝕜:=ℂ)).mp
    exact hdense.induction_on (p:=fun y => inner ℂ x y=0) x
      (isClosed_eq (continuous_const.inner continuous_id) continuous_const) hin
  refine ⟨B,hBM,hBpos,hB1,?_,?_,?_⟩
  · intro x y hxy
    apply sub_eq_zero.mp
    apply hker
    simp only [map_sub,hxy,sub_self]
  · intro n; rw [←hPeq]; exact hBP n
  · intro x; simpa only [hPeq] using hlim x

end Kadison.PositiveWOT

end

end
end

end OAI
