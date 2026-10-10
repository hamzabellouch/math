import Mathlib
import OAI.Analysis.Commutator.DyadicSpectral
import OAI.Analysis.Commutator.VonNeumannCStar

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open Filter

open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Kadison.ProjectionFaithfulFunctional

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

theorem positive_eq_zero_of_projection_faithful
    (hfaith : ∀ p : M,IsStarProjection (p : H →L[ℂ] H) → τ p=0 → p=0)
    (a : M) (ha : 0≤a) (hτa : τ a=0) : a=0 := by
  let c : ℝ := ‖a‖+1
  have hc : 0<c := by dsimp [c]; positivity
  let b : M := ((c⁻¹:ℝ):ℂ) • a
  have hb : 0≤b := smul_nonneg (show (0:ℂ)≤(c⁻¹:ℝ) from by exact_mod_cast inv_nonneg.mpr hc.le) ha
  have hbn : ‖b‖≤1 := by
    have he : ‖a‖≤c := by dsimp [c]; linarith
    have hh : c⁻¹ * ‖a‖≤1 := by
      simpa only [inv_mul_cancel₀ hc.ne'] using mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hc.le)
    simpa only [b,norm_smul,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr hc.le)] using hh
  have hb1 : b≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg b hb).mp hbn
  have hτb : τ b=0 := by simp only [b,map_smul,hτa,smul_zero]
  let B (n : ℕ) : M := ⟨Polar.dyadicRemainder (b:H →L[ℂ] H) n,
    Polar.dyadicRemainder_mem M b.property n⟩
  let P (n : ℕ) : M := ⟨Polar.halfCut (B n : H →L[ℂ] H),Polar.halfCut_mem M (B n).property⟩
  have hBpos (n : ℕ) : 0≤B n := (Polar.dyadicRemainder_bounds hb hb1 n).1
  have hPproj (n : ℕ) : IsStarProjection (P n : H →L[ℂ] H) := Polar.isProjection_halfCut _
  have hnext (n : ℕ) : B (n+1)=B n+B n-P n := rfl
  have hPpos (n : ℕ) : 0≤P n := (hPproj n).nonneg
  have hPτ (n : ℕ) : τ (B n)=0 ∧ P n=0 := by
    induction n with
    | zero =>
      have hz : τ (B 0)=0 := hτb
      have hsmall : τ (P 0)≤0 := by
        have h : τ (P 0)≤τ (B 0+B 0) := τ.monotone
          (show P 0≤B 0+B 0 from sub_nonneg.mp (hnext 0 ▸ hBpos 1))
        simpa only [map_add,hz,zero_add] using h
      exact ⟨hz,hfaith (P 0) (hPproj 0) (le_antisymm hsmall (τ.map_nonneg (hPpos 0)))⟩
    | succ n ih =>
      have hz : τ (B (n+1))=0 := by rw [hnext,ih.2,sub_zero,map_add,ih.1,zero_add]
      have hsmall : τ (P (n+1))≤0 := by
        have h : τ (P (n+1))≤τ (B (n+1)+B (n+1)) := τ.monotone
          (show P (n+1)≤B (n+1)+B (n+1) from
          sub_nonneg.mp (hnext (n+1) ▸ hBpos (n+2)))
        simpa only [map_add,hz,zero_add] using h
      exact ⟨hz,hfaith (P (n+1)) (hPproj (n+1))
        (le_antisymm hsmall (τ.map_nonneg (hPpos (n+1))))⟩
  have hstep (n : ℕ) : Polar.dyadicStep (b:H →L[ℂ] H) n=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have he : Polar.halfCut (Polar.dyadicRemainder (b:H →L[ℂ] H) i)=0 :=
      congrArg (fun a : M => (a:H →L[ℂ] H)) (hPτ i).2
    rw [he,smul_zero]
  have hnorm : ‖b‖≤0 := by
    apply le_of_tendsto_of_tendsto (tendsto_const_nhds (x:=‖b‖))
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤2⁻¹) (by norm_num))
    apply Eventually.of_forall
    intro n
    have h := Polar.dyadicStep_norm_error hb hb1 n
    change ‖(b:H →L[ℂ] H)‖≤2⁻¹^n
    simpa only [hstep,sub_zero] using h
  have hzero : b=0 := norm_le_zero_iff.mp hnorm
  have hc0 : ((c⁻¹:ℝ):ℂ)≠0 := by exact_mod_cast inv_ne_zero hc.ne'
  exact (smul_eq_zero.mp hzero).resolve_left hc0

end Kadison.ProjectionFaithfulFunctional

end

end
end

end OAI
