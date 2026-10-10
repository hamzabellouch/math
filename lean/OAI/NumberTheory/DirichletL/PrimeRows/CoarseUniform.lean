import OAI.NumberTheory.DirichletL.PrimeRows.FirstWGrowth
import OAI.NumberTheory.DirichletL.PrimeRows.Conductor
import OAI.NumberTheory.DirichletL.Hecke.DyadicScale

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

lemma selectedFirstBound_polynomial {Q : ℝ} (hQ : 1≤Q) : selectedFirstBound Q 2≤8192*Q^3 := by
  have hQ0 : 0≤Q := by linarith
  have hsmall : Q^(1/100:ℝ)≤Q := by
    simpa using Real.rpow_le_rpow_of_exponent_le hQ (by norm_num : (1/100:ℝ)≤1)
  have hsmall0 : 0≤Q^(1/100:ℝ) := Real.rpow_nonneg hQ0 _
  have hQQ : Q≤Q^2 := by nlinarith
  have hQ2 : 0≤Q^2 := sq_nonneg Q
  have hQ3 : Q^2≤Q^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hQ) (sq_nonneg Q)]
  unfold selectedFirstBound
  rw [Real.rpow_two]
  calc
    _ ≤ 2*((2*Q^2)*2*(2*Q)*388+Q*(2*Q)) := by gcongr <;> nlinarith
    _ ≤ _ := by nlinarith

theorem nonprincipal_first_uniform_growth :
    ∃C : ℝ,0<C ∧ ∀χ : Character,χ.residue≠1 → ∀s : ℂ,-(1/100:ℝ)≤s.re →
      ‖HeckeOrigin.continued χ s‖≤C*(χ.modulus.absNorm:ℝ)^3*(3+|s.im|)^2 := by
  obtain ⟨Cd,hCd,hd⟩ := HeckeDeletionBounds.factors_any_re_subpower_bound 1 (by norm_num)
  let U := HeckeLogarithmicInput.uniformConstant
  have hU : 0≤U := HeckeLogarithmicInput.uniformConstant_nonneg
  refine ⟨1+U*Cd,by positivity,?_⟩
  intro χ hχ s hs
  obtain ⟨ψ,_,hp,hQ,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue≠1 := fun h=>hχ ((HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mpr h)
  have hN : (1:ℝ)≤χ.modulus.absNorm := HeckeLogarithmicInput.modulus_norm_ge_one χ
  have hψN : (1:ℝ)≤ψ.modulus.absNorm := HeckeLogarithmicInput.modulus_norm_ge_one ψ
  have hQ' : (ψ.modulus.absNorm:ℝ)≤χ.modulus.absNorm := by exact_mod_cast hQ
  have hpow : (ψ.modulus.absNorm:ℝ)^(3/5:ℝ)≤χ.modulus.absNorm := by
    apply le_trans _ hQ'
    simpa using Real.rpow_le_rpow_of_exponent_le hψN (by norm_num : (3/5:ℝ)≤1)
  have hg := HeckeLogarithmicInput.regular_right_growth ψ hp (by linarith : -(1/10:ℝ)≤s.re)
  rw [HeckeLogarithmicInput.regular_eq_nonprincipal ψ hψ] at hg
  have hl : ‖LFunction ψ s‖≤U*(χ.modulus.absNorm:ℝ)*(3+|s.im|)^2 := by
    exact hg.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hU) (sq_nonneg _))
  have hdel : ‖HeckeFiniteDeletion.factors χ.modulus ψ s‖≤Cd*(χ.modulus.absNorm:ℝ)^2 := by
    apply (hd χ.modulus ψ s).trans
    apply mul_le_mul_of_nonneg_left _ hCd.le
    calc
      _ ≤ (χ.modulus.absNorm:ℝ)^(max (-s.re) 0+1) := Real.rpow_le_rpow (by positivity)
        (HeckeDyadic.radical_norm_le_modulus χ) (by positivity)
      _ ≤ (χ.modulus.absNorm:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hN
        (by have hm : max (-s.re) 0≤(1/100:ℝ) := max_le (by linarith) (by norm_num);linarith)
      _ = _ := Real.rpow_two _
  rw [HeckeOrigin.continued,ite_eq_right hχ,HeckeDyadicReflection.LFunction_eq_of_mask_entire χ ψ hχ hmask,norm_mul]
  calc
    _ ≤ (U*(χ.modulus.absNorm:ℝ)*(3+|s.im|)^2)*(Cd*(χ.modulus.absNorm:ℝ)^2) :=
      mul_le_mul hl hdel (norm_nonneg _) (by positivity)
    _ ≤ _ := by nlinarith [mul_nonneg (pow_nonneg (by positivity : (0:ℝ)≤χ.modulus.absNorm) 3) (sq_nonneg (3+|s.im|))]

theorem calibrated_numerator_first_uniform_growth
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0<C ∧ ∀u : FreeRow,u.val≠1 → ∀s : ℂ,-(1/100:ℝ)≤s.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) s‖≤
        C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^3*(3+|s.im|)^2 := by
  obtain ⟨C,hC,hmain⟩ := nonprincipal_first_uniform_growth
  let A : ℝ := (conductorConstant:ℝ)*((∏P∈S,P).absNorm:ℝ)
  have hA : 0≤A := by dsimp [A];positivity
  refine ⟨C*(1+A^3),by positivity,?_⟩
  intro u hu s hs
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · simp only [hc,star_zero,zero_mul,norm_zero]
    positivity
  · have hnp := calibrated_row_nonprincipal S hS.prime hmax hS.bad u hu hc
    have hg := hmain (rowCharacter S hS.prime u) hnp s hs
    have hcal : ‖star ((calibrationForSet S hmax).residueMonoid u.val)‖≤1 := by
      rw [norm_star]
      exact (calibrationForSet S hmax).residueMonoid_norm_le_one _
    have hQ : ((rowCharacter S hS.prime u).modulus.absNorm:ℝ)≤
        A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ) := by
      have h := rowCharacter_conductor S hS.prime u
      dsimp [A]
      exact_mod_cast (by simpa only [mul_right_comm] using h)
    rw [norm_mul]
    calc
      _ ≤ ‖HeckeOrigin.continued (rowCharacter S hS.prime u) s‖ :=
        mul_le_of_le_one_left (norm_nonneg _) hcal
      _ ≤ C*((rowCharacter S hS.prime u).modulus.absNorm:ℝ)^3*(3+|s.im|)^2 := hg
      _ ≤ C*(A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ))^3*(3+|s.im|)^2 := by gcongr
      _ ≤ _ := by
        rw [mul_pow]
        nlinarith [mul_nonneg (pow_nonneg (by positivity : (0:ℝ)≤(Ideal.span {u.val}:Ideal O).absNorm) 3)
          (sq_nonneg (3+|s.im|))]

end SevenEighths.ProbeHighRowFamily

end

end OAI
