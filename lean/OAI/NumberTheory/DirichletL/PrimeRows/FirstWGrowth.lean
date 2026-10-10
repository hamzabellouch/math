import OAI.NumberTheory.DirichletL.PrimeRows.SelectedFirstBounds
import OAI.NumberTheory.DirichletL.PrimeRows.PrincipalMask
import OAI.NumberTheory.DirichletL.Hecke.LogarithmicInput
import OAI.NumberTheory.DirichletL.Hecke.DyadicReflectedFamily

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem nonprincipal_first_growth (χ : Character) (hχ : χ.residue≠1) :
    ∃C : ℝ,0<C ∧ ∀s : ℂ,-(1/100:ℝ)≤s.re →
      ‖HeckeOrigin.continued χ s‖≤C*(3+|s.im|)^2 := by
  obtain ⟨ψ,_,hp,hQ,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue≠1 := fun h=>hχ ((HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mpr h)
  obtain ⟨Cd,hCd,hd⟩ := HeckeDeletionBounds.factors_any_re_subpower_bound 1 (by norm_num)
  let R : ℝ := (HeckeDeletionBounds.radical χ.modulus).absNorm
  have hR : 1≤R := by
    dsimp only [R]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (HeckeDeletionBounds.radical_ne_zero χ.modulus))
  have hU := HeckeLogarithmicInput.uniformConstant_nonneg
  let C : ℝ := HeckeLogarithmicInput.uniformConstant*(ψ.modulus.absNorm:ℝ)^(3/5:ℝ)*Cd*R^(101/100:ℝ)
  have hC : 0≤C := by dsimp [C];positivity
  refine ⟨1+C,by linarith,?_⟩
  intro s hs
  have hl := HeckeLogarithmicInput.regular_right_growth ψ hp (by linarith : -(1/10:ℝ)≤s.re)
  rw [HeckeLogarithmicInput.regular_eq_nonprincipal ψ hψ] at hl
  have hdel : ‖HeckeFiniteDeletion.factors χ.modulus ψ s‖≤Cd*R^(101/100:ℝ) := by
    apply (hd χ.modulus ψ s).trans
    apply mul_le_mul_of_nonneg_left _ hCd.le
    exact Real.rpow_le_rpow_of_exponent_le hR (by have hm : max (-s.re) 0≤(1/100:ℝ) := max_le (by linarith) (by norm_num); linarith)
  rw [HeckeOrigin.continued,ite_eq_right hχ,HeckeDyadicReflection.LFunction_eq_of_mask_entire χ ψ hχ hmask,norm_mul]
  calc
    _ ≤ (HeckeLogarithmicInput.uniformConstant*(ψ.modulus.absNorm:ℝ)^(3/5:ℝ)*(3+|s.im|)^2)*
        (Cd*R^(101/100:ℝ)) := mul_le_mul hl hdel (norm_nonneg _) (by positivity)
    _ = C*(3+|s.im|)^2 := by dsimp [C];ring
    _ ≤ (1+C)*(3+|s.im|)^2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

theorem calibrated_numerator_first_growth (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (u : FreeRow) (hu : u.val≠1) :
    ∃C : ℝ,0<C ∧ ∀s : ℂ,-(1/100:ℝ)≤s.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) s‖≤C*(3+|s.im|)^2 := by
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · refine ⟨1,by norm_num,?_⟩
    intro s hs
    simp only [hc,star_zero,zero_mul,norm_zero,one_mul]
    positivity
  · obtain ⟨C,hC,hbound⟩ := nonprincipal_first_growth (rowCharacter S hS.prime u)
      (calibrated_row_nonprincipal S hS.prime hmax hS.bad u hu hc)
    refine ⟨C,hC,?_⟩
    intro s hs
    rw [norm_mul,norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) ((calibrationForSet S hmax).residueMonoid_norm_le_one _)).trans
      (hbound s hs)

theorem calibrated_physicalRow_first_w_growth (eps : ℝ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (x z : ℂ) (l : ℝ)
    (hx : (51/100:ℝ)≤x.re) (hl : -(1/100:ℝ)≤l) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+l) :
    ∃C : ℝ,0<C ∧ ∀w : ℂ,l≤w.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤C*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_growth S hS hmax u hu
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=>selectedFirstBound P.val.val.absNorm x.re
  let L : ℝ := ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖*
    ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖
  let C : ℝ := L*Cn*(Ch*N)*∏P:T,A P
  have hA (P : T) : 0≤A P := selectedFirstBound_nonneg _ _ (by positivity)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=>hA P)
  have hC : 0≤C := by dsimp [C,L,N];positivity
  refine ⟨1+C,by linarith,?_⟩
  intro w hw
  have hn' := hn w (hl.trans hw)
  have hh' := hh eps S hS hfirst T η u x w z hx (hl.trans hw) hz (by linarith)
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P hP
    exact continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x.re x w z hx le_rfl
      (hl.trans hw) hz (by linarith [hfirst.positive])
  have he : star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
        ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [he,norm_mul,norm_mul,norm_mul]
  have hh'' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh'
  calc
    _ ≤ L*(Cn*(3+|w.im|)^2)*(Ch*N)*(∏P:T,A P) := by
      rw [norm_mul]
      apply mul_le_mul _ hg (norm_nonneg _) (by dsimp [L,N];positivity)
      apply mul_le_mul _ hh'' (norm_nonneg _) (by dsimp [L,N];positivity)
      exact mul_le_mul_of_nonneg_left hn' (by positivity)
    _ = C*(3+|w.im|)^2 := by dsimp [C];ring
    _ ≤ (1+C)*(3+|w.im|)^2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

end SevenEighths.ProbeHighRowFamily

end

end OAI
