import OAI.NumberTheory.DirichletL.PrimeRows.TupleGrowth
import OAI.NumberTheory.DirichletL.PrimeRows.ReciprocalGrowth

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem calibrated_scalar_growth (e δ : ℝ) (he : 0<e) (he' : e<1/1000)
    (hδ : 0<δ) (hδ' : δ≤1) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 → ∀(x w z : ℂ),
      HeckeZeroSupremum.beta+8*e≤x.re → (1/2:ℝ)≤w.re → (17/50:ℝ)≤z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
          HeckeOrigin.continued (rowCharacter S hS.prime u) w*
          HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)‖≤
        C*(η.modulus.absNorm:ℝ)^δ*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(3/5+δ)*
          (3+|x.im|)^2*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_positive_growth (1/2) (δ/2) (by norm_num) (by linarith) S hS hmax
  obtain ⟨Cr,hCr,hr⟩ := targetRow_reciprocal_growth e (δ/2) he he' (by linarith) (by linarith) S hS.prime
  let B : ℝ := HeckeReciprocalBound.bound 2
  have hB : 0≤B := tsum_nonneg (fun _=>norm_nonneg _)
  refine ⟨(1+B)*Cn*Cr,by positivity,?_⟩
  intro η u hu x w z hx hw hz
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hN : 0<N := by
    dsimp [N]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  have hn' := hn u hu w hw
  have hr' := hr η u x hx
  have hz' : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤1+B := by
    apply (HeckeStripActual.LFunction_norm_le _ (by norm_num : (1:ℝ)<2) (s:=6*z) ?_).trans
    · dsimp [B];linarith
    · norm_num [Complex.mul_re];linarith
  have hη : (η.modulus.absNorm:ℝ)^(δ/2)≤(η.modulus.absNorm:ℝ)^δ :=
    Real.rpow_le_rpow_of_exponent_le (HeckeLogarithmicInput.modulus_norm_ge_one η) (by linarith)
  have he : star ((calibrationForSet S hmax).residueMonoid u.val)*
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) w*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)=
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x := by ring
  rw [he,norm_mul,norm_mul]
  calc
    _ ≤ (1+B)*(Cn*N^(3/5+δ/2)*(3+|w.im|)^2)*
        (Cr*(η.modulus.absNorm:ℝ)^(δ/2)*N^(δ/2)*(3+|x.im|)^2) := by
      apply mul_le_mul _ hr' (norm_nonneg _) (by positivity)
      exact mul_le_mul hz' hn' (norm_nonneg _) (by positivity)
    _ ≤ (1+B)*(Cn*N^(3/5+δ/2)*(3+|w.im|)^2)*
        (Cr*(η.modulus.absNorm:ℝ)^δ*N^(δ/2)*(3+|x.im|)^2) := by gcongr
    _ = ((1+B)*Cn*Cr)*(η.modulus.absNorm:ℝ)^δ*N^(3/5+δ)*(3+|x.im|)^2*(3+|w.im|)^2 := by
      have hp : N^(3/5+δ/2)*N^(δ/2)=N^(3/5+δ) := by
        rw [←Real.rpow_add hN]
        congr 1
        ring
      calc
        _ = ((1+B)*Cn*Cr)*(η.modulus.absNorm:ℝ)^δ*(N^(3/5+δ/2)*N^(δ/2))*(3+|x.im|)^2*(3+|w.im|)^2 := by ring
        _ = _ := by rw [hp]

end SevenEighths.ProbeHighRowFamily
end

end OAI
