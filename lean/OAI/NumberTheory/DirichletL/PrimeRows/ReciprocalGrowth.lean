import OAI.NumberTheory.DirichletL.PrimeRows.Conductor
import OAI.NumberTheory.DirichletL.Hecke.ReciprocalGrowth
import OAI.NumberTheory.DirichletL.Hecke.DyadicScale

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem targetRow_reciprocal_growth (e δ : ℝ) (he : 0<e) (he' : e<1/1000)
    (hδ : 0<δ) (hδ' : δ≤2) (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) (x : ℂ),
      HeckeZeroSupremum.beta+8*e≤x.re →
      ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS) x‖≤
        C*(η.modulus.absNorm:ℝ)^δ*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^δ*(3+|x.im|)^2 := by
  obtain ⟨D,hD,hmain⟩ := HeckeReciprocalGrowth.reciprocal_subpower e (δ/2) he he' (by linarith)
  let A : ℝ := (conductorConstant:ℝ)*((∏P∈S,P).absNorm:ℝ)
  have hA : 0≤A := by dsimp [A];positivity
  refine ⟨D*(2:ℝ)^(δ/2)*(1+A^δ),by positivity,?_⟩
  intro η u x hx
  let q : ℝ := η.modulus.absNorm
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hq : 0≤q := by dsimp [q];positivity
  have hN : 0≤N := by dsimp [N];positivity
  have hQ : (((targetRow η u).excludePrimes S hS).modulus.absNorm:ℝ)≤A*q*N := by
    have hh := targetRow_excluded_conductor S hS η u
    dsimp [A,q,N]
    exact_mod_cast (by simpa only [mul_assoc,mul_left_comm,mul_comm] using hh)
  have hc := HeckeDyadic.presentationComplexity_le_of_modulus_le
    ((targetRow η u).excludePrimes S hS) (A*q*N) x.im hQ
  have ht : 0≤3+|x.im| := by positivity
  have hpow : (2*(A*q*N)^2*(3+|x.im|)^2)^(δ/2)=
      (2:ℝ)^(δ/2)*A^δ*q^δ*N^δ*(3+|x.im|)^δ := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by norm_num : (0:ℝ)≤2) (by positivity),
      ←Real.rpow_natCast_mul (mul_nonneg (mul_nonneg hA hq) hN),
      ←Real.rpow_natCast_mul ht]
    norm_num only [Nat.cast_ofNat]
    rw [show (2:ℝ)*(δ/2)=δ by ring,
      Real.mul_rpow (mul_nonneg hA hq) hN,Real.mul_rpow hA hq]
    ring
  have hbase := hmain ((targetRow η u).excludePrimes S hS) x hx
  calc
    _ ≤ D*(2*(A*q*N)^2*(3+|x.im|)^2)^(δ/2) := by
      apply hbase.trans
      apply mul_le_mul_of_nonneg_left _ hD.le
      exact Real.rpow_le_rpow (by unfold HeckeReciprocalGrowth.presentationComplexity HeckeLogarithmic.complexity;positivity) hc (by linarith)
    _ = D*(2:ℝ)^(δ/2)*A^δ*q^δ*N^δ*(3+|x.im|)^δ := by rw [hpow];ring
    _ ≤ D*(2:ℝ)^(δ/2)*(1+A^δ)*q^δ*N^δ*(3+|x.im|)^2 := by
      have hh : (3+|x.im|)^δ≤(3+|x.im|)^2 := by
        simpa only [Real.rpow_ofNat] using
          (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg x.im] : (1:ℝ)≤3+|x.im|) hδ')
      apply mul_le_mul _ hh (Real.rpow_nonneg ht δ) (by positivity)
      gcongr
      linarith

end SevenEighths.ProbeHighRowFamily
end

end OAI
