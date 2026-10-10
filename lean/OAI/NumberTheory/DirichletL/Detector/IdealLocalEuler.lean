import OAI.NumberTheory.DirichletL.Detector.HighSeries
import OAI.NumberTheory.DirichletL.Detector.SourcePrimeFactor
import OAI.NumberTheory.DirichletL.IdealEuler

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein ProbePhase ProbeEuler ProbePrimePower ProbeRow
local notation "O" => ActualEisensteinCubic.O

lemma primaryGenerator_prime_power (p : O) (hp : p≠0) (hprimary : goodLambda^2∣p-1) (e : ℕ) :
    primaryGenerator ((Ideal.span {p})^e)=p^e := by
  rw [primaryGenerator_pow,primaryGenerator_span p hp hprimary]

lemma prime_power_small_squarefree (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (e : ℕ) (he : e≤1) :
    Squarefree ((Ideal.span {p})^e) := by
  have hP : Prime (Ideal.span {p}:Ideal O) :=
    Ideal.prime_of_isPrime (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero) inferInstance
  have hcases : e=0 ∨ e=1 := by omega
  rcases hcases with rfl|rfl
  · simpa only [pow_zero] using (squarefree_one : Squarefree (1:Ideal O))
  · simpa only [pow_one] using hP.squarefree

theorem bareIdealHighCoefficient_at_prime (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (e l k m : ℕ) (he : e≤1) :
    bareIdealHighCoefficient η 1 ((Ideal.span {p})^e) ((Ideal.span {p})^l)
      ((Ideal.span {p})^k) ((Ideal.span {p})^m) =
    bareSourceCoefficient η (Ideal.span {p^e})
      (by rw [← Ideal.span_singleton_pow,primaryGenerator_prime_power p hp.ne_zero hprimary e];
          exact pow_ne_zero _ hp.ne_zero)
      (p^(e+3*l)) (p^k) (pow_ne_zero _ hp.ne_zero) (p^(6*m)) := by
  have hguard : Squarefree ((Ideal.span {p})^e) ∧ Supported ((Ideal.span {p})^e) ∧
      Supported ((Ideal.span {p})^l) ∧ Supported ((Ideal.span {p})^k) ∧ Supported ((Ideal.span {p})^m) :=
    ⟨prime_power_small_squarefree p hp e he,supported_pow hs e,supported_pow hs l,supported_pow hs k,supported_pow hs m⟩
  unfold bareIdealHighCoefficient
  rw [dite_eq_left hguard]
  simp only [primaryGenerator_prime_power p hp.ne_zero hprimary,one_mul]
  have hA : p^e*(p^l)^3=p^(e+3*l) := by rw [←pow_mul,Nat.mul_comm l 3,←pow_add]
  have hH : (p^m)^6=p^(6*m) := by rw [←pow_mul,Nat.mul_comm m 6]
  simp only [hA,hH,Ideal.span_singleton_pow]

lemma fullIdealWeight_power (s : ℂ) (I : Ideal O) (n : ℕ) :
    fullIdealWeight s (I^n)=fullIdealWeight s I^n := (IdealEuler.normWeight s).map_pow I n

lemma prime_spectral_weights (p : O) (hp : p≠0) (e l k m : ℕ) (x w z : ℂ) :
    fullIdealWeight (x+1/2) ((Ideal.span {p})^e) *
      fullIdealWeight (1+3*x) ((Ideal.span {p})^l) *
      fullIdealWeight w ((Ideal.span {p})^k) * fullIdealWeight (6*z) ((Ideal.span {p})^m) =
    (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) := by
  have hI : (Ideal.span {p}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr hp
  have hQ : (Ideal.absNorm (Ideal.span {p}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hI
  simp only [fullIdealWeight_power]
  simp only [fullIdealWeight,ite_eq_right hI]
  rw [←Complex.cpow_mul_nat,←Complex.cpow_mul_nat,←Complex.cpow_mul_nat,←Complex.cpow_mul_nat,
    ←Complex.cpow_add _ _ hQ,←Complex.cpow_add _ _ hQ,←Complex.cpow_add _ _ hQ]
  congr 1
  ring

theorem bareIdealHighSummand_at_prime (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (e l k m : ℕ) (he : e≤1) (x w z : ℂ) :
    bareIdealHighSummand η 1 x w z ((Ideal.span {p})^e) ((Ideal.span {p})^l)
      ((Ideal.span {p})^k) ((Ideal.span {p})^m) =
    sourcePrincipalTerm p hp hg (targetMonoid η p) (actualACube η p) x w z e l k m := by
  unfold bareIdealHighSummand
  rw [bareIdealHighCoefficient_at_prime η p hp hprimary hs e l k m he]
  have hw := prime_spectral_weights p hp.ne_zero e l k m x w z
  simp only [mul_assoc] at hw ⊢
  rw [hw]
  simpa only [mul_assoc] using
    bareSourceCoefficient_weighted_prime η p hp hg hchar hprimary hs e l k m he _ x w z

def idealHighLocalFactor (η : HeckeFamily.Character) (P : Ideal O) (x w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l, ∑' k, ∑' m,
    bareIdealHighSummand η 1 x w z (P^e.val) (P^l) (P^k) (P^m)

theorem idealHighLocalFactor_eq_source (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (x w z : ℂ) :
    idealHighLocalFactor η (Ideal.span {p}) x w z =
      sourcePrincipalSeries p hp hg (targetMonoid η p) (actualACube η p) x w z := by
  unfold idealHighLocalFactor sourcePrincipalSeries
  apply Finset.sum_congr rfl
  intro e he
  apply tsum_congr
  intro l
  apply tsum_congr
  intro k
  apply tsum_congr
  intro m
  exact bareIdealHighSummand_at_prime η p hp hg hchar hprimary hs e.val l k m (by omega) x w z

theorem idealHighLocalFactor_euler_identity (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) ((actualACube η p)^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1)
    (hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) (targetMonoid η p) 1 x≠0) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    idealHighLocalFactor η (Ideal.span {p}) x w z =
      (1-coordD Q (targetMonoid η p) 1 x) / ((1-coordV Q z)*(1-coordW Q 1 w)) *
        unramifiedClosed Q ((actualACube η p)^2) (targetMonoid η p) 1 x w z := by
  rw [idealHighLocalFactor_eq_source η p hp hg hchar hprimary hs]
  exact sourcePrincipalSeries_euler_identity p hp hg hchar _ _ x w z hV hR hW hD

end SevenEighths.ProbePhysical
end

end OAI
