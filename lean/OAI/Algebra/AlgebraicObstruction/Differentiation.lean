import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.SeriesJets

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries
variable {R σ τ ι S : Type*} [CommRing R]

 theorem Jet.mul {n : ℕ} {f f' g g' : MvPowerSeries σ R}
    (hf : Jet n f f') (hg : Jet n g g') : Jet n (f*g) (f'*g') := by
  change Vanishes n (f*g-f'*g')
  have heq : f*g-f'*g' = (f-f')*g + f'*(g-g') := by ring
  rw [heq]
  exact (Vanishes.mul_right hf g).add (Vanishes.mul_left hg f')

 theorem Jet.pderiv {n : ℕ} {f g : MvPowerSeries σ R}
    (h : Jet (n+1) f g) (i : σ) : Jet n (MvPowerSeries.pderiv (R := R) i f) (MvPowerSeries.pderiv (R := R) i g) := by
  classical
  apply Jet.iff_coeff.mpr
  intro e he
  simp only [MvPowerSeries.coeff_pderiv]
  rw [Jet.iff_coeff.mp h (e + Finsupp.single i 1) (by
    simp only [map_add, Finsupp.degree_single]; omega)]

 theorem Vanishes.pderiv {n : ℕ} {f : MvPowerSeries σ R}
    (h : Vanishes (n+1) f) (i : σ) : Vanishes n (MvPowerSeries.pderiv (R := R) i f) := by
  have hf : Jet (n+1) f 0 := by simpa only [Jet, sub_zero] using h
  simpa only [Jet, map_zero, sub_zero] using hf.pderiv i

 theorem jet_trunc [Finite σ] (n : ℕ) (f : MvPowerSeries σ R) :
    Jet n f (truncTotal n f).toMvPowerSeries := by
  apply Jet.iff_coeff.mpr
  intro e he
  simp only [MvPolynomial.coeff_coe, coeff_truncTotal _ he]

 theorem Jet.subst_series [Finite σ] [Finite τ] {n : ℕ} {f g : MvPowerSeries σ R}
    (a : σ → MvPowerSeries τ R) (ha : ∀ i, constantCoeff (a i) = 0) (h : Jet n f g) :
    Jet n (MvPowerSeries.subst a f) (MvPowerSeries.subst a g) := by
  apply jet_iff_truncTotal.mpr
  have hh := jet_iff_truncTotal.mp h
  calc
    truncTotal n (MvPowerSeries.subst a f) = truncTotal n (MvPowerSeries.subst a (truncTotal n f).toMvPowerSeries) :=
      truncTotal_subst_eq_truncTotal_truncTotal_subst ha
    _ = truncTotal n (MvPowerSeries.subst a (truncTotal n g).toMvPowerSeries) := by rw [hh]
    _ = truncTotal n (MvPowerSeries.subst a g) := (truncTotal_subst_eq_truncTotal_truncTotal_subst ha).symm

 theorem Vanishes.subst [Finite σ] [Finite τ] {n : ℕ} {f : MvPowerSeries σ R}
    (hf : Vanishes n f) (a : σ → MvPowerSeries τ R) (ha : ∀ i, constantCoeff (a i) = 0) :
    Vanishes n (MvPowerSeries.subst a f) := by
  have h : Jet n f 0 := by simpa only [Jet,sub_zero] using hf
  have hh := Jet.subst_series a ha h
  simpa only [Jet, ← MvPowerSeries.substAlgHom_apply (hasSubst_of_constantCoeff_zero ha), map_zero, sub_zero] using hh

theorem derivation_aeval [Fintype σ] [CommRing S] [Algebra R S]
    (D : Derivation R S S) (a : σ → S) (p : MvPolynomial σ R) :
    D (MvPolynomial.aeval a p) =
      ∑ i, MvPolynomial.aeval a (MvPolynomial.pderiv i p) * D (a i) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p t hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, MvPolynomial.aeval_X,
      MvPolynomial.pderiv_X, map_add, add_mul, Finset.sum_add_distrib, hp]
    simp [Pi.single_apply, Finset.mul_sum, mul_assoc]

 theorem pderiv_subst_polynomial [Fintype σ] (a : σ → MvPowerSeries τ R)
    (p : MvPolynomial σ R) (j : τ) :
    MvPowerSeries.pderiv (R := R) j (MvPowerSeries.subst a p.toMvPowerSeries) =
      ∑ i, subst a (MvPowerSeries.pderiv (R := R) i p.toMvPowerSeries) * MvPowerSeries.pderiv (R := R) j (a i) := by
  simp only [subst_coe, MvPowerSeries.pderiv_coe]
  exact derivation_aeval (MvPowerSeries.pderiv (R := R) j) a p

theorem pderiv_subst [Fintype σ] [Finite τ] (a : σ → MvPowerSeries τ R)
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) (j : τ) :
    MvPowerSeries.pderiv (R := R) j (MvPowerSeries.subst a f) =
      ∑ i, subst a (MvPowerSeries.pderiv (R := R) i f) * MvPowerSeries.pderiv (R := R) j (a i) := by
  classical
  ext e
  let p := truncTotal (e.degree+2) f
  have hfp : Jet (e.degree+2) f p.toMvPowerSeries := jet_trunc _ _
  have hleft : Jet (e.degree+1) (MvPowerSeries.pderiv (R := R) j (MvPowerSeries.subst a f))
      (MvPowerSeries.pderiv (R := R) j (MvPowerSeries.subst a p.toMvPowerSeries)) :=
    (Jet.subst_series a ha hfp).pderiv j
  have hright : Jet (e.degree+1)
      (∑ i, subst a (MvPowerSeries.pderiv (R := R) i f) * MvPowerSeries.pderiv (R := R) j (a i))
      (∑ i, subst a (MvPowerSeries.pderiv (R := R) i p.toMvPowerSeries) * MvPowerSeries.pderiv (R := R) j (a i)) := by
    apply Jet.iff_coeff.mpr
    intro exponent degree_lt
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro index _
    exact Jet.iff_coeff.mp
      ((Jet.subst_series a ha (hfp.pderiv index)).mul (Jet.refl _ _)) exponent degree_lt
  rw [Jet.iff_coeff.mp hleft e (Nat.lt_succ_self _), pderiv_subst_polynomial]
  exact (Jet.iff_coeff.mp hright e (Nat.lt_succ_self _)).symm

end BoundaryOnly.FormalObstruction.FormalCorrection

end

end OAI
