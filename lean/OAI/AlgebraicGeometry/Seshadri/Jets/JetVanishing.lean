import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Analytic.CoordinateJets

namespace OAI


                                             
section
namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open MvPowerSeries
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.FormalCoordinates
open scoped Topology

lemma formalTrunc_eq_zero_iff {σ F : Type*} [Finite σ] [Field F]
    (n : ℕ) (f : MvPowerSeries σ F) :
    formalTrunc n f = 0 ↔ ∀ e, e.degree < n → MvPowerSeries.coeff e f = 0 := by
  change Ideal.Quotient.mk _ (f.truncTotal n) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, MvPolynomial.mem_pow_idealOfVars_iff']
  constructor <;> intro h e he
  · simpa only [MvPowerSeries.coeff_truncTotal f he] using h e he
  · simpa only [MvPowerSeries.coeff_truncTotal f he] using h e he

lemma binaryDegree (a b : ℕ) :
    (Finsupp.cons b (Finsupp.cons a (0 : Fin 0 →₀ ℕ))).degree = a + b := by
  change (Finsupp.cons b (Finsupp.cons a (0 : Fin 0 →₀ ℕ))).sum (fun _ n => n) = _
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp only [Fin.sum_univ_succ, Finsupp.cons_zero, Finsupp.cons_succ,
    Fin.sum_univ_zero, add_zero]
  omega

lemma analyticTrunc_zero_of_ideal_power
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (q : (ℂ × ℂ) → (A →ₐ[ℂ] ℂ))
    (hq : ∀ a, AnalyticAt ℂ (fun z => q z a) 0)
    (n : ℕ) (hn : 0 < n) (a : A) (ha : a ∈ (RingHom.ker (q 0))^n) :
    formalTrunc n (analyticTaylor q hq a) = 0 := by
  let ψ := (formalTrunc n).comp (analyticTaylor q hq)
  have hmap : (RingHom.ker (q 0)).map ψ.toRingHom ≤
      RingHom.ker (jetAugment (σ := Fin 2) (R := ℂ) n hn) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro b hb
    change jetAugment n hn (formalTrunc n (analyticTaylor q hq b)) = 0
    rw [formalTrunc_augment n hn, analyticTaylor_constantCoeff]
    exact hb
  have hmapn : ((RingHom.ker (q 0))^n).map ψ.toRingHom ≤ ⊥ := by
    rw [Ideal.map_pow]
    calc
      _ ≤ RingHom.ker (jetAugment (σ := Fin 2) (R := ℂ) n hn)^n :=
        pow_le_pow_left' hmap n
      _ = ⊥ := jetAugment_ker_pow n hn
  exact (Ideal.mem_bot).mp (hmapn (Ideal.mem_map_of_mem _ ha))

theorem mixedDeriv_zero_of_ideal_power
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (q : (ℂ × ℂ) → (A →ₐ[ℂ] ℂ))
    (hq : ∀ a, AnalyticAt ℂ (fun z => q z a) 0)
    (n : ℕ)
    (a : A) (ha : a ∈ (RingHom.ker (q 0))^n)
    (i j : ℕ) (hij : i + j < n) :
    iteratedDeriv j (fun z => iteratedDeriv i (fun x => q (x,z) a) 0) 0 = 0 := by
  have hz := analyticTrunc_zero_of_ideal_power q hq n (by omega) a ha
  have hc := (formalTrunc_eq_zero_iff n _).mp hz
    (Finsupp.cons j (Finsupp.cons i 0)) (by simpa only [binaryDegree] using hij)
  have hb : biCoeff (analyticFormal (analyticPullback q hq a)) (i,j) = 0 := by
    have hb := binaryEquiv_coeff (analyticTaylor q hq a) i j
    change biCoeff (binaryEquiv ℂ (analyticTaylor q hq a)) (i,j) = _ at hb
    rw [analyticTaylor, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.apply_symm_apply] at hb
    exact hb.trans hc
  have hd := analyticCoefficients_eq_derivative (analyticPullback q hq a) i j
  have hb' : analyticCoefficients (analyticPullback q hq a) (i,j) = 0 := by
    change biCoeff (biSeries (analyticCoefficients (analyticPullback q hq a))) (i,j) = 0 at hb
    rwa [biCoeff_biSeries] at hb
  rw [hb', zero_mul, zero_mul] at hd
  exact hd.symm

lemma mixedDeriv_shift (f : ℂ × ℂ → ℂ) (p : ℂ × ℂ) (i j : ℕ) :
    iteratedDeriv j (fun z => iteratedDeriv i (fun x => f (p + (x,z))) 0) 0 =
      iteratedDeriv j (fun z => iteratedDeriv i (fun x => f (x,z)) p.1) p.2 := by
  change iteratedDeriv j (fun z =>
    iteratedDeriv i (fun x => f (p.1 + x, p.2 + z)) 0) 0 = _
  have hx (z : ℂ) : iteratedDeriv i (fun x => f (p.1 + x, p.2 + z)) 0 =
      iteratedDeriv i (fun x => f (x, p.2 + z)) p.1 := by
    exact (congrFun (iteratedDeriv_comp_const_add i
      (fun x => f (x, p.2 + z)) p.1) 0).trans (by rw [add_zero])
  simp_rw [hx]
  exact (congrFun (iteratedDeriv_comp_const_add j
    (fun z => iteratedDeriv i (fun x => f (x,z)) p.1) p.2) 0).trans (by rw [add_zero])

theorem mixedDeriv_zero_at_of_ideal_power
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (q : (ℂ × ℂ) → (A →ₐ[ℂ] ℂ)) (p : ℂ × ℂ)
    (hq : ∀ a, AnalyticAt ℂ (fun z => q (p + z) a) 0)
    (n : ℕ)
    (a : A) (ha : a ∈ (RingHom.ker (q p))^n)
    (i j : ℕ) (hij : i + j < n) :
    iteratedDeriv j (fun z => iteratedDeriv i (fun x => q (x,z) a) p.1) p.2 = 0 := by
  have hz := mixedDeriv_zero_of_ideal_power (fun z => q (p + z)) hq n
    a (by simpa only [add_zero] using ha) i j hij
  exact (mixedDeriv_shift (fun z => q z a) p i j).symm.trans hz

end
end MaximalSeshadri.AlgebraicJets

end



end OAI
