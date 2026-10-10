import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryUnitTwist
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedMissingResidue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedThreeTwists

namespace OAI

/-! The literal three-row ramified expansion at the actual theta pole.
All unit twists are retained as frequencies of the same arithmetic residue. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace CubicFirstMoment

private instance : Finite Eisensteinˣ :=
  Nat.finite_of_card_ne_zero (by rw [eisenstein_units_card]; norm_num)
private instance : Fintype Eisensteinˣ := Fintype.ofFinite _

lemma cubicThetaRamifiedFactor_analytic (e : Eisensteinˣ) (n : ℕ)
    (h : Eisenstein) (s : ℂ) :
    AnalyticAt ℂ (fun z => cubicThetaRamifiedFactor e n z h) s := by
  have hN : (norm ((e:Eisenstein)*lambdaE^(n+2)):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero
      (mul_ne_zero e.ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero))).ne'
  let _ : NeZero (norm ((e:Eisenstein)*lambdaE^(n+2)):ℂ) := ⟨hN⟩
  exact analyticAt_const.mul
    (((differentiable_const_cpow_of_neZero (norm ((e:Eisenstein)*lambdaE^(n+2)):ℂ)).analyticAt _).comp
      (f:=fun z : ℂ => -z) (x:=s) analyticAt_id.neg)

def cubicThetaRamifiedShortContinuation (h : Eisenstein) (s : ℂ) : ℂ :=
  ∑' e : Eisensteinˣ, ∑ j : Fin 3, cubicThetaRamifiedFactor e j s h*
    cubicThetaRegularizedPrimaryTwist j (h*(e:Eisenstein)) s

lemma cubicThetaRamifiedShortContinuation_analytic {h : Eisenstein} (hh : h≠0)
    {s : ℂ} (hs : 1<s.re) :
    AnalyticAt ℂ (cubicThetaRamifiedShortContinuation h) s := by
  unfold cubicThetaRamifiedShortContinuation
  simp only [tsum_fintype]
  apply Finset.analyticAt_fun_sum
  intro e _
  apply Finset.analyticAt_fun_sum
  intro j _
  exact (cubicThetaRamifiedFactor_analytic e j h s).mul
    (cubicThetaRegularizedPrimaryTwist_analytic j (mul_ne_zero hh e.ne_zero) s hs)

lemma cubicThetaRamifiedShortContinuation_right {h : Eisenstein} (hh : h≠0)
    (hM : ∀ n : ℕ, 3≤n → ¬lambdaE^n∣h) {s : ℂ} (hs : 3<s.re) :
    cubicThetaRamifiedShortContinuation h s=cubicThetaRegularizedFrequency h s := by
  rw [cubicThetaRegularizedFrequency_right hh hs,
    cubicThetaFrequencyDirichlet_primary_finite (by linarith) h 3 hM,
    cubicThetaRamifiedShortContinuation,tsum_fintype,tsum_fintype,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp_rw [cubicThetaRegularizedPrimaryTwist_right _ (mul_ne_zero hh e.ne_zero) hs,
    ←cubicThetaPrimaryFourierSeries_unit]
  simp only [Fin.sum_univ_three,Fin.val_zero,Fin.val_one,Fin.val_two,
    Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  ring

theorem cubicThetaRamifiedShortContinuation_eq {h : Eisenstein} (hh : h≠0)
    (hM : ∀ n : ℕ, 3≤n → ¬lambdaE^n∣h) {s : ℂ} (hs : 1<s.re) :
    cubicThetaRamifiedShortContinuation h s=cubicThetaRegularizedFrequency h s := by
  have he : cubicThetaRamifiedShortContinuation h=ᶠ[𝓝[≠] s]
      cubicThetaRegularizedFrequency h := by
    apply cubicThetaMeromorphic_identity
      (fun z hz => (cubicThetaRamifiedShortContinuation_analytic hh hz).meromorphicAt)
      (fun z hz => (cubicThetaRegularizedFrequency_analytic hh z hz).meromorphicAt)
      (convex_halfSpace_re_gt 1).isPreconnected (z₀:=(4:ℂ))
      (by change 1<(4:ℂ).re; norm_num) hs
    have hn : ∀ᶠ z : ℂ in 𝓝 4, 3<z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [nhdsWithin_le_nhds hn] with z hz
    exact cubicThetaRamifiedShortContinuation_right hh hM hz
  exact tendsto_nhds_unique
    (((cubicThetaRamifiedShortContinuation_analytic hh hs).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).congr' he)
    ((cubicThetaRegularizedFrequency_analytic hh s hs).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds)

theorem cubicThetaArithmeticFourierResidue_ramified_finite {h : Eisenstein} (hh : h≠0)
    (hM : ∀ n : ℕ, 3≤n → ¬lambdaE^n∣h) :
    cubicThetaArithmeticFourierResidue h (4/3)=
      ∑' e : Eisensteinˣ, ∑ j : Fin 3, cubicThetaRamifiedFactor e j (4/3) h*
        cubicThetaArithmeticFourierResidue (lambdaE^(((j:ℕ)+2)%3)*(h*(e:Eisenstein))) (4/3) := by
  rw [←cubicThetaRegularizedFrequency_residue hh,
    ←cubicThetaRamifiedShortContinuation_eq hh hM (by norm_num)]
  unfold cubicThetaRamifiedShortContinuation cubicThetaRegularizedPrimaryTwist
  apply tsum_congr
  intro e
  apply Finset.sum_congr rfl
  intro j _
  rw [cubicThetaRegularizedPrimaryOne_residue_eq
    (mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) (mul_ne_zero hh e.ne_zero))]

theorem cubicThetaArithmeticFourierResidue_lambda_square_system
    {h : Eisenstein} (hh : ¬lambdaE∣h) :
    cubicThetaArithmeticFourierResidue (lambdaE^2*h) (4/3)=
      ∑' e : Eisensteinˣ,
        (cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*h)*
          cubicThetaArithmeticFourierResidue (lambdaE^2*(h*(e:Eisenstein))) (4/3)+
         cubicThetaRamifiedFactor e 2 (4/3) (lambdaE^2*h)*
          cubicThetaArithmeticFourierResidue (h*(e:Eisenstein)) (4/3)) := by
  have hh0 : h≠0 := fun he => hh (he ▸ dvd_zero lambdaE)
  have hM (n : ℕ) (hn : 3≤n) : ¬lambdaE^n∣lambdaE^2*h := by
    intro hd
    have ht := (pow_dvd_pow lambdaE hn).trans hd
    rw [show (3:ℕ)=2+1 by omega,pow_succ,
      mul_dvd_mul_iff_left (pow_ne_zero 2 lambdaE_prime.ne_zero)] at ht
    exact hh ht
  rw [cubicThetaArithmeticFourierResidue_ramified_finite
    (mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) hh0) hM]
  apply tsum_congr
  intro e
  have he0 : h*(e:Eisenstein)≠0 := mul_ne_zero hh0 e.ne_zero
  have hecop : ¬lambdaE∣h*(e:Eisenstein) := by
    intro hd
    rcases lambdaE_prime.dvd_mul.mp hd with hd | hd
    · exact hh hd
    · exact lambdaE_prime.not_isUnit (isUnit_of_dvd_unit hd e.isUnit)
  have hzero : cubicThetaArithmeticFourierResidue
      (lambdaE^2*(lambdaE^2*h*(e:Eisenstein))) (4/3)=0 := by
    rw [show lambdaE^2*(lambdaE^2*h*(e:Eisenstein))=
      lambdaE^3*(lambdaE*(h*(e:Eisenstein))) by ring,
      cubicThetaArithmeticFourierResidue_lambda_cube (mul_ne_zero lambdaE_prime.ne_zero he0),
      cubicThetaArithmeticFourierResidue_lambda_missing hecop]
  have hcube : cubicThetaArithmeticFourierResidue
      (lambdaE*(lambdaE^2*h*(e:Eisenstein))) (4/3)=
      cubicThetaArithmeticFourierResidue (h*(e:Eisenstein)) (4/3) := by
    rw [show lambdaE*(lambdaE^2*h*(e:Eisenstein))=lambdaE^3*(h*(e:Eisenstein)) by ring,
      cubicThetaArithmeticFourierResidue_lambda_cube he0]
  simp only [Fin.sum_univ_three,Fin.val_zero,Fin.val_one,Fin.val_two,Nat.reduceAdd,
    Nat.reduceMod,pow_zero,one_mul,pow_one,hzero,hcube,mul_zero,zero_add]
  rw [mul_assoc]

end CubicFirstMoment

end

end OAI
