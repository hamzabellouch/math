import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedMiddleSupport

namespace OAI

/-! The literal middle-row operator on the six-unit orbit has row norm
at most two thirds. The ramified residue system therefore has a unique
solution for each fixed base-frequency forcing. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

private instance : Finite Eisensteinˣ :=
  Nat.finite_of_card_ne_zero (by rw [eisenstein_units_card]; norm_num)
private instance : Fintype Eisensteinˣ := Fintype.ofFinite _

lemma cubicThetaRamifiedFactor_neg (e : Eisensteinˣ) (h : Eisenstein) (s : ℂ) :
    cubicThetaRamifiedFactor e 1 s (-h)=cubicThetaRamifiedFactor (-e) 1 s h := by
  have h3 : (3:Eisenstein)∣(e:Eisenstein)*lambdaE^3 := by
    refine ⟨-(e:Eisenstein)*lambdaE,?_⟩
    rw [pow_succ,lambdaE_sq]
    ring
  have h0 : (e:Eisenstein)*lambdaE^3≠0 :=
    mul_ne_zero e.ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero)
  have he := cubicThetaEisensteinGaussCoefficient_neg h3 h0 (-h)
  rw [neg_neg] at he
  unfold cubicThetaRamifiedFactor
  norm_num only [Nat.reduceAdd]
  rw [cubicThetaNorm_unit_lambda_pow,cubicThetaNorm_unit_lambda_pow]
  rw [Units.val_neg,neg_mul,he]

lemma cubicThetaRamifiedMiddle_sum_norm_pos {h : Eisenstein} (hh : lambdaE∣h-1) :
    (∑' e : Eisensteinˣ, ‖cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*h)‖)≤2/3 := by
  rw [tsum_fintype]
  have hb (e : Eisensteinˣ) :
      ‖cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*h)‖≤
        (if e=cubicThetaOmegaUnit then (1/3:ℝ) else 0)+
        (if e=-(cubicThetaOmegaUnit^2) then (1/3:ℝ) else 0) := by
    by_cases he : e=cubicThetaOmegaUnit
    · rw [ite_eq_left he]
      exact (cubicThetaRamifiedMiddleFactor_norm_le e h).trans (le_add_of_nonneg_right (by positivity))
    by_cases he' : e=-(cubicThetaOmegaUnit^2)
    · rw [ite_eq_left he',ite_eq_right he,zero_add]
      exact cubicThetaRamifiedMiddleFactor_norm_le e h
    · have hz : cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*h)=0 := by
        by_contra hz
        exact (cubicThetaRamifiedMiddleFactor_support e hh hz).elim he he'
      simp only [hz,norm_zero,ite_eq_right he,ite_eq_right he',add_zero,le_refl]
  calc
    _ ≤ ∑ e : Eisensteinˣ, ((if e=cubicThetaOmegaUnit then (1/3:ℝ) else 0)+
        (if e=-(cubicThetaOmegaUnit^2) then (1/3:ℝ) else 0)) :=
      Finset.sum_le_sum (fun e _ => hb e)
    _ = 2/3 := by rw [Finset.sum_add_distrib]; simp; norm_num

lemma cubicThetaRamifiedMiddle_sum_norm {h : Eisenstein}
    (hh : lambdaE∣h-1 ∨ lambdaE∣h+1) :
    (∑' e : Eisensteinˣ, ‖cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*h)‖)≤2/3 := by
  rcases hh with hh | hh
  · exact cubicThetaRamifiedMiddle_sum_norm_pos hh
  · have hn : lambdaE∣(-h)-1 := by
      convert dvd_neg.mpr hh using 1
      ring
    calc
      _ = ∑' e : Eisensteinˣ, ‖cubicThetaRamifiedFactor (-e) 1 (4/3) (lambdaE^2*h)‖ :=
        ((Equiv.neg Eisensteinˣ).tsum_eq _).symm
      _ = ∑' e : Eisensteinˣ, ‖cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*(-h))‖ := by
        apply tsum_congr
        intro e
        rw [show lambdaE^2*(-h)=-(lambdaE^2*h) by ring,cubicThetaRamifiedFactor_neg]
      _ ≤ 2/3 := cubicThetaRamifiedMiddle_sum_norm_pos hn

lemma cubicThetaUnitOrbit_lambda_class {h : Eisenstein} (hh : lambdaE∣h-1)
    (e : Eisensteinˣ) : lambdaE∣h*(e:Eisenstein)-1 ∨ lambdaE∣h*(e:Eisenstein)+1 := by
  obtain ⟨r,hr | hr⟩ := cubicThetaUnit_signed_power e
  · left
    have he : lambdaE∣(e:Eisenstein)-1 := by
      rw [hr]
      exact cubicThetaLambda_dvd_omega_pow_sub_one r
    convert dvd_add (dvd_mul_of_dvd_left hh (e:Eisenstein)) he using 1
    ring
  · right
    have he : lambdaE∣(e:Eisenstein)+1 := by
      rw [hr]
      convert dvd_neg.mpr (cubicThetaLambda_dvd_omega_pow_sub_one r) using 1
      ring
    convert dvd_add (dvd_mul_of_dvd_left hh (e:Eisenstein)) he using 1
    ring

theorem cubicThetaRamifiedUnitSystem_unique {h : Eisenstein} (hh : lambdaE∣h-1)
    (b f g : Eisensteinˣ → ℂ)
    (hf : ∀ d, f d=(∑' e : Eisensteinˣ,
      cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*(h*(d:Eisenstein)))*f (d*e))+b d)
    (hg : ∀ d, g d=(∑' e : Eisensteinˣ,
      cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*(h*(d:Eisenstein)))*g (d*e))+b d) : f=g := by
  let v (d : Eisensteinˣ) := f d-g d
  have hv (d : Eisensteinˣ) : v d=∑' e : Eisensteinˣ,
      cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*(h*(d:Eisenstein)))*v (d*e) := by
    dsimp only [v]
    rw [hf d,hg d,add_sub_add_right_eq_sub,←Summable.tsum_sub Summable.of_finite Summable.of_finite]
    apply tsum_congr
    intro e
    ring
  obtain ⟨d,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset Eisensteinˣ)
    (fun e => ‖v e‖) Finset.univ_nonempty
  have hn : ‖v d‖≤(2/3:ℝ)*‖v d‖ := by
    calc
      ‖v d‖ = ‖∑ e : Eisensteinˣ,
          cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*(h*(d:Eisenstein)))*v (d*e)‖ := by
        rw [hv d,tsum_fintype]
      _ ≤ ∑ e : Eisensteinˣ,
          ‖cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*(h*(d:Eisenstein)))*v (d*e)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ e : Eisensteinˣ,
          ‖cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*(h*(d:Eisenstein)))‖*‖v d‖ := by
        apply Finset.sum_le_sum
        intro e _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hmax (d*e) (Finset.mem_univ _)) (_root_.norm_nonneg _)
      _ = (∑' e : Eisensteinˣ,
          ‖cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*(h*(d:Eisenstein)))‖)*‖v d‖ := by
        rw [tsum_fintype,Finset.sum_mul]
      _ ≤ (2/3:ℝ)*‖v d‖ := mul_le_mul_of_nonneg_right
        (cubicThetaRamifiedMiddle_sum_norm (cubicThetaUnitOrbit_lambda_class hh d)) (_root_.norm_nonneg _)
  have hz : ‖v d‖=0 := by have hp := _root_.norm_nonneg (v d); linarith
  funext e
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have he := hmax e (Finset.mem_univ _)
  change ‖f e-g e‖≤‖v d‖ at he
  rw [hz] at he
  exact le_antisymm he (_root_.norm_nonneg _)

end CubicFirstMoment

end

end OAI
