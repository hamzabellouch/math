import OAI.MathematicalPhysics.Transonic.Phase.OperatorTarget

namespace OAI

section
noncomputable section
namespace SepticProfile
open Set Filter
open scoped ContDiff Topology BigOperators

lemma GlobalProfile.minkowski_radial (P : GlobalProfile) {t : ℝ} (ht : 0<t)
    (X : PhysicalSpace) :
    minkowskiSquare P.s0 t X=(t^(-P.beta))^2*P.radialM (radiusSq X/t^2) := by
  rw [P.s0_minkowskiSquare ht X,← P.radialM_sq,div_pow,radius_sq]

lemma power_flux_factor {t beta : ℝ} (ht : 0<t) :
    ((t^(-beta))^2)^((1:ℝ)/3)*t^(-beta)=t^(-ell*beta) := by
  have h1 : (t^(-beta))^2=t^((-beta)*2) := by
    rw [Real.rpow_mul ht.le,Real.rpow_two]
  rw [h1,← Real.rpow_mul ht.le,← Real.rpow_add ht]
  congr 1
  unfold ell
  ring

lemma GlobalProfile.time_flux (P : GlobalProfile) {t : ℝ} (ht : 0<t)
    (X : PhysicalSpace) :
    (minkowskiSquare P.s0 t X)^((1:ℝ)/3)*partialTime P.s0 t X=
      -t^(-ell*P.beta)*P.radialF (radiusSq X/t^2) := by
  rw [partialTime,(P.s0_time_derivative ht X).deriv,P.minkowski_radial ht X,
    Real.mul_rpow (sq_nonneg _) (P.radialM_pos (div_nonneg (radiusSq_nonneg X) (sq_nonneg t))).le]
  have he : ((t^(-P.beta))^2)^((1:ℝ)/3)*P.radialM (radiusSq X/t^2)^((1:ℝ)/3)*
      (-t^(-P.beta)*P.A (radius X/t))=
    -( ((t^(-P.beta))^2)^((1:ℝ)/3)*t^(-P.beta))*
      (P.radialM (radiusSq X/t^2)^((1:ℝ)/3)*P.A (radius X/t)) := by ring
  rw [he,power_flux_factor ht,GlobalProfile.radialF,← P.radialA_sq,div_pow,radius_sq]

lemma GlobalProfile.space_flux (P : GlobalProfile) {t : ℝ} (ht : 0<t)
    (X : PhysicalSpace) (j : Fin 4) :
    (minkowskiSquare P.s0 t X)^((1:ℝ)/3)*partialSpace P.s0 j t X=
      t^(-ell*P.beta)/t*P.radialJ (radiusSq X/t^2)*X j := by
  rw [partialSpace,(P.s0_coordinate_derivative_simple ht X j).deriv,P.minkowski_radial ht X,
    Real.mul_rpow (sq_nonneg _) (P.radialM_pos (div_nonneg (radiusSq_nonneg X) (sq_nonneg t))).le]
  have hc : P.A (radius X/t)*P.g (radiusSq X/t^2)=P.radialC (radiusSq X/t^2) := by
    have hy : (radius X/t)^2=radiusSq X/t^2 := by rw [div_pow,radius_sq]
    rw [← hy,P.radialC_sq]
  calc
    _=(((t^(-P.beta))^2)^((1:ℝ)/3)*t^(-P.beta))/t*
      (P.radialM (radiusSq X/t^2)^((1:ℝ)/3)*
      (P.A (radius X/t)*P.g (radiusSq X/t^2)))*X j := by ring
    _=_ := by rw [power_flux_factor ht,hc]; rfl

lemma radial_time_derivative {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Ici 0))
    (c : ℝ) {t : ℝ} (ht : 0<t) (X : PhysicalSpace) :
    HasDerivAt (fun q => q^c*f (radiusSq X/q^2))
      (t^(c-1)*(c*f (radiusSq X/t^2)-2*(radiusSq X/t^2)*
        derivWithin f (Ici 0) (radiusSq X/t^2))) t := by
  have hz : 0≤radiusSq X/t^2 := div_nonneg (radiusSq_nonneg X) (sq_nonneg t)
  have ha := (hasDerivAt_const t (radiusSq X)).div ((hasDerivAt_id t).pow 2)
    (pow_ne_zero 2 (ne_of_gt ht))
  have hd := (hf.differentiableOn (by simp) _ hz).hasDerivWithinAt.comp_hasDerivAt
    (h:=fun q => radiusSq X/q^2) t ha
    (Filter.Eventually.of_forall (fun q => div_nonneg (radiusSq_nonneg X) (sq_nonneg q)))
  have hp := (hasDerivAt_id t).rpow_const (p:=c) (Or.inl (ne_of_gt ht))
  convert hp.mul hd using 1 <;> try rfl
  simp only [Pi.pow_apply,Function.comp_apply,id_eq,Nat.cast_ofNat,one_mul,zero_mul,zero_sub]
  have he : t^c=t*t^(c-1) := by
    calc
      _=t^(1+(c-1)) := by congr 1; ring
      _=_ := by rw [Real.rpow_add ht,Real.rpow_one]
  rw [he]
  field_simp [ne_of_gt ht]
  ring

lemma radial_space_derivative {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Ici 0))
    {t : ℝ} (X : PhysicalSpace) (j : Fin 4) :
    HasDerivAt (fun r => f (radiusSq (coordinateLine X j r)/t^2)*(coordinateLine X j r) j)
      (f (radiusSq X/t^2)+2*(X j)^2/t^2*derivWithin f (Ici 0) (radiusSq X/t^2)) 0 := by
  have hz : 0≤radiusSq (coordinateLine X j 0)/t^2 :=
    div_nonneg (radiusSq_nonneg _) (sq_nonneg t)
  have hd := (hf.differentiableOn (by simp) _ hz).hasDerivWithinAt.comp_hasDerivAt
    (h:=fun r => radiusSq (coordinateLine X j r)/t^2) 0
    ((radiusSq_coordinate_derivative X j).div_const (t^2))
    (Filter.Eventually.of_forall (fun r => div_nonneg (radiusSq_nonneg _) (sq_nonneg t)))
  simp only [coordinateLine_zero] at hd
  have hi : HasDerivAt (fun r => (coordinateLine X j r) j) 1 0 := by
    convert (hasDerivAt_const (0:ℝ) (X j)).add (hasDerivAt_id (0:ℝ)) using 1 <;>
      first | rfl | simp [coordinateLine, Pi.add_def]
  convert hd.mul hi using 1 <;> try rfl
  simp only [Function.comp_apply,coordinateLine_zero]
  ring

end SepticProfile

end
end

end OAI
