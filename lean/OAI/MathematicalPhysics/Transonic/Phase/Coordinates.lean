import OAI.MathematicalPhysics.Transonic.Phase.Flux

namespace OAI

section
noncomputable section
namespace SepticProfile
open Set Filter
open scoped ContDiff Topology BigOperators

abbrev PhysicalSpace := Fin 4 → ℝ
def radiusSq (X : PhysicalSpace) : ℝ := ∑ i, X i^2
def radius (X : PhysicalSpace) : ℝ := Real.sqrt (radiusSq X)
def coordinateLine (X : PhysicalSpace) (j : Fin 4) (r : ℝ) : PhysicalSpace :=
  fun i => X i + if i=j then r else 0
lemma radiusSq_nonneg (X : PhysicalSpace) : 0≤radiusSq X :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (X i))
lemma radius_sq (X : PhysicalSpace) : radius X^2=radiusSq X :=
  Real.sq_sqrt (radiusSq_nonneg X)
lemma coordinateLine_zero (X : PhysicalSpace) (j : Fin 4) : coordinateLine X j 0=X := by
  ext i
  simp [coordinateLine]
lemma radiusSq_coordinateLine (X : PhysicalSpace) (j : Fin 4) (r : ℝ) :
    radiusSq (coordinateLine X j r)=radiusSq X+2*X j*r+r^2 := by
  classical
  have he (i : Fin 4) : (X i+if i=j then r else 0)^2=X i^2+if i=j then 2*X j*r+r^2 else 0 := by
    split_ifs with h
    · subst i; ring
    · ring
  simp_rw [radiusSq,coordinateLine,he,Finset.sum_add_distrib]
  simp
  ring
lemma radiusSq_coordinate_derivative (X : PhysicalSpace) (j : Fin 4) :
    HasDerivAt (fun r => radiusSq (coordinateLine X j r)) (2*X j) 0 := by
  have he : (fun r => radiusSq (coordinateLine X j r))=(fun r => radiusSq X+2*X j*r+r^2) :=
    funext (radiusSq_coordinateLine X j)
  rw [he]
  convert ((hasDerivAt_const (0:ℝ) (radiusSq X)).add
    ((hasDerivAt_id (0:ℝ)).const_mul (2*X j))).add ((hasDerivAt_id (0:ℝ)).pow 2) using 1 <;> first | rfl | simp

lemma GlobalProfile.radialH_derivative (P : GlobalProfile) {z : ℝ} (hz : 0≤z) :
    HasDerivWithinAt P.radialH (P.b/2*P.radialH z*P.radialIntegrand z) (Ici 0) z := by
  have hd := (((P.radialPrimitive_derivative hz).const_mul (P.b/2)).exp).const_mul (1/P.b)
  convert hd using 1 <;> try rfl
  unfold GlobalProfile.radialH
  ring

def GlobalProfile.s0 (P : GlobalProfile) (t : ℝ) (X : PhysicalSpace) : ℝ :=
  t^(-P.b)*P.H (radius X/t)
lemma GlobalProfile.s0_radial (P : GlobalProfile) {t : ℝ} (X : PhysicalSpace) :
    P.s0 t X=t^(-P.b)*P.radialH (radiusSq X/t^2) := by
  rw [GlobalProfile.s0,P.H_radial,div_pow,radius_sq]

lemma GlobalProfile.s0_coordinate_derivative (P : GlobalProfile) {t : ℝ}
    (X : PhysicalSpace) (j : Fin 4) :
    HasDerivAt (fun r => P.s0 t (coordinateLine X j r))
      (t^(-P.b)*(P.b*P.radialH (radiusSq X/t^2)*P.radialIntegrand (radiusSq X/t^2))*X j/t^2) 0 := by
  have hz : 0≤radiusSq X/t^2 := div_nonneg (radiusSq_nonneg X) (sq_nonneg t)
  have hm (r : ℝ) : radiusSq (coordinateLine X j r)/t^2∈Ici (0:ℝ) :=
    div_nonneg (radiusSq_nonneg _) (sq_nonneg t)
  have hd := (P.radialH_derivative (hm 0)).comp_hasDerivAt
    (h:=fun r => radiusSq (coordinateLine X j r)/t^2) 0
    ((radiusSq_coordinate_derivative X j).div_const (t^2))
    (Filter.Eventually.of_forall hm)
  have he : (fun r => P.s0 t (coordinateLine X j r))=
      (fun r => t^(-P.b)*P.radialH (radiusSq (coordinateLine X j r)/t^2)) :=
    funext (fun r => P.s0_radial (t:=t) _)
  rw [he]
  simp only [coordinateLine_zero] at hd
  convert hd.const_mul (t^(-P.b)) using 1 <;> try rfl
  ring

lemma GlobalProfile.s0_time_derivative (P : GlobalProfile) {t : ℝ} (ht : 0<t)
    (X : PhysicalSpace) :
    HasDerivAt (fun q => P.s0 q X) (-t^(-P.beta)*P.A (radius X/t)) t := by
  have hp := (hasDerivAt_id t).rpow_const (p:= -P.b) (Or.inl (ne_of_gt ht))
  have hi := (hasDerivAt_const t (radius X)).div (hasDerivAt_id t) (ne_of_gt ht)
  have hd := hp.mul ((P.H_derivative (radius X/t)).comp t hi)
  change HasDerivAt (fun q => q^(-P.b)*P.H (radius X/q)) _ t
  convert hd using 1 <;> try rfl
  simp only [id_eq,one_mul,zero_mul,zero_sub,Function.comp_apply]
  have hpow : t^(-P.b)=t*t^(-P.beta) := by
    have he : -P.b=1+(-P.beta) := by unfold GlobalProfile.b; ring
    rw [he,Real.rpow_add ht,Real.rpow_one]
  have hpow' : t^(-P.b-1)=t^(-P.beta) := by congr 1; unfold GlobalProfile.b; ring
  rw [hpow,hpow']
  rw [GlobalProfile.A,(P.H_derivative (radius X/t)).deriv]
  field_simp [ne_of_gt ht]
  ring

end SepticProfile

end
end

end OAI
