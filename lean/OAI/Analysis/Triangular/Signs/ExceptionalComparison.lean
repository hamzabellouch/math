import OAI.Analysis.Triangular.Signs.ExceptionalSign0
import OAI.Analysis.Triangular.Signs.ExceptionalSign1
import OAI.Analysis.Triangular.Signs.ExceptionalSign2
import OAI.Analysis.Triangular.Signs.ExceptionalSign3

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma frozenTaylor_affine (z : ℝ) (e : Fin 8 → ℝ) (v : ℝ) :
    frozenTaylor z e v=(1-z/Z)*frozenTaylor 0 e v+(z/Z)*frozenTaylor Z e v := by
  unfold frozenTaylor
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [←mul_assoc,Finset.mul_sum]
  rw [←add_mul,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  unfold frozenTaylorRow
  split_ifs <;> (try omega) <;> norm_num [Z] <;> ring
lemma frozenTaylor_actual (e : Fin 8 → ℝ) (he : e 1=1) (v : ℝ) :
    frozenTaylor (e 0) e v= -finiteTaylor 0 1 1 e v := by
  have heq : freezeParameter (e 0) e=e := by
    ext r
    unfold freezeParameter
    split_ifs with hr
    · rw [show r=0 from Fin.ext hr]
    · rfl
  rw [frozenTaylor_eq _ _ he,heq]
lemma exceptional_adjusted_nonneg (e : Fin 8 → ℝ) (he : ParameterPolytope e)
    {v z : ℝ} (hv : v∈Icc 0 1) (hz : 0 ≤ z) (hzB : z ≤ Z) :
    0 ≤ Q 1*(v+3*z)+(v^2+4*z*v+6*z^2)*
      ((1-z/Z)*(frozenTaylor 0 e v-3/1000)+(z/Z)*(frozenTaylor Z e v-3/1000)) := by
  let A := frozenTaylor 0 e v
  let D := frozenTaylor Z e v
  let B0 := v^2
  let B1 := v^2+2*Z*v
  let B2 := v^2+4*Z*v+6*Z^2
  have h0 := exceptional_sign_0 e he hv
  have h1 := exceptional_sign_1 e he hv
  have h2 := exceptional_sign_2 e he hv
  have h3 := exceptional_sign_3 e he hv
  change 46/1000 < Q 1+v*A at h0
  change 56/1000 < Q 1*(v+Z)+(2*B1*A+B0*D)/3 at h1
  change 24/1000 < Q 1*(v+2*Z)+(B2*A+2*B1*D)/3 at h2
  change 27/1000 < Q 1*(v+3*Z)+B2*D at h3
  have hv2 : v^2 ≤ 1 := by nlinarith [hv.1,hv.2]
  have hB0 : B0 ≤ 7/2 := by dsimp[B0]; linarith
  have hB1 : B1 ≤ 7/2 := by dsimp[B1,Z]; nlinarith [hv.1,hv.2]
  have hB2 : B2 ≤ 7/2 := by dsimp[B2,Z]; nlinarith [hv.1,hv.2]
  let b0 := v*(Q 1+v*(A-3/1000))
  let b1 := Q 1*(v+Z)+(2*B1*(A-3/1000)+B0*(D-3/1000))/3
  let b2 := Q 1*(v+2*Z)+(B2*(A-3/1000)+2*B1*(D-3/1000))/3
  let b3 := Q 1*(v+3*Z)+B2*(D-3/1000)
  have hb0 : 0 ≤ b0 := by dsimp[b0]; apply mul_nonneg hv.1; nlinarith [hv.2]
  have hb1 : 0 ≤ b1 := by dsimp[b1]; nlinarith
  have hb2 : 0 ≤ b2 := by dsimp[b2]; nlinarith
  have hb3 : 0 ≤ b3 := by dsimp[b3]; nlinarith
  let t := z/Z
  have ht0 : 0 ≤ t := div_nonneg hz (by norm_num[Z])
  have ht1 : t ≤ 1 := (div_le_one (by norm_num[Z])).mpr hzB
  have hzt : z=t*Z := by dsimp[t]; rw [div_mul_cancel₀ _ (by norm_num[Z] : Z≠0)]
  have hid : Q 1*(v+3*z)+(v^2+4*z*v+6*z^2)*
      ((1-z/Z)*(A-3/1000)+(z/Z)*(D-3/1000)) =
      b0*(1-t)^3+3*b1*t*(1-t)^2+3*b2*t^2*(1-t)+b3*t^3 := by
    change Q 1*(v+3*z)+(v^2+4*z*v+6*z^2)*((1-t)*(A-3/1000)+t*(D-3/1000))=_
    rw[hzt]
    dsimp[b0,b1,b2,b3,B0,B1,B2]
    ring
  change 0 ≤ Q 1*(v+3*z)+(v^2+4*z*v+6*z^2)*((1-z/Z)*(A-3/1000)+(z/Z)*(D-3/1000))
  rw[hid]
  positivity
lemma exceptional_rational_comparison (e : Fin 8 → ℝ) (he : ParameterPolytope e)
    {v : ℝ} (hv : v∈Icc 0 1) (hz : 0<e 0) (hzB : e 0 ≤ Z) :
    finiteTaylor 0 1 1 e v+3/1000 ≤ Q 1*((3*(e 0)+v)/(6*(e 0)^2+4*(e 0)*v+v^2)) := by
  have hh := exceptional_adjusted_nonneg e he hv hz.le hzB
  have ha := frozenTaylor_affine (e 0) e v
  rw [frozenTaylor_actual e (polytope_one e he)] at ha
  have hv0 := hv.1
  have hd : 0<6*(e 0)^2+4*(e 0)*v+v^2 := by positivity
  rw [←mul_div_assoc,le_div_iff₀ hd]
  nlinarith
end AtomicTriangular.Construction
end

end OAI
