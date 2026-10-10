import OAI.NumberTheory.DirichletL.Moments.FirstScale
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentFirstExceptionalPrefactor
open CenteredMomentFirstScale CenteredMomentCanonicalFirst CenteredMomentCompleteCommon

lemma exceptional_core_nominal (K V E R C D A : ℝ)
    (hK:0<K)(hV:0<V)(hE:0<E)(hR:0<R)(hC:0<C)(hD:0<D)(hA:0<A):
    K*Real.sqrt (C*D)/(E*Real.sqrt R*V^2)*
      (V/C)^((2:ℝ)/3)*(V/D)^((2:ℝ)/3)*A^((5:ℝ)/6) =
    V*K^((1:ℝ)/6)*R^((1:ℝ)/3)/(E^((1:ℝ)/6)*C*D)*
      (A/(E*R*V^2/(K*C*D)))^((5:ℝ)/6) := by
  apply Real.log_injOn_pos
  · simp only [Set.mem_Ioi]; positivity
  · simp only [Set.mem_Ioi]; positivity
  · simp (disch := positivity) only [Real.log_mul,Real.log_div,Real.log_rpow,
      Real.log_sqrt,Real.log_pow]
    ring

lemma amplified_nominal_ratio (Z T j g : ℝ)(hZ:1<Z)(hT:0<T):
    (Z^(j+g)/T)^((5:ℝ)/6)=Z^(5*(j-Real.logb Z T+g)/6) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  rw [show j-Real.logb Z T+g=j+g-Real.logb Z T by ring]
  rw [show 5*(j+g-Real.logb Z T)/6=(j+g-Real.logb Z T)*((5:ℝ)/6) by ring,
    Real.rpow_mul hz.le,Real.rpow_sub hz,Real.rpow_logb hz (ne_of_gt hZ) hT]

theorem exceptional_core_log (K V E R C D Z j g : ℝ)
    (hK:0<K)(hV:0<V)(hE:0<E)(hR:0<R)(hC:0<C)(hD:0<D)(hZ:1<Z):
    K*Real.sqrt (C*D)/(E*Real.sqrt R*V^2)*
      (V/C)^((2:ℝ)/3)*(V/D)^((2:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6) =
    V*K^((1:ℝ)/6)*R^((1:ℝ)/3)/(E^((1:ℝ)/6)*C*D)*
      Z^(5*(j-Real.logb Z (E*R*V^2/(K*C*D))+g)/6) := by
  rw [exceptional_core_nominal K V E R C D (Z^(j+g)) hK hV hE hR hC hD
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)]
  rw [amplified_nominal_ratio Z _ j g hZ (by positivity)]

theorem scalar_exceptional_bound (s μ H K V E R C D Z j g : ℝ)
    (hK:0<K)(hV:0<V)(hE:0<E)(hR:0<R)(hC:0<C)(hD:0<D)(hZ:1<Z)
    (hs:s*V≤μ*H*K*Real.sqrt (C*D)/(E*Real.sqrt R)):
    s/V*(V/C)^((2:ℝ)/3)*(V/D)^((2:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6) ≤
    μ*H*(V*K^((1:ℝ)/6)*R^((1:ℝ)/3)/(E^((1:ℝ)/6)*C*D)*
      Z^(5*(j-Real.logb Z (E*R*V^2/(K*C*D))+g)/6)) := by
  have hdiv:=div_le_div_of_nonneg_right hs (sq_nonneg V)
  have he:s*V/V^2=s/V:=by field_simp
  rw [he] at hdiv
  calc
    _≤(μ*H*K*Real.sqrt (C*D)/(E*Real.sqrt R)/V^2)*
        (V/C)^((2:ℝ)/3)*(V/D)^((2:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6):=by
      gcongr
    _=μ*H*(K*Real.sqrt (C*D)/(E*Real.sqrt R*V^2)*
        (V/C)^((2:ℝ)/3)*(V/D)^((2:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6)):=by ring
    _=_:=by rw [exceptional_core_log K V E R C D Z j g hK hV hE hR hC hD hZ]

theorem actual_nominal_cancellation
    (I J E : Ideal ActualEisensteinCubic.O) (hE:E≠0)
    (K V Z j g : ℝ)(hK:0<K)(hV:0<V)(hZ:1<Z):
    let C : ℝ := (commonPart I J).absNorm;
    let D : ℝ := (commonPart J I).absNorm;
    let N : ℝ := E.absNorm;
    let R : ℝ := (Ideal.span {activeConductor I J}).absNorm;
    K*Real.sqrt (C*D)/(N*Real.sqrt R*V^2)*
      (V/C)^((2:ℝ)/3)*(V/D)^((2:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6) =
    V*K^((1:ℝ)/6)*R^((1:ℝ)/3)/(N^((1:ℝ)/6)*C*D)*
      Z^(5*(j-Real.logb Z (firstNominalScale I J E K V)+g)/6) := by
  exact exceptional_core_log K V _ _ _ _ Z j g hK hV (norm_pos E hE)
    (active_norm_pos I J) (norm_pos _ (commonPart_ne_zero I J))
    (norm_pos _ (commonPart_ne_zero J I)) hZ

end SevenEighths.CenteredMomentFirstExceptionalPrefactor

end

end OAI
