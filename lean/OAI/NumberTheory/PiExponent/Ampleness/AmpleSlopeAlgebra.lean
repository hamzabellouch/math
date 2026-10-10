import OAI.NumberTheory.PiExponent.Ampleness.AmplePositiveTwist
import OAI.NumberTheory.PiExponent.Ampleness.FinitePullbackAmple
import OAI.NumberTheory.PiExponent.Ampleness.LineAmpleOperations
import OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

def slopeBundle (L H : LineBundle X) (a b : ℕ) : LineBundle X :=
  (L.pow b).tensor (H.pow a)

def slopeBundlePowIso (L H : LineBundle X) (a b n : ℕ) :
    ((slopeBundle L H a b).pow n).sheaf ≅ (slopeBundle L H (a*n) (b*n)).sheaf :=
  lineTensorPow (L.pow b) (H.pow a) n ≪≫
    moduleTensorIso (linePowerMul L b n) (linePowerMul H a n)

def slopeBundleAddIso (L H : LineBundle X) (a b e : ℕ) :
    ((slopeBundle L H a b).tensor (H.pow e)).sheaf ≅ (slopeBundle L H (a+e) b).sheaf :=
  lineTensorAssoc (L.pow b) (H.pow a) (H.pow e) ≪≫
    moduleTensorIso (Iso.refl _) (linePowerAdd H a e).symm

def slopeBundleCongrIso (L H : LineBundle X) (a b c d : ℕ)
    (ha : a = c) (hb : b = d) :
    (slopeBundle L H a b).sheaf ≅ (slopeBundle L H c d).sheaf := by
  subst c
  subst d
  exact Iso.refl _

def slopeBundleCrossIso (L H : LineBundle X) (a b c d : ℕ) (h : a*d ≤ c*b) :
    (((slopeBundle L H a b).pow d).tensor (H.pow (c*b-a*d))).sheaf ≅
      ((slopeBundle L H c d).pow b).sheaf :=
  moduleTensorIso (slopeBundlePowIso L H a b d) (Iso.refl _) ≪≫
    slopeBundleAddIso L H (a*d) (b*d) (c*b-a*d) ≪≫
      slopeBundleCongrIso L H (a*d+(c*b-a*d)) (b*d) (c*b) (d*b)
        (Nat.add_sub_of_le h) (Nat.mul_comm b d) ≪≫
      (slopeBundlePowIso L H c d b).symm

theorem ample_tensor_nonnegative_power (A H : LineBundle X)
    (hA : A.IsAmple) (hH : H.IsAmple) (n : ℕ) : (A.tensor (H.pow n)).IsAmple := by
  cases n with
  | zero =>
    exact PiExponent.AmpleIso.isAmple_of_sheaf_iso A (A.tensor (H.pow 0))
      (moduleTensorRightUnit A.sheaf).symm hA
  | succ n => exact hA.tensor (hH.pow (n+1) (by omega))

theorem ample_slope_of_cross_le (L H : LineBundle X) (hH : H.IsAmple)
    (a b c d : ℕ) (hb : 0 < b) (hd : 0 < d) (hcross : a*d ≤ c*b)
    (hA : (slopeBundle L H a b).IsAmple) : (slopeBundle L H c d).IsAmple := by
  have hp := ample_tensor_nonnegative_power ((slopeBundle L H a b).pow d) H
    (hA.pow d hd) hH (c*b-a*d)
  apply LineBundle.IsAmple.of_pow (slopeBundle L H c d) hb
  exact PiExponent.AmpleIso.isAmple_of_sheaf_iso _ _ (slopeBundleCrossIso L H a b c d hcross) hp

def linePowerTensorInverseIso (H : LineBundle X) (a : ℕ) (ha : 0 < a) :
    ((H.pow a).tensor H.inverse).sheaf ≅ (H.pow (a-1)).sheaf :=
  moduleTensorIso
    (eqToIso (congrArg (fun n => (H.pow n).sheaf) (by omega : a = a-1+1)) ≪≫
      linePowerAdd H (a-1) 1 ≪≫
        moduleTensorIso (Iso.refl _) (moduleTensorRightUnit H.sheaf))
    (Iso.refl _) ≪≫ moduleTensorInverseCancelIso (H.pow (a-1)).sheaf H

def slopeBundleSubtractIso (L H : LineBundle X) (a b : ℕ) (ha : 0 < a) :
    ((slopeBundle L H a b).tensor H.inverse).sheaf ≅ (slopeBundle L H (a-1) b).sheaf :=
  lineTensorAssoc (L.pow b) (H.pow a) H.inverse ≪≫
    moduleTensorIso (Iso.refl _) (linePowerTensorInverseIso H a ha)

theorem exists_smaller_ample_slope [IsIntegral X] [CompactSpace X]
    (L H : LineBundle X) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hA : (slopeBundle L H a b).IsAmple) :
    ∃ n : ℕ, 0 < n ∧ (slopeBundle L H (a*n-1) (b*n)).IsAmple ∧
      ((a*n-1 : ℕ) : ℚ) / (b*n : ℕ) < (a:ℚ)/b := by
  obtain ⟨n,hn,hamp⟩ := (slopeBundle L H a b).exists_ample_twist H.inverse hA
  have han := Nat.mul_pos ha hn
  have ham : (slopeBundle L H (a*n-1) (b*n)).IsAmple :=
    PiExponent.AmpleIso.isAmple_of_sheaf_iso _ _
      (moduleTensorIso (slopeBundlePowIso L H a b n) (Iso.refl _) ≪≫
        slopeBundleSubtractIso L H (a*n) (b*n) han) hamp
  refine ⟨n,hn,ham,?_⟩
  have hbq : (0:ℚ) < b := by exact_mod_cast hb
  have hnq : (0:ℚ) < n := by exact_mod_cast hn
  have hsub : ((a*n-1:ℕ):ℚ) = (a:ℚ)*n-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ a*n), Nat.cast_mul, Nat.cast_one]
  rw [hsub, Nat.cast_mul]
  apply (div_lt_div_iff₀ (mul_pos hbq hnq) hbq).mpr
  nlinarith

theorem exists_ample_slope [IsIntegral X] [CompactSpace X]
    (L H : LineBundle X) (hH : H.IsAmple) :
    ∃ a : ℕ, 0 < a ∧ (slopeBundle L H a 1).IsAmple := by
  obtain ⟨a,ha,hA⟩ := H.exists_ample_twist L hH
  refine ⟨a,ha,PiExponent.AmpleIso.isAmple_of_sheaf_iso _ _ ?_ hA⟩
  exact moduleTensorComm (H.pow a).sheaf L.sheaf ≪≫
    moduleTensorIso (moduleTensorRightUnit L.sheaf).symm (Iso.refl _)

end
end PiExponent.NumericalAmpleness

end OAI
