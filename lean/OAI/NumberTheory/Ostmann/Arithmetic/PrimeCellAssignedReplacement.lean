import OAI.NumberTheory.Ostmann.Arithmetic.AssignedPrimeCellReplacement
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellGridIdentities

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.LogCellPartition
open scoped BigOperators
open PrimeProgression PrimeCellReplacement PrimeCellFreezing Characters.RationalHistory
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ} [NeZero M]

theorem assignedJointTestSum_tupleWeight (N : ι → ℕ) (lo hi η Z : ι → ℝ)
    (j : GridBoxIndex lo hi η) (F : (ι → (ZMod M)ˣ) → ℂ) :
    assignedJointComplexTestSum N M lo hi η Z j F =
      ∑ p : AssignedPrimeTuple N lo hi η j,
        (assignedTupleWeight N lo hi η Z j p:ℂ)*jointUnitTest F (fun i => ((p i).val:ZMod M)) := by
  simp only [assignedJointComplexTestSum,assignedTupleWeight,Complex.ofReal_prod]

theorem assignedAbsMass_cast (N : ι → ℕ) (lo hi η Z : ι → ℝ)
    (j : GridBoxIndex lo hi η) (F : (ι → (ZMod M)ˣ) → ℂ) :
    (assignedAbsMass N M lo hi η Z j F:ℂ) =
      assignedJointComplexTestSum N M lo hi η Z j (fun u => (‖F u‖:ℂ)) := by
  simp only [assignedAbsMass,assignedJointComplexTestSum,Complex.ofReal_sum,
    Complex.ofReal_mul,assignedTupleWeight,Complex.ofReal_prod,jointAbsTest_cast]

theorem assignedAbsMass_le_of_error (N : ι → ℕ) (lo hi η Z : ι → ℝ)
    (j : GridBoxIndex lo hi η) (F : (ι → (ZMod M)ˣ) → ℂ) (main error : ℝ)
    (he : ‖assignedJointComplexTestSum N M lo hi η Z j (fun u => (‖F u‖:ℂ))-
      (main:ℂ)*∑ u : ι → (ZMod M)ˣ,(‖F u‖:ℂ)‖ ≤ error*∑ u : ι → (ZMod M)ˣ,‖F u‖) :
    assignedAbsMass N M lo hi η Z j F ≤ (main+error)*∑ u : ι → (ZMod M)ˣ,‖F u‖ := by
  rw [← assignedAbsMass_cast,← Complex.ofReal_sum,← Complex.ofReal_mul,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs] at he
  have hh := (le_abs_self _).trans he
  linarith

theorem assigned_smooth_replacement_of_errors (N : ι → ℕ) (lo hi η Z : ι → ℝ)
    (hZ : ∀ i, 0 < Z i) (hlo : ∀ i, 0 < lo i) (horder : ∀ i, lo i ≤ hi i)
    (j : GridBoxIndex lo hi η) (F : (ι → (ZMod M)ˣ) → ℂ) (f : (ι → ℝ) → ℂ)
    {D mesh error : ℝ} (hD : 0 ≤ D) (hm : 0 ≤ mesh)
    (hwidth : ∀ i, boxUpper lo hi η j i-boxLower lo hi η j i ≤ mesh)
    (hf : ∀ z∈logRectangle (boxLower lo hi η j) (boxUpper lo hi η j),
      DifferentiableAt ℝ (fun y => f (fun q => Real.exp (y q))) z)
    (hd : ∀ z∈logRectangle (boxLower lo hi η j) (boxUpper lo hi η j),∀ i,
      ‖deriv (fun t => f (Expr.logCurve (fun q => Real.exp (z q)) i t)) 0‖ ≤ D)
    {base : ι → ℝ} (hbase : base∈logRectangle (boxLower lo hi η j) (boxUpper lo hi η j))
    (he : ‖assignedJointComplexTestSum N M lo hi η Z j F-
      (principalMass M (boxLower lo hi η j) (boxUpper lo hi η j) Z:ℂ)*
        ∑ u : ι → (ZMod M)ˣ,F u‖ ≤ error*∑ u : ι → (ZMod M)ˣ,‖F u‖)
    (heAbs : ‖assignedJointComplexTestSum N M lo hi η Z j (fun u => (‖F u‖:ℂ))-
      (principalMass M (boxLower lo hi η j) (boxUpper lo hi η j) Z:ℂ)*
        ∑ u : ι → (ZMod M)ˣ,(‖F u‖:ℂ)‖ ≤ error*∑ u : ι → (ZMod M)ˣ,‖F u‖) :
    ‖smoothAssignedJointTestSum N M lo hi η Z j F f-
      principalIntegral M (boxLower lo hi η j) (boxUpper lo hi η j) Z f*
        ∑ u : ι → (ZMod M)ˣ,F u‖ ≤
      ((Fintype.card ι:ℝ)*D*mesh*
          (2*principalMass M (boxLower lo hi η j) (boxUpper lo hi η j) Z+error)+
        ‖f (fun q => Real.exp (base q))‖*error)*∑ u : ι → (ZMod M)ˣ,‖F u‖ := by
  classical
  let v : ℝ := (Fintype.card ι:ℝ)*D*mesh
  let f₀ := f (fun q => Real.exp (base q))
  let S := ∑ u : ι → (ZMod M)ˣ,F u
  let T := ∑ u : ι → (ZMod M)ˣ,‖F u‖
  let mass := principalMass M (boxLower lo hi η j) (boxUpper lo hi η j) Z
  let integral := principalIntegral M (boxLower lo hi η j) (boxUpper lo hi η j) Z f
  let actual := assignedJointComplexTestSum N M lo hi η Z j F
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hmass := assignedAbsMass_le_of_error N lo hi η Z j F mass error heAbs
  have hdisc := smooth_assigned_freezing_bound N lo hi η Z (fun i => (hZ i).le) j F f
    hD hm hwidth hf hd hbase
  rw [← assignedJointTestSum_tupleWeight] at hdisc
  have hdisc' : ‖smoothAssignedJointTestSum N M lo hi η Z j F f-f₀*actual‖ ≤
      v*((mass+error)*T) := hdisc.trans (mul_le_mul_of_nonneg_left hmass hv)
  have hap : ‖f₀*actual-f₀*((mass:ℂ)*S)‖ ≤ ‖f₀‖*(error*T) := by
    rw [← mul_sub,norm_mul]
    exact mul_le_mul_of_nonneg_left he (norm_nonneg _)
  have hint := residue_integral_freezing_bound M Z (boxLower lo hi η j) (boxUpper lo hi η j)
    hZ (fun i => (hlo i).trans_le (boxLower_ge lo hi η horder j i))
    (box_order lo hi η horder j) f hD hm hwidth hf hd hbase
  have hint' : ‖(mass:ℂ)*f₀-integral‖ ≤ v*mass := by
    rw [norm_sub_rev]
    simpa only [integral,mass,principalIntegral,principalMass,Complex.real_smul] using hint
  have hmain : ‖f₀*((mass:ℂ)*S)-integral*S‖ ≤ (v*mass)*T := by
    have heq : f₀*((mass:ℂ)*S)-integral*S = ((mass:ℂ)*f₀-integral)*S := by ring
    rw [heq,norm_mul]
    exact mul_le_mul hint' (norm_sum_le _ _) (norm_nonneg _) ((norm_nonneg _).trans hint')
  calc
    _ ≤ ‖smoothAssignedJointTestSum N M lo hi η Z j F f-f₀*actual‖+
        ‖f₀*actual-f₀*((mass:ℂ)*S)‖+‖f₀*((mass:ℂ)*S)-integral*S‖ := by
      have h₁ := norm_sub_le_norm_sub_add_norm_sub
        (smoothAssignedJointTestSum N M lo hi η Z j F f) (f₀*actual) (integral*S)
      have h₂ := norm_sub_le_norm_sub_add_norm_sub (f₀*actual) (f₀*((mass:ℂ)*S)) (integral*S)
      simpa only [add_assoc] using h₁.trans (add_le_add le_rfl h₂)
    _ ≤ v*((mass+error)*T)+‖f₀‖*(error*T)+(v*mass)*T :=
      add_le_add (add_le_add hdisc' hap) hmain
    _ = _ := by dsimp only [v,f₀,T,mass]; ring

end Ostmann.Arithmetic.LogCellPartition

end

end OAI
