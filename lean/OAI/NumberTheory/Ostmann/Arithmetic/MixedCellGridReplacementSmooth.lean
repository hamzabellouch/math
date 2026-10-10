import OAI.NumberTheory.Ostmann.Arithmetic.MixedCellGridReplacementDiscrete

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.LogCellPartition
open scoped BigOperators
open PrimeCellFreezing MixedCellIntegralFreezing Characters.RationalHistory
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ} [NeZero M]

theorem mixedAssignedAbsMass_le_of_error (NI : ℕ) (N : ι → ℕ)
    (loI hiI ηI G : ℝ) (φ : ℝ → ℝ) (lo hi η Z : ι → ℝ)
    (j : MixedGridIndex loI hiI ηI lo hi η) (F : ZMod M → (ι → (ZMod M)ˣ) → ℂ)
    (main error : ℝ)
    (he : ‖mixedAssignedTestSum NI N M loI hiI ηI G φ lo hi η Z j (fun r u => (‖F r u‖:ℂ))-
      (main:ℂ)*∑ r : ZMod M, ∑ u : ι → (ZMod M)ˣ,(‖F r u‖:ℂ)‖ ≤
      error*∑ r : ZMod M, ∑ u : ι → (ZMod M)ˣ,‖F r u‖) :
    mixedAssignedAbsMass NI N M loI hiI ηI G φ lo hi η Z j F ≤
      (main+error)*∑ r : ZMod M, ∑ u : ι → (ZMod M)ˣ,‖F r u‖ := by
  rw [← mixedAssignedAbsMass_cast] at he
  simp only [← Complex.ofReal_sum,← Complex.ofReal_mul,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs] at he
  have hh := (le_abs_self _).trans he
  linarith

theorem mixed_assigned_smooth_replacement_of_errors (NI : ℕ) (N : ι → ℕ)
    (loI hiI ηI G : ℝ) (φ : ℝ → ℝ) (lo hi η Z : ι → ℝ)
    (j : MixedGridIndex loI hiI ηI lo hi η)
    (hφ : Continuous φ)
    (hφ0 : ∀ t ∈ Set.Icc (gridPoint loI hiI ηI j.1.val)
      (gridPoint loI hiI ηI (j.1.val+1)), 0 ≤ φ (t-G))
    (hZ : ∀ i, 0 < Z i) (hlo : ∀ i, 0 < boxLower lo hi η j.2 i)
    (F : ZMod M → (ι → (ZMod M)ˣ) → ℂ) (f : (Option ι → ℝ) → ℂ)
    {D mesh error : ℝ} (hD : 0 ≤ D) (hm : 0 ≤ mesh)
    (hwidthI : gridPoint loI hiI ηI (j.1.val+1)-gridPoint loI hiI ηI j.1.val ≤ mesh)
    (hwidth : ∀ i, boxUpper lo hi η j.2 i-boxLower lo hi η j.2 i ≤ mesh)
    (hf : ∀ z∈logRectangle
      (Option.elim' (gridPoint loI hiI ηI j.1.val) (boxLower lo hi η j.2))
      (Option.elim' (gridPoint loI hiI ηI (j.1.val+1)) (boxUpper lo hi η j.2)),
      DifferentiableAt ℝ (fun y => f (fun i => Real.exp (y i))) z)
    (hd : ∀ z∈logRectangle
      (Option.elim' (gridPoint loI hiI ηI j.1.val) (boxLower lo hi η j.2))
      (Option.elim' (gridPoint loI hiI ηI (j.1.val+1)) (boxUpper lo hi η j.2)), ∀ i,
      ‖deriv (fun t => f (Expr.logCurve (fun i => Real.exp (z i)) i t)) 0‖ ≤ D)
    {base : ℝ × (ι → ℝ)} (hbase : base∈mixedLogRectangle
      (gridPoint loI hiI ηI j.1.val) (gridPoint loI hiI ηI (j.1.val+1))
      (boxLower lo hi η j.2) (boxUpper lo hi η j.2))
    (he : ‖mixedAssignedTestSum NI N M loI hiI ηI G φ lo hi η Z j F-
      (mixedPrincipalMass M (gridPoint loI hiI ηI j.1.val)
        (gridPoint loI hiI ηI (j.1.val+1)) G φ (boxLower lo hi η j.2) (boxUpper lo hi η j.2) Z:ℂ)*
        ∑ r : ZMod M, ∑ u : ι → (ZMod M)ˣ,F r u‖ ≤ error*∑ r : ZMod M, ∑ u : ι → (ZMod M)ˣ,‖F r u‖)
    (heAbs : ‖mixedAssignedTestSum NI N M loI hiI ηI G φ lo hi η Z j (fun r u => (‖F r u‖:ℂ))-
      (mixedPrincipalMass M (gridPoint loI hiI ηI j.1.val)
        (gridPoint loI hiI ηI (j.1.val+1)) G φ (boxLower lo hi η j.2) (boxUpper lo hi η j.2) Z:ℂ)*
        ∑ r : ZMod M, ∑ u : ι → (ZMod M)ˣ,(‖F r u‖:ℂ)‖ ≤ error*∑ r : ZMod M, ∑ u : ι → (ZMod M)ˣ,‖F r u‖) :
    ‖mixedSmoothAssignedTestSum NI N M loI hiI ηI G φ lo hi η Z j F f-
      mixedPrincipalIntegral M (gridPoint loI hiI ηI j.1.val)
        (gridPoint loI hiI ηI (j.1.val+1)) G φ (boxLower lo hi η j.2) (boxUpper lo hi η j.2) Z f*
        ∑ r : ZMod M, ∑ u : ι → (ZMod M)ˣ,F r u‖ ≤
      (((Fintype.card ι:ℝ)+1)*D*mesh*
        (2*mixedPrincipalMass M (gridPoint loI hiI ηI j.1.val)
          (gridPoint loI hiI ηI (j.1.val+1)) G φ (boxLower lo hi η j.2) (boxUpper lo hi η j.2) Z+error)+
        ‖f (optionCoordinates (mixedExp base))‖*error)*∑ r : ZMod M, ∑ u : ι → (ZMod M)ˣ,‖F r u‖ := by
  classical
  let v : ℝ := ((Fintype.card ι:ℝ)+1)*D*mesh
  let f₀ := f (optionCoordinates (mixedExp base))
  let S := ∑ r : ZMod M, ∑ u : ι → (ZMod M)ˣ,F r u
  let T := ∑ r : ZMod M, ∑ u : ι → (ZMod M)ˣ,‖F r u‖
  let mass := mixedPrincipalMass M (gridPoint loI hiI ηI j.1.val)
    (gridPoint loI hiI ηI (j.1.val+1)) G φ (boxLower lo hi η j.2) (boxUpper lo hi η j.2) Z
  let integral := mixedPrincipalIntegral M (gridPoint loI hiI ηI j.1.val)
    (gridPoint loI hiI ηI (j.1.val+1)) G φ (boxLower lo hi η j.2) (boxUpper lo hi η j.2) Z f
  let actual := mixedAssignedTestSum NI N M loI hiI ηI G φ lo hi η Z j F
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hmass := mixedAssignedAbsMass_le_of_error NI N loI hiI ηI G φ lo hi η Z j F mass error heAbs
  have hdisc := smooth_mixed_assigned_freezing_bound NI N loI hiI ηI G φ lo hi η Z j
    (fun i => (hZ i).le) hφ0 F f hD hm hwidthI hwidth hf hd
    ((optionCoordinates_mem_logRectangle _ _ _ _).mpr hbase)
  have hdisc' : ‖mixedSmoothAssignedTestSum NI N M loI hiI ηI G φ lo hi η Z j F f-f₀*actual‖ ≤
      v*((mass+error)*T) := by
    simpa only [f₀,optionCoordinates_mixedExp] using
      hdisc.trans (mul_le_mul_of_nonneg_left hmass hv)
  have hap : ‖f₀*actual-f₀*((mass:ℂ)*S)‖ ≤ ‖f₀‖*(error*T) := by
    rw [← mul_sub,norm_mul]
    exact mul_le_mul_of_nonneg_left he (norm_nonneg _)
  have hint := mixed_integral_freezing_of_log_partials M
    (gridPoint loI hiI ηI j.1.val) (gridPoint loI hiI ηI (j.1.val+1)) G φ
    (fun i => ((Nat.totient M:ℝ)*Z i)⁻¹) (boxLower lo hi η j.2) (boxUpper lo hi η j.2)
    hφ hφ0 (fun i => inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (hZ i).le)) hlo
    f hD hm hwidthI hwidth hf hd hbase
  have hint' : ‖(mass:ℂ)*f₀-integral‖ ≤ v*mass := by
    rw [norm_sub_rev]
    simpa only [integral,mass,mixedPrincipalIntegral,mixedPrincipalMass,Complex.real_smul] using hint
  have hS : ‖S‖ ≤ T := (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => norm_sum_le _ _)
  have hmain : ‖f₀*((mass:ℂ)*S)-integral*S‖ ≤ (v*mass)*T := by
    have heq : f₀*((mass:ℂ)*S)-integral*S = ((mass:ℂ)*f₀-integral)*S := by ring
    rw [heq,norm_mul]
    exact mul_le_mul hint' hS (norm_nonneg _) ((norm_nonneg _).trans hint')
  calc
    _ ≤ ‖mixedSmoothAssignedTestSum NI N M loI hiI ηI G φ lo hi η Z j F f-f₀*actual‖+
        ‖f₀*actual-f₀*((mass:ℂ)*S)‖+‖f₀*((mass:ℂ)*S)-integral*S‖ := by
      have h₁ := norm_sub_le_norm_sub_add_norm_sub
        (mixedSmoothAssignedTestSum NI N M loI hiI ηI G φ lo hi η Z j F f) (f₀*actual) (integral*S)
      have h₂ := norm_sub_le_norm_sub_add_norm_sub (f₀*actual) (f₀*((mass:ℂ)*S)) (integral*S)
      simpa only [add_assoc] using h₁.trans (add_le_add le_rfl h₂)
    _ ≤ v*((mass+error)*T)+‖f₀‖*(error*T)+(v*mass)*T := add_le_add (add_le_add hdisc' hap) hmain
    _ = _ := by dsimp only [v,f₀,T,mass]; ring

end Ostmann.Arithmetic.LogCellPartition

end

end OAI
