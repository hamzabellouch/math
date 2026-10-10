import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellSmoothFreezing

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.PrimeCellReplacement
open scoped BigOperators
open PrimeProgression PrimeCellFreezing Characters.RationalHistory
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ} [NeZero M]

def principalMass (M : ℕ) (lo hi Z : ι → ℝ) : ℝ :=
  ∏ i, harmonicIntegral M (lo i) (hi i)/Z i

def principalIntegral (M : ℕ) (lo hi Z : ι → ℝ) (f : (ι → ℝ) → ℂ) : ℂ :=
  logCellIntegral (fun i => ((Nat.totient M:ℝ)*Z i)⁻¹) lo hi f

theorem smooth_replacement_of_errors (N : ι → ℕ) (lo hi Z : ι → ℝ)
    (hZ : ∀ i, 0 < Z i) (hlo : ∀ i, 0 < lo i) (horder : ∀ i, lo i ≤ hi i)
    (F : (ι → (ZMod M)ˣ) → ℂ) (f : (ι → ℝ) → ℂ)
    {D mesh error : ℝ} (hD : 0 ≤ D) (hm : 0 ≤ mesh)
    (hwidth : ∀ i, hi i-lo i ≤ mesh)
    (hf : ∀ z∈logRectangle lo hi,DifferentiableAt ℝ (fun y => f (fun j => Real.exp (y j))) z)
    (hd : ∀ z∈logRectangle lo hi,∀ i,
      ‖deriv (fun t => f (Expr.logCurve (fun j => Real.exp (z j)) i t)) 0‖ ≤ D)
    {base : ι → ℝ} (hbase : base∈logRectangle lo hi)
    (he : ‖jointComplexTestSum N M lo hi Z F-
      (principalMass M lo hi Z:ℂ)*∑ u : ι → (ZMod M)ˣ,F u‖ ≤ error*∑ u : ι → (ZMod M)ˣ,‖F u‖)
    (heAbs : ‖jointComplexTestSum N M lo hi Z (fun u => (‖F u‖:ℂ))-
      (principalMass M lo hi Z:ℂ)*∑ u : ι → (ZMod M)ˣ,(‖F u‖:ℂ)‖ ≤
      error*∑ u : ι → (ZMod M)ˣ,‖F u‖) :
    ‖smoothJointTestSum N M lo hi Z F f-principalIntegral M lo hi Z f*∑ u : ι → (ZMod M)ˣ,F u‖ ≤
      ((Fintype.card ι:ℝ)*D*mesh*(2*principalMass M lo hi Z+error)+
        ‖f (fun j => Real.exp (base j))‖*error)*∑ u : ι → (ZMod M)ˣ,‖F u‖ := by
  classical
  let v : ℝ := (Fintype.card ι:ℝ)*D*mesh
  let f₀ := f (fun j => Real.exp (base j))
  let S := ∑ u : ι → (ZMod M)ˣ,F u
  let T := ∑ u : ι → (ZMod M)ˣ,‖F u‖
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hmass := jointAbsMass_le_of_error N lo hi Z F (principalMass M lo hi Z) error heAbs
  have hdisc := smooth_freezing_bound N lo hi Z (fun i => (hZ i).le) F f hD hm hwidth hf hd hbase
  have hdisc' : ‖smoothJointTestSum N M lo hi Z F f-f₀*jointComplexTestSum N M lo hi Z F‖ ≤
      v*((principalMass M lo hi Z+error)*T) :=
    hdisc.trans (mul_le_mul_of_nonneg_left hmass hv)
  have hap : ‖f₀*jointComplexTestSum N M lo hi Z F-f₀*((principalMass M lo hi Z:ℂ)*S)‖ ≤
      ‖f₀‖*(error*T) := by
    rw [← mul_sub,norm_mul]
    exact mul_le_mul_of_nonneg_left he (norm_nonneg _)
  have hint := residue_integral_freezing_bound M Z lo hi hZ hlo horder f hD hm hwidth hf hd hbase
  have hint' : ‖(principalMass M lo hi Z:ℂ)*f₀-principalIntegral M lo hi Z f‖ ≤
      v*principalMass M lo hi Z := by
    rw [norm_sub_rev]
    simpa only [principalIntegral,principalMass,Complex.real_smul] using hint
  have hmain : ‖f₀*((principalMass M lo hi Z:ℂ)*S)-principalIntegral M lo hi Z f*S‖ ≤
      (v*principalMass M lo hi Z)*T := by
    have heq : f₀*((principalMass M lo hi Z:ℂ)*S)-principalIntegral M lo hi Z f*S =
        ((principalMass M lo hi Z:ℂ)*f₀-principalIntegral M lo hi Z f)*S := by ring
    rw [heq,norm_mul]
    have hnonneg : 0 ≤ v*principalMass M lo hi Z := (norm_nonneg _).trans hint'
    exact mul_le_mul hint' (norm_sum_le _ _) (norm_nonneg _) hnonneg
  calc
    _ ≤ ‖smoothJointTestSum N M lo hi Z F f-f₀*jointComplexTestSum N M lo hi Z F‖+
        ‖f₀*jointComplexTestSum N M lo hi Z F-f₀*((principalMass M lo hi Z:ℂ)*S)‖+
        ‖f₀*((principalMass M lo hi Z:ℂ)*S)-principalIntegral M lo hi Z f*S‖ := by
      have h₁ := norm_sub_le_norm_sub_add_norm_sub
        (smoothJointTestSum N M lo hi Z F f) (f₀*jointComplexTestSum N M lo hi Z F)
        (principalIntegral M lo hi Z f*S)
      have h₂ := norm_sub_le_norm_sub_add_norm_sub (f₀*jointComplexTestSum N M lo hi Z F)
        (f₀*((principalMass M lo hi Z:ℂ)*S)) (principalIntegral M lo hi Z f*S)
      simpa only [add_assoc] using h₁.trans (add_le_add le_rfl h₂)
    _ ≤ v*((principalMass M lo hi Z+error)*T)+‖f₀‖*(error*T)+(v*principalMass M lo hi Z)*T :=
      add_le_add (add_le_add hdisc' hap) hmain
    _ = _ := by dsimp only [v,f₀,T]; ring

end Ostmann.Arithmetic.PrimeCellReplacement

end

end OAI
