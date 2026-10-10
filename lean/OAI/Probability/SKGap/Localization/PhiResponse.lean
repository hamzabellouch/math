import Mathlib
import OAI.Probability.SKGap.Localization.PhiAlgebra

namespace OAI

section

noncomputable section
namespace SKGap.Stein
open KernelExpr

def phiR (z r a : ℝ) : ℝ := eval (dr (atom 0 0 false)) z r a
def phiRZ (z r a : ℝ) : ℝ := eval (dz (dr (atom 0 0 false))) z r a

lemma phiR_hasDerivAt (z r a : ℝ) : HasDerivAt (fun r=>phi z r a) (phiR z r a) r := by
  simpa only [eval,moment_base,phiR] using hasDerivAt_r (atom 0 0 false) z r a
lemma phiR_hasDerivAt_z (z r a : ℝ) : HasDerivAt (fun z=>phiR z r a) (phiRZ z r a) z :=
  hasDerivAt_z (dr (atom 0 0 false)) z r a
lemma phiZR_commute (z r a : ℝ) :
    eval (dr (dz (atom 0 0 false))) z r a=phiRZ z r a := by
  simp only [phiRZ,dz,dr,eval]
  ring
lemma phiZ_kernel (z r a : ℝ) : phiZ z r a=eval (dz (atom 0 0 false)) z r a := by
  exact (phi_hasDerivAt z r a).unique (by simpa only [eval,moment_base] using hasDerivAt_z (atom 0 0 false) z r a)
lemma phiZ_hasDerivAt_r (z r a : ℝ) : HasDerivAt (fun r=>phiZ z r a) (phiRZ z r a) r := by
  simpa only [phiZ_kernel,phiZR_commute] using hasDerivAt_r (dz (atom 0 0 false)) z r a

theorem phiR_stein (z r a : ℝ) :
    (z-r-a*Real.tanh z)*phiR z r a-a*phiRZ z r a=phi z r a-SKGapCutoff.scalarVariance r := by
  have hc : HasDerivAt (fun r=>z-r-a*Real.tanh z) (-1) r := by
    convert! ((hasDerivAt_const r z).sub (hasDerivAt_id r)).sub_const (a*Real.tanh z) using 1
    simp
  have hleft := (hc.mul (phiR_hasDerivAt z r a)).sub ((phiZ_hasDerivAt_r z r a).const_mul a)
  have hright : HasDerivAt (fun r=>Real.tanh z-Real.tanh r) (-SKGapCutoff.scalarVariance r) r := by
    convert! (hasDerivAt_const r (Real.tanh z)).sub (SKGapCutoff.tanh_hasDerivAt r) using 1
    simp
  have hh : (fun r=>(z-r-a*Real.tanh z)*phi z r a-a*phiZ z r a)=
      (fun r=>Real.tanh z-Real.tanh r) := funext fun r=>phi_stein z r a
  change HasDerivAt (fun r=>(z-r-a*Real.tanh z)*phi z r a-a*phiZ z r a) _ r at hleft
  rw [hh] at hleft
  have he:=hleft.unique hright
  linarith

lemma phiR_bound (z r a : ℝ) : |phiR z r a|≤2*phi z r a := by
  convert! KernelExpr.relative_bound (dr (atom 0 0 false)) z r a using 1
  norm_num [phiR,KernelExpr.mass,dr]

end SKGap.Stein

end
end

end OAI
