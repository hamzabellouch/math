import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.SuffixDescendants

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory
open scoped Classical
lemma assembly_small_parameters (n : ℕ) {chi Cd : ℝ} (hchi : 0<chi) (hCd : 0≤Cd) :
    ∃ beta : ℝ, 0<beta ∧ beta< min (chi/10) (1/10) ∧
    ∃ kap : ℝ, 0<kap ∧ kap≤1/1000 ∧
    ∃ sig : ℝ, 0<sig ∧ sig<kap/1000 ∧ beta+(n+4:ℝ)*sig<chi/4 ∧
    ∃ omega : ℝ, 0<omega ∧ 4*(n+1:ℝ)*omega<beta/8 ∧
      -beta+Cd*(kap+sig/kap)+beta/8+4*(n+1:ℝ)*omega ≤ -beta/2 := by
  obtain ⟨beta,hbeta,hbetasm⟩ := exists_between
    (show (0:ℝ)< min (chi/10) (1/10) from lt_min (by positivity) (by norm_num))
  have hCb : 0<Cd+1 := by linarith
  obtain ⟨kap,hkap,hkapub⟩ := exists_between
    (show (0:ℝ)< min (1/1000) (beta/(32*(Cd+1))) from lt_min (by norm_num) (by positivity))
  have hkap1 : kap≤1/1000 := (hkapub.trans_le (min_le_left _ _)).le
  have hkapCd : Cd*kap<beta/32 := by
    have hh := (lt_div_iff₀ (by positivity : 0<32*(Cd+1))).mp
      (hkapub.trans_le (min_le_right _ _))
    nlinarith
  have hdiff : 0<chi/4-beta := by
    have := hbetasm.trans_le (min_le_left _ _)
    linarith
  have hn4 : 0<(n+4:ℝ) := by positivity
  obtain ⟨sig,hsig,hsigub⟩ := exists_between
    (show (0:ℝ)< min (kap/1000) (min (kap*beta/(32*(Cd+1))) ((chi/4-beta)/(n+4:ℝ))) from
      lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hsigkap : sig<kap/1000 := hsigub.trans_le (min_le_left _ _)
  have hsig2 := hsigub.trans_le (min_le_right _ _)
  have hsigCd : Cd*(sig/kap)<beta/32 := by
    have hh := (lt_div_iff₀ (by positivity : 0<32*(Cd+1))).mp
      (hsig2.trans_le (min_le_left _ _))
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hkap).mpr
    nlinarith
  have hsmall : beta+(n+4:ℝ)*sig<chi/4 := by
    have hh := (lt_div_iff₀ hn4).mp (hsig2.trans_le (min_le_right _ _))
    linarith
  obtain ⟨omega,homega,homegaub⟩ := exists_between
    (show (0:ℝ)<beta/(32*(n+1:ℝ)) from by positivity)
  have homegasm : 4*(n+1:ℝ)*omega<beta/8 := by
    have hh := (lt_div_iff₀ (by positivity : 0<32*(n+1:ℝ))).mp homegaub
    linarith
  refine ⟨beta,hbeta,hbetasm,kap,hkap,hkap1,sig,hsig,hsigkap,hsmall,omega,homega,homegasm,?_⟩
  nlinarith
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
