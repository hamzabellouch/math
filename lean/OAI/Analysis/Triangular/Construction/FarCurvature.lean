import OAI.Analysis.Triangular.Construction.CurvatureEnvelope
import OAI.Analysis.Triangular.Construction.ActualInterpolation
import OAI.Analysis.Triangular.Signs.SineGridAnalytic

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

def transformedP (s : ℝ) : ℝ := (spectralPCLM (waveFunctionJet 0 1 0 s)).re
lemma hasDerivAt_spectralP_wave (br : Fin 2) (k : ℕ) (s : ℂ) :
    HasDerivAt (fun t => spectralPCLM (waveFunctionJet 0 br k t))
      (spectralPCLM (waveFunctionJet 0 br (k+1) s)) s :=
  spectralPCLM.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_waveFunctionJet 0 br k s)
lemma transformedP_contDiff : ContDiff ℝ ⊤ transformedP := by
  exact (show Differentiable ℂ (fun s => spectralPCLM (waveFunctionJet 0 1 0 s)) from
    fun s => (hasDerivAt_spectralP_wave 1 0 s).differentiableAt).contDiff.real_of_complex
lemma transformedP_jet (k : ℕ) :
    (fun s : ℝ => (spectralPCLM (waveFunctionJet 0 1 k s)).re)=iteratedDeriv k transformedP := by
  induction k with
  | zero => rfl
  | succ k hk =>
    rw [iteratedDeriv_succ,←hk]
    exact funext fun s => ((hasDerivAt_spectralP_wave 1 k s).real_of_complex).deriv.symm
lemma realP_contDiff : ContDiff ℝ ⊤ realP := by unfold realP; fun_prop
lemma realP_jet_zero (n : Node) : realP n.val=0 ∧ deriv realP n.val=0 := by
  have he (s : ℝ) : (spectralPCLM (waveFunctionJet 0 0 0 s)).re=realP s := by
    rw [(spectralP_direct _).1,P_ofReal,ofReal_re]
  constructor
  · rw [←he,(spectralP_direct _).1]
    norm_cast
    rw [P_node,zero_re]
  · have hh := ((hasDerivAt_spectralP_wave 0 0 (n.val:ℂ)).real_of_complex).deriv
    simp only [he] at hh
    rw [hh,(spectralP_direct _).2]
    norm_cast
    rw [deriv_P_node,zero_re]
lemma rawConstantCurvature_antitone {u s : ℝ} (hus : u ≤ s) :
    rawConstantCurvature s ≤ rawConstantCurvature u := by
  unfold rawConstantCurvature
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (curvatureWave_antitone 0 1 (abs_le.mpr (frequency_mem j)) hus) (norm_nonneg _)
lemma transformedP_curvature {s : ℝ} (hs : 29/2 ≤ s) :
    |iteratedDeriv 2 transformedP s|/2 ≤ 2/1000 := by
  rw [←transformedP_jet]
  have hh := abs_re_le_norm (spectralPCLM (waveFunctionJet 0 1 2 s))
  have hn := norm_sum_le (s:=Finset.univ) (fun j : Fin 31 => fourierCoeff j*(waveFunctionJet 0 1 2 (s:ℂ)) ⟨frequency j,frequency_mem j⟩)
  have he (j : Fin 31) :
      ‖fourierCoeff j*(waveFunctionJet 0 1 2 (s:ℂ)) ⟨frequency j,frequency_mem j⟩‖=
        curvatureWave 0 1 s (frequency j)*‖fourierCoeff j‖ := by
    rw [norm_mul,waveFunctionJet_apply,norm_finiteWaveJet_two]
    ring
  simp only [he] at hn
  change ‖spectralPCLM (waveFunctionJet 0 1 2 s)‖ ≤ _ at hn
  have hb := (rawConstantCurvature_antitone hs).trans curvatureConstant3_bound.le
  change rawConstantCurvature s ≤ 122/100000 at hb
  dsimp only [rawConstantCurvature] at hb
  nlinarith
lemma inputJJet_constant (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (br : Fin 2) (k : ℕ) (s : ℂ) :
    inputJJet (coefficientInput C a w) br k s=
      (C:ℂ)*spectralPCLM (waveFunctionJet 0 br k s)+inputJJet (coefficientInput 0 a w) br k s := by
  simp only [inputJJet,tailSpectral_coefficient,finiteSpectral_coefficient_apply,
    add_apply,smul_apply,smul_eq_mul,ofReal_zero,zero_mul,zero_add]
  ring

def sideConstant (side : Fin 2) : ℝ := if side.val=0 then -(3/500) else 3/500
def actualJ0 (side : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z ≤ Z) : ℝ → ℝ :=
  pairJ (coefficientInput 0 (actualTrigonometric side z hz hzB) (actualTail side z hz hzB))
    (coefficientInput 0 (actualTrigonometric (otherSide side) z hz hzB) (actualTail (otherSide side) z hz hzB))+
      sideConstant (otherSide side) • transformedP
lemma actualJ0_contDiff (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) :
    ContDiff ℝ ⊤ (actualJ0 side z hz hzB) :=
  by
    change ContDiff ℝ ⊤ (fun s => _+sideConstant (otherSide side)*transformedP s)
    exact (pairJ_contDiff _ _).add (by simpa only [smul_eq_mul] using transformedP_contDiff.const_smul (sideConstant (otherSide side)))
lemma actualJ_decompose (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) :
    actualJ side z hz hzB=sideConstant side • realP+actualJ0 side z hz hzB := by
  funext s
  simp only [actualJ,actualInput,pairJ,pairJJet,actualJ0,Pi.add_apply,
    Pi.smul_apply,smul_eq_mul]
  rw [inputJJet_constant (if side.val=0 then -(3/500) else 3/500) _ _ 0,
    inputJJet_constant (if (otherSide side).val=0 then -(3/500) else 3/500) _ _ 1]
  simp only [add_re]
  rw [(spectralP_direct _).1,P_ofReal]
  simp only [ofReal_re,mul_re,ofReal_im,zero_mul,sub_zero,transformedP,sideConstant]
  ring
lemma actualJ0_curvature (side : Fin 2) {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (i : Fin 5) (hs : curvaturePoint i ≤ s) (hs14 : 29/2 ≤ s) :
    |iteratedDeriv 2 (actualJ0 side z hz hzB) s|/2 ≤
      (301/100)*finiteCurvatureEnvelope i+(3/1000000000)*tailCurvatureEnvelope i+(3/500)*(2/1000) := by
  let f := pairJ (coefficientInput 0 (actualTrigonometric side z hz hzB) (actualTail side z hz hzB))
    (coefficientInput 0 (actualTrigonometric (otherSide side) z hz hzB) (actualTail (otherSide side) z hz hzB))
  have hf : ContDiff ℝ 2 f := (pairJ_contDiff _ _).of_le (by norm_num)
  have hg : ContDiff ℝ 2 (sideConstant (otherSide side) • transformedP) := by
    change ContDiff ℝ 2 (fun s => sideConstant (otherSide side)*transformedP s)
    simpa only [smul_eq_mul] using (transformedP_contDiff.const_smul (sideConstant (otherSide side))).of_le (show (2:WithTop ℕ∞) ≤ ⊤ by exact le_top)
  have hl (side : Fin 2) : ‖actualTrigonometric side z hz hzB‖ ≤ 301/100 := by
    have hh := actualTrigonometric_norm side hz hzB
    linarith
  have ht (side : Fin 2) : ‖actualTail side z hz hzB‖ ≤ (3/1000000000:ℝ) := by
    simpa only [show (10:ℝ)^9=1000000000 by norm_num] using (actualTail_norm side hz hzB).le
  have hh := pairJ_curvature _ _ _ _ i hs (hl side) (hl (otherSide side)) (ht side) (ht (otherSide side))
  have hT := transformedP_curvature hs14
  change |iteratedDeriv 2 (f+sideConstant (otherSide side) • transformedP) s|/2 ≤ _
  rw [iteratedDeriv_add hf.contDiffAt hg.contDiffAt,iteratedDeriv_const_smul ((transformedP_contDiff.of_le (by norm_num)).contDiffAt)]
  simp only [smul_eq_mul]
  have hc : |sideConstant (otherSide side)|=(3/500:ℝ) := by unfold sideConstant; split_ifs <;> norm_num
  have ha := abs_add_le (iteratedDeriv 2 f s) (sideConstant (otherSide side)*iteratedDeriv 2 transformedP s)
  rw [abs_mul,hc] at ha
  change |iteratedDeriv 2 f s|/2 ≤ _ at hh
  nlinarith
end AtomicTriangular.Construction
end

end OAI
