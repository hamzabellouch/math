import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReplacementErrorBasic
import OAI.NumberTheory.Ostmann.Construction.SourcePriorGridDeletion

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantPriorExceptionalError
open Construction SourcePriorGridDeletion ScaleBudget PrimeCellMeshBudget PrimeCellActualErrorBudget Filter

def exceptionalEnvelope (G : ℝ) : ℝ := (24+4*Real.exp 1)*G*Real.exp (1-G)

theorem exceptionalEnvelope_nonneg {G : ℝ} (hG : 0≤G) : 0≤exceptionalEnvelope G := by
  unfold exceptionalEnvelope
  positivity

theorem eventually_exceptionalEnvelope_decay :
    ∀ᶠ G : ℝ in atTop, exceptionalEnvelope G ≤ Real.exp (-G/2) := by
  filter_upwards [eventually_poly_exp_le ((24+4*Real.exp 1)*Real.exp 1) 1
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (0:ℝ)<1)] with G hG
  simp only [pow_one,zero_mul,Real.exp_zero,mul_one,one_mul] at hG
  have hh := mul_le_mul_of_nonneg_right hG (Real.exp_nonneg (-G))
  calc
    _ = ((24+4*Real.exp 1)*Real.exp 1*G)*Real.exp (-G) := by
      unfold exceptionalEnvelope
      rw [sub_eq_add_neg,Real.exp_add]
      ring
    _ ≤ Real.exp ((1/2:ℝ)*G)*Real.exp (-G) := hh
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

theorem eventually_growth_exceptionalEnvelope (k : ℕ) (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (G : ℝ) (M a : ℕ),
      0<M → a≤HistoryGiantReplacementError.residueCostExponent k →
      Real.log (M:ℝ)≤Real.exp (giant.μ*L) → Real.exp (giant.a₀*L)≤G-1 →
      (M:ℝ)^a*smoothGrowthFactor k C giant.μ L*exceptionalEnvelope G ≤
        Real.exp (-Real.exp (giant.target*L)) := by
  let D := C+(HistoryGiantReplacementError.residueCostExponent k:ℝ)
  obtain ⟨G0,hG0⟩ := eventually_atTop.mp eventually_exceptionalEnvelope_decay
  have ht := Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop
    (show 0<giant.a₀ by norm_num [giant]))
  filter_upwards [ht.eventually_ge_atTop G0,
    eventually_double_exp_error (2*bulkCostConstant k D) 1
      (by norm_num [giant] : giant.μ<giant.a₀)
      (by norm_num [giant] : giant.target<giant.a₀) (by norm_num : (0:ℝ)<1/2),
    eventually_ge_atTop (1:ℝ)] with L hGmin hbudget hL
  change G0≤Real.exp (giant.a₀*L) at hGmin
  intro G M a hM ha hmod hG
  have hGpos : 0≤G := by linarith [Real.exp_pos (giant.a₀*L)]
  have henv := hG0 G (by linarith)
  have hgrowth := HistoryGiantReplacementError.modulus_growth_le k C ha hM hmod
  have hcost := variation_cost_le k D hL (show 0≤giant.μ by norm_num [giant])
  calc
    _ ≤ smoothGrowthFactor k D giant.μ L*Real.exp (-G/2) :=
      mul_le_mul hgrowth henv (exceptionalEnvelope_nonneg hGpos) (Real.exp_nonneg _)
    _ = Real.exp (D*((Conclusion.bulkSize k L:ℝ)+1)*(Real.exp (giant.μ*L)+1)-G/2) := by
      unfold smoothGrowthFactor
      rw [←Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(1/2:ℝ)*Real.exp (giant.a₀*L)+
        (2*bulkCostConstant k D)*L^1*Real.exp (giant.μ*L)) := by
      apply Real.exp_le_exp.mpr
      simp only [pow_one]
      nlinarith only [hcost,hG]
    _ ≤ _ := hbudget

theorem exceptional_errors_le_envelope (G : ℝ) (E : Finset ℕ)
    (hG : 1≤G) (hE : E.card≤2) (hZ : 0<logCellMass G E)
    (hinv : (logCellMass G E)⁻¹≤2*G) (hsmall : deletionCap G E≤1) :
    deletionCap G E*(1+fullMassRatio G E)≤exceptionalEnvelope G ∧
    3*deletionCap G E≤exceptionalEnvelope G ∧
    (Real.exp 1+1)*deletionCap G E≤exceptionalEnvelope G ∧
    Real.exp (1-G)/logCellMass G E≤exceptionalEnvelope G ∧
    8*Real.exp (-G)≤exceptionalEnvelope G := by
  have hbase : 0≤G*Real.exp (1-G) := mul_nonneg (by linarith) (Real.exp_nonneg _)
  have hpoint : Real.exp (1-G)/logCellMass G E≤2*(G*Real.exp (1-G)) := by
    rw [div_eq_mul_inv]
    nlinarith only [mul_le_mul_of_nonneg_left hinv (Real.exp_nonneg (1-G))]
  have hdel : deletionCap G E≤4*(G*Real.exp (1-G)) := by
    have hh := deletionCap_le_two G E hZ hE
    have he : 2*Real.exp (1-G)/logCellMass G E=2*(Real.exp (1-G)/logCellMass G E) := by ring
    rw [he] at hh
    linarith
  have hd0 := deletionCap_nonneg G E hZ
  have hr : fullMassRatio G E≤2 := (fullMassRatio_le_one_add G E hZ).trans (by linarith)
  have hpair : deletionCap G E*(1+fullMassRatio G E)≤3*deletionCap G E := by
    nlinarith only [mul_le_mul_of_nonneg_left hr hd0]
  have hexp : Real.exp (-G)≤G*Real.exp (1-G) := by
    exact (Real.exp_le_exp.mpr (by linarith : -G≤1-G)).trans
      (le_mul_of_one_le_left (Real.exp_nonneg _) hG)
  unfold exceptionalEnvelope
  have he := Real.exp_pos (1:ℝ)
  have hcost : 0≤Real.exp 1*(G*Real.exp (1-G)) := mul_nonneg he.le hbase
  refine ⟨?_,?_,?_,?_,?_⟩
  · nlinarith only [hpair,hdel,hbase,hcost]
  · nlinarith only [hdel,hbase,hcost]
  · have hh := mul_le_mul_of_nonneg_left hdel (show 0≤Real.exp 1+1 by positivity)
    nlinarith only [hh,hbase]
  · nlinarith only [hpoint,hbase,hcost]
  · nlinarith only [hexp,hbase,hcost]

end Ostmann.Arithmetic.HistoryGiantPriorExceptionalError

end

end OAI
