import Mathlib
import OAI.Probability.LogConcave.Complexity.Envelope

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open Filter MeasureTheory ProbabilityTheory
open scoped Classical NNReal Topology

theorem exists_primitive_producer {κ P : ℝ} (hκ : 0<κ) (hP : 1≤P) :
    ∃t : ℝ,0<t ∧ t<1/100 ∧ 40*(P+2)*t<1/4 ∧
    ∃K : ℝ,0≤K ∧ ∃e : ℕ → ℝ,LogPowerRate e (κ*P) ∧
      (∀ᶠ d : ℕ in atTop,0<e d) ∧
      ∀ᶠ d : ℕ in atTop,∃S : ℝ → ℝ → ReservedProgram d,∃B : ℕ,
        (B:ℝ)≤(d:ℝ)^(κ*t) ∧
        (∀r : ℝ,SampleBudget B r 1 (S r 1)) ∧
        ∀{F : Point d → ℝ} {lam : ℝ≥0},Primitive F lam → 0<lam → (lam:ℝ)≤1 →
          SampleCorrect F lam ((d:ℝ)^(-κ)) K (e d) ((d:ℝ)^(-(κ*t))) S := by
  let t : ℝ := 1/(1000*(P+2))
  have ht : 0<t := by dsimp [t]; positivity
  have heq : t*(1000*(P+2))=1 := by dsimp [t]; exact one_div_mul_cancel (by positivity)
  have hsmall : 40*(P+2)*t<1/4 := by nlinarith only [heq]
  have hts : t<1/100 := by nlinarith [mul_nonneg ht.le (by linarith : 0≤P)]
  let J := P+1
  have hJ : 1≤J := by dsimp [J]; linarith
  let N := numericalLayerCount J
  obtain ⟨w,hw,hwt,hbudget⟩ := exists_uniform_routine_mesh (K:=P) hκ ht (by linarith) N
  obtain ⟨n,hnw,hnt,hnn,hnum⟩ := exists_source_numerical_ready hκ hJ ht hts hw hwt
  have hR : ∀ᶠ d : ℕ in atTop,(d:ℝ)^(-(κ*t))≤1 := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd) (by nlinarith)
  have hb : ∀ᶠ d : ℕ in atTop,∀C : CircuitParameters,SourceShape κ t w n N d C →
      ∃B : ℕ,(B:ℝ)≤C.D ∧ ∀L : RoutineLabel,L.Admissible t P →
      RoutineBudget B (Real.sqrt (1-C.T^2)/C.T) 1 (constructRoutine d C ht (by linarith) L) := by
    filter_upwards [hbudget n,hR] with d hd hRd
    intro C hC
    obtain ⟨B,hB,hbud⟩ := hd C hC
    exact ⟨B,hB,fun L hL => hbud L hL 1 hRd le_rfl⟩
  have ha := uniform_routine_accuracy hκ ht hts hw hwt (show P≤J by dsimp [J]; linarith)
    (show N=numericalLayerCount J from rfl) hb hnum
    ⟨.sample,1,P⟩ (topLabel_admissible (by linarith) ht.le hsmall)
  have hq : LogPowerRate (fun d : ℕ => (d:ℝ)^(-κ)) (κ*1) := by
    simpa only [mul_one] using LogPowerRate.power κ
  have hqp : ∀ᶠ d : ℕ in atTop,0<(d:ℝ)^(-κ) := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
    exact Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  obtain ⟨K,hK,e,her,hep,he⟩ := ha _ hq hqp
  refine ⟨t,ht,hts,hsmall,K,hK,e,her,hep,?_⟩
  filter_upwards [he,hb,exists_source_shape hκ ht hw n N] with d hd hbd hshape
  obtain ⟨C,hC⟩ := hshape
  obtain ⟨B,hB,hbud⟩ := hbd C hC
  refine ⟨constructRoutine d C ht (by linarith) ⟨.sample,1,P⟩,B,?_,?_,?_⟩
  · simpa only [hC.D_eq] using hB
  · intro r
    exact hbud _ (topLabel_admissible (by linarith) ht.le hsmall) r 1 (Or.inr rfl)
  · intro F lam hF hlam hlam1
    exact hd C hC hF hlam hlam1

end LogConcaveSampling.OracleCompiler

end

end

end OAI
