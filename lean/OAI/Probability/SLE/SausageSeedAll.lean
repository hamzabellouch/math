import Mathlib
import OAI.Probability.SLE.LowerPositivity
import OAI.Probability.SLE.SausageScaling

namespace OAI

/-! Sausage Seed All for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
namespace RegularSLEPresentation
variable {Ω : Type} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
lemma source_positive_probability_initial_sausage_all (hκ : 0 < κ) (hκ8 : κ < 8)
    (z₀ : ℂ) (hz : 2 < z₀.im) :
    ∃ (T : ℝ≥0) (p b e₀ : ℝ), 0 < T ∧ 0 < p ∧ 0 < b ∧ 0 < e₀ ∧
      ∀ e : ℝ, 0 < e → e < e₀ →
        ENNReal.ofReal p ≤ (P.comap (Subtype.val : a.samples → Ω))
          {ω | ENNReal.ofReal b ≤ ENNReal.ofReal (e^(-codimension κ))*
            volume (closedBall z₀ 1 ∩ sourceSausageSet (γ ω) 0 T e)} := by
  have hk : 0 < κ := by linarith
  let Q := P.comap (Subtype.val : a.samples → Ω)
  obtain ⟨T,e₀,m₀,M,hT,he₀,hm₀,hM,hMom⟩ := source_retained_seed_all κ hκ hκ8 Ω m P inferInstance γ a z₀ hz
  let C := ((1:ℝ)/2)^(-codimension κ)
  have hC : 0 < C := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨T,(m₀/2)^2/M,(m₀/2)/C,min 1 (2*e₀),hT,by positivity,by positivity,lt_min (by norm_num) (by positivity),?_⟩
  intro e he hecut
  let X := fun ω : a.samples => finiteSpatialGreenMass κ
    (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (e/2) T (closedBall z₀ 1)
  have hXm : Measurable X := (a.sourceFiniteGreenDensity_measurable (e/2) T).lintegral_prod_right'
  have hhalf : e/2 ≤ e₀ := by have := hecut.trans_le (min_le_right _ _); linarith
  have hXX := hMom (e/2) (by positivity) hhalf
  apply (source_second_moment_seed Q X hXm m₀ M hm₀ hM hXX.1 hXX.2).trans
  apply measure_mono
  intro ω hω
  have hbound := a.source_finite_mass_le_sausage hk hκ8 z₀ hz T he
    (hecut.le.trans (min_le_left _ _)) ω
  have heq : (e/2)^(-codimension κ) = C*e^(-codimension κ) := by
    rw [show e/2 = (1/2)*e by ring,Real.mul_rpow (by norm_num) he.le]
  rw [heq,ENNReal.ofReal_mul hC.le,mul_assoc] at hbound
  have hdiv : ENNReal.ofReal (m₀/2) / ENNReal.ofReal C ≤
      ENNReal.ofReal (e^(-codimension κ))*volume (closedBall z₀ 1 ∩ sourceSausageSet (γ ω) 0 T e) := by
    apply (ENNReal.div_le_iff (by simpa using hC) ENNReal.ofReal_ne_top).mpr
    simpa only [mul_comm] using (hω.trans hbound)
  simpa only [mem_ofPred_eq,ENNReal.ofReal_div_of_pos hC] using hdiv
end RegularSLEPresentation
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance SausageUniformSeedAllI5  : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance SausageUniformSeedAllI6  : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩
lemma RegularSLEPresentation.source_uniform_sausage_seed_all
    {Ω : Type} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8) :
    ∃ p : ℝ≥0∞, 0 < p ∧ p ≤ 1 ∧ ∀ δ : ℝ≥0, 0 < δ →
      ∃ (K : Set ℂ) (b e₀ : ℝ), IsCompact K ∧ K ⊆ upperHalfPlane ∧ 0 < b ∧ 0 < e₀ ∧
        ∀ e : ℝ, 0 < e → e < e₀ →
          p ≤ (P.comap (Subtype.val : a.samples → Ω))
            {ω | ENNReal.ofReal b ≤ ENNReal.ofReal (e^(-codimension κ))*
              volume (K ∩ sourceSausageSet (γ ω) 0 δ e)} := by
  have hk : 0 < κ := by linarith
  let z₀ : ℂ := 3*I
  have hz₀ : 2 < z₀.im := by norm_num [z₀]
  obtain ⟨T,p,b,e₀,hT,hp,hb,he₀,hseed⟩ := a.source_positive_probability_initial_sausage_all hκ hκ8 z₀ hz₀
  let Q := P.comap (Subtype.val : a.samples → Ω)
  have hp1 : ENNReal.ofReal p ≤ 1 := (hseed (e₀/2) (by positivity) (by linarith)).trans prob_le_one
  refine ⟨ENNReal.ofReal p,ENNReal.ofReal_pos.mpr hp,hp1,?_⟩
  intro δ hδ
  let c := NNReal.sqrt (δ/T)
  have hc : 0 < c := by dsimp [c]; exact NNReal.sqrt_pos.mpr (div_pos hδ hT)
  have hc2 : c^2 = δ/T := NNReal.sq_sqrt _
  have hcR : 0 < (c:ℝ) := hc
  have ht : sourceScaleTime c δ = T := by
    unfold sourceScaleTime
    rw [hc2]
    field_simp
  let K := (fun z : ℂ => (c:ℂ)*z) '' closedBall z₀ 1
  have hK : IsCompact K := (isCompact_closedBall z₀ 1).image (continuous_const.mul continuous_id)
  have hKH : K ⊆ upperHalfPlane := by
    rintro _ ⟨z,hz,rfl⟩
    have hz' : 0 < z.im := zero_lt_one.trans (source_unit_ball_height hz₀ hz)
    change 0 < ((c:ℂ)*z).im
    simpa only [mul_im,ofReal_re,ofReal_im,zero_mul,add_zero] using mul_pos hcR hz'
  let C := ((c:ℝ)⁻¹)^(-codimension κ)*((c:ℝ)⁻¹)^2
  have hC : 0 < C := mul_pos (Real.rpow_pos_of_pos (inv_pos.mpr hcR) _) (sq_pos_of_pos (inv_pos.mpr hcR))
  refine ⟨K,b/C,(c:ℝ)*e₀,hK,hKH,div_pos hb hC,mul_pos hcR he₀,?_⟩
  intro e he hecut
  let gp := sourceTracePath (fun ω : a.samples => γ ω) a.trace_continuous
  let sp := sourceTracePath (fun ω : a.samples => sourceScaleTrace c (γ ω)) (a.sourceScaled c hc).trace_continuous
  let A : Set C(ℝ≥0,ℂ) := {g | ENNReal.ofReal (b/C) ≤ ENNReal.ofReal (e^(-codimension κ))*volume (K ∩ sourceSausageSet g 0 δ e)}
  have hA : MeasurableSet A := measurableSet_le measurable_const
    (measurable_const.mul (source_sausage_local_volume_measurable 0 δ e K))
  have hmap := congrArg (fun μ : Measure C(ℝ≥0,ℂ) => μ A) (a.source_scale_trace_law hk hκ8 c hc)
  have hgm : Measurable gp := a.source_trace_path_measurable
  have hsm : Measurable sp := (a.sourceScaled c hc).source_trace_path_measurable
  rw [Measure.map_apply hgm hA,Measure.map_apply hsm hA] at hmap
  change ENNReal.ofReal p ≤ Q (gp ⁻¹' A)
  rw [hmap]
  have hmesh : e/(c:ℝ) < e₀ := (div_lt_iff₀ hcR).mpr (by simpa only [mul_comm] using hecut)
  apply (hseed (e/(c:ℝ)) (div_pos he hcR) hmesh).trans
  apply measure_mono
  intro ω hω
  have hh := hω.trans (source_sausage_scale_mass_bound κ hc (γ ω) T δ ht (closedBall z₀ 1) e he)
  change ENNReal.ofReal (b/C) ≤ _
  rw [ENNReal.ofReal_div_of_pos hC]
  apply (ENNReal.div_le_iff (by simpa using hC) ENNReal.ofReal_ne_top).mpr
  simpa only [C,K,sp,sourceTracePath,ContinuousMap.coe_mk,mul_comm] using hh
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance SausageConditionalAllI6  : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance SausageConditionalAllI7  : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩
local instance SausageConditionalAllI8  : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance SausageConditionalAllI9  : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩
lemma RegularSLEPresentation.source_uniform_sausage_slot_bound_all
    {Ω : Type} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8) :
    ∃ p : ℝ≥0∞, 0 < p ∧ p ≤ 1 ∧ ∀ (s δ : ℝ≥0), 0 < δ →
      ∀ ε : ℝ, 0 < ε → ∃ b e₀ : ℝ, 0 < b ∧ 0 < e₀ ∧
        ∀ e : ℝ, 0 < e → e < e₀ →
        ∀ A : Set a.samples, MeasurableSet[a.filtration s] A →
          (P.comap (Subtype.val : a.samples → Ω))
            (A ∩ {ω | sourceSausageMass κ (γ ω) s (s+δ) e < ENNReal.ofReal b}) ≤
          (1-p)*(P.comap (Subtype.val : a.samples → Ω)) A + ENNReal.ofReal ε := by
  have hk : 0 < κ := by linarith
  let Q := P.comap (Subtype.val : a.samples → Ω)
  obtain ⟨p,hp,hp1,hseed⟩ := a.source_uniform_sausage_seed_all hκ hκ8
  refine ⟨p,hp,hp1,?_⟩
  intro s δ hδ ε hε
  obtain ⟨K,b,e₀,hK,hKH,hb,he₀,hKP⟩ := hseed δ hδ
  obtain ⟨Φ,hΦm,hΦe,hrestart⟩ := sourceStoppedTraceLaw κ hk hκ8 a.B a.brownian
    a.measurable_B a.continuous_B (fun ω : a.samples => γ ω) a.G a.F a.witness
  let τ : a.samples → ℝ≥0 := fun _ => s
  have hτ : IsStoppingTime a.filtration (fun ω => (τ ω : WithTop ℝ≥0)) := isStoppingTime_const a.filtration s
  obtain ⟨hlaw,hident⟩ := hrestart τ hτ
  let rp := sourceRestartDriverPath a.B a.continuous_B τ
  let gp := sourceTracePath (fun ω : a.samples => γ ω) a.trace_continuous
  let η := fun ω : a.samples => Φ (rp ω)
  have hrm : Measurable rp := by
    apply source_path_measurable
    intro t
    exact (a.measurable_B (s+t)).sub (a.measurable_B s)
  have hem : Measurable η := hΦm.comp hrm
  have hgm : Measurable gp := a.source_trace_path_measurable
  have hfull : ∀ᵐ ω ∂Q, ∃ N : ℕ, sourceSausageChartGood (η ω) (gp ω) K s δ N := by
    filter_upwards [hident] with ω hω
    obtain ⟨N,hN,hbound⟩ := source_restart_sausage_countable_bound
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (a.F ω) (a.witness ω) s δ (η ω) hω hK hKH
    exact ⟨N,hN,fun q hq hqN => hbound q hq hqN⟩
  obtain ⟨N,hN,hbad⟩ := source_chart_good_high_probability Q η gp hem hgm K s δ hfull ε hε
  have hNp : 0 < (N:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  let C := ((2*(N:ℝ))⁻¹)^(-codimension κ)*(N:ℝ)^2
  have hC : 0 < C := mul_pos (Real.rpow_pos_of_pos (by positivity) _) (sq_pos_of_pos hNp)
  refine ⟨b/C,min (1/(N:ℝ)) (2*(N:ℝ)*e₀),div_pos hb hC,lt_min (by positivity) (by positivity),?_⟩
  intro e he hecut A hA
  have hmesh : e/(2*(N:ℝ)) < e₀ := (div_lt_iff₀ (by positivity)).mpr
    (by simpa only [mul_comm] using hecut.trans_le (min_le_right _ _))
  let D : Set C(ℝ≥0,ℂ) := {g | ENNReal.ofReal b ≤ ENNReal.ofReal ((e/(2*(N:ℝ)))^(-codimension κ))*
      volume (K ∩ sourceSausageSet g 0 δ (e/(2*(N:ℝ))))}
  let E : Set a.samples := η ⁻¹' D
  let B : Set a.samples := {ω | ¬sourceSausageChartGood (η ω) (gp ω) K s δ N}
  have hD : MeasurableSet D := measurableSet_le measurable_const
    (measurable_const.mul (source_sausage_local_volume_measurable 0 δ (e/(2*(N:ℝ))) K))
  have hEm : MeasurableSet E := hD.preimage hem
  have hAm : MeasurableSet A := (a.filtration.le s) A hA
  have hAstop : MeasurableSet[hτ.measurableSpace] A := by
    change MeasurableSet[(isStoppingTime_const a.filtration s).measurableSpace] A
    rw [IsStoppingTime.measurableSpace_const]
    exact hA
  have hprob : p*Q A ≤ Q (A ∩ E) := by
    have hEq := congrArg (fun μ : Measure C(ℝ≥0,ℂ) => μ D) (hlaw A hAstop)
    rw [Measure.map_apply hem hD,Measure.smul_apply,Measure.map_apply hgm hD,
      Measure.restrict_apply (hD.preimage hem)] at hEq
    change Q (E ∩ A) = Q A*Q {ω | ENNReal.ofReal b ≤ ENNReal.ofReal ((e/(2*(N:ℝ)))^(-codimension κ))*
      volume (K ∩ sourceSausageSet (γ ω) 0 δ (e/(2*(N:ℝ))))} at hEq
    rw [inter_comm] at hEq
    rw [hEq,mul_comm p (Q A)]
    exact mul_le_mul' le_rfl (hKP (e/(2*(N:ℝ))) (by positivity) hmesh)
  have hins : A ∩ {ω | sourceSausageMass κ (γ ω) s (s+δ) e < ENNReal.ofReal (b/C)} ⊆ (A \ E) ∪ B := by
    intro ω hω
    by_cases hG : sourceSausageChartGood (η ω) (gp ω) K s δ N
    · left
      refine ⟨hω.1,?_⟩
      intro hE
      have hEE : ENNReal.ofReal b ≤ ENNReal.ofReal ((e/(2*(N:ℝ)))^(-codimension κ))*
          volume (K ∩ sourceSausageSet (η ω) 0 δ (e/(2*(N:ℝ)))) := hE
      have hmass := hEE.trans (source_chart_good_mass_bound κ (η ω) (gp ω) K s δ N hG he
        (hecut.trans_le (min_le_left _ _)))
      have hlow : ENNReal.ofReal (b/C) ≤ sourceSausageMass κ (γ ω) s (s+δ) e := by
        rw [ENNReal.ofReal_div_of_pos hC]
        apply (ENNReal.div_le_iff (by simpa using hC) ENNReal.ofReal_ne_top).mpr
        simpa only [C,gp,sourceTracePath,ContinuousMap.coe_mk,mul_comm] using hmass
      exact (not_lt_of_ge hlow) hω.2
    · exact Or.inr hG
  have hdiff : Q (A \ E) = Q A - Q (A ∩ E) := by
    have heq : A \ E = A \ (A ∩ E) := by ext ω; simp only [Set.mem_sdiff,mem_inter_iff]; tauto
    rw [heq]
    exact measure_sdiff inter_subset_left (hAm.inter hEm).nullMeasurableSet (measure_ne_top Q _)
  calc
    Q (A ∩ {ω | sourceSausageMass κ (γ ω) s (s+δ) e < ENNReal.ofReal (b/C)})
        ≤ Q ((A \ E) ∪ B) := measure_mono hins
    _ ≤ Q (A \ E) + Q B := measure_union_le _ _
    _ ≤ (Q A-p*Q A)+ENNReal.ofReal ε := by rw [hdiff]; exact add_le_add (tsub_le_tsub_left hprob _) hbad.le
    _ = (1-p)*Q A+ENNReal.ofReal ε := by
      rw [ENNReal.sub_mul (fun _ _ => measure_ne_top Q A),one_mul]
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

lemma RegularSLEPresentation.source_sausage_nslot_bound_all
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8) :
    ∃ c : ℝ≥0∞, c < 1 ∧ ∀ (s δ : ℝ≥0), 0 < δ → ∀ ν : ℝ, 0 < ν →
      ∀ n : ℕ, ∃ b e₀ : ℝ, 0 < b ∧ 0 < e₀ ∧ ∀ e : ℝ, 0 < e → e < e₀ →
        (P.comap (Subtype.val : a.samples → Ω))
          {ω | sourceSausageMass κ (γ ω) s (s+(n:ℝ≥0)*δ) e < ENNReal.ofReal b} ≤
        c^n + (n:ℝ≥0∞)*ENNReal.ofReal ν := by
  let Q := P.comap (Subtype.val : a.samples → Ω)
  obtain ⟨p,hp,hp1,hslot⟩ := a.source_uniform_sausage_slot_bound_all hκ hκ8
  let c : ℝ≥0∞ := 1-p
  have hc : c < 1 := ENNReal.sub_lt_self (by simp) (by simp) hp.ne'
  refine ⟨c,hc,?_⟩
  intro s δ hδ ν hν n
  induction n with
  | zero =>
    refine ⟨1,1,by norm_num,by norm_num,?_⟩
    intro e he hel
    simpa only [pow_zero,Nat.cast_zero,zero_mul,add_zero] using
      (prob_le_one (μ := Q) (s := {ω | sourceSausageMass κ (γ ω) s (s+(0:ℝ≥0)*δ) e < ENNReal.ofReal 1}))
  | succ n ih =>
    obtain ⟨b₀,e₀,hb₀,he₀,hprev⟩ := ih
    obtain ⟨b₁,e₁,hb₁,he₁,hstep⟩ := hslot (s+(n:ℝ≥0)*δ) δ hδ ν hν
    refine ⟨min b₀ b₁,min e₀ e₁,lt_min hb₀ hb₁,lt_min he₀ he₁,?_⟩
    intro e he hel
    have hend : s+((n+1:ℕ):ℝ≥0)*δ = (s+(n:ℝ≥0)*δ)+δ := by push_cast; ring
    let A : Set a.samples := {ω | sourceSausageMass κ (γ ω) s (s+(n:ℝ≥0)*δ) e < ENNReal.ofReal b₀}
    have hA : MeasurableSet[a.filtration (s+(n:ℝ≥0)*δ)] A :=
      measurableSet_lt (a.source_sausage_mass_measurable_at s _ e) measurable_const
    rw [hend]
    calc
      Q {ω | sourceSausageMass κ (γ ω) s (s+(n:ℝ≥0)*δ+δ) e < ENNReal.ofReal (min b₀ b₁)}
          ≤ Q (A ∩ {ω | sourceSausageMass κ (γ ω) (s+(n:ℝ≥0)*δ) (s+(n:ℝ≥0)*δ+δ) e < ENNReal.ofReal b₁}) := by
          apply measure_mono
          intro ω hω
          constructor
          · exact ((source_sausage_mass_mono_interval κ (γ ω) e
              (Icc_subset_Icc le_rfl (le_add_of_nonneg_right (show 0 ≤ δ from bot_le)))).trans_lt hω).trans_le
                (ENNReal.ofReal_le_ofReal (min_le_left _ _))
          · exact ((source_sausage_mass_mono_interval κ (γ ω) e
              (Icc_subset_Icc (le_add_of_nonneg_right (by positivity)) le_rfl)).trans_lt hω).trans_le
                (ENNReal.ofReal_le_ofReal (min_le_right _ _))
      _ ≤ c*Q A+ENNReal.ofReal ν := hstep e he (hel.trans_le (min_le_right _ _)) A hA
      _ ≤ c*(c^n+(n:ℝ≥0∞)*ENNReal.ofReal ν)+ENNReal.ofReal ν := by
          exact add_le_add (mul_le_mul' le_rfl (hprev e he (hel.trans_le (min_le_left _ _)))) le_rfl
      _ ≤ c^(n+1)+((n+1:ℕ):ℝ≥0∞)*ENNReal.ofReal ν := by
          rw [mul_add,pow_succ,mul_comm (c^n) c,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
          rw [←add_assoc]
          exact add_le_add (add_le_add le_rfl (mul_le_of_le_one_left' hc.le)) le_rfl
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
def SourceSmallSausageAllTarget : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 8 →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : MeasureTheory.Measure Ω),
    MeasureTheory.IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ), IsOrdinaryChordalSLE κ γ P →
  ∀ s t : ℝ≥0, s < t → ∀ ε : ℝ, 0 < ε →
    ∃ a e₀ : ℝ, 0 < a ∧ 0 < e₀ ∧ ∀ e : ℝ, 0 < e → e < e₀ →
      P {ω | sourceSausageMass κ (γ ω) s t e < ENNReal.ofReal a} < ENNReal.ofReal ε

lemma RegularSLEPresentation.source_small_sausage_all
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8) (s t : ℝ≥0) (hst : s < t) (ε : ℝ) (hε : 0 < ε) :
    ∃ b e₀ : ℝ, 0 < b ∧ 0 < e₀ ∧ ∀ e : ℝ, 0 < e → e < e₀ →
      (P.comap (Subtype.val : a.samples → Ω))
        {ω | sourceSausageMass κ (γ ω) s t e < ENNReal.ofReal b} < ENNReal.ofReal ε := by
  obtain ⟨c,hc,hsteps⟩ := a.source_sausage_nslot_bound_all hκ hκ8
  have hev : ∀ᶠ n : ℕ in atTop, c^n < ENNReal.ofReal (ε/4) :=
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hc).eventually
      (gt_mem_nhds (ENNReal.ofReal_pos.mpr (by positivity)))
  obtain ⟨n,hn,hcn⟩ := ((eventually_ge_atTop 1).and hev).exists
  have hn0 : 0 < (n:ℝ≥0) := by exact_mod_cast (show 0 < n by omega)
  let δ : ℝ≥0 := (t-s)/(n:ℝ≥0)
  have hδ : 0 < δ := div_pos (tsub_pos_iff_lt.mpr hst) hn0
  have hend : s+(n:ℝ≥0)*δ = t := by
    dsimp [δ]
    rw [mul_div_cancel₀ _ hn0.ne',add_tsub_cancel_of_le hst.le]
  let ν : ℝ := ε/(4*((n:ℝ)+1))
  have hν : 0 < ν := by dsimp [ν]; positivity
  obtain ⟨b,e₀,hb,he₀,hbound⟩ := hsteps s δ hδ ν hν n
  have hnν : (n:ℝ≥0∞)*ENNReal.ofReal ν ≤ ENNReal.ofReal (ε/4) := by
    rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (Nat.cast_nonneg n)]
    apply ENNReal.ofReal_le_ofReal
    calc (n:ℝ)*ν ≤ ((n:ℝ)+1)*ν := mul_le_mul_of_nonneg_right (by linarith) hν.le
      _ = ε/4 := by dsimp [ν]; field_simp
  refine ⟨b,e₀,hb,he₀,?_⟩
  intro e he hel
  have hh := hbound e he hel
  rw [hend] at hh
  apply hh.trans_lt
  calc c^n+(n:ℝ≥0∞)*ENNReal.ofReal ν
      ≤ ENNReal.ofReal (ε/4)+ENNReal.ofReal (ε/4) := add_le_add hcn.le hnν
    _ = ENNReal.ofReal (ε/2) := by rw [←ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
    _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)
theorem sourceSmallSausageAll_proved : SourceSmallSausageAllTarget := by
  intro κ hκ hκ8 Ω m P hP γ hSLE s t hst ε hε
  let : IsProbabilityMeasure P := hP
  obtain ⟨a⟩ := exists_regular_sle_presentation hSLE
  obtain ⟨b,e₀,hb,he₀,hbound⟩ := a.source_small_sausage_all hκ hκ8 s t hst ε hε
  refine ⟨b,e₀,hb,he₀,?_⟩
  intro e he hel
  have hh := hbound e he hel
  rw [←a.measurePreserving_val.map_eq]
  rwa [(MeasurableEmbedding.subtype_coe a.measurable_samples).map_apply] 
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance sausageSeedAllUniverseDriverMeasurableSpace : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance sausageSeedAllUniverseTraceMeasurableSpace : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance sausageSeedAllUniverseDriverBorelSpace : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance sausageSeedAllUniverseTraceBorelSpace : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
lemma source_sausage_universe_single {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    {γ : Ω → ℝ≥0 → ℂ} (hSLE : IsOrdinaryChordalSLE κ γ P)
    (s t : ℝ≥0) (hst : s < t) (ε : ℝ) (hε : 0 < ε) :
    ∃ b e₀ : ℝ, 0 < b ∧ 0 < e₀ ∧ ∀ e : ℝ, 0 < e → e < e₀ →
      P {ω | sourceSausageMass κ (γ ω) s t e < ENNReal.ofReal b} < ENNReal.ofReal ε := by
  obtain ⟨a⟩ := exists_regular_sle_presentation hSLE
  let μ := P.comap (Subtype.val : a.samples → Ω)
  let : IsProbabilityMeasure μ := a.probability
  let bp := sourceDriverPath a.B a.continuous_B
  let gp := sourceTracePath (γ ∘ Subtype.val) a.trace_continuous
  have hbm : Measurable bp := source_path_measurable bp a.measurable_B
  have hgm : Measurable gp := source_path_measurable gp (fun t => (hSLE.1 t).comp measurable_subtype_coe)
  let pair : a.samples → C(ℝ≥0,ℝ) × C(ℝ≥0,ℂ) := fun ω => (bp ω, gp ω)
  have hpair : Measurable pair := hbm.prodMk hgm
  let X := range pair
  let f : a.samples → X := fun ω => ⟨pair ω, mem_range_self ω⟩
  have hfm : Measurable f := hpair.subtype_mk
  let Q := μ.map f
  let : IsProbabilityMeasure Q := inferInstance
  let B : ℝ≥0 → X → ℝ := fun t x => x.val.1 t
  let η : X → ℝ≥0 → ℂ := fun x t => x.val.2 t
  have hBm (t : ℝ≥0) : Measurable (B t) :=
    (continuous_eval_const t).measurable.comp (measurable_fst.comp measurable_subtype_coe)
  have hηm (t : ℝ≥0) : Measurable (fun x => η x t) :=
    (continuous_eval_const t).measurable.comp (measurable_snd.comp measurable_subtype_coe)
  have hBrownian : IsBrownianReal B Q := by
    constructor
    · constructor
      intro I
      have hmI : Measurable (fun x : X => I.restrict (B · x)) :=
        Measurable.of_eval (fun index => hBm index)
      refine ⟨hmI.aemeasurable, ?_⟩
      rw [show Q = μ.map f from rfl, Measure.map_map hmI hfm]
      exact (a.brownian.hasLaw I).map_eq
    · exact Eventually.of_forall (fun x => x.val.1.continuous)
  have hη : IsOrdinaryChordalSLE κ η Q := by
    refine ⟨hηm, B, hBrownian, Eventually.of_forall ?_⟩
    intro x
    obtain ⟨ω, hω⟩ := x.property
    refine ⟨a.G ω, a.F ω, ?_⟩
    have hp : pair ω = x.val := hω
    have heB : ∀ t, B t x = a.B t ω := fun t => congrArg (fun z => z.1 t) hp.symm
    have heη : η x = γ ω := by
      exact congrArg (fun z => (z.2 : ℝ≥0 → ℂ)) hp.symm
    simpa only [heB,heη] using a.witness ω
  obtain ⟨b,e₀,hb,he₀,hbound⟩ :=
    sourceSmallSausageAll_proved κ hκ hκ8 X inferInstance Q inferInstance η hη s t hst ε hε
  refine ⟨b,e₀,hb,he₀,?_⟩
  intro e he hel
  have hset : MeasurableSet {x : X | sourceSausageMass κ (η x) s t e < ENNReal.ofReal b} := by
    exact measurableSet_lt ((source_sausage_mass_measurable κ s t e).comp
      (measurable_snd.comp measurable_subtype_coe)) measurable_const
  have hh := hbound e he hel
  change (μ.map f) _ < _ at hh
  rw [Measure.map_apply hfm hset] at hh
  rw [←a.measurePreserving_val.map_eq,
    (MeasurableEmbedding.subtype_coe a.measurable_samples).map_apply]
  exact hh
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
universe v_sausage
 

def SourceSmallSausageMainTarget : Prop :=
  ∀ (Ω : Type v_sausage) (_ : MeasurableSpace Ω) (P : MeasureTheory.Measure Ω),
    MeasureTheory.IsProbabilityMeasure P →
  ∀ κ : ℝ, 0 < κ → κ < 8 →
  ∀ (γ : Ω → ℝ≥0 → ℂ), IsOrdinaryChordalSLE κ γ P →
  ∀ I : Finset (ℝ≥0 × ℝ≥0), (∀ J ∈ I, J.1 < J.2) →
  ∀ ε : ℝ, 0 < ε → ∃ a e₀ : ℝ, 0 < a ∧ 0 < e₀ ∧
    ∀ e : ℝ, 0 < e → e < e₀ →
      P {ω | ∃ J ∈ I, sourceSausageMass κ (γ ω) J.1 J.2 e < ENNReal.ofReal a} < ENNReal.ofReal ε
end SLEExactGauge
namespace SLEExactGauge
theorem sourceSmallSausageMain_proved : SourceSmallSausageMainTarget := by
  classical
  intro Ω m P hP κ hκ hκ8 γ hSLE I hI
  let : IsProbabilityMeasure P := hP
  revert hI
  induction I using Finset.induction_on with
  | empty =>
      intro _ ε hε
      refine ⟨1,1,by norm_num,by norm_num,?_⟩
      intro e he hel
      simpa using ENNReal.ofReal_pos.mpr hε
  | @insert J I hJI ih =>
      intro hI ε hε
      have hε2 : 0 < ε/2 := by positivity
      obtain ⟨a₁,e₁,ha₁,he₁,hb₁⟩ := source_sausage_universe_single hκ hκ8 hSLE
        J.1 J.2 (hI J (Finset.mem_insert_self _ _)) (ε/2) hε2
      obtain ⟨a₂,e₂,ha₂,he₂,hb₂⟩ := ih
        (fun K hK => hI K (Finset.mem_insert_of_mem hK)) (ε/2) hε2
      refine ⟨min a₁ a₂,min e₁ e₂,lt_min ha₁ ha₂,lt_min he₁ he₂,?_⟩
      intro e he hel
      have hsub : {ω | ∃ K ∈ insert J I,
          sourceSausageMass κ (γ ω) K.1 K.2 e < ENNReal.ofReal (min a₁ a₂)} ⊆
          {ω | sourceSausageMass κ (γ ω) J.1 J.2 e < ENNReal.ofReal a₁} ∪
          {ω | ∃ K ∈ I, sourceSausageMass κ (γ ω) K.1 K.2 e < ENNReal.ofReal a₂} := by
        rintro ω ⟨K,hK,hm⟩
        rcases Finset.mem_insert.mp hK with rfl | hK
        · exact Or.inl (hm.trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
        · exact Or.inr ⟨K,hK,hm.trans_le (ENNReal.ofReal_le_ofReal (min_le_right _ _))⟩
      calc
        P {ω | ∃ K ∈ insert J I,
            sourceSausageMass κ (γ ω) K.1 K.2 e < ENNReal.ofReal (min a₁ a₂)} ≤
            P ({ω | sourceSausageMass κ (γ ω) J.1 J.2 e < ENNReal.ofReal a₁} ∪
              {ω | ∃ K ∈ I, sourceSausageMass κ (γ ω) K.1 K.2 e < ENNReal.ofReal a₂}) := measure_mono hsub
        _ ≤ P {ω | sourceSausageMass κ (γ ω) J.1 J.2 e < ENNReal.ofReal a₁} +
            P {ω | ∃ K ∈ I, sourceSausageMass κ (γ ω) K.1 K.2 e < ENNReal.ofReal a₂} := measure_union_le _ _
        _ < ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/2) := ENNReal.add_lt_add
          (hb₁ e he (hel.trans_le (min_le_left _ _)))
          (hb₂ e he (hel.trans_le (min_le_right _ _)))
        _ = ENNReal.ofReal ε := by
          rw [←ENNReal.ofReal_add hε2.le hε2.le]
          congr 1
          ring
end SLEExactGauge
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge
 
def wholeTrace (γ : ℝ≥0 → ℂ) : Set ℂ := range γ

 
def integerRectangle (m : ℕ) : Set ℂ :=
  {z | -(m : ℝ) ≤ z.re ∧ z.re ≤ m ∧ 0 ≤ z.im ∧ z.im ≤ m}

 

def MainEvent {Ω : Type*} (h : ℝ → ℝ) (γ : Ω → ℝ≥0 → ℂ) : Set Ω :=
  {ω | (∀ s t : ℝ≥0, 0 < s → s < t →
      0 < hausdorffGauge h (segment (γ ω) s t) ∧
      hausdorffGauge h (segment (γ ω) s t) < ∞) ∧
    (∀ m : ℕ, 0 < m →
      hausdorffGauge h (wholeTrace (γ ω) ∩ integerRectangle m) < ∞)}

 
def MainConclusion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : ℝ → ℝ) (γ : Ω → ℝ≥0 → ℂ) : Prop :=
  (∀ᵐ ω ∂P, ω ∈ MainEvent h γ) ∧
  (∀ R : ℝ, 0 < R →
    AEMeasurable (fun ω => hausdorffGauge h
      (wholeTrace (γ ω) ∩ Metric.closedBall 0 R)) P ∧
    ∃ C : ℝ≥0, (∫⁻ ω, hausdorffGauge h
      (wholeTrace (γ ω) ∩ Metric.closedBall 0 R) ∂P) ≤ C)

end SLEExactGauge
end
 
section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance sausageSeedAllOpenCoverTraceMeasurableSpace : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance sausageSeedAllOpenCoverTraceBorelSpace : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
lemma source_compact_finite_open_cover_lt (h : ℝ → ℝ) (hh : IsGauge h)
    (K : Set ℂ) (hK : IsCompact K) (r : ℝ) (hr : 0 < r)
    (ε : ℝ≥0∞) (hε : hausdorffGauge h K < ε) :
    sourceFiniteOpenCover h (ENNReal.ofReal r) ε K := by
  obtain ⟨b,hb,hbε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  obtain ⟨δ,hδ,hbδ⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hbε
  have hsmall :
      (⨅ (U : ℕ → Set ℂ) (_ : K ⊆ ⋃ n, U n)
        (_ : ∀ n, ediam (U n) ≤ ENNReal.ofReal (r/2)),
          ∑' n, extendedGauge h (ediam (U n))) < (b : ℝ≥0∞) := by
    apply lt_of_le_of_lt (b := hausdorffGauge h K) _ hb
    rw [source_gauge_cover_formula h hh]
    exact le_iSup_of_le (ENNReal.ofReal (r/2))
      (le_iSup_of_le (ENNReal.ofReal_pos.mpr (by positivity)) le_rfl)
  obtain ⟨U,hU,hdiam,hcost⟩ := (by simpa only [iInf_lt_iff] using hsmall)
  obtain ⟨e,he,hes⟩ := ENNReal.exists_pos_sum_of_countable
    (ENNReal.coe_pos.mpr hδ).ne' ℕ
  have hfin (n : ℕ) : ediam (U n) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hdiam n)
  have hrd (n : ℕ) : (ediam (U n)).toReal < r := by
    have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hdiam n)
    rw [ENNReal.toReal_ofReal (by positivity)] at hb
    linarith
  choose V hopen hUV hVdiam hVcost using fun n =>
    source_gauge_open_enlargement h hh (U n) r (hrd n) (hfin n) (e n) (he n)
  obtain ⟨I,hI⟩ := hK.elim_finite_subcover V hopen (hU.trans (iUnion_mono hUV))
  refine ⟨V,I,fun n _ => hopen n,fun n _ => (hVdiam n).le,hI,?_⟩
  calc
    (∑ n ∈ I, extendedGauge h (ediam (V n))) ≤ ∑' n, extendedGauge h (ediam (V n)) :=
      ENNReal.sum_le_tsum I
    _ ≤ ∑' n, (extendedGauge h (ediam (U n)) + e n) := ENNReal.tsum_le_tsum hVcost
    _ = (∑' n, extendedGauge h (ediam (U n))) + ∑' n, (e n : ℝ≥0∞) := ENNReal.tsum_add
    _ < (b : ℝ≥0∞) + δ := ENNReal.add_lt_add hcost hes
    _ < ε := hbδ

def sourceOpenGaugeContent (h : ℝ → ℝ) (r : ℝ≥0∞) (K : Set ℂ) : ℝ≥0∞ :=
  ⨅ ε : ℝ≥0∞, ⨅ (_ : sourceFiniteOpenCover h r ε K), ε
lemma source_open_content_measurable (h : ℝ → ℝ) (C : Set ℂ) (hC : IsClosed C)
    (s t : ℝ≥0) (r : ℝ≥0∞) :
    Measurable (fun γ : C(ℝ≥0,ℂ) => sourceOpenGaugeContent h r (C ∩ (γ '' Icc s t))) := by
  apply measurable_of_Iio
  intro a
  have heq : (fun γ : C(ℝ≥0,ℂ) => sourceOpenGaugeContent h r (C ∩ (γ '' Icc s t))) ⁻¹' Iio a =
      ⋃ ε : ℝ≥0∞, ⋃ (_ : ε < a), {γ : C(ℝ≥0,ℂ) | sourceFiniteOpenCover h r ε (C ∩ (γ '' Icc s t))} := by
    ext γ
    simp only [mem_preimage,mem_Iio,sourceOpenGaugeContent,iInf_lt_iff,mem_iUnion,mem_ofPred_eq]
    tauto
  rw [heq]
  exact (isOpen_iUnion (fun ε => isOpen_iUnion (fun _ =>
    source_finite_open_cover_trace_isOpen h C hC s t r ε))).measurableSet
lemma source_compact_gauge_sup_open (h : ℝ → ℝ) (hh : IsGauge h)
    (K : Set ℂ) (hK : IsCompact K) :
    hausdorffGauge h K = ⨆ n : ℕ, sourceOpenGaugeContent h (sourceCoverScale n) K := by
  apply le_antisymm
  · rw [source_gauge_cover_formula h hh]
    refine iSup_le fun R => iSup_le fun hR => ?_
    obtain ⟨n,hn⟩ := (source_coverScale_tendsto.eventually (gt_mem_nhds hR)).exists
    apply le_iSup_of_le n
    change sourceFineGaugeContent h R K ≤ sourceOpenGaugeContent h (sourceCoverScale n) K
    unfold sourceOpenGaugeContent
    exact le_iInf fun ε => le_iInf fun hcov => (source_fine_content_finite_cover h hh hn.le hcov).le
  · refine iSup_le fun n => ?_
    apply le_of_forall_gt_imp_ge_of_dense
    intro ε hε
    unfold sourceOpenGaugeContent
    exact iInf_le_of_le ε (iInf_le_of_le
      (source_compact_finite_open_cover_lt h hh K hK (1/((n:ℝ)+1)) (by positivity) ε hε) le_rfl)
lemma source_compact_trace_measure_measurable (h : ℝ → ℝ) (hh : IsGauge h)
    (C : Set ℂ) (hC : IsClosed C) (s t : ℝ≥0) :
    Measurable (fun γ : C(ℝ≥0,ℂ) => hausdorffGauge h (C ∩ (γ '' Icc s t))) := by
  have heq : (fun γ : C(ℝ≥0,ℂ) => hausdorffGauge h (C ∩ (γ '' Icc s t))) =
      fun γ : C(ℝ≥0,ℂ) => ⨆ n : ℕ, sourceOpenGaugeContent h (sourceCoverScale n) (C ∩ (γ '' Icc s t)) := by
    funext γ
    exact source_compact_gauge_sup_open h hh _ ((isCompact_Icc.image γ.continuous).inter_left hC)
  rw [heq]
  exact Measurable.iSup (fun n => source_open_content_measurable h C hC s t _)
end
end SLEExactGauge
end

 
end
end
end

end OAI
