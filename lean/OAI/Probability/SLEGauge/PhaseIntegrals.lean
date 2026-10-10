import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.PhaseStopping

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open scoped Topology
open Set
open MeasureTheory Filter
open scoped NNReal Topology
open MeasureTheory Filter Set Metric Function ODE
open MeasureTheory ProbabilityTheory Filter Set
open Filter
open Filter Set
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open MeasureTheory
open scoped Classical
namespace ExactSLEPasting
lemma integral_finite_partition {Ω P : Type*} [MeasurableSpace Ω] [Fintype P]
    {μ : Measure Ω} (phase : Ω → P) (f : Ω → ℝ)
    (hf : ∀ p, Integrable (fun ω => if phase ω=p then f ω else 0) μ) :
    (∫ ω, f ω ∂μ)=∑ p, ∫ ω, (if phase ω=p then f ω else 0) ∂μ := by
  rw [←integral_finsetSum _ (fun p _ => hf p)]
  congr 1
  funext ω
  simp
lemma integral_le_of_finite_partition {Ω P : Type*} [MeasurableSpace Ω] [Fintype P]
    {μ : Measure Ω} (phase : Ω → P) (f g : Ω → ℝ)
    (hf : ∀ p, Integrable (fun ω => if phase ω=p then f ω else 0) μ)
    (hg : ∀ p, Integrable (fun ω => if phase ω=p then g ω else 0) μ)
    (hle : ∀ p, (∫ ω, (if phase ω=p then f ω else 0) ∂μ)≤
      ∫ ω, (if phase ω=p then g ω else 0) ∂μ) : (∫ ω, f ω ∂μ)≤∫ ω, g ω ∂μ := by
  rw [integral_finite_partition phase f hf,integral_finite_partition phase g hg]
  exact Finset.sum_le_sum fun p _ => hle p
end ExactSLEPasting

 
namespace ExactSLEGreen
open ExactSLEMain ExactSLEGenerator ExactSLEFiniteTilt ExactSLECalculus MeasureTheory Set Filter
open scoped Classical NNReal ENNReal
lemma clamped_delta_continuous (a η : ℝ) (hη : 0<η) (N : ℝ≥0) (cap σ off : ℝ) :
    Continuous (fun v : State => physicalDelta a cap σ off (regimeClamp η N v)) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  have hy := hη.trans_le (regimeClamp_height η N v)
  have hc := (physicalClock_smooth a cap (regimeClamp η N v) hy).continuousAt.comp_of_eq
    (regimeClamp_continuous η N).continuousAt rfl
  exact (continuousAt_const.add (continuousAt_const.mul hc)).rexp
lemma clamped_speed_continuous (η : ℝ) (hη : 0<η) (N : ℝ≥0) :
    Continuous (fun v : State => physicalV (regimeClamp η N v)) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  have hy := hη.trans_le (regimeClamp_height η N v)
  exact (Y.continuous.continuousAt.div ((X.continuous.pow 2).add (Y.continuous.pow 2)).continuousAt
    (Q_pos hy).ne').comp_of_eq (regimeClamp_continuous η N).continuousAt rfl
lemma regimeState_discount_le {m : ℕ} (s : Finset (Fin m)) {a ε η : ℝ}
    (ha : 1/4<a) (hε : 0<ε) (hη : 0<η) (N : ℝ≥0) (cap σ off : Fin m → ℝ)
    (z : Fin m → ℂ) (b : ExactSLEGenerator.Driver) (S T : ℝ≥0)
    (J₀ J₁ : ℝ) (hJ₀ : 0≤J₀) (hJ₁ : 0≤J₁)
    (hsingle : ∀ i∈s, (∫ t in (S:ℝ)..(T:ℝ),
      physicalDelta a (cap i) (σ i) (off i) (regimeClamp η N (vectorState a η hη z t.toNNReal b i))*
      physicalV (regimeClamp η N (vectorState a η hη z t.toNNReal b i))^2)≤J₀)
    (hpair : ∀ i∈s, ∀ j∈s.erase i, (∫ t in (S:ℝ)..(T:ℝ),
      (physicalDelta a (cap i) (σ i) (off i) (regimeClamp η N (vectorState a η hη z t.toNNReal b i))*
       physicalDelta a (cap j) (σ j) (off j) (regimeClamp η N (vectorState a η hη z t.toNNReal b j)))^(-regM a)*
       physicalV (regimeClamp η N (vectorState a η hη z t.toNNReal b i))*
       physicalV (regimeClamp η N (vectorState a η hη z t.toNNReal b j)))≤J₁) :
    (regimeState s a ε η hη N cap σ off z T b).2-
      (regimeState s a ε η hη N cap σ off z S b).2≤
      regC a*(m*J₀)+regYoungC a ε/2*(m*(m*J₁)) := by
  let V := fun (t : ℝ) (i : Fin m) => regimeClamp η N (vectorState a η hη z t.toNNReal b i)
  have hd (i : Fin m) : Continuous (fun t : ℝ => physicalDelta a (cap i) (σ i) (off i) (V t i)) :=
    (clamped_delta_continuous a η hη N (cap i) (σ i) (off i)).comp
      ((localState_continuous a η hη (z i) b).comp continuous_real_toNNReal)
  have hv (i : Fin m) : Continuous (fun t : ℝ => physicalV (V t i)) :=
    (clamped_speed_continuous η hη N).comp ((localState_continuous a η hη (z i) b).comp continuous_real_toNNReal)
  have hf (i : Fin m) : Continuous (fun t : ℝ => physicalDelta a (cap i) (σ i) (off i) (V t i)*physicalV (V t i)^2) := (hd i).mul ((hv i).pow 2)
  have hg (i j : Fin m) : Continuous (fun t : ℝ =>
      (physicalDelta a (cap i) (σ i) (off i) (V t i)*physicalDelta a (cap j) (σ j) (off j) (V t j))^(-regM a)*
      physicalV (V t i)*physicalV (V t j)) :=
    (((hd i).mul (hd j)).rpow_const (fun t => Or.inl (mul_pos (Real.exp_pos _) (Real.exp_pos _)).ne')).mul (hv i) |>.mul (hv j)
  have hk : Continuous (fun t : ℝ => regimeDiscountCut s a ε η N cap σ off (vectorState a η hη z t.toNNReal b)) :=
    (regimeDiscountCut_continuous s a ε η hη N cap σ off).comp ((vectorState_continuous a η hη z b).comp continuous_real_toNNReal)
  have he := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (hk.intervalIntegrable 0 S) (hk.intervalIntegrable S T)
  have hsum (r : Finset (Fin m)) {J : ℝ} (hJ : 0≤J) (f : Fin m → ℝ) (h : ∀ i∈r,f i≤J) :
      (∑ i ∈ r, f i) ≤ (m:ℝ)*J := by
    calc
      _ ≤ ∑ i ∈ r, J := Finset.sum_le_sum h
      _ = (r.card:ℝ)*J := by simp
      _ ≤ m*J := mul_le_mul_of_nonneg_right (by exact_mod_cast (show r.card ≤ m by simpa only [Fintype.card_fin] using r.card_le_univ)) hJ
  change (∫ t in (0:ℝ)..(T:ℝ), _)-(∫ t in (0:ℝ)..(S:ℝ), _)≤_
  rw [←he,add_sub_cancel_left]
  unfold regimeDiscountCut regimeDiscount
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum (f:=fun i t => physicalDelta a (cap i) (σ i) (off i) (V t i)*physicalV (V t i)^2) (fun i hi => (hf i).intervalIntegrable _ _),
      intervalIntegral.integral_finsetSum (fun i hi => (continuous_finsetSum _ fun j hj => hg i j).intervalIntegrable _ _)]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (hsum s hJ₀ _ hsingle) (regC_pos ha).le
    · apply mul_le_mul_of_nonneg_left _ (by have := regEta_lt_half ha; have := regC2_pos ha; have := regEta_pos ha; unfold regYoungC; apply div_nonneg; apply mul_nonneg; apply mul_nonneg; linarith; positivity; positivity; norm_num)
      apply hsum s (mul_nonneg (by positivity) hJ₁)
      intro i hi
      rw [intervalIntegral.integral_finsetSum (fun j hj => (hg i j).intervalIntegrable _ _)]
      exact hsum (s.erase i) hJ₁ _ (hpair i hi)
  · exact ((continuous_finsetSum s fun i hi => hf i).const_mul _).intervalIntegrable _ _
  · exact ((continuous_finsetSum s fun i hi => continuous_finsetSum _ fun j hj => hg i j).const_mul _).intervalIntegrable _ _
end ExactSLEGreen
namespace ExactSLEGreen
open ExactSLEMain ExactSLEGenerator ExactSLEFiniteTilt ExactSLEStops MeasureTheory Set Filter
open scoped Classical NNReal ENNReal
noncomputable def pairDiscountConstant (a : ℝ) : ℝ :=
  Real.exp (2*(regM a*regBeta a))/(2*a*(1-Real.exp (2*(regM a*regBeta a)-a)))
lemma pairDiscountConstant_pos {a : ℝ} (ha : 1/4<a) : 0<pairDiscountConstant a := by
  have ha0 : 0<a := by linarith
  have he : Real.exp (2*(regM a*regBeta a)-a)<1 := Real.exp_lt_one_iff.mpr (by nlinarith [regBeta_discount ha])
  unfold pairDiscountConstant
  positivity
noncomputable def phaseDiscountConstant (m : ℕ) (a ε : ℝ) : ℝ :=
  regC a*(m*(1/regBeta a))+regYoungC a ε/2*(m*(m*pairDiscountConstant a))
lemma phaseDiscountConstant_nonneg (m : ℕ) {a ε : ℝ} (ha : 1/4<a) (hε : 0<ε) :
    0≤phaseDiscountConstant m a ε := by
  have hC₂ := regC2_pos ha
  have hη₀ := regEta_pos ha
  have hY : 0≤regYoungC a ε := by
    unfold regYoungC
    apply mul_nonneg
    · apply mul_nonneg
      · linarith [regEta_lt_half ha]
      · positivity
    · positivity
  unfold phaseDiscountConstant
  have := (pairDiscountConstant_pos ha).le
  have := (regBeta_pos ha).le
  have := (regC_pos ha).le
  positivity
lemma actual_phase_discount {m : ℕ} {a ε : ℝ} (ha : 1/4<a) (hε : 0<ε)
    (z : Fin m → ℂ) (hz : ∀ i,0<(z i).im) (hinj : Function.Injective z)
    (cap U : Fin m → ℝ) (hc : ∀ i,0<cap i) (hr : ∀ i,cap i≤2*(z i).im)
    (hsep : ∀ i j,i≠j → cap i≤‖z i-z j‖) (hu : ∀ i,0≤U i)
    (η : ℝ) (hη : 0<η) (M : ℝ≥0) (b : ExactSLEGenerator.Driver) (S T : ℝ≥0)
    (hST : S≤T)
    (hboundary : ∀ i, levelTime a b (z i) (cap i) (U i)≤(S:ℝ≥0∞) ∨
      (T:ℝ≥0∞)≤levelTime a b (z i) (cap i) (U i))
    (hsafe : ∀ t, S≤t → t≤T → ‖vectorState a η hη z t b‖≤M ∧
      ∀ i∈phaseActive (actualPhase a z cap U S b),
      alive a b.1 t (z i) ∧ η≤Y (vectorState a η hη z t b i) ∧
      vectorState a η hη z t b i=actualState a b.1 t (z i)) :
    (regimeState (phaseActive (actualPhase a z cap U S b)) a ε η hη M cap
      (phaseSigma a (actualPhase a z cap U S b)) (phaseOffset a U (actualPhase a z cap U S b)) z T b).2-
    (regimeState (phaseActive (actualPhase a z cap U S b)) a ε η hη M cap
      (phaseSigma a (actualPhase a z cap U S b)) (phaseOffset a U (actualPhase a z cap U S b)) z S b).2≤
      phaseDiscountConstant m a ε := by
  have ha0 : 0<a := by linarith
  let p := actualPhase a z cap U S b
  let A := fun i => (levelTime a b (z i) (cap i) 0).toNNReal
  have htimes (i) (hi : i∈phaseActive p) := active_phase_interval
    (levelTime_mono a ha0 (z i) (hz i) (cap i) (hc i) (hr i) b 0 (U i/2) le_rfl (by have := hu i; linarith))
    (levelTime_mono a ha0 (z i) (hz i) (cap i) (hc i) (hr i) b (U i/2) (U i) (by have := hu i; linarith) (by have := hu i; linarith))
    (hboundary i) ((phaseActive_mem p i).mp hi)
  have hA (i) (hi : i∈phaseActive p) : A i≤S :=
    ENNReal.coe_le_coe.mp (ENNReal.coe_toNNReal_le_self.trans (htimes i hi).1)
  have hR (i) (hi : i∈phaseActive p) : fullLoewnerRadius a b.1 (z i) (A i)=cap i :=
    levelTime_fullRadius a ha0 (z i) (hz i) (cap i) (hc i) (hr i) b
      (ne_top_of_le_ne_top (by simp) (htimes i hi).1)
  have hclockT (i) (hi : i∈phaseActive p) : physicalClock a (cap i) (actualState a b.1 T (z i))≤U i :=
    levelTime_clock_le a ha0 (z i) (hz i) (cap i) (U i) (hc i) (hr i) (hu i) b T
      ((hsafe T hST le_rfl).2 i hi).1 (htimes i hi).2.1
  have hclockS (i) (hi : i∈phaseActive p) (hp : p i=2) :
      U i/2≤physicalClock a (cap i) (actualState a b.1 S (z i)) :=
    levelTime_clock_ge a ha0 (z i) (hz i) (cap i) (U i/2) (hc i) (hr i) (by have := hu i; linarith) b S
      ((hsafe S le_rfl hST).2 i hi).1 ((htimes i hi).2.2 hp)
  have he (t : ℝ) (ht : t∈uIcc (S:ℝ) (T:ℝ)) (i) (hi : i∈phaseActive p) :
      regimeClamp η M (vectorState a η hη z t.toNNReal b i)=actualState a b.1 t.toNNReal (z i) := by
    have ht' : t∈Icc (S:ℝ) T := by simpa only [uIcc_of_le (show (S:ℝ)≤T from hST)] using ht
    have hlo : S≤t.toNNReal := by exact_mod_cast (show (S:ℝ)≤(t.toNNReal:ℝ) by rw [Real.coe_toNNReal _ (S.coe_nonneg.trans ht'.1)]; exact ht'.1)
    have hhi : t.toNNReal≤T := by exact_mod_cast (show (t.toNNReal:ℝ)≤T by rw [Real.coe_toNNReal _ (S.coe_nonneg.trans ht'.1)]; exact ht'.2)
    have hs := hsafe t.toNNReal hlo hhi
    rw [regimeClamp_eq η M _ hη ((norm_le_pi_norm _ i).trans hs.1) (hs.2 i hi).2.1]
    exact (hs.2 i hi).2.2
  apply regimeState_discount_le (phaseActive p) ha hε hη M cap (phaseSigma a p) (phaseOffset a U p) z b S T
    (1/regBeta a) (pairDiscountConstant a) (by have := regBeta_pos ha; positivity) (pairDiscountConstant_pos ha).le
  · intro i hi
    obtain ⟨f,hf⟩ := ((hsafe T hST le_rfl).2 i hi).1
    have hh := actual_regularized_single_discount ha b.1.continuous hST (hA i hi) hf (hc i) (hR i hi)
      (U:=U i) (σ:=phaseSigma a p i) (off:=phaseOffset a U p i)
    have hp : (phaseSigma a p i=-regBeta a ∧ phaseOffset a U p i=0) ∨
      (phaseSigma a p i=regBeta a ∧ phaseOffset a U p i=-regBeta a*U i ∧ activeODEClock b.1 T (A i) f T≤U i) := by
      by_cases hh : p i=2
      · right
        refine ⟨by simp [phaseSigma,hh],by simp [phaseOffset,hh],?_⟩
        rw [←actual_clock_eq ha0.ne' (hc i) b.1.continuous hf ((hA i hi).trans hST) le_rfl (hR i hi)]
        exact hclockT i hi
      · exact Or.inl ⟨by simp [phaseSigma,hh],by simp [phaseOffset,hh]⟩
    apply (le_of_eq ?_).trans (hh hp)
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [he t ht i hi]
  · intro i hi j hj
    have hj' := Finset.mem_of_mem_erase hj
    obtain ⟨f,hf⟩ := ((hsafe T hST le_rfl).2 i hi).1
    obtain ⟨g,hg⟩ := ((hsafe T hST le_rfl).2 j hj').1
    have hij : i≠j := (Finset.ne_of_mem_erase hj).symm
    have hp (k : Fin m) (hk : k∈phaseActive p) (f : ℝ → ℂ) (hf : odeUntil a b.1 (z k) T f) :
      (phaseSigma a p k=-regBeta a ∧ phaseOffset a U p k=0) ∨
      (phaseSigma a p k=regBeta a ∧ phaseOffset a U p k=-regBeta a*U k ∧ U k/2≤activeODEClock b.1 T (A k) f S) := by
      by_cases hh : p k=2
      · right
        refine ⟨by simp [phaseSigma,hh],by simp [phaseOffset,hh],?_⟩
        rw [←actual_clock_eq ha0.ne' (hc k) b.1.continuous hf ((hA k hk).trans hST) hST (hR k hk)]
        exact hclockS k hk hh
      · exact Or.inl ⟨by simp [phaseSigma,hh],by simp [phaseOffset,hh]⟩
    have hh := actual_regularized_pair_discount ha b.1.continuous hST (hA i hi) (hA j hj') hf hg
      (hinj.ne hij) (hc i) (hc j) (hR i hi) (hR j hj') (hsep i j hij)
      (by simpa only [norm_sub_rev] using hsep j i hij.symm) (hp i hi f hf) (hp j hj' g hg)
    apply (le_of_eq ?_).trans hh
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [he t ht i hi,he t ht j hj']
end ExactSLEGreen
namespace ExactSLEGreen
open ExactSLEMain ExactSLEGenerator ExactSLEFiniteTilt ExactSLEStops MeasureTheory ProbabilityTheory Set Filter
open scoped Classical NNReal ENNReal
lemma stopped_phaseProduct_measurable {m : ℕ} (a : ℝ) (ha : 0<a)
    (z : Fin m → ℂ) (hz : ∀ i,0<(z i).im) (cap U : Fin m → ℝ)
    (hc : ∀ i,0<cap i) (hr : ∀ i,cap i≤2*(z i).im) (hu : ∀ i,0≤U i)
    (η : ℝ) (hη : 0<η) (S : ExactSLEGenerator.Driver → ℝ≥0)
    (hS : IsStoppingTime rawFiltration (fun b => (S b : WithTop ℝ≥0))) :
    Measurable (fun b => phaseProduct a cap U (actualPhase a z cap U (S b) b)
      (vectorState a η hη z (S b) b)) := by
  have hp := (actualPhase_measurable a ha z hz cap U hc hr hu S hS).mono hS.measurableSpace_le le_rfl
  have hv := (vectorState_stopped_measurable a η hη z S hS).mono hS.measurableSpace_le le_rfl
  have he : (fun b => phaseProduct a cap U (actualPhase a z cap U (S b) b) (vectorState a η hη z (S b) b))=
      fun b => ∑ p : PhaseVector m, if actualPhase a z cap U (S b) b=p then
        phaseProduct a cap U p (vectorState a η hη z (S b) b) else 0 := by funext b; simp
  rw [he]
  apply Finset.measurable_sum
  intro p hp'
  exact ((phaseProduct_measurable a cap U p).comp hv).ite (hp (measurableSet_singleton p)) measurable_const
lemma actual_phase_expectation_step {m : ℕ} {a ε : ℝ} (ha : 1/4<a) (hε : 0<ε)
    (hsize : ε*((m:ℝ)-1)≤regK a/2)
    (z : Fin m → ℂ) (hz : ∀ i,0<(z i).im) (hinj : Function.Injective z)
    (cap U : Fin m → ℝ) (hc : ∀ i,0<cap i) (hr : ∀ i,cap i≤2*(z i).im)
    (hsep : ∀ i j,i≠j → cap i≤‖z i-z j‖) (hu : ∀ i,0≤U i)
    (η : ℝ) (hη : 0<η) (M : ℝ≥0)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (S T : ExactSLEGenerator.Driver → ℝ≥0) (B : ℝ≥0)
    (hS : IsStoppingTime rawFiltration (fun b => (S b : WithTop ℝ≥0)))
    (hT : IsStoppingTime rawFiltration (fun b => (T b : WithTop ℝ≥0)))
    (hST : ∀ b,S b≤T b) (hTB : ∀ b,T b≤B)
    (hboundary : ∀ b i, ∀ u∈({0,U i/2,U i}:Finset ℝ),
      levelTime a b (z i) (cap i) u≤(S b:ℝ≥0∞) ∨ (T b:ℝ≥0∞)≤levelTime a b (z i) (cap i) u)
    (hsafe : ∀ b t, t≤T b → (∃ i, (t:ℝ≥0∞)≤levelTime a b (z i) (cap i) (U i)) →
      ‖vectorState a η hη z t b‖≤M ∧ ∀ i,
      (t:ℝ≥0∞)≤levelTime a b (z i) (cap i) (U i) →
      alive a b.1 t (z i) ∧ η≤Y (vectorState a η hη z t b i) ∧
      vectorState a η hη z t b i=actualState a b.1 t (z i)) :
    (∫ b, phaseProduct a cap U (actualPhase a z cap U (T b) b) (vectorState a η hη z (T b) b) ∂W)≤
      Real.exp (phaseDiscountConstant m a ε)*
      (∫ b, phaseProduct a cap U (actualPhase a z cap U (S b) b) (vectorState a η hη z (S b) b) ∂W) := by
  classical
  have ha0 : 0<a := by linarith
  let P := fun (Q : ExactSLEGenerator.Driver → ℝ≥0) (b : ExactSLEGenerator.Driver) => phaseProduct a cap U (actualPhase a z cap U (Q b) b) (vectorState a η hη z (Q b) b)
  let E := fun p : PhaseVector m => {b | actualPhase a z cap U (S b) b=p}
  have hE (p) : MeasurableSet[hS.measurableSpace] (E p) :=
    actualPhase_measurable a ha0 z hz cap U hc hr hu S hS (measurableSet_singleton p)
  have hE' (p) : MeasurableSet (E p) := hS.measurableSpace_le _ (hE p)
  have htrans (b) : P T b≤phaseProduct a cap U (actualPhase a z cap U (S b) b) (vectorState a η hη z (T b) b) := by
    apply actual_phase_transition ha z hz cap U hc hr hu η hη b (S b) (T b) (hST b) (hboundary b)
    intro i hi
    exact ((hsafe b (T b) le_rfl ⟨i,hi⟩).2 i hi).2.2
  have hint (p : PhaseVector m) (Q : ExactSLEGenerator.Driver → ℝ≥0)
      (hQ : IsStoppingTime rawFiltration (fun b => (Q b : WithTop ℝ≥0)))
      (hSQ : ∀ b,S b≤Q b) (hQT : ∀ b,Q b≤T b) :
      Integrable (fun b => if b∈E p then phaseProduct a cap U p (vectorState a η hη z (Q b) b) else 0) W := by
    by_cases hp : (phaseActive p).Nonempty
    · have hi : Integrable (fun b => if b∈E p then regularizedProduct (phaseActive p) a cap (phaseSigma a p)
          (phaseOffset a U p) (vectorState a η hη z (Q b) b) else 0) W := by
        have hs : ∀ b∈E p, ‖vectorState a η hη z (Q b) b‖≤M ∧ ∀ i∈phaseActive p, η≤Y (vectorState a η hη z (Q b) b i) := by
          intro b hb
          have he : actualPhase a z cap U (S b) b=p := hb
          have hn : (phaseActive (actualPhase a z cap U (S b) b)).Nonempty := he ▸ hp
          have hh := actual_phase_interval_safe ha z hz cap U hc hr hu η hη M b (S b) (T b) (hST b) hn
            (fun i => hboundary b i (U i) (by simp)) (hsafe b)
            (Q b) (hSQ b) (hQT b)
          rw [he] at hh
          exact ⟨hh.1,fun i hi => (hh.2 i hi).1⟩
        convert regularizedProduct_indicator_integrable (phaseActive p) a η hη M cap (phaseSigma a p) (phaseOffset a U p) z W Q hQ (E p) (hE' p) hs using 1
        funext b
        by_cases hb : b∈E p <;> simp only [ite_eq_left,ite_eq_right,hb,not_false_eq_true]
      convert hi.const_mul (phaseConstant a U p) using 1
      funext b
      dsimp only [phaseProduct]
      split_ifs <;> simp
    · have he : phaseActive p=∅ := Finset.not_nonempty_iff_eq_empty.mp hp
      simp only [phaseProduct,he,regularizedProduct,Finset.prod_empty,mul_one]
      have hic : Integrable (fun _ : ExactSLEGenerator.Driver => phaseConstant a U p) W := integrable_const _
      convert hic.indicator (hE' p) using 1
      all_goals first | rfl | (funext b; by_cases hb : b∈E p <;> simp [hb,Set.indicator])
  have hPi (p) : Integrable (fun b => if b∈E p then P T b else 0) W := by
    have hm : Measurable (fun b => if b∈E p then P T b else 0) :=
      (stopped_phaseProduct_measurable a ha0 z hz cap U hc hr hu η hη T hT).ite (hE' p) measurable_const
    apply (hint p T hT hST (fun _ => le_rfl)).mono' hm.aestronglyMeasurable
    apply Eventually.of_forall
    intro b
    by_cases hb : b∈E p
    · simp only [ite_eq_left hb,Real.norm_eq_abs,abs_of_pos (show 0<P T b from phaseProduct_pos a cap U _ _)]
      simpa only [show actualPhase a z cap U (S b) b=p from hb] using htrans b
    · simp only [ite_eq_right hb,norm_zero,le_refl]
  have hSi (p) : Integrable (fun b => if b∈E p then P S b else 0) W := by
    convert hint p S hS (fun _ => le_rfl) hST using 1
    funext b
    by_cases hb : b∈E p
    · simp only [ite_eq_left hb,P,show actualPhase a z cap U (S b) b=p from hb]
    · simp only [ite_eq_right hb]
  have hlocal (p) : (∫ b, (if b∈E p then phaseProduct a cap U p (vectorState a η hη z (T b) b) else 0) ∂W)≤
      Real.exp (phaseDiscountConstant m a ε)*(∫ b, (if b∈E p then phaseProduct a cap U p (vectorState a η hη z (S b) b) else 0) ∂W) := by
    by_cases hp : (phaseActive p).Nonempty
    · have hsiz : ε*(((phaseActive p).card:ℝ)-1)≤regK a/2 := by
        have hcard : ((phaseActive p).card:ℝ)≤ m := by exact_mod_cast (show (phaseActive p).card ≤ m by simpa using (phaseActive p).card_le_univ)
        exact (mul_le_mul_of_nonneg_left (sub_le_sub_right hcard 1) hε.le).trans hsize
      have hh := vector_regime_event_comparison (phaseActive p) ha hε hη hsiz M cap (phaseSigma a p) (phaseOffset a U p)
        (fun i hi => phaseSigma_bound ha p i) z W hW S T B hS hT hST hTB (E p) (hE p)
      have hsafe' : ∀ b∈E p, ∀ t, S b≤t → t≤T b → ‖vectorState a η hη z t b‖≤M ∧
        ∀ i∈phaseActive p, η≤Y (vectorState a η hη z t b i) ∧
        physicalDelta a (cap i) (phaseSigma a p i) (phaseOffset a U p i) (vectorState a η hη z t b i)≤1 := by
        intro b hb
        have he : actualPhase a z cap U (S b) b=p := hb
        have hh := actual_phase_interval_safe ha z hz cap U hc hr hu η hη M b (S b) (T b) (hST b)
          (he ▸ hp) (fun i => hboundary b i (U i) (by simp)) (hsafe b)
        simpa only [he] using hh
      have hD : ∀ b∈E p,
        (regimeState (phaseActive p) a ε η hη M cap (phaseSigma a p) (phaseOffset a U p) z (T b) b).2-
        (regimeState (phaseActive p) a ε η hη M cap (phaseSigma a p) (phaseOffset a U p) z (S b) b).2≤phaseDiscountConstant m a ε := by
        intro b hb
        have he : actualPhase a z cap U (S b) b=p := hb
        have h := actual_phase_discount ha hε z hz hinj cap U hc hr hsep hu η hη M b (S b) (T b) (hST b)
          (fun i => hboundary b i (U i) (by simp))
        apply (he ▸ h)
        intro t hst htt
        have h1 := hsafe' b hb t hst htt
        refine ⟨h1.1,?_⟩
        intro i hi
        have hi' : i∈phaseActive (actualPhase a z cap U (S b) b) := he ▸ hi
        have htarg := (active_phase_interval
          (levelTime_mono a ha0 (z i) (hz i) (cap i) (hc i) (hr i) b 0 (U i/2) le_rfl (by have := hu i; linarith))
          (levelTime_mono a ha0 (z i) (hz i) (cap i) (hc i) (hr i) b (U i/2) (U i) (by have := hu i; linarith) (by have := hu i; linarith))
          (hboundary b i (U i) (by simp)) ((phaseActive_mem _ i).mp hi')).2.1
        have hti := (ENNReal.coe_le_coe.mpr htt).trans htarg
        exact (hsafe b t htt ⟨i,hti⟩).2 i hti
      have hh' := mul_le_mul_of_nonneg_left (hh hsafe' _ hD) (phaseConstant_pos a U p).le
      simpa only [←integral_const_mul,phaseProduct,mul_ite,mul_zero,mul_assoc,mul_left_comm] using hh'
    · have he : phaseActive p=∅ := Finset.not_nonempty_iff_eq_empty.mp hp
      have hnon : 0≤∫ b, (if b∈E p then phaseConstant a U p else 0) ∂W := integral_nonneg fun b => by have := phaseConstant_pos a U p; split_ifs <;> positivity
      simp only [phaseProduct,he,regularizedProduct,Finset.prod_empty,mul_one]
      exact le_mul_of_one_le_left hnon (Real.one_le_exp_iff.mpr (phaseDiscountConstant_nonneg m ha hε))
  rw [←integral_const_mul]
  apply ExactSLEPasting.integral_le_of_finite_partition (fun b => actualPhase a z cap U (S b) b)
  · intro p
    convert hPi p using 1
    funext b
    by_cases hb : b∈E p <;> simp [E] at hb ⊢ <;> simp [hb,P]
  · intro p
    convert (hSi p).const_mul (Real.exp (phaseDiscountConstant m a ε)) using 1
    funext b
    by_cases hb : b∈E p <;> simp [E] at hb ⊢ <;> simp [hb,P]
  · intro p
    have h1 : (∫ b, (if b∈E p then P T b else 0) ∂W) ≤
        ∫ b, (if b∈E p then phaseProduct a cap U p (vectorState a η hη z (T b) b) else 0) ∂W :=
      integral_mono (hPi p) (hint p T hT hST (fun _ => le_rfl)) (fun b => by
        split_ifs with hb
        · simpa only [show actualPhase a z cap U (S b) b=p from hb] using htrans b
        · exact le_rfl)
    have h2 : (∫ b, (if b∈E p then phaseProduct a cap U p (vectorState a η hη z (S b) b) else 0) ∂W) =
        ∫ b, (if b∈E p then P S b else 0) ∂W := by
      congr 1
      funext b
      by_cases hb : b∈E p
      · simp only [ite_eq_left hb,P,show actualPhase a z cap U (S b) b=p from hb]
      · simp only [ite_eq_right hb]
    have h3 := h1.trans (hlocal p)
    rw [h2,←integral_const_mul] at h3
    convert h3 using 1 <;> congr 1 <;> funext b <;>
      (by_cases hb : b∈E p <;> simp [E] at hb ⊢ <;> simp [hb,P])
end ExactSLEGreen
namespace ExactSLEGreen
open ExactSLEMain ExactSLEGenerator ExactSLEFiniteTilt ExactSLEStops MeasureTheory Set Filter
open scoped Classical NNReal ENNReal
lemma actualState_zero {a : ℝ} (ha : 0<a) (b : ExactSLEGenerator.Driver) {z : ℂ} (hz : 0<z.im) :
    actualState a b.1 0 z=(z,0) := by
  have h0 := radialStop_actual a ha z hz (z.im/2) (by positivity) (by linarith) 0 b 0 (show (0:ℝ≥0)≤_ from bot_le)
  obtain ⟨f,hf⟩ := h0
  have hm : loewnerMap a b.1 0 z=z := (loewnerMap_eq hf).trans (by simpa using hf.1)
  have hd : deriv (loewnerMap a b.1 0) z=1 := by
    simpa using (hasDerivAt_loewnerMap b.1.continuous (show alive a b.1 0 z from ⟨f,hf⟩)).deriv
  simp [actualState,hm,hd,b.2]
lemma actual_phaseProduct_initial {m : ℕ} {a : ℝ} (ha : 1/4<a)
    (z : Fin m → ℂ) (hz : ∀ i,0<(z i).im) (cap U : Fin m → ℝ)
    (hc : ∀ i,0<cap i) (hr : ∀ i,cap i≤2*(z i).im) (hu : ∀ i,0≤U i)
    (η : ℝ) (hη : 0<η) (b : ExactSLEGenerator.Driver) :
    phaseProduct a cap U (actualPhase a z cap U 0 b) (vectorState a η hη z 0 b)≤1 := by
  have ha0 : 0<a := by linarith
  rw [phaseProduct_eq_prod]
  apply Finset.prod_le_one₀
  · intro i hi
    exact (phaseFactor_pos _ _ _ _ _).le
  · intro i hi
    have h0 := radialStop_actual a ha0 (z i) (hz i) ((z i).im/2) (by have := hz i; positivity) (by have := hz i; linarith) 0 b 0 (show (0:ℝ≥0)≤_ from bot_le)
    have hc0 : physicalClock a (cap i) (actualState a b.1 0 (z i))≤0 := by
      rw [actualState_zero ha0 b (hz i),physicalClock_radius a (cap i) (hc i) _ (hz i)]
      simp only [physicalRadius,Y_apply,J_apply,neg_zero,Real.exp_zero,mul_one]
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      exact Real.log_nonpos (by have := hc i; have := hz i; positivity) ((div_le_one (by have := hz i; positivity)).mpr (hr i))
    have hAB := levelTime_mono a ha0 (z i) (hz i) (cap i) (hc i) (hr i) b 0 (U i/2) le_rfl (by have := hu i; linarith)
    have hBC := levelTime_mono a ha0 (z i) (hz i) (cap i) (hc i) (hr i) b (U i/2) (U i) (by have := hu i; linarith) (by have := hu i; linarith)
    have he : vectorState a η hη z 0 b i=actualState a b.1 0 (z i) := by
      simp only [vectorState,localState_zero,actualState_zero ha0 b (hz i)]
    rw [he]
    generalize hp : actualPhase a z cap U 0 b i=p
    fin_cases p
    · norm_num [phaseFactor,Fin.ext_iff]
    · have hat := ((phase_one_iff _ _ _ 0 hAB hBC).mp hp).1
      have hge := levelTime_clock_ge a ha0 (z i) (hz i) (cap i) 0 (hc i) (hr i) le_rfl b 0 h0 hat
      have heq := le_antisymm hc0 hge
      simpa [phaseFactor,Fin.ext_iff] using physicalRegularized_activation (σ := -regBeta a) (off := 0) ha _ heq rfl
    · have hbt := ((phase_two_iff _ _ _ 0 hAB hBC).mp hp).1
      have hge := levelTime_clock_ge a ha0 (z i) (hz i) (cap i) (U i/2) (hc i) (hr i) (by have := hu i; linarith) b 0 h0 hbt
      have hu0 : U i=0 := by have := hu i; linarith
      have heq : physicalClock a (cap i) (actualState a b.1 0 (z i))=0 := by linarith
      simpa [phaseFactor,Fin.ext_iff,hu0] using physicalRegularized_activation (σ := regBeta a) (off := 0) ha _ heq rfl
    · have hct := (phase_three_iff _ _ _ 0).mp hp
      have hge := levelTime_clock_ge a ha0 (z i) (hz i) (cap i) (U i) (hc i) (hr i) (hu i) b 0 h0 hct
      have hu0 : U i=0 := by have := hu i; linarith
      norm_num [phaseFactor,Fin.ext_iff,hu0]
lemma actual_phaseProduct_completed {m : ℕ} (a : ℝ) (z : Fin m → ℂ) (cap U : Fin m → ℝ)
    (η : ℝ) (hη : 0<η) (b : ExactSLEGenerator.Driver) (T : ℝ≥0)
    (h : ∀ i,levelTime a b (z i) (cap i) (U i)≤(T:ℝ≥0∞)) :
    phaseProduct a cap U (actualPhase a z cap U T b) (vectorState a η hη z T b)=
      ∏ i, Real.exp (regP a*U i/2)/3 := by
  rw [phaseProduct_eq_prod]
  apply Finset.prod_congr rfl
  intro i hi
  have hp : actualPhase a z cap U T b i=3 := (phase_three_iff _ _ _ T).mpr (h i)
  simp [phaseFactor,hp,Fin.ext_iff]
end ExactSLEGreen
end

end OAI
