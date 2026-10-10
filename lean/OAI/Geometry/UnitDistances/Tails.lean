import OAI.Geometry.UnitDistances.RareBudget

namespace OAI

namespace PlanarUnitDistances.IncidenceCoercivity
open Filter FiniteLaw FiniteStarCoupling RareLabels RareMoments ScoreBook
  IncidenceSequence IncidenceScale IncidenceBook IncidenceNoise ActualScoreBook BudgetParameters
  EnvelopeCoercivity
open scoped Classical
noncomputable section
variable {s : Sequence} {a : Params} {i : ℕ}
local instance : Fintype (s.P i⊕s.Q i) := inferInstance
local instance : Fintype (s.P i×s.Q i) := inferInstance
local instance : Fintype ((s.P i⊕s.Q i)→Bool) := labelFintype _
local instance : Fintype (LevelSnapshot.Data (s.P i⊕s.Q i) (s.P i×s.Q i)) := snapshotFintype _ _ _
variable (R : Realization s a i)

def errorCoefficient (a : Params) (C ξ r : ℝ) : ℝ :=
  250000*BookEnvelope.total a C (27/50) (1/25) ξ r+r/a.epsilon+
  8*BookEnvelope.j a C (27/50) (1/25) ξ r+8*r+
  2*(a.d+BudgetParameters.joint C (27/50) (1/25) a.epsilon ξ/Real.sqrt a.d)*BookEnvelope.height C r

theorem bounds {C L : ℝ} (hC : 0<C) (hL : 0<L) (hv : R.Valid C L) (hscale : 0<scale s i) :
    R.book.CQ ≤ 250000*BookEnvelope.total a C (27/50) (1/25) (s.ξ i) (noise s a i)*R.book.S ∧
    R.book.S ≤ pointConstant L*R.book.HP+
      lossConstant L*BookEnvelope.total a C (27/50) (1/25) (s.ξ i) (noise s a i)*R.book.S ∧
    R.book.CQ+R.book.WB+8*R.book.J+8*R.book.M+2*WedgeSummary.JW R.book ≤
      errorCoefficient a C (s.ξ i) (noise s a i)*R.book.S := by
  obtain ⟨hM,hWC,hWB,hH,hJ,hEP,hDP,hDQ,hDT,hT⟩ := IncidenceEstimates.upper R hC hv hscale
  have hh := EnvelopeCoercivity.bounds R.book a hC hL.le (s.good i).error_nonneg
    (IncidenceNoise.nonneg s a i) (positive s i) (positiveQ s i)
    hv.2.2.2.2.1 hv.2.2.2.2.2.1 hM hWC hWB hJ hEP hDP hDQ hDT hT
  refine ⟨hh.1,hh.2.2,?_⟩
  have hw := hv.2.2.2.2.2.2.2.2.2.2.1
  have hc : 0 ≤ a.d+BudgetParameters.joint C (27/50) (1/25) a.epsilon (s.ξ i)/Real.sqrt a.d := by
    have hd := a.d_pos
    have he := a.epsilon_pos
    have hx := (s.good i).error_nonneg
    unfold BudgetParameters.joint
    positivity
  have hn := R.book.nonneg
  have hp : R.book.HP ≤ BookEnvelope.height C (noise s a i)*R.book.S := by linarith [hn.2.2.2.1]
  have hw' := hw.trans (mul_le_mul_of_nonneg_left hp hc)
  unfold errorCoefficient
  nlinarith

omit R in
theorem error_limit (s : Sequence) (a : Params) (C : ℝ) :
    Tendsto (fun i => errorCoefficient a C (s.ξ i) (noise s a i)) atTop
      (nhds (250000*leading a C (27/50) (1/25)+
        4*BudgetParameters.joint C (27/50) (1/25) a.epsilon 0*C+2*BudgetParameters.wedge a C (27/50) (1/25))) := by
  have hr := IncidenceNoise.limit s a
  have ht := BookEnvelope.total_limit a C (27/50) (1/25) (s.ξ) (noise s a) s.error_limit hr
  have hj : Tendsto (fun i => BudgetParameters.joint C (27/50) (1/25) a.epsilon (s.ξ i)) atTop
      (nhds (BudgetParameters.joint C (27/50) (1/25) a.epsilon 0)) :=
    (tendsto_const_nhds.add s.error_limit).div_const _
  have hh : Tendsto (fun i => BookEnvelope.height C (noise s a i)) atTop (nhds C) := by
    simpa only [BookEnvelope.height,add_zero,mul_one] using ((tendsto_const_nhds (x:=1)).add hr).const_mul C
  have h := ((((ht.const_mul 250000).add (hr.div_const a.epsilon)).add
    (((hj.div_const 2).mul hh).const_mul 8)).add (hr.const_mul 8)).add
      (((((tendsto_const_nhds (x:=a.d)).add (hj.div_const (Real.sqrt a.d))).mul hh)).const_mul 2)
  convert h using 1
  · funext i
    unfold errorCoefficient BookEnvelope.j
    ring
  · unfold BudgetParameters.wedge
    ring_nf

omit R in
lemma leading_joint (a : Params) {C : ℝ} (hC : 0<C) :
    4*BudgetParameters.joint C (27/50) (1/25) a.epsilon 0*C ≤ leading a C (27/50) (1/25) := by
  have he := a.epsilon_pos
  have hd := a.delta_pos
  have ha := a.eta_pos
  have hz := a.zeta_pos
  have hs := BookEnvelope.sampling_nonneg a
  have hj : 0≤BudgetParameters.joint C (27/50) (1/25) a.epsilon 0 := by unfold BudgetParameters.joint; positivity
  unfold leading
  have hq : 0≤(96*a.eta+20*a.delta+24*CommonTemplate.samplingError a.k (a.eta^2)+
    (12*(a.k:ℝ)/a.zeta+20/a.delta)*4/(a.m:ℝ))/a.epsilon := by positivity
  nlinarith
end
end PlanarUnitDistances.IncidenceCoercivity

namespace PlanarUnitDistances.IncidenceRare
open Filter FiniteLaw FiniteStarCoupling ScoreBook IncidenceSequence IncidenceScale
  IncidenceBook IncidenceNoise ActualScoreBook BudgetParameters EnvelopeCoercivity
open scoped Classical
noncomputable section
variable {s : Sequence} {a : Params} {i : ℕ}
local instance : Fintype (s.P i⊕s.Q i) := inferInstance
local instance : Fintype (s.P i×s.Q i) := inferInstance
local instance : Fintype ((s.P i⊕s.Q i)→Bool) := labelFintype _
local instance : Fintype (LevelSnapshot.Data (s.P i⊕s.Q i) (s.P i×s.Q i)) := snapshotFintype _ _ _

def Ready (R : Realization s a i) (c C τ : ℝ) : Prop :=
  R.fractional ∧ R.scale_eq ∧ R.mistake_bound ∧ R.common_bound ∧ R.bad_bound ∧
  c*scale s i ≤ mass (model s i).support*R.book.HP ∧
  mass (model s i).support*(R.book.HP+R.book.HQ) ≤ C*scale s i ∧
  mass (model s i).support*(R.book.CQ+R.book.WB+8*R.book.J+8*R.book.M+2*WedgeSummary.JW R.book) ≤ τ*scale s i

theorem prepare (s : Sequence) : ∃c C : ℝ,0<c ∧ 0<C ∧
    ∀τ : ℝ,0<τ → ∃a : Params,∀ᶠi in atTop,∃R : Realization s a i,Ready R c C τ := by
  obtain ⟨s₀,C,L,hs,hC,hL,hbook⟩ := IncidenceBook.constants s
  let pc := pointConstant L
  let lc := lossConstant L
  have hpc : 0<pc := by dsimp [pc,pointConstant]; positivity
  have hlc : 0<lc := by dsimp [lc,lossConstant]; positivity
  refine ⟨1/(2*pc),2*C,by positivity,by positivity,?_⟩
  intro τ hτ
  let ρ := min (1/(4*lc)) (τ/500010)
  have hρ : 0<ρ := lt_min (by positivity) (by positivity)
  obtain ⟨a,ha,hlead,hwedge⟩ := BudgetParameters.exists_small hC
    (by norm_num : (0:ℝ)<27/50) (by norm_num : (0:ℝ)<1/25) hs hρ
  have ha' : 2*a.epsilon ≤ s₀ := by linarith
  have ht := BookEnvelope.total_limit a C (27/50) (1/25) (s.ξ) (noise s a) s.error_limit (IncidenceNoise.limit s a)
  have herrlim := IncidenceCoercivity.error_limit s a C
  have herror : 250000*leading a C (27/50) (1/25)+
      4*BudgetParameters.joint C (27/50) (1/25) a.epsilon 0*C+2*BudgetParameters.wedge a C (27/50) (1/25)<τ := by
    have hj := IncidenceCoercivity.leading_joint a hC
    have hr : ρ≤τ/500010 := min_le_right _ _
    have hh : 500010*ρ≤τ := by have hh := (le_div_iff₀ (by norm_num : (0:ℝ)<500010)).mp hr; linarith
    linarith
  refine ⟨a,?_⟩
  filter_upwards [hbook a ha',(scale_limit s).eventually_gt_atTop 0,
    ht.eventually_lt_const (show leading a C (27/50) (1/25)<2*ρ by linarith),
    herrlim.eventually_le_const herror,(IncidenceNoise.limit s a).eventually_le_const (by norm_num : (0:ℝ)<1)]
      with i hi hscale htotal herr hnoise
  obtain ⟨R,hR⟩ := hi
  have hu := IncidenceEstimates.upper R hC hR hscale
  have hc := IncidenceCoercivity.bounds R hC hL hR hscale
  have hS := R.book.nonneg.1
  have hE : lc*BookEnvelope.total a C (27/50) (1/25) (s.ξ i) (noise s a i)≤1/2 := by
    have hr : ρ≤1/(4*lc) := min_le_left _ _
    have hh : ρ*(4*lc)≤1 := (le_div_iff₀ (by positivity : 0<4*lc)).mp hr
    nlinarith [mul_le_mul_of_nonneg_left htotal.le hlc.le]
  have hp := EnvelopeCoercivity.positive_fraction hL.le hS hc.2.1 hE
  have hm := R.mass_pos.le
  have heq := hR.2.1
  refine ⟨R,hR.1,heq,hR.2.2.1,hR.2.2.2.2.2.2.1,hR.2.2.2.2.2.2.2.1,?_,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left hp hm
    calc
      1/(2*pc)*scale s i=mass (model s i).support*(R.book.S/(2*pc)) := by rw [←heq]; ring
      _ ≤ _ := hh
  · have hh := mul_le_mul_of_nonneg_left hu.2.2.2.1 hm
    have hc' : BookEnvelope.height C (noise s a i)≤2*C := by unfold BookEnvelope.height; nlinarith
    calc
      _ ≤ mass (model s i).support*(BookEnvelope.height C (noise s a i)*R.book.S) := hh
      _ = BookEnvelope.height C (noise s a i)*scale s i := by rw [←heq]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc' hscale.le
  · calc
      _ ≤ mass (model s i).support*(IncidenceCoercivity.errorCoefficient a C (s.ξ i) (noise s a i)*R.book.S) := mul_le_mul_of_nonneg_left hc.2.2 hm
      _ = IncidenceCoercivity.errorCoefficient a C (s.ξ i) (noise s a i)*scale s i := by rw [←heq]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right herr hscale.le
end
end PlanarUnitDistances.IncidenceRare

namespace PlanarUnitDistances.IncidenceHeights
open Filter FiniteLaw FiniteStarCoupling IncidenceSequence IncidenceScale IncidenceBook
  IncidenceRare ActualScoreBook ActualProfiles ProfileBudget
open scoped Classical
noncomputable section
variable {s : Sequence} {a : BudgetParameters.Params} {i : ℕ}
local instance : Fintype (s.P i⊕s.Q i) := inferInstance
local instance : Fintype (s.P i×s.Q i) := inferInstance
local instance : Fintype ((s.P i⊕s.Q i)→Bool) := labelFintype _
local instance : Fintype (LevelSnapshot.Data (s.P i⊕s.Q i) (s.P i×s.Q i)) := snapshotFintype _ _ _
variable (R : Realization s a i)

def Z (x : s.Q i×(s.P i×s.P i)) : ℝ := error R.input true x+error R.input false x
lemma Z_nonneg (x) : 0≤Z R x := add_nonneg (error_nonneg R.input true x) (error_nonneg R.input false x)

theorem averages {c C τ : ℝ} (hR : Ready R c C τ) :
    c*scale s i≤avg (left (graph s i)) (height R.input) ∧
    avg (left (graph s i)) (height R.input)≤C*scale s i ∧
    avg (right (graph s i)) (ActualHeights.center R.input)≤C*scale s i ∧
    avg (graph s i) (fun pq => ActualHeights.mistake R.input pq.1 pq.2)≤2*Real.log 2+4 ∧
    avg (WedgeLaw.law (graph s i)) (Z R)≤τ*scale s i := by
  obtain ⟨_,_,hm,_,_,hp,hH,he⟩ := hR
  have hn := R.book.nonneg
  have hmass := R.mass_pos.le
  have hPa := height_average R.input
  have hQa := ActualHeights.center_average R.input
  have hMa := ActualHeights.mistake_average R.input
  have hE₁ := residual_budget R.input
  have hE₂ := size_budget R.input
  change avg (left (graph s i)) (height R.input)=mass (model s i).support*R.book.HP at hPa
  change avg (right (graph s i)) (ActualHeights.center R.input)=mass (model s i).support*R.book.HQ at hQa
  change avg (graph s i) (fun pq => ActualHeights.mistake R.input pq.1 pq.2)=mass (model s i).support*R.book.M at hMa
  change avg (WedgeLaw.law (graph s i)) (error R.input true)≤ mass (model s i).support*(R.book.CQ+R.book.WB+4*R.book.J+4*R.book.M) at hE₁
  change avg (WedgeLaw.law (graph s i)) (error R.input false)≤ mass (model s i).support*(2*WedgeSummary.JW R.book+4*R.book.J+4*R.book.M) at hE₂
  refine ⟨?_,?_,?_,?_,?_⟩
  · rwa [hPa]
  · rw [hPa]
    nlinarith [mul_nonneg hmass hn.2.2.2.1]
  · rw [hQa]
    nlinarith [mul_nonneg hmass hn.2.2.1]
  · rwa [hMa]
  · change avg (WedgeLaw.law (graph s i)) (fun x => error R.input true x+error R.input false x)≤_
    rw [avg_add]
    nlinarith

lemma row_support (p : s.P i) (q : s.Q i) (h : (row (graph s i) p).val q≠0) :
    GeometricLaw.E (s.P i) (s.Q i) p q := by
  apply support s i p q
  rw [←row_weight]
  exact mul_pos (positive s i p) (lt_of_le_of_ne ((row (graph s i) p).nonneg q) (Ne.symm h))

theorem pointwise (p : s.P i) (q r : s.Q i) (hqr : q≠r)
    (hq : (row (graph s i) p).val q≠0) (hr : (row (graph s i) p).val r≠0) :
    2*height R.input p≤3*(ActualHeights.center R.input q+ActualHeights.center R.input r+
      ActualHeights.mistake R.input p q+ActualHeights.mistake R.input p r)+
      mass (model s i).support*(R.book.WC+R.book.WB)+2*Real.log 2 := by
  let M := model s i
  exact ActualHeights.pointwise R.input a.epsilon_lt p q r
    (M.unit_identity p q (row_support p q hq)) (M.unit_identity p r (row_support p r hr))
    (M.center_injective.ne hqr) (M.sub_mem (.inl p) (.inr q)) (M.sub_mem (.inl p) (.inr r))
    (M.difference_mem (.inl p) (.inr q) (.inr r))

theorem baseline {c C τ : ℝ} (hR : Ready R c C τ) :
    mass (model s i).support*(R.book.WC+R.book.WB)+2*Real.log 2≤
      scale s i/a.epsilon+(2*Real.log 2+4)/a.epsilon+2*Real.log 2 := by
  obtain ⟨_,hs,hm,hc,hb,_⟩ := hR
  have hmass := R.mass_pos.le
  have hc' := mul_le_mul_of_nonneg_left hc hmass
  have hb' := mul_le_mul_of_nonneg_left hb hmass
  have hm' := div_le_div_of_nonneg_right hm a.epsilon_pos.le
  dsimp only [Realization.common_bound,Realization.bad_bound,Realization.mistake_bound] at *
  rw [←mul_div_assoc,hs] at hc'
  rw [←mul_div_assoc] at hb'
  nlinarith
end
end PlanarUnitDistances.IncidenceHeights

namespace PlanarUnitDistances.TailControl
open Finset MeasureTheory Set
open scoped BigOperators

noncomputable def layer (a t : ℝ) : ℝ := (Ioc 0 a).indicator (fun _ => 1) t

lemma layer_apply (a t : ℝ) : layer a t = if 0 < t ∧ t ≤ a then 1 else 0 := by
  classical
  simp [layer, Set.indicator_apply]

lemma layer_integrable (a : ℝ) : Integrable (layer a) := by
  apply (integrable_indicator_iff measurableSet_Ioc).mpr
  exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)

lemma integral_layer {a : ℝ} (ha : 0 ≤ a) : ∫ t, layer a t = a := by
  change (∫ t, (Ioc 0 a).indicator (fun _ : ℝ => (1 : ℝ)) t) = a
  rw [integral_indicator measurableSet_Ioc, integral_const]
  simp [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal ha]

lemma layer_min (a b t : ℝ) : layer (min a b) t = layer a t * layer b t := by
  simp only [layer_apply, le_min_iff]
  split_ifs <;> simp_all

lemma layer_nonneg (a t : ℝ) : 0 ≤ layer a t := by
  simp only [layer_apply]; split_ifs <;> norm_num

noncomputable def mass {P : Type*} (μ : P → ℝ) (F : Finset P) : ℝ := ∑ p ∈ F, μ p

section Finite
variable {P Q : Type*} [Fintype P] [Fintype Q]

noncomputable def tails (μ a : P → ℝ) (t : ℝ) : ℝ := ∑ p, μ p * layer (a p) t

lemma tails_integrable (μ a : P → ℝ) : Integrable (tails μ a) := by
  exact integrable_finsetSum _ (fun p _ => (layer_integrable (a p)).const_mul (μ p))

lemma integral_tails (μ a : P → ℝ) (ha : ∀ p, 0 ≤ a p) :
    ∫ t, tails μ a t = ∑ p, μ p * a p := by
  unfold tails
  rw [integral_finsetSum _ (fun p _ => (layer_integrable (a p)).const_mul (μ p))]
  simp only [integral_const_mul, integral_layer (ha _)]

lemma tails_nonneg (μ a : P → ℝ) (hμ : ∀ p, 0 ≤ μ p) (t : ℝ) : 0 ≤ tails μ a t :=
  sum_nonneg (fun p _ => mul_nonneg (hμ p) (layer_nonneg _ _))

lemma tails_eq_mass (μ a : P → ℝ) {t : ℝ} (ht : 0 < t) :
    tails μ a t = mass μ (univ.filter (fun p => t ≤ a p)) := by
  classical
  simp only [tails, mass, sum_filter, layer_apply, ht, true_and]
  apply sum_congr rfl
  intro p _
  split_ifs <;> simp

lemma tails_eq_zero (μ a : P → ℝ) {t : ℝ} (ht : ¬0 < t) : tails μ a t = 0 := by
  simp [tails, layer_apply, ht]

noncomputable def pairTails (w : P → Q → ℝ) (a : P → ℝ) (b : Q → ℝ) (t : ℝ) : ℝ :=
  ∑ p, ∑ q, w p q * layer (min (a p) (b q)) t

lemma pairTails_integrable (w : P → Q → ℝ) (a : P → ℝ) (b : Q → ℝ) :
    Integrable (pairTails w a b) := by
  exact integrable_finsetSum _ (fun p _ => integrable_finsetSum _
    (fun q _ => (layer_integrable _).const_mul _))

lemma integral_pairTails (w : P → Q → ℝ) (a : P → ℝ) (b : Q → ℝ)
    (ha : ∀ p, 0 ≤ a p) (hb : ∀ q, 0 ≤ b q) :
    ∫ t, pairTails w a b t = ∑ p, ∑ q, w p q * min (a p) (b q) := by
  unfold pairTails
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _
    (fun q _ => (layer_integrable _).const_mul _))]
  apply sum_congr rfl
  intro p _
  rw [integral_finsetSum _ (fun q _ => (layer_integrable _).const_mul _)]
  simp only [integral_const_mul, integral_layer (le_min (ha _) (hb _))]

lemma pairTails_eq_rectangle (w : P → Q → ℝ) (a : P → ℝ) (b : Q → ℝ)
    {t : ℝ} (ht : 0 < t) :
    pairTails w a b t =
      ∑ p ∈ univ.filter (fun p => t ≤ a p), ∑ q ∈ univ.filter (fun q => t ≤ b q), w p q := by
  classical
  simp only [pairTails, sum_filter, layer_apply, ht, true_and, le_min_iff]
  apply sum_congr rfl
  intro p _
  by_cases hp : t ≤ a p
  · simp only [hp, true_and, ↓reduceIte]
    apply sum_congr rfl
    intro q _
    split_ifs <;> simp
  · simp [hp]

lemma pairTails_eq_zero (w : P → Q → ℝ) (a : P → ℝ) (b : Q → ℝ)
    {t : ℝ} (ht : ¬0 < t) : pairTails w a b t = 0 := by
  simp [pairTails, layer_apply, ht]

lemma layer_young {x y θ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    θ * Real.sqrt (x*y) ≤ x/24 + 6*θ^2*y := by
  rw [Real.sqrt_mul hx]
  nlinarith [sq_nonneg (Real.sqrt x - 12*θ*Real.sqrt y),
    Real.sq_sqrt hx, Real.sq_sqrt hy]

theorem capped_expectation (w : P → Q → ℝ) (μ : P → ℝ) (κ : Q → ℝ)
    (hμ : ∀ p, 0 ≤ μ p) (hκ : ∀ q, 0 ≤ κ q)
    (a : P → ℝ) (b : Q → ℝ) (ha : ∀ p, 0 ≤ a p) (hb : ∀ q, 0 ≤ b q)
    (T : Finset P) (hzero : ∀ p, p ∉ T → a p = 0) (θ : ℝ)
    (hexp : ∀ F : Finset P, F ⊆ T → ∀ G : Finset Q,
      (∑ p ∈ F, ∑ q ∈ G, w p q) ≤ θ * Real.sqrt (mass μ F * mass κ G)) :
    (∑ p, ∑ q, w p q * min (a p) (b q)) ≤
      (∑ p, μ p * a p)/24 + 6*θ^2*(∑ q, κ q * b q) := by
  classical
  have hpoint (t : ℝ) : pairTails w a b t ≤ tails μ a t / 24 + 6*θ^2*tails κ b t := by
    by_cases ht : 0 < t
    · have hsub : univ.filter (fun p => t ≤ a p) ⊆ T := by
        intro p hp
        by_contra hn
        have hp' := (mem_filter.mp hp).2
        rw [hzero p hn] at hp'
        exact (not_le_of_gt ht) hp'
      have he := hexp _ hsub (univ.filter (fun q => t ≤ b q))
      rw [← pairTails_eq_rectangle w a b ht, ← tails_eq_mass μ a ht,
        ← tails_eq_mass κ b ht] at he
      exact he.trans (layer_young (tails_nonneg μ a hμ t) (tails_nonneg κ b hκ t))
    · simp only [pairTails_eq_zero _ _ _ ht, tails_eq_zero _ _ ht]
      norm_num
  have hint := integral_mono (pairTails_integrable w a b)
    ((tails_integrable μ a).div_const 24 |>.add ((tails_integrable κ b).const_mul (6*θ^2))) hpoint
  change (∫ t, pairTails w a b t) ≤ (∫ t, tails μ a t / 24 + 6*θ^2*tails κ b t) at hint
  rw [integral_pairTails w a b ha hb, integral_add
    ((tails_integrable μ a).div_const 24) ((tails_integrable κ b).const_mul _),
    integral_div, integral_const_mul, integral_tails μ a ha, integral_tails κ b hb] at hint
  exact hint

lemma average_distinct (π c : Q → ℝ) (hπ : ∀ q, 0 ≤ π q)
    (hs : ∑ q, π q = 1) (hmax : ∀ q, π q ≤ 1/2) (hc : ∀ q, 0 ≤ c q)
    {a : ℝ} (ha : 0 ≤ a)
    (hcap : ∀ q r, q ≠ r → π q ≠ 0 → π r ≠ 0 → a ≤ 3*(c q+c r)) :
    a/2 ≤ 6 * ∑ q, π q*c q := by
  classical
  have hcoll : ∑ q, π q*π q ≤ 1/2 := by
    calc
      _ ≤ ∑ q, π q*(1/2) := sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left (hmax q) (hπ q))
      _ = 1/2 := by rw [← sum_mul, hs]; norm_num
  have hp (q r : Q) : π q*π r*a ≤
      3*(π q*π r*c q+π q*π r*c r) + if q=r then π q*π r*a else 0 := by
    by_cases hqr : q = r
    · simp only [hqr, ↓reduceIte]
      nlinarith [mul_nonneg (mul_nonneg (hπ r) (hπ r)) (hc r)]
    · simp only [hqr, ↓reduceIte, add_zero]
      by_cases hq : π q = 0
      · simp [hq]
      by_cases hr : π r = 0
      · simp [hr]
      have hh := mul_le_mul_of_nonneg_left (hcap q r hqr hq hr) (mul_nonneg (hπ q) (hπ r))
      nlinarith
  have hh := sum_le_sum (s := univ) (fun q _ => sum_le_sum (s := univ) (fun r _ => hp q r))
  have he (q : Q) : (∑ r, π q*π r*a) = π q*a := by
    calc
      _ = π q*a * ∑ r, π r := by rw [mul_sum]; apply sum_congr rfl; intro r _; ring
      _ = _ := by rw [hs, mul_one]
  have he₁ (q : Q) : (∑ r, π q*π r*c q) = π q*c q := by
    calc
      _ = π q*c q * ∑ r, π r := by rw [mul_sum]; apply sum_congr rfl; intro r _; ring
      _ = _ := by rw [hs, mul_one]
  have he₂ (q : Q) : (∑ r, π q*π r*c r) = π q*(∑ r, π r*c r) := by
    rw [mul_sum]; apply sum_congr rfl; intro r _; ring
  simp only [sum_add_distrib, ← mul_sum, he, he₁, he₂, sum_ite_eq] at hh
  rw [← sum_mul, hs, one_mul, ← sum_mul, hs, one_mul] at hh
  simp only [Finset.mem_univ, ite_true] at hh
  rw [← sum_mul] at hh
  nlinarith [mul_le_mul_of_nonneg_right hcoll ha]

noncomputable def capped (a : P → ℝ) (T : Finset P) (p : P) : ℝ := by
  classical
  exact if p ∈ T then a p else 0

theorem finite_tail_bound (μ : P → ℝ) (κ : Q → ℝ) (π m : P → Q → ℝ)
    (hμ : ∀ p, 0 ≤ μ p) (hκ : ∀ q, 0 ≤ κ q)
    (hπ : ∀ p q, 0 ≤ π p q) (hsπ : ∀ p, ∑ q, π p q = 1)
    (hmπ : ∀ p q, π p q ≤ 1/2) (hm : ∀ p q, 0 ≤ m p q)
    (a : P → ℝ) (b : Q → ℝ) (ha : ∀ p, 0 ≤ a p) (hb : ∀ q, 0 ≤ b q)
    (T : Finset P) (θ : ℝ)
    (hcap : ∀ p ∈ T, ∀ q r, q ≠ r → π p q ≠ 0 → π p r ≠ 0 →
      a p ≤ 3*(min (a p) (b q)+min (a p) (b r)+m p q+m p r))
    (hexp : ∀ F : Finset P, F ⊆ T → ∀ G : Finset Q,
      (∑ p ∈ F, ∑ q ∈ G, μ p*π p q) ≤ θ * Real.sqrt (mass μ F * mass κ G)) :
    (∑ p, μ p * capped a T p) ≤ 144*θ^2*(∑ q, κ q*b q) +
      24*(∑ p, ∑ q, μ p*π p q*m p q) := by
  classical
  have hz (p : P) : 0 ≤ capped a T p := by simp only [capped]; split_ifs; exact ha p; positivity
  have hrow (p : P) : capped a T p / 2 ≤
      6 * ∑ q, π p q * (min (capped a T p) (b q) + m p q) := by
    apply average_distinct (π p) (fun q => min (capped a T p) (b q)+m p q)
      (hπ p) (hsπ p) (hmπ p) (fun q => add_nonneg (le_min (hz p) (hb q)) (hm p q)) (hz p)
    intro q r hqr hq hr
    by_cases hp : p ∈ T
    · simp only [capped, hp, ↓reduceIte]
      linarith [hcap p hp q r hqr hq hr]
    · simp only [capped, hp, ↓reduceIte, min_eq_left (hb q), min_eq_left (hb r), zero_add]
      exact mul_nonneg (by norm_num) (add_nonneg (hm p q) (hm p r))
  have havg := sum_le_sum (s := univ) (fun p _ => mul_le_mul_of_nonneg_left (hrow p) (hμ p))
  have havg' : (∑ p, μ p*capped a T p)/2 ≤
      6*(∑ p, ∑ q, μ p*π p q*min (capped a T p) (b q)) +
      6*(∑ p, ∑ q, μ p*π p q*m p q) := by
    have heq : (∑ p, μ p * (6 * ∑ q, π p q * (min (capped a T p) (b q) + m p q))) =
        6*(∑ p, ∑ q, μ p*π p q*min (capped a T p) (b q)) +
          6*(∑ p, ∑ q, μ p*π p q*m p q) := by
      calc
        _ = ∑ p, ∑ q, (6*(μ p*π p q*min (capped a T p) (b q)) +
            6*(μ p*π p q*m p q)) := by
          apply sum_congr rfl
          intro p _
          rw [← mul_assoc, mul_sum]
          apply sum_congr rfl
          intro q _
          ring
        _ = _ := by simp only [sum_add_distrib, ← mul_sum]
    rw [heq] at havg
    simpa only [mul_div_assoc, sum_div] using havg
  have hmin := capped_expectation (fun p q => μ p*π p q) μ κ hμ hκ (capped a T) b hz hb
    T (fun p hp => by simp [capped, hp]) θ hexp
  linarith

end Finite
end PlanarUnitDistances.TailControl

namespace PlanarUnitDistances.LawTail
open Finset FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
variable {P Q : Type} [Fintype P] [Fintype Q]
lemma capped_pointwise {a b c e f B : ℝ} (ha : 0≤a) (hb : 0≤b) (hc : 0≤c)
    (he : 0≤e) (hf : 0≤f) (hB : B≤a) (h : 2*a≤3*(b+c+e+f)+B) :
    a≤3*(min a b+min a c+e+f) := by
  by_cases h₁ : a≤b
  · rw [min_eq_left h₁]
    have hv : 0≤ min a c := le_min ha hc
    linarith
  · by_cases h₂ : a≤c
    · rw [min_eq_left h₂]
      have hv : 0≤ min a b := le_min ha hb
      linarith
    · rw [min_eq_right (le_of_not_ge h₁),min_eq_right (le_of_not_ge h₂)]
      linarith

theorem estimate (π : Law (P×Q)) (U : Law P) (V : Law Q) (a : P → ℝ) (b : Q → ℝ)
    (m : P → Q → ℝ) {γ η ξ C S R B M : ℝ}
    (hγ : 0<γ) (hη : 0≤η) (hξ : 0≤ξ) (_hC : 0≤C) (hS : 0<S) (hR : 0<R)
    (hμ : ∀p,γ*U.val p≤(left π).val p) (hκ : ∀q,γ*V.val q≤(right π).val q)
    (hexp : ∀F : Finset P,∀G : Finset Q,event π (fun pq => pq.1∈F ∧ pq.2∈G)≤
      Real.sqrt (event U (fun p => p∈F)*event V (fun q => q∈G))*
        ((event U (fun p => p∈F)*event V (fun q => q∈G))^η+ξ))
    (ha : ∀p,0≤a p) (hb : ∀q,0≤b q) (hm : ∀p q,0≤ m p q)
    (hrow : ∀p q,(row π p).val q≤1/2)
    (hmean : avg (left π) a≤C*S) (hmeanQ : avg (right π) b≤C*S)
    (hmmean : avg π (fun pq => m pq.1 pq.2)≤M) (hbase : B≤R*S)
    (hp : ∀p q r,q≠r → (row π p).val q≠0 → (row π p).val r≠0 →
      2*a p≤3*(b q+b r+m p q+m p r)+B) :
    avg (left π) (fun p => if R*S<a p then a p else 0)≤
      144*((((C/R)/γ)^η+ξ)/γ)^2*(C*S)+24*M := by
  let T := univ.filter (fun p => R*S<a p)
  have hT : event (left π) (fun p => p∈T)≤C/R := by
    rw [←LawExpansion.mass_event]
    exact ExpansionConsequences.height_tail_mass (left π).val a (left π).nonneg ha hS hR hmean
  have he (F : Finset P) (hF : F⊆T) (G : Finset Q) :
      (∑p∈F,∑q∈G,(left π).val p*(row π p).val q)≤
        ((((C/R)/γ)^η+ξ)/γ)*Real.sqrt
          (TailControl.mass (left π).val F*TailControl.mass (right π).val G) := by
    simp_rw [row_weight]
    change ExpansionConsequences.rect (fun p q => π.val (p,q)) F G≤_
    rw [LawExpansion.rect_event]
    change _≤((((C/R)/γ)^η+ξ)/γ)*Real.sqrt
      (ExpansionConsequences.mass (left π).val F*ExpansionConsequences.mass (right π).val G)
    rw [LawExpansion.mass_event,LawExpansion.mass_event]
    exact LawRare.small_rect π U V hγ hη hξ hμ hκ hexp F G
      ((event_mono (left π) (fun _ h => hF h)).trans hT)
  have ht := TailControl.finite_tail_bound (left π).val (right π).val
    (fun p q => (row π p).val q) m (left π).nonneg (right π).nonneg
    (fun p => (row π p).nonneg) (fun p => (row π p).total) hrow hm a b ha hb T
    ((((C/R)/γ)^η+ξ)/γ) (fun p hpT q r hqr hq hr =>
      capped_pointwise (ha p) (hb q) (hb r) (hm p q) (hm p r)
        (hbase.trans (mem_filter.mp hpT).2.le) (hp p q r hqr hq hr)) he
  have hM : (∑p,∑q,(left π).val p*(row π p).val q*m p q)=avg π (fun pq => m pq.1 pq.2) := by
    simp only [row_weight,avg,Fintype.sum_prod_type]
  rw [hM] at ht
  have heq : (∑p,(left π).val p*TailControl.capped a T p)=
      avg (left π) (fun p => if R*S<a p then a p else 0) := by
    simp only [avg,TailControl.capped,T,mem_filter,mem_univ,true_and]
  rw [heq] at ht
  have h₁ := mul_le_mul_of_nonneg_left hmeanQ (by positivity : 0≤144*((((C/R)/γ)^η+ξ)/γ)^2)
  simp only [avg] at ht h₁ hmmean ⊢
  linarith
end
end PlanarUnitDistances.LawTail

namespace PlanarUnitDistances.AccurateBand
open FiniteLaw Finset
open scoped Classical BigOperators
noncomputable section
variable {X : Type*} [Fintype X]

def kept (W Z : X → ℝ) (L U δ : ℝ) (x : X) : Prop :=
  L ≤ W x ∧ W x ≤ U ∧ Z x ≤ δ*W x

lemma weighted_kept (μ : Law X) (W Z : X → ℝ) {L U δ : ℝ}
    (hW : ∀x,0≤W x) (hZ : ∀x,0≤Z x) (hL : 0≤L) (hδ : 0<δ) :
    avg μ W-avg μ Z/δ-L-avg μ (fun x => if U<W x then W x else 0) ≤
      avg μ (fun x => if kept W Z L U δ x then W x else 0) := by
  have h := avg_mono μ (f := fun x => W x-Z x/δ-L-(if U<W x then W x else 0))
    (g := fun x => if kept W Z L U δ x then W x else 0) (fun x => by
      have hz := div_nonneg (hZ x) hδ.le
      by_cases ha : kept W Z L U δ x
      · simp only [ha,↓reduceIte]
        split_ifs <;> linarith [hW x]
      · simp only [ha,↓reduceIte]
        by_cases ht : U<W x
        · simp only [ht,↓reduceIte]; linarith
        · simp only [ht,↓reduceIte,sub_zero]
          have hu := le_of_not_gt ht
          by_cases hl : L≤W x
          · have he : δ*W x<Z x := lt_of_not_ge (fun he => ha ⟨hl,hu,he⟩)
            have hw : W x<Z x/δ := (lt_div_iff₀ hδ).mpr (by nlinarith)
            linarith
          · linarith)
  simpa only [avg_sub,avg_const,div_eq_mul_inv,←avg_smul,mul_comm] using h

lemma kept_probability (μ : Law X) (W Z : X → ℝ) {L U δ : ℝ} (_hU : 0≤U) :
    avg μ (fun x => if kept W Z L U δ x then W x else 0) ≤
      U*event μ (kept W Z L U δ) := by
  unfold event
  rw [←avg_smul]
  apply avg_mono
  intro x
  by_cases h : kept W Z L U δ x
  · simpa only [h,ite_eq_left,mul_one] using h.2.1
  · simp [h]

lemma dyadic_cover {L U W : ℝ} {N : ℕ} (hL : 0<L) (hLW : L≤W)
    (hWU : W≤U) (hU : U<L*2^N) :
    ∃j : Fin N, L*2^(j:ℕ)≤W ∧ W≤2*(L*2^(j:ℕ)) := by
  obtain ⟨j,hj,hj'⟩ := exists_nat_pow_near ((one_le_div hL).mpr hLW) (by norm_num : (1:ℝ)<2)
  have hjN : j<N := by
    by_contra hn
    have hm := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (le_of_not_gt hn)
    have ht : L*2^j≤W := by have ht := (le_div_iff₀ hL).mp hj; nlinarith
    nlinarith
  refine ⟨⟨j,hjN⟩,?_,?_⟩
  · have ht := (le_div_iff₀ hL).mp hj
    nlinarith
  · have ht := (div_lt_iff₀ hL).mp hj'
    rw [pow_succ] at ht
    nlinarith

lemma exists_cover_piece (μ : Law X) {Y : Type*} [Fintype Y] [Nonempty Y]
    (A : X → Prop) (B : Y → X → Prop) (hcover : ∀x,A x → ∃y,B y x) :
    ∃y,event μ A/(Fintype.card Y:ℝ) ≤ event μ (B y) := by
  have h : event μ A ≤ ∑y,event μ (B y) := by
    calc
      _ ≤ avg μ (fun x => ∑y,if B y x then 1 else 0) := by
        apply avg_mono
        intro x
        by_cases ha : A x
        · obtain ⟨y,hy⟩ := hcover x ha
          simp only [ha,↓reduceIte]
          have hh := single_le_sum (s := univ) (f := fun y => if B y x then (1:ℝ) else 0)
            (fun y _ => by split_ifs <;> norm_num) (mem_univ y)
          simpa only [hy,ite_eq_left] using hh
        · simp only [ha,↓reduceIte]
          exact sum_nonneg fun y _ => by split_ifs <;> norm_num
      _ = _ := by simp only [avg,event,mul_sum]; rw [sum_comm]
  by_contra hn
  have ht : ∀y,event μ (B y)<event μ A/(Fintype.card Y:ℝ) := by
    simpa only [not_exists,not_le] using hn
  have hh := sum_lt_sum_of_nonempty (s := univ) univ_nonempty (fun y _ => ht y)
  have hc : (Fintype.card Y:ℝ)≠0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card Y≠0)
  simp only [sum_const,card_univ,nsmul_eq_mul,mul_div_cancel₀ _ hc] at hh
  linarith

theorem select (μ : Law X) (W Z : X → ℝ) {L U δ m : ℝ} {N : ℕ}
    (hW : ∀x,0≤W x) (hZ : ∀x,0≤Z x) (hL : 0<L) (hU : 0<U)
    (hδ : 0<δ) (hLU : L≤U) (hN : 0<N) (hUN : U<L*2^N)
    (hm : m≤avg μ W-avg μ Z/δ-L-avg μ (fun x => if U<W x then W x else 0)) :
    ∃J,L≤J ∧ J≤U ∧ m/(U*N)≤event μ (fun x => J≤W x ∧ W x≤2*J ∧ Z x≤δ*W x) := by
  let : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  let A := kept W Z L U δ
  let B (j : Fin N) (x : X) := A x ∧ L*2^(j:ℕ)≤W x ∧ W x≤2*(L*2^(j:ℕ))
  obtain ⟨j,hj⟩ := exists_cover_piece μ A B (fun x hx => by
    obtain ⟨j,hj⟩ := dyadic_cover hL hx.1 hx.2.1 hUN
    exact ⟨j,hx,hj⟩)
  have hmass : m≤U*event μ A := (hm.trans (weighted_kept μ W Z hW hZ hL.le hδ)).trans
    (kept_probability μ W Z hU.le)
  have hc : (0:ℝ)<N := by exact_mod_cast hN
  have hp : m/(U*N)≤event μ (B j) := by
    simp only [Fintype.card_fin] at hj
    apply le_trans _ hj
    rw [div_mul_eq_div_div]
    exact div_le_div_of_nonneg_right ((div_le_iff₀ hU).mpr (by nlinarith [hmass])) hc.le
  by_cases hJU : L*2^(j:ℕ)≤U
  · refine ⟨L*2^(j:ℕ),?_,hJU,?_⟩
    · nlinarith [(one_le_pow₀ (n := (j:ℕ)) (by norm_num : (1:ℝ)≤2))]
    · exact hp.trans (event_mono μ (fun x hx => ⟨hx.2.1,hx.2.2,hx.1.2.2⟩))
  · have hz : event μ (B j)=0 := by
      unfold event
      calc
        _ = avg μ (fun _ => 0) := avg_congr μ (fun x => ite_eq_right (fun hx => hJU (hx.2.1.trans hx.1.2.1)))
        _ = 0 := avg_const μ 0

    have hm0 : m/(U*N)≤0 := hp.trans_eq hz
    exact ⟨L,le_rfl,hLU,hm0.trans (event_nonneg μ _)⟩
end
end PlanarUnitDistances.AccurateBand

namespace PlanarUnitDistances.RareBand
open FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
variable {P Q : Type} [Fintype P] [Fintype Q]
lemma pair_tail {a b T : ℝ} (ha : 0≤a) (hb : 0≤b) :
    (if 2*T<a+b then a+b else 0)≤2*(if T<a then a else 0)+2*(if T<b then b else 0) := by
  split_ifs <;> linarith
lemma wedge_tail (π : Law (P×Q)) (h : P → ℝ) (hh : ∀p,0≤h p) (T : ℝ) :
    avg (WedgeLaw.law π) (fun a => if 2*T<h a.2.1+h a.2.2 then h a.2.1+h a.2.2 else 0) ≤
      4*avg (left π) (fun p => if T<h p then h p else 0) := by
  calc
    _ ≤ avg (WedgeLaw.law π) (fun a => 2*(if T<h a.2.1 then h a.2.1 else 0)+
      2*(if T<h a.2.2 then h a.2.2 else 0)) := avg_mono _ (fun a => pair_tail (hh _) (hh _))
    _ = _ := by rw [avg_add,avg_smul,avg_smul,WedgeLaw.first_point π (fun p=>if T<h p then h p else 0),WedgeLaw.second_point π (fun p=>if T<h p then h p else 0)]; ring

theorem select (π : Law (P×Q)) (h : P → ℝ) (Z : Q×(P×P) → ℝ)
    {c S R δ : ℝ} {N : ℕ} (hc : 0<c) (hS : 0<S) (hR : 0<R) (hδ : 0<δ)
    (hN : 0<N) (hRc : c≤4*R) (hRN : 4*R<c*2^N)
    (hh : ∀p,0≤h p) (hZ : ∀a,0≤Z a)
    (hmean : c*S≤avg (left π) h)
    (herr : avg (WedgeLaw.law π) Z≤δ*c*S/2)
    (htail : avg (left π) (fun p => if R*S<h p then h p else 0)≤c*S/8) :
    ∃J,c*S/2≤J ∧ J≤2*R*S ∧
      c/(4*R*N)≤event (WedgeLaw.law π)
        (fun a => J≤h a.2.1+h a.2.2 ∧ h a.2.1+h a.2.2≤2*J ∧ Z a≤δ*(h a.2.1+h a.2.2)) := by
  have hwmean : 2*c*S≤avg (WedgeLaw.law π) (fun a => h a.2.1+h a.2.2) := by
    rw [avg_add,WedgeLaw.first_point,WedgeLaw.second_point]
    linarith
  have hzt : avg (WedgeLaw.law π) Z/δ≤c*S/2 := by
    apply (div_le_iff₀ hδ).mpr
    nlinarith
  have hwt := (wedge_tail π h hh (R*S)).trans (mul_le_mul_of_nonneg_left htail (by norm_num : (0:ℝ)≤4))
  obtain ⟨J,hJ,hJU,hprob⟩ := AccurateBand.select (WedgeLaw.law π)
    (fun a => h a.2.1+h a.2.2) Z (L:=c*S/2) (U:=2*(R*S)) (δ:=δ) (m:=c*S/2)
    (N:=N) (fun a => add_nonneg (hh _) (hh _)) hZ (by positivity) (by positivity) hδ
    (by nlinarith [mul_le_mul_of_nonneg_right hRc hS.le]) hN
    (by nlinarith [mul_lt_mul_of_pos_right hRN hS]) (by linarith)
  refine ⟨J,hJ,by nlinarith,?_⟩
  have hn : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  have heq : (c*S/2)/(2*(R*S)*(N:ℝ))=c/(4*R*N) := by field_simp; ring
  rwa [heq] at hprob
end
end PlanarUnitDistances.RareBand

namespace PlanarUnitDistances.TailParameters
open Filter
noncomputable section

def coefficient (C R ξ : ℝ) : ℝ := 144*((((C/R)/(27/50:ℝ))^(1/25:ℝ)+ξ)/(27/50:ℝ))^2*C
lemma noise_limit (C R : ℝ) {ξ : ℕ → ℝ} (hξ : Tendsto ξ atTop (nhds 0)) :
    Tendsto (fun n => coefficient C R (ξ n)) atTop (nhds (coefficient C R 0)) :=
  ((((tendsto_const_nhds.add hξ).div_const _).pow 2).const_mul 144).mul_const C
lemma radius_limit (C : ℝ) : Tendsto (fun R : ℝ => coefficient C R 0) atTop (nhds 0) := by
  have h : Tendsto (fun R : ℝ => (C/R)/(27/50:ℝ)) atTop (nhds 0) := by
    simpa only [zero_div,id_eq] using (tendsto_const_nhds.div_atTop tendsto_id).div_const (27/50:ℝ)
  have hp := h.rpow_const_nhds_zero (by norm_num : (0:ℝ)<1/25)
  simpa only [coefficient,add_zero,zero_div,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,zero_mul]
    using (((hp.div_const (27/50:ℝ)).pow 2).const_mul 144).mul_const C
lemma exists_radius {c : ℝ} (hc : 0<c) (C B : ℝ) :
    ∃R : ℝ,0<R ∧ B≤R ∧ c≤4*R ∧ coefficient C R 0<c/16 := by
  obtain ⟨R,hR,hB,hcR,h⟩ := ((eventually_gt_atTop (0:ℝ)).and
    ((eventually_ge_atTop B).and ((eventually_ge_atTop (c/4)).and
      ((radius_limit C).eventually_lt_const (by positivity : (0:ℝ)<c/16))))).exists
  exact ⟨R,hR,hB,by linarith,h⟩
lemma exists_band {c R : ℝ} (hc : 0<c) : ∃N : ℕ,0<N ∧ 4*R<c*2^N := by
  have ht : Tendsto (fun n : ℕ => (2:ℝ)^n) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨N,hN,h⟩ := ((eventually_gt_atTop 0).and (ht.eventually_gt_atTop (4*R/c))).exists
  exact ⟨N,hN,by have hh := (div_lt_iff₀ hc).mp h; nlinarith⟩
end
end PlanarUnitDistances.TailParameters

namespace PlanarUnitDistances.IncidenceBand
open Filter FiniteLaw FiniteStarCoupling IncidenceSequence IncidenceScale IncidenceBook
  IncidenceRare IncidenceHeights ActualProfiles ProfileBudget BudgetParameters
open scoped Classical
noncomputable section
variable {s : Sequence} {a : Params} {i : ℕ}
local instance : Fintype (s.P i⊕s.Q i) := inferInstance
local instance : Fintype (s.P i×s.Q i) := inferInstance
local instance : Fintype ((s.P i⊕s.Q i)→Bool) := labelFintype _
local instance : Fintype (LevelSnapshot.Data (s.P i⊕s.Q i) (s.P i×s.Q i)) := snapshotFintype _ _ _

def band (R : Realization s a i) (J δ : ℝ) (x : s.Q i×(s.P i×s.P i)) : Prop :=
  J≤height R.input x.2.1+height R.input x.2.2 ∧
  height R.input x.2.1+height R.input x.2.2≤2*J ∧
  Z R x≤δ*(height R.input x.2.1+height R.input x.2.2)

lemma tail {c C τ R₀ : ℝ} (R : Realization s a i) (hR : Ready R c C τ)
    (_hc : 0<c) (hC : 0<C) (hscale : 1≤ scale s i) (hR₀ : 0<R₀)
    (hb : 1/a.epsilon+(2*Real.log 2+4)/a.epsilon+2*Real.log 2≤R₀)
    (hrow : IncidenceNoise.noise s a i≤1/2)
    (hcoeff : TailParameters.coefficient C R₀ (s.ξ i)≤c/16)
    (hconst : 24*(2*Real.log 2+4)≤c*scale s i/16) :
    avg (left (graph s i)) (fun p => if R₀*scale s i<height R.input p then height R.input p else 0)≤c*scale s i/8 := by
  have hS : 0<scale s i := lt_of_lt_of_le zero_lt_one hscale
  have hm := IncidenceHeights.averages R hR
  let U := GeometricLaw.counting (s.P i) (GeometricLaw.card_pos _ _ (s.good i).positive).1
  let V := GeometricLaw.counting (s.Q i) (GeometricLaw.card_pos _ _ (s.good i).positive).2
  have hμ (p : s.P i) : (27/50:ℝ)*U.val p≤(left (graph s i)).val p := by
    rw [graph,GeometricLaw.left_eq]
    simpa only [U,GeometricLaw.counting,mul_one_div] using (s.good i).atomP p p.property
  have hκ (q : s.Q i) : (27/50:ℝ)*V.val q≤(right (graph s i)).val q := by
    rw [graph,GeometricLaw.right_eq]
    simpa only [V,GeometricLaw.counting,mul_one_div] using (s.good i).atomQ q q.property
  have hbase := IncidenceHeights.baseline R hR
  have hbase' : ActualScoreBook.mass (model s i).support*(R.book.WC+R.book.WB)+2*Real.log 2≤R₀*scale s i := by
    have he := a.epsilon_pos
    have hlog : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
    have h₁ := mul_le_mul_of_nonneg_left hscale (show 0≤(2*Real.log 2+4)/a.epsilon+2*Real.log 2 by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hb hS.le
    simp only [div_eq_mul_inv,mul_one,one_mul] at hbase h₁ h₂ ⊢
    nlinarith
  have ht := LawTail.estimate (graph s i) U V (height R.input) (ActualHeights.center R.input)
    (ActualHeights.mistake R.input) (γ:=27/50) (η:=1/25) (ξ:=s.ξ i) (C:=C)
    (S:=scale s i) (R:=R₀) (M:=2*Real.log 2+4)
    (by norm_num) (by norm_num) (s.good i).error_nonneg hC.le hS hR₀ hμ hκ
    (GeometricLaw.expansion _ _ (s.good i).positive (s.good i).expansion)
    (height_nonneg R.input) (ActualHeights.center_nonneg R.input) (ActualHeights.mistake_nonneg R.input)
    (fun p q => ((IncidenceNoise.row_atom s i p q).trans
      ((IncidenceNoise.dp_le_collision s a i).trans (IncidenceNoise.components s a i).2.1)).trans hrow)
    hm.2.1 hm.2.2.1 hm.2.2.2.1 hbase' (fun p q r hqr hq hr => by
      simpa only [add_assoc] using IncidenceHeights.pointwise R p q r hqr hq hr)
  have hh := mul_le_mul_of_nonneg_right hcoeff hS.le
  dsimp only [TailParameters.coefficient] at hh
  nlinarith

theorem choose (s : Sequence) : ∃c : ℝ,0<c ∧ ∀δ : ℝ,0<δ →
    ∃a : Params,∃b : ℝ,0<b ∧ ∀ᶠi in atTop,∃R : Realization s a i,∃J : ℝ,
      c*scale s i/2≤J ∧ b≤event (WedgeLaw.law (graph s i)) (band R J δ) := by
  obtain ⟨c,C,hc,hC,hprep⟩ := IncidenceRare.prepare s
  refine ⟨c,hc,?_⟩
  intro δ hδ
  obtain ⟨a,ha⟩ := hprep (δ*c/2) (by positivity)
  obtain ⟨R₀,hR₀,hb,hcR,hcoef⟩ := TailParameters.exists_radius hc C
    (1/a.epsilon+(2*Real.log 2+4)/a.epsilon+2*Real.log 2)
  obtain ⟨N,hN,hRN⟩ := TailParameters.exists_band (R:=R₀) hc
  refine ⟨a,c/(4*R₀*N),by positivity,?_⟩
  have hconst : ∀ᶠi in atTop,24*(2*Real.log 2+4)≤c*scale s i/16 := by
    filter_upwards [(scale_limit s).eventually_ge_atTop (384*(2*Real.log 2+4)/c)] with i hi
    have hh := (div_le_iff₀ hc).mp hi
    nlinarith
  filter_upwards [ha,(scale_limit s).eventually_ge_atTop 1,
    (IncidenceNoise.limit s a).eventually_le_const (by norm_num : (0:ℝ)<1/2),
    (TailParameters.noise_limit C R₀ s.error_limit).eventually_le_const hcoef,hconst]
      with i hi hscale hrow hcoeff hco
  obtain ⟨R,hR⟩ := hi
  have ht := tail R hR hc hC hscale hR₀ hb hrow hcoeff hco
  have hm := IncidenceHeights.averages R hR
  obtain ⟨J,hJ,_,hprob⟩ := RareBand.select (graph s i) (height R.input) (Z R)
    hc (lt_of_lt_of_le zero_lt_one hscale) hR₀ hδ hN hcR hRN
    (height_nonneg R.input) (Z_nonneg R) hm.1 (by convert hm.2.2.2.2 using 1; ring) ht
  exact ⟨R,J,hJ,hprob⟩
end
end PlanarUnitDistances.IncidenceBand

end OAI
