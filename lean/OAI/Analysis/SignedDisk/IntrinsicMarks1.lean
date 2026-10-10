import OAI.Analysis.SignedDisk.PlanePotential2

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace SignedDisk

namespace IntrinsicMarks
open Finset
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

def validPath : Tree ι E → List ι → Prop
  | .leaf _, p => p = []
  | .branch _, [] => False
  | .branch t, i::p => validPath (t i) p

omit [InnerProductSpace ℝ E] in
lemma rootEval_mono_on (t : Tree ι E) {F G : List ι → ℝ}
    (h : ∀ p, validPath t p → F p ≤ G p) : rootEval t F ≤ rootEval t G := by
  induction t generalizing F G with
  | leaf v => exact mul_le_mul_of_nonneg_left (h [] rfl) (norm_nonneg _)
  | branch t ih =>
    apply mul_le_mul_of_nonneg_left _ (survival_nonneg t)
    exact sum_le_sum fun i _ => ih i (fun p hp => h (i::p) hp)

omit [InnerProductSpace ℝ E] in
lemma lateEval_mono_on (t : Tree ι E) {F G : List ι → ℕ → ℝ}
    (h : ∀ p b, validPath t p → b ≤ p.length → F p b ≤ G p b) :
    lateEval t F ≤ lateEval t G := by
  induction t generalizing F G with
  | leaf v => rfl
  | branch t ih =>
    unfold lateEval
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr (survival_le_one t))
      exact sum_le_sum fun i _ => rootEval_mono_on (t i) (fun p hp => h (i::p) 1 hp (by simp))
    · exact sum_le_sum fun i _ => ih i (fun p b hp hb => h (i::p) (b+1) hp (by simpa using Nat.succ_le_succ hb))

omit [InnerProductSpace ℝ E] in
/-- Particle monotonicity requires bounds only on genuine terminal paths and
legal birth times; the explicit construction has no mass elsewhere. -/
theorem particleEval_mono_on (t : Tree ι E) {F G : List ι → ℕ → ℝ}
    (h : ∀ p b, validPath t p → b ≤ p.length → F p b ≤ G p b) :
    particleEval t F ≤ particleEval t G := by
  exact add_le_add (rootEval_mono_on t (fun p hp => h p 0 hp (Nat.zero_le _)))
    (lateEval_mono_on t h)

/-- Intrinsic marks as an actual function on prefixes, with first-crossing
reset. Prefixes outside the tree have zero charge. -/
def markIndicator (e : E) (δ : ℝ) : Tree ι E → E → List ι → ℝ
  | .leaf v, n, [] => if δ < ‖direction e v-n‖ then 1 else 0
  | .leaf _, _, _::_ => 0
  | .branch t, n, [] => if δ < ‖direction e (∑ i, vector (t i))-n‖ then 1 else 0
  | .branch t, n, i::p =>
      let v := ∑ j, vector (t j)
      markIndicator e δ (t i) (if δ < ‖direction e v-n‖ then direction e v else n) p

def rootMarkIndicator (e : E) (δ : ℝ) : Tree ι E → List ι → ℝ
  | _, [] => 1
  | .leaf _, _::_ => 0
  | .branch t, i::p => markIndicator e δ (t i) (direction e (∑ j, vector (t j))) p

lemma marked_occupancy (e : E) (δ : ℝ) (t : Tree ι E) (n : E) :
    nodeCharge t (markIndicator e δ t n) = markedCost e δ t n := by
  induction t generalizing n with
  | leaf v => simp only [nodeCharge,markIndicator,markedCost]; split_ifs <;> simp
  | branch t ih =>
    simp only [nodeCharge,markIndicator,markedCost]
    split_ifs with h
    · simp only [mul_one]
      congr 1
      exact sum_congr rfl (fun i _ => ih i _)
    · simp only [mul_zero,zero_add]
      exact sum_congr rfl (fun i _ => ih i _)

lemma root_marked_occupancy (e : E) (δ : ℝ) (t : Tree ι E) :
    nodeCharge t (rootMarkIndicator e δ t) = costWithRoot e δ t := by
  cases t with
  | leaf v => simp [nodeCharge,rootMarkIndicator,costWithRoot]
  | branch t => simp only [nodeCharge,rootMarkIndicator,costWithRoot,mul_one,marked_occupancy]

theorem particle_mark_budget {e : E} (he : ‖e‖ = 1) {δ : ℝ} (hδ : 0 < δ)
    (t : Tree ι E) :
    particleEval t (pathCharge (rootMarkIndicator e δ t)) ≤
      (1+2/δ^2)*terminalMass t := by
  rw [particle_occupancy,root_marked_occupancy]
  exact costWithRoot_le he hδ t

/-- Turning a genuine pathwise switch bound into the global budget uses exact
occupancy, rather than a false assumption that every particle is born at a root. -/
theorem particle_switch_budget {e : E} (he : ‖e‖ = 1) {δ c : ℝ} (hδ : 0 < δ)
    (t : Tree ι E) (energy : List ι → ℝ) (switches : List ι → ℕ → ℝ)
    (hpath : ∀ p b, validPath t p → b ≤ p.length → switches p b ≤
      1+2*pathCharge (rootMarkIndicator e δ t) p b+c*pathCharge energy p b) :
    particleEval t switches ≤ (3+4/δ^2)*terminalMass t+c*nodeCharge t energy := by
  have h := particleEval_mono_on t hpath
  simp only [particleEval_add,particleEval_smul,particleEval_const,particle_occupancy,
    root_marked_occupancy] at h
  have hm := costWithRoot_le he hδ t
  calc
    _ ≤ terminalMass t*1 + 2*((1+2/δ^2)*terminalMass t)+c*nodeCharge t energy :=
      h.trans (by gcongr)
    _ = _ := by ring

end IntrinsicMarks

namespace SignedAssembly
open Finset
open scoped RealInnerProductSpace
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure RowJet (ι E : Type*) [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  law : FiniteLabels.Law ι
  grad : ι → E
  total_grad : ∑ i, grad i = 0

inductive JetTree (ι E : Type*) [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  | leaf : E → JetTree ι E
  | branch : RowJet ι E → E → ℝ → (ι → JetTree ι E) → JetTree ι E

def mean : JetTree ι E → E
  | .leaf v => v
  | .branch row _ _ t => ∑ i, row.law i • mean (t i)

def flux : JetTree ι E → ℝ
  | .leaf _ => 0
  | .branch row _ _ t => ∑ i, ⟪row.grad i,mean (t i)⟫ + ∑ i, row.law i*flux (t i)

/-- Product-rule expansion over all terminal label histories. The carried mass
and its derivative are updated by the exact Leibniz rule. -/
def pathFlux : JetTree ι E → ℝ → E → ℝ
  | .leaf v, _, G => ⟪G,v⟫
  | .branch row _ _ t, q, G =>
      ∑ i, pathFlux (t i) (q*row.law i) (q • row.grad i+row.law i • G)

lemma pathFlux_eq (t : JetTree ι E) (q : ℝ) (G : E) :
    pathFlux t q G = ⟪G,mean t⟫+q*flux t := by
  induction t generalizing q G with
  | leaf v => simp [pathFlux,mean,flux]
  | branch row c B t ih =>
    simp only [pathFlux,ih,inner_add_left,real_inner_smul_left,sum_add_distrib,
      ← mul_sum,mean,flux,inner_sum,real_inner_smul_right]
    simp only [mul_assoc, ← mul_sum]
    ring

lemma terminal_flux (t : JetTree ι E) : pathFlux t 1 0 = flux t := by
  rw [pathFlux_eq,inner_zero_left,one_mul,zero_add]

def TerminalBound : JetTree ι E → E → ℝ → Prop
  | .leaf v, c, B => ‖v-c‖ ≤ B
  | .branch _ _ _ t, c, B => ∀ i, TerminalBound (t i) c B

lemma mean_bound (t : JetTree ι E) (c : E) (B : ℝ) (h : TerminalBound t c B) :
    ‖mean t-c‖ ≤ B := by
  induction t with
  | leaf v => exact h
  | branch row _ _ t ih =>
    have he : mean (.branch row (0:E) 0 t)-c = ∑ i, row.law i • (mean (t i)-c) := by
      simp only [mean,smul_sub,sum_sub_distrib,← sum_smul,row.law.total,one_smul]
    change ‖mean (.branch row (0:E) 0 t)-c‖ ≤ B
    rw [he]
    calc
      _ ≤ ∑ i, ‖row.law i • (mean (t i)-c)‖ := norm_sum_le _ _
      _ = ∑ i, row.law i*‖mean (t i)-c‖ := by
        simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (row.law.nonneg _)]
      _ ≤ ∑ i, row.law i*B := sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (ih i (h i)) (row.law.nonneg i)
      _ = B := by rw [← sum_mul,row.law.total,one_mul]

/-- This is the exact zero-row-sum cancellation. No unsigned path-potential
bound is used and the parent prefix may be arbitrarily large. -/
lemma prefix_cancellation (row : RowJet ι E) (v : ι → E) (c : E) :
    (∑ i, ⟪row.grad i,v i⟫) = ∑ i, ⟪row.grad i,v i-c⟫ := by
  simp only [inner_sub_right,sum_sub_distrib,← sum_inner,row.total_grad,inner_zero_left,sub_zero]

lemma row_flux_bound (row : RowJet ι E) (v : ι → E) (c : E) (B : ℝ)
    (h : ∀ i, ‖v i-c‖ ≤ B) :
    |∑ i, ⟪row.grad i,v i⟫| ≤ (∑ i, ‖row.grad i‖)*B := by
  rw [prefix_cancellation row v c]
  calc
    _ ≤ ∑ i, |⟪row.grad i,v i-c⟫| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ‖row.grad i‖*B := sum_le_sum fun i _ =>
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (h i) (norm_nonneg _))
    _ = _ := by rw [← sum_mul]

def Controlled : JetTree ι E → Prop
  | .leaf _ => True
  | .branch _ c B t => (∀ i, TerminalBound (t i) c B) ∧ ∀ i, Controlled (t i)

def cost : JetTree ι E → ℝ
  | .leaf _ => 0
  | .branch row _ B t => (∑ i, ‖row.grad i‖)*B+∑ i, row.law i*cost (t i)

/-- Full finite-history signed flux estimate, with all stochastic prefix
weights kept. The node bound is the tail oscillation, not the old envelope. -/
theorem signed_flux_bound (t : JetTree ι E) (ht : Controlled t) :
    |pathFlux t 1 0| ≤ cost t := by
  rw [terminal_flux]
  induction t with
  | leaf v => simp [flux,cost]
  | branch row c B t ih =>
    change |(∑ i, ⟪row.grad i,mean (t i)⟫)+∑ i, row.law i*flux (t i)| ≤ _
    calc
      _ ≤ |∑ i, ⟪row.grad i,mean (t i)⟫|+|∑ i, row.law i*flux (t i)| := abs_add_le _ _
      _ ≤ (∑ i, ‖row.grad i‖)*B+∑ i, row.law i*cost (t i) := by
        apply add_le_add (row_flux_bound row (fun i => mean (t i)) c B
          (fun i => mean_bound (t i) c B (ht.1 i)))
        calc
          _ ≤ ∑ i, |row.law i*flux (t i)| := abs_sum_le_sum_abs _ _
          _ = ∑ i, row.law i*|flux (t i)| := by
            simp only [abs_mul,abs_of_nonneg (row.law.nonneg _)]
          _ ≤ _ := sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (ih i (ht.2 i)) (row.law.nonneg i)
      _ = _ := rfl

end SignedAssembly

open scoped ContDiff
namespace PlanePotential
lemma potential_norm_lintegral {L : ℂ → ℂ} (hL : Measurable L) {b : ℂ → ℂ}
    (hb : Integrable b) :
    (∫⁻ y, ‖⟪L y,b y⟫‖ₑ) ≤
      ∫⁻ y, ENNReal.ofReal ‖L y‖ ∂volume.withDensity (fun y => ENNReal.ofReal ‖b y‖) := by
  rw [lintegral_withDensity_eq_lintegral_mul₀' hb.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal
    hL.norm.ennreal_ofReal.aemeasurable]
  apply lintegral_mono
  intro y
  dsimp only [Pi.mul_apply]
  rw [← ofReal_norm]
  change ENNReal.ofReal ‖⟪L y,b y⟫‖ ≤ ENNReal.ofReal ‖b y‖ * ENNReal.ofReal ‖L y‖
  rw [← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal ((norm_inner_le_norm _ _).trans_eq (mul_comm _ _))

lemma potential_integrable_of_density {L : ℂ → ℂ} (hL : Measurable L) {b : ℂ → ℂ}
    (hb : Integrable b)
    (hfinite : (∫⁻ y, ENNReal.ofReal ‖L y‖ ∂volume.withDensity (fun y => ENNReal.ofReal ‖b y‖)) < ⊤) :
    Integrable (fun y => ⟪L y,b y⟫) := by
  refine ⟨hL.aestronglyMeasurable.inner hb.aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact (potential_norm_lintegral hL hb).trans_lt hfinite

/-- Finiteness of the genuine singular integrals, obtained from the column
estimate itself. This justifies insertion of the finite vector decomposition. -/
theorem kernel_potential_ae_integrable (μ : Measure ℂ) [SFinite μ]
    {K : ℂ × ℂ → ℂ} (hK : Measurable K) {b : ℂ → ℂ} (hb : Integrable b)
    {C : ℝ≥0∞} (hC : C < ⊤)
    (hcol : ∀ᵐ y ∂volume.withDensity (fun y => ENNReal.ofReal ‖b y‖),
      (∫⁻ x, (ENNReal.ofReal ‖K (x,y)‖)^(3/2:ℝ) ∂μ) ≤ C) :
    ∀ᵐ x ∂μ, Integrable (fun y => ⟪K (x,y),b y⟫) := by
  let ν := volume.withDensity (fun y => ENNReal.ofReal ‖b y‖)
  have hm : ν univ = ENNReal.ofReal (∫ y, ‖b y‖) := by
    dsimp only [ν]
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact (ofReal_integral_eq_lintegral_ofReal hb.norm
      (ae_of_all _ (fun _ => norm_nonneg _))).symm
  have hν : ν univ < ⊤ := by rw [hm]; exact ENNReal.ofReal_lt_top
  have : IsFiniteMeasure ν := ⟨hν⟩
  have hlp := kernel_column_lp μ ν hK.norm.ennreal_ofReal hcol
  have hfinite : (∫⁻ x, (∫⁻ y, ENNReal.ofReal ‖K (x,y)‖ ∂ν)^(3/2:ℝ) ∂μ) ≠ ⊤ :=
    ne_of_lt (hlp.trans_lt (ENNReal.mul_lt_top hC (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hν.ne)))
  have hae := ae_lt_top (hK.norm.ennreal_ofReal.lintegral_prod_right.pow_const _) hfinite
  filter_upwards [hae] with x hx
  apply potential_integrable_of_density (hK.comp (measurable_const.prodMk measurable_id)) hb
  apply lt_top_iff_ne_top.mpr
  intro htop
  change (∫⁻ y, ENNReal.ofReal ‖K (x,y)‖ ∂ν) = ⊤ at htop
  rw [htop,ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < 3/2)] at hx
  exact (lt_irrefl _ hx)

lemma green_root_column {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X Y B : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hXY : 0 < X+Y) {y : ℂ} (hy : ‖y‖ ≤ Y) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X}, (ENNReal.ofReal ‖green ψ x y‖)^(3/2:ℝ)) ≤
    ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(2*(X+Y))^(1/2:ℝ))) := by
  apply kernel_near_three_halves (by positivity) (by positivity : 0 < 2*(X+Y)) y
  · intro x hx
    rw [mem_ball,dist_eq_norm]
    have hn := norm_sub_le x y
    change ‖x‖ ≤ X at hx
    linarith
  · intro x hx
    exact green_size_all hψm hψs hψB hM hB hx

lemma green_ae_integrable {ψ : ℂ → ℝ} {β : ℂ → ℂ}
    (hψm : Measurable ψ) {R X Y B : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hXY : 0 < X+Y)
    (hβ : Integrable β) (hβs : ∀ y, β y ≠ 0 → ‖y‖ ≤ Y) :
    ∀ᵐ x ∂volume.restrict {x : ℂ | ‖x‖ ≤ X}, Integrable (fun y => ⟪green ψ x y,β y⟫) := by
  apply kernel_potential_ae_integrable _ (green_measurable ψ hψm) hβ ENNReal.ofReal_lt_top
  rw [ae_withDensity_iff' hβ.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal]
  filter_upwards with y hy
  apply green_root_column hψm hψs hψB hM hB hXY
  apply hβs y
  intro hy0
  simp [hy0] at hy

lemma green_root_lp {ψ : ℂ → ℝ} {β : ℂ → ℂ}
    (hψm : Measurable ψ) {R X Y B : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hXY : 0 < X+Y)
    (hβ : Integrable β) (hβs : ∀ y, β y ≠ 0 → ‖y‖ ≤ Y) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X}, (ENNReal.ofReal |∫ y, ⟪green ψ x y,β y⟫|)^(3/2:ℝ)) ≤
    ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(2*(X+Y))^(1/2:ℝ))) *
      (ENNReal.ofReal (∫ y, ‖β y‖))^(3/2:ℝ) := by
  let ν := volume.withDensity (fun y => ENNReal.ofReal ‖β y‖)
  have hν : ν univ = ENNReal.ofReal (∫ y, ‖β y‖) := by
    dsimp only [ν]
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact (ofReal_integral_eq_lintegral_ofReal hβ.norm
      (ae_of_all _ (fun _ => norm_nonneg _))).symm
  have : IsFiniteMeasure ν := ⟨by rw [hν]; exact ENNReal.ofReal_lt_top⟩
  have hm := green_measurable ψ hψm
  have hcol := kernel_column_lp (volume.restrict {x : ℂ | ‖x‖ ≤ X}) ν hm.norm.ennreal_ofReal
    (C := ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(2*(X+Y))^(1/2:ℝ)))) (by
      rw [ae_withDensity_iff' hβ.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal]
      filter_upwards with y hy
      apply green_root_column hψm hψs hψB hM hB hXY
      apply hβs y
      intro hy0
      simp [hy0] at hy)
  rw [hν] at hcol
  apply le_trans _ hcol
  apply lintegral_mono
  intro x
  exact ENNReal.rpow_le_rpow (potential_domination
    (hm.comp (measurable_const.prodMk measurable_id)) hβ) (by norm_num)

lemma eLpNorm_three_halves_bound (μ : Measure ℂ) {F : ℂ → ℝ} {K m : ℝ≥0∞}
    (h : (∫⁻ x, (ENNReal.ofReal |F x|)^(3/2:ℝ) ∂μ) ≤ K*m^(3/2:ℝ)) :
    eLpNorm' F (3/2:ℝ) μ ≤ K^(2/3:ℝ)*m := by
  rw [eLpNorm'_eq_lintegral_enorm]
  norm_num only [one_div_div]
  have hpow := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 2/3)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2/3),← ENNReal.rpow_mul] at hpow
  norm_num only [show (3/2:ℝ)*(2/3)=1 by norm_num,ENNReal.rpow_one] at hpow
  simpa only [← ofReal_norm,Real.norm_eq_abs] using hpow

lemma potential_aestronglyMeasurable (μ : Measure ℂ) {K : ℂ × ℂ → ℂ}
    (hK : Measurable K) {β : ℂ → ℂ} (hβ : Integrable β) :
    AEStronglyMeasurable (fun x => ∫ y, ⟪K (x,y),β y⟫) μ := by
  have h : AEStronglyMeasurable (fun z : ℂ × ℂ => @inner ℝ ℂ _ (K z) (β z.2)) (μ.prod volume) :=
    hK.aestronglyMeasurable.inner hβ.aestronglyMeasurable.comp_snd
  exact h.integral_prod_right'

lemma potential_memLp_of_bound (μ : Measure ℂ) {K : ℂ × ℂ → ℂ}
    (hK : Measurable K) {β : ℂ → ℂ} (hβ : Integrable β) {C m : ℝ≥0∞}
    (hC : C < ⊤) (hm : m < ⊤)
    (h : (∫⁻ x, (ENNReal.ofReal |∫ y, ⟪K (x,y),β y⟫|)^(3/2:ℝ) ∂μ) ≤ C*m^(3/2:ℝ)) :
    MemLp (fun x => ∫ y, ⟪K (x,y),β y⟫) (3/2) μ := by
  rw [memLp_iff, eLpNorm_eq_eLpNorm' (by norm_num : (3/2:ℝ≥0∞) ≠ 0)
    (by finiteness) (potential_aestronglyMeasurable μ hK hβ)]
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_ofNat]
  exact (eLpNorm_three_halves_bound μ h).trans_lt
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hC.ne) hm)

/-- A genuine fixed smooth probability cutoff. Its finite size and Lipschitz
constants depend on no input, no dyadic level and no number of scales. -/
theorem exists_kernel_cutoff : ∃ (ψ : ℂ → ℝ) (B L : ℝ),
    0 ≤ B ∧ 0 ≤ L ∧ ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
    (∫ x, ψ x) = 1 ∧ (∀ x, ψ x ≠ 0 → ‖x‖ ≤ 1) ∧
    (∀ x, |ψ x| ≤ B) ∧ (∀ x y, |ψ x-ψ y| ≤ L*‖x-y‖) := by
  let φ : ContDiffBump (0:ℂ) := ⟨1/2,1,by norm_num,by norm_num⟩
  let ψ := φ.normed volume
  have hc : HasCompactSupport ψ := φ.hasCompactSupport_normed
  have hd : ContDiff ℝ ∞ ψ := φ.contDiff_normed
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuous hd.continuous
  obtain ⟨L,hL⟩ := hd.lipschitzWith_of_hasCompactSupport hc (by simp)
  refine ⟨ψ,B,L,le_trans (norm_nonneg (ψ 0)) (hB 0),L.coe_nonneg,hd,hc,
    φ.integral_normed,?_,?_,?_⟩
  · intro x hx
    have hs : x ∈ Function.support ψ := hx
    rw [φ.support_normed_eq] at hs
    exact (show ‖x‖ < 1 by simpa only [mem_ball,dist_zero_right] using hs).le
  · intro x
    simpa only [Real.norm_eq_abs] using hB x
  · intro x y
    simpa only [Real.norm_eq_abs] using hL.norm_sub_le x y

end PlanePotential

end SignedDisk

end

end OAI
