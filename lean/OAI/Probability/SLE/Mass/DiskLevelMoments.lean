import OAI.Probability.SLE.Geometry.PhysicalCenteredWeights
import OAI.Probability.SLE.Mass.CompactLevelMoments
import OAI.Probability.SLE.Angle.TargetPotentialMeasurability

namespace OAI

/-! Centered level moments in the prescribed physical disk. The radius
cap and spatial kernel are independent of the chart angle. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped NNReal ENNReal

namespace SLEExactGauge.Multipoint

def diskStoppedGreen {Ω : Type*} (κ θ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℝ) (ω : Ω) (x : ℂ) : ℝ :=
  ‖deriv (Target.diskMap θ) (Target.diskMapInv θ x)‖^(-codimension κ) *
    stoppedGreen κ (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (Target.diskMapInv θ x) u

def diskLevelMass {Ω : Type*} (κ θ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℝ) (K : Set ℂ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ x in K, ENNReal.ofReal (diskStoppedGreen κ θ B γ G u ω x)

def diskCenterHit {Ω : Type*} (γ : Ω → ℝ≥0 → ℂ)
    (G : Ω → ℝ≥0 → ℂ → ℂ) (θ e : ℝ) : Set Ω :=
  {ω | ∃ t : ℝ≥0, Target.diskMapInv θ 0 ∈ survivingDomain (γ ω) t ∧
    physicalConformalRadius (Target.diskMap θ) (G ω) t (Target.diskMapInv θ 0) ≤ e}

lemma diskStoppedGreen_nonneg {Ω : Type*} {κ θ : ℝ} {B : ℝ≥0 → Ω → ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {G F : Ω → ℝ≥0 → ℂ → ℂ}
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (u : ℝ) (ω : Ω) (x : ℂ) : 0 ≤ diskStoppedGreen κ θ B γ G u ω x :=
  mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (stoppedGreen_nonneg (hw ω) κ _ _)

lemma measurable_diskStoppedGreen
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ θ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω)) :
    Measurable (Function.uncurry (diskStoppedGreen κ θ B γ G u)) := by
  have hi : Measurable (fun p : Ω × ℂ => Target.diskMapInv θ p.2) :=
    (Target.measurable_diskMapInv θ).comp measurable_snd
  have hd : Measurable (fun p : Ω × ℂ =>
      ‖deriv (Target.diskMap θ) (Target.diskMapInv θ p.2)‖^(-codimension κ)) :=
    ((measurable_deriv (Target.diskMap θ)).comp hi).norm.pow_const _
  exact hd.mul ((actual_stoppedGreen_joint_measurable hm hc κ u hu γ G F hw).comp
    (measurable_fst.prodMk hi))

lemma measurableSet_diskCenterHit
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (e : ℝ) (he : 0<e) (he1 : e≤1) : MeasurableSet (diskCenterHit γ G θ e) := by
  have hu : 0 ≤ Real.log (1/e) := Real.log_nonneg ((one_le_div he).mpr he1)
  have hτ := (actual_radiusLevel_joint_measurable hm hc κ (Real.log (1/e)) hu γ G F hw).comp
    (measurable_id.prodMk (measurable_const : Measurable (fun _ : Ω => Target.diskMapInv θ 0)))
  have heq : diskCenterHit γ G θ e =
      {ω | radiusLevelTime (γ ω) (G ω) (Target.diskMapInv θ 0) (Real.log (1/e)) < ∞} := by
    ext ω
    exact physical_radius_hit_iff_finite_level ((hc ω).const_mul _) (hw ω)
      (Target.diskMap θ) (Target.diskMapInv θ 0) 1 e zero_lt_one he he1
      (Target.initialRadius_zero hθ).symm
  rw [heq]
  exact measurableSet_lt hτ measurable_const

theorem diskStoppedGreen_centered_product_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    {κ : ℝ} (hκ : 0<κ) (hκ8 : κ<8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (m : ℕ)
    (x : Fin m → ℂ) (hx : ∀ i, x i ∈ ball 0 1)
    (hinj : Function.Injective (Fin.cons (0:ℂ) x))
    (b : ℝ) (hb : 0<b) (hb1 : b≤1) (hbx : ∀ i, b≤1-‖x i‖^2)
    (e : ℝ) (he : 0<e) (u : ℝ) :
    (∫⁻ ω, (diskCenterHit γ G θ e).indicator
      (fun ω => ENNReal.ofReal (∏ i, diskStoppedGreen κ θ B γ G u ω (x i))) ω ∂P) ≤
      ENNReal.ofReal (multipointConstant κ (m+1)*e^codimension κ) *
        cappedDistanceKernel (codimension κ) b (Fin.cons 0 x) := by
  let y : Fin (m+1) → ℂ := Fin.cons (0:ℂ) x
  let z := fun i => Target.diskMapInv θ (y i)
  have hy (i) : y i ∈ ball 0 1 := Fin.cases (by change (0:ℂ)∈ball 0 1; simp) hx i
  have hz (i) : z i ∈ upperHalfPlane := Target.diskMapInv_maps hθ (hy i)
  have heq (i) : Target.diskMap θ (z i)=y i := Target.diskMap_diskMapInv hθ (hy i)
  have hzi : Function.Injective z := fun i j h => hinj (by
    simpa only [heq] using congrArg (Target.diskMap θ) h)
  have hbR (i) : b≤2*(z i).im*‖deriv (Target.diskMap θ) (z i)‖ := by
    rw [Target.diskMap_initial_radius hθ (hz i),heq]
    exact Fin.cases (by simpa only [y,Fin.cons_zero,norm_zero,pow_two,mul_zero,sub_zero] using hb1) hbx i
  let es : Fin (m+1) → ℝ := Fin.cons e
    (fun i => (2*(z i.succ).im*‖deriv (Target.diskMap θ) (z i.succ)‖)*Real.exp (-u))
  have hes (i) : 0<es i := Fin.cases he (fun i =>
    mul_pos (hb.trans_le (hbR i.succ)) (Real.exp_pos _)) i
  have hu (i : Fin m) : Real.log
      (2*(z i.succ).im*‖deriv (Target.diskMap θ) (z i.succ)‖/es i.succ)=u := by
    change Real.log ((2*(z i.succ).im*‖deriv (Target.diskMap θ) (z i.succ)‖)/
      ((2*(z i.succ).im*‖deriv (Target.diskMap θ) (z i.succ)‖)*Real.exp (-u)))=u
    rw [div_mul_eq_div_div,div_self (hb.trans_le (hbR i.succ)).ne',one_div,← Real.exp_neg,
      neg_neg,Real.log_exp]
  have hbound := physical_stoppedGreen_centered_product_bound hB hm hBm hc h0 hκ hκ8
    γ G F hw hgrowth (Target.diskMap θ) (Target.diskMap_differentiableOn hθ)
    (Target.diskMap_injOn hθ) m z hz hzi (cappedDistance b y) es hes
    (fun i => cap_pos hb hinj i) (fun i => (cap_le_fixed b y i).trans (hbR i))
    (fun i j hij => by simpa only [heq] using cap_le_dist b y i j hij)
  simp only [hu,es,Fin.cons_zero] at hbound
  apply hbound.trans_eq
  rw [ENNReal.ofReal_mul (mul_nonneg (multipointConstant_pos _ _).le
    (Real.rpow_nonneg he.le _))]
  congr 1
  exact ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (cap_pos hb hinj i).le _)

end SLEExactGauge.Multipoint

end

end OAI
