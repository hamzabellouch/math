import OAI.GroupTheory.PolycyclicRecognition.Geometry.SupportFlowLegs
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarsePathConcatenation

namespace OAI

/-! # Outward, switch, and return paths

The actual three curves are concatenated, retaining their exact heights and
the logarithmic switch error. This statement is independent of how the
switch estimate is obtained and is used below for the Cartan root curves.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped unitInterval

variable {G W : Type*} [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G] [AddCommGroup W] [Module ℝ W]

def flowPath (d : ℝ → G) (hd : Continuous d) (hzero : d 0 = 1) (x : G) (r : ℝ) :
    Path x (x * d r) where
  toFun t := flowLeg d x r t
  continuous_toFun := continuous_const.mul (hd.comp (continuous_const.mul continuous_subtype_val))
  source' := by simp [flowLeg, hzero]
  target' := by simp [flowLeg]

/-- The specified outward-switch-return path, with no choice of curves. -/
def supportVisitPath (d : ℝ → G) (hd : Continuous d) (hzero : d 0 = 1)
    (f : ℝ → G) (hf : Continuous f) (hf₀ : f 0 = 1) (n d₀ : G) (r b : ℝ) :
    Path (n * d₀) (n * f b * d₀) :=
  let p₀ := flowPath d hd hzero (n * d₀) r
  let p₁ := flowPath d hd hzero (n * f b * d₀) r
  let q : Path ((n * d₀) * d r) ((n * f b * d₀) * d r) := {
    toFun := fun t => n * f ((t : ℝ) * b) * (d₀ * d r)
    continuous_toFun := (continuous_const.mul
      (hf.comp (continuous_subtype_val.mul continuous_const))).mul continuous_const
    source' := by simp [hf₀, mul_assoc]
    target' := by simp [mul_assoc] }
  (p₀.trans q).trans p₁.symm

omit [IsIsometricSMul G G] in
/-- Pointwise changes of representation preserve the specified visit curve. -/
theorem supportVisitPath_apply_congr
    (d d' f f' : ℝ → G) (hd : Continuous d) (hd' : Continuous d')
    (hd₀ : d 0 = 1) (hd₀' : d' 0 = 1)
    (hf : Continuous f) (hf' : Continuous f') (hf₀ : f 0 = 1) (hf₀' : f' 0 = 1)
    (he_d : ∀ t, d t = d' t) (he_f : ∀ t, f t = f' t)
    (n k k' : G) (he_k : k = k') (r b : ℝ) (t : unitInterval) :
    supportVisitPath d hd hd₀ f hf hf₀ n k r b t =
      supportVisitPath d' hd' hd₀' f' hf' hf₀' n k' r b t := by
  obtain rfl := funext he_d
  obtain rfl := funext he_f
  obtain rfl := he_k
  rfl

omit [IsIsometricSMul G G] in
/-- Every fixed time sample depends continuously on the initial sheet and
the switch amplitude. -/
theorem continuous_supportVisitPath_sample
    (d : ℝ → G) (hd : Continuous d) (hzero : d 0 = 1)
    (f : ℝ → G) (hf : Continuous f) (hf₀ : f 0 = 1)
    {Y : Type*} [TopologicalSpace Y] (n : Y → G) (hn : Continuous n)
    (b : Y → ℝ) (hb : Continuous b) (d₀ : G) (r : ℝ) (t : unitInterval) :
    Continuous (fun y => supportVisitPath d hd hzero f hf hf₀ (n y) d₀ r (b y) t) := by
  let p₀ y := flowPath d hd hzero (n y * d₀) r
  let p₁ y := flowPath d hd hzero (n y * f (b y) * d₀) r
  let q (y : Y) : Path ((n y * d₀) * d r) ((n y * f (b y) * d₀) * d r) := {
    toFun := fun t => n y * f ((t : ℝ) * b y) * (d₀ * d r)
    continuous_toFun := (continuous_const.mul
      (hf.comp (continuous_subtype_val.mul continuous_const))).mul continuous_const
    source' := by simp [hf₀, mul_assoc]
    target' := by simp [mul_assoc] }
  have hp₀ (u : unitInterval) : Continuous (fun y => p₀ y u) := by
    change Continuous (fun y => (n y * d₀) * d (r * (u : ℝ)))
    exact (hn.mul_const d₀).mul_const _
  have hp₁ (u : unitInterval) : Continuous (fun y => (p₁ y).symm u) := by
    change Continuous (fun y => (n y * f (b y) * d₀) * d (r * (unitInterval.symm u : ℝ)))
    exact ((hn.mul (hf.comp hb)).mul_const d₀).mul_const _
  have hq (u : unitInterval) : Continuous (fun y => q y u) := by
    change Continuous (fun y => n y * f ((u : ℝ) * b y) * (d₀ * d r))
    exact (hn.mul (hf.comp (continuous_const.mul hb))).mul_const _
  exact continuous_path_trans_sample (fun y => (p₀ y).trans (q y)) (fun y => (p₁ y).symm)
    (fun u => continuous_path_trans_sample p₀ q hp₀ hq u) hp₁ t

/-- Concatenate a support leg, a height-zero switch, and the reverse leg.
The constants are uniform over both the translated sheet and the pivot. -/
theorem supportVisitPath_uniform_bound
    (π : G →* Multiplicative W) (d : ℝ → G) (hd : Continuous d) (hzero : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t)
    {E : Set W} (hE : Convex ℝ E) {w₀ w₁ : W} (hw₀ : w₀ ∈ E) (hw₁ : w₁ ∈ E)
    (hπd : ∀ t, (π (d t)).toAdd = t • (w₁ - w₀)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), 0 ≤ r → ∀ (n d₀ : G),
      π n = 1 → (π d₀).toAdd = r • w₀ →
      ∀ (f : ℝ → G) (hf : Continuous f) (hf₀ : f 0 = 1), (∀ t, π (f t) = 1) →
      ∀ (b κ : ℝ), 0 ≤ κ →
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist (n * f (s * b) * (d₀ * d r)) (n * f (t * b) * (d₀ * d r)) ≤ κ) →
      PathMetricBound (supportVisitPath d hd hzero f hf hf₀ n d₀ r b)
        (4 * C * r) (4 * (C + κ)) ∧
        ∀ t, ∃ w ∈ E,
          (π (supportVisitPath d hd hzero f hf hf₀ n d₀ r b t)).toAdd = r • w := by
  obtain ⟨C, hC, hb⟩ := exists_flowLeg_coarse_bound d hd hzero hmul
  refine ⟨C, hC, ?_⟩
  intro r hr n d₀ hn hd₀ f hf hf₀ hπf b κ hκ hswitch
  let p₀ := flowPath d hd hzero (n * d₀) r
  let p₁ := flowPath d hd hzero (n * f b * d₀) r
  let q : Path ((n * d₀) * d r) ((n * f b * d₀) * d r) := {
    toFun := fun t => n * f ((t : ℝ) * b) * (d₀ * d r)
    continuous_toFun := (continuous_const.mul
      (hf.comp (continuous_subtype_val.mul continuous_const))).mul continuous_const
    source' := by simp [hf₀, mul_assoc]
    target' := by simp [mul_assoc] }
  have hn₀ : (π (n * d₀)).toAdd = r • w₀ := by simpa [hn] using hd₀
  have hn₁ : (π (n * f b * d₀)).toAdd = r • w₀ := by simpa [hn, hπf] using hd₀
  have hp₀ : ∀ t, ∃ w ∈ E, (π (p₀ t)).toAdd = r • w := fun t =>
    flowLeg_height_mem π d hE hw₀ hw₁ hπd hn₀ t.property
  have hp₁ : ∀ t, ∃ w ∈ E, (π (p₁ t)).toAdd = r • w := fun t =>
    flowLeg_height_mem π d hE hw₀ hw₁ hπd hn₁ t.property
  have hq : ∀ t, ∃ w ∈ E, (π (q t)).toAdd = r • w := by
    intro t
    obtain ⟨w, hw, he⟩ := hp₀ 1
    refine ⟨w, hw, ?_⟩
    have he' : π (q t) = π (p₀ 1) := by
      change π (n * f ((t : ℝ) * b) * (d₀ * d r)) = π (flowLeg d (n * d₀) r 1)
      simp [flowLeg, hn, hπf]
    rw [he']
    exact he
  have hp₀b : PathMetricBound p₀ (C * r) (C + κ) := by
    intro s t
    have h := hb (n * d₀) r hr (s : ℝ) (t : ℝ)
    change dist (p₀ s) (p₀ t) ≤ C * r * |(t : ℝ) - s| + C at h
    rw [abs_sub_comm] at h
    linarith
  have hp₁b : PathMetricBound p₁ (C * r) (C + κ) := by
    intro s t
    have h := hb (n * f b * d₀) r hr (s : ℝ) (t : ℝ)
    change dist (p₁ s) (p₁ t) ≤ C * r * |(t : ℝ) - s| + C at h
    rw [abs_sub_comm] at h
    linarith
  have hqb : PathMetricBound q (C * r) (C + κ) := by
    intro s t
    have h := hswitch s s.property t t.property
    change dist (q s) (q t) ≤ κ at h
    have := mul_nonneg (mul_nonneg hC hr) (abs_nonneg ((s : ℝ) - t))
    linarith
  let p := (p₀.trans q).trans p₁.symm
  change PathMetricBound p (4 * C * r) (4 * (C + κ)) ∧
    ∀ t, ∃ w ∈ E, (π (p t)).toAdd = r • w
  constructor
  · have hsum : 0 ≤ C + κ := add_nonneg hC hκ
    have hback : PathMetricBound p₁.symm (2 * (C * r)) (2 * (C + κ)) :=
      hp₁b.symm.mono (by nlinarith [mul_nonneg hC hr]) (by linarith)
    have h := (hp₀b.trans hsum hqb).trans (by positivity) hback
    convert h using 1 <;> ring
  · exact path_trans_range_mem (p := p₀.trans q) (q := p₁.symm)
      (S := {g | ∃ w ∈ E, (π g).toAdd = r • w})
      (path_trans_range_mem hp₀ hq) (fun t => hp₁ (unitInterval.symm t))

/-- The explicit visit path also supplies the existential interface. -/
theorem exists_support_visit_path_bound
    (π : G →* Multiplicative W) (d : ℝ → G) (hd : Continuous d) (hzero : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t)
    {E : Set W} (hE : Convex ℝ E) {w₀ w₁ : W} (hw₀ : w₀ ∈ E) (hw₁ : w₁ ∈ E)
    (hπd : ∀ t, (π (d t)).toAdd = t • (w₁ - w₀)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), 0 ≤ r → ∀ (n d₀ : G),
      π n = 1 → (π d₀).toAdd = r • w₀ →
      ∀ (f : ℝ → G), Continuous f → f 0 = 1 → (∀ t, π (f t) = 1) →
      ∀ (b κ : ℝ), 0 ≤ κ →
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist (n * f (s * b) * (d₀ * d r)) (n * f (t * b) * (d₀ * d r)) ≤ κ) →
      ∃ p : Path (n * d₀) (n * f b * d₀),
        PathMetricBound p (4 * C * r) (4 * (C + κ)) ∧
        ∀ t, ∃ w ∈ E, (π (p t)).toAdd = r • w := by
  obtain ⟨C, hC, hb⟩ := supportVisitPath_uniform_bound π d hd hzero hmul hE hw₀ hw₁ hπd
  refine ⟨C, hC, ?_⟩
  intro r hr n d₀ hn hd₀ f hf hf₀ hπf b κ hκ hswitch
  exact ⟨supportVisitPath d hd hzero f hf hf₀ n d₀ r b,
    hb r hr n d₀ hn hd₀ f hf hf₀ hπf b κ hκ hswitch⟩

end PolycyclicRecognition

end

end OAI
