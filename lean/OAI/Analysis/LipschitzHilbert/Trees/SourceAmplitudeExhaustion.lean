import OAI.Analysis.LipschitzHilbert.Trees.SourceAmplitudeIntegral
import OAI.Analysis.LipschitzHilbert.Trees.SourceLpExhaustion

namespace OAI

/-! A single exhaustion, independent of the complex phase, bounds all
original packet bases and the absolute logarithms along their paths. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace
namespace LipschitzHilbert.AngularGrid
variable {τ σ X κ : Type*} [MeasurableSpace X] [Fintype κ]

def pathLogSize (g : AngularGrid) (mass boundary : ℕ → ℤ → ℝ)
    (lower upper : ℕ) (slope : ℝ) : ℝ :=
  ∑ j ∈ Finset.Ico lower upper,
    |Real.log (mass (j+1) (g.index (j+1) slope)/boundary j (g.index (j+1) slope))|

omit [MeasurableSpace X] [Fintype κ] in
theorem pathLogSize_nonneg (g : AngularGrid) (mass boundary : ℕ → ℤ → ℝ)
    (lower upper : ℕ) (slope : ℝ) : 0 ≤ g.pathLogSize mass boundary lower upper slope :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

omit [MeasurableSpace X] [Fintype κ] in
theorem pathLogCombination_norm_le (g : AngularGrid) (mass boundary : ℕ → ℤ → ℝ)
    (phase : ℕ → ℂ) (lower upper : ℕ) (slope : ℝ) :
    ‖g.pathLogCombination mass boundary phase lower upper slope‖ ≤
      (∑ j ∈ Finset.Ico lower upper, ‖phase j‖)*g.pathLogSize mass boundary lower upper slope := by
  unfold pathLogCombination pathLogSize
  calc
    _ ≤ ∑ j ∈ Finset.Ico lower upper,
        ‖phase j*(Real.log (mass (j+1) (g.index (j+1) slope)/boundary j (g.index (j+1) slope)):ℂ)‖ :=
      norm_sum_le _ _
    _ = ∑ j ∈ Finset.Ico lower upper, ‖phase j‖*
        |Real.log (mass (j+1) (g.index (j+1) slope)/boundary j (g.index (j+1) slope))| := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    _ ≤ ∑ j ∈ Finset.Ico lower upper, (∑ k ∈ Finset.Ico lower upper, ‖phase k‖)*
        |Real.log (mass (j+1) (g.index (j+1) slope)/boundary j (g.index (j+1) slope))| := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun k _ => norm_nonneg (phase k)) hj) (abs_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

def sourceAmplitudeRadius (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) (weight : τ → X → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (a : ℝ) (level : ℕ) (cell : ℤ) (x : X) : ℝ :=
  ∑ s ∈ g.packetSet packets (fun s => slope (assigned s)) stop level cell,
    (‖g.sourcePacketBase tops slope precision cutoff weight assigned stop (value x) a x s‖ +
      g.pathLogSize (fun j c => g.mass tops slope precision cutoff weight j c x)
        (fun j c => g.sourceBoundaryMass tops slope precision cutoff weight K gap j c x)
        level (stop s) (slope (assigned s)))

theorem measurable_sourceAmplitudeRadius (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (hv : ∀ s, Measurable (fun x => value x s))
    (a : ℝ) (level : ℕ) (cell : ℤ) :
    Measurable (g.sourceAmplitudeRadius tops slope precision cutoff weight K gap packets assigned stop value a level cell) := by
  unfold sourceAmplitudeRadius
  apply Finset.measurable_sum
  intro s _
  apply (g.measurable_sourcePacketBase tops slope precision cutoff weight hw assigned stop value hv a s).norm.add
  unfold pathLogSize
  apply Finset.measurable_sum
  intro j _
  simpa only [Real.norm_eq_abs,Pi.div_apply] using ((g.measurable_mass tops slope precision cutoff weight hw _ _).div
    (g.measurable_sourceBoundaryMass tops slope precision cutoff weight hw K gap _ _)).log.norm

omit [MeasurableSpace X] in
theorem sourceAmplitudeRadius_base_le (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (a : ℝ) (level : ℕ) (cell : ℤ)
    (s : σ) (hs : s ∈ g.packetSet packets (fun s => slope (assigned s)) stop level cell) (x : X) :
    ‖g.sourcePacketBase tops slope precision cutoff weight assigned stop (value x) a x s‖ ≤
      g.sourceAmplitudeRadius tops slope precision cutoff weight K gap packets assigned stop value a level cell x := by
  unfold sourceAmplitudeRadius
  let B := fun t => ‖g.sourcePacketBase tops slope precision cutoff weight assigned stop (value x) a x t‖
  let Q := fun t => g.pathLogSize (fun j c => g.mass tops slope precision cutoff weight j c x)
    (fun j c => g.sourceBoundaryMass tops slope precision cutoff weight K gap j c x)
    level (stop t) (slope (assigned t))
  have hQ (t : σ) : 0 ≤ Q t := g.pathLogSize_nonneg _ _ _ _ _
  change B s ≤ ∑ t ∈ g.packetSet packets (fun t => slope (assigned t)) stop level cell, (B t+Q t)
  exact (le_add_of_nonneg_right (hQ s)).trans (Finset.single_le_sum
    (fun t _ => add_nonneg (norm_nonneg _) (hQ t)) hs)

omit [MeasurableSpace X] in
theorem sourceAmplitudeRadius_log_le (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (a : ℝ) (level : ℕ) (cell : ℤ)
    (s : σ) (hs : s ∈ g.packetSet packets (fun s => slope (assigned s)) stop level cell) (x : X) :
    g.pathLogSize (fun j c => g.mass tops slope precision cutoff weight j c x)
        (fun j c => g.sourceBoundaryMass tops slope precision cutoff weight K gap j c x)
        level (stop s) (slope (assigned s)) ≤
      g.sourceAmplitudeRadius tops slope precision cutoff weight K gap packets assigned stop value a level cell x := by
  unfold sourceAmplitudeRadius
  let B := fun t => ‖g.sourcePacketBase tops slope precision cutoff weight assigned stop (value x) a x t‖
  let Q := fun t => g.pathLogSize (fun j c => g.mass tops slope precision cutoff weight j c x)
    (fun j c => g.sourceBoundaryMass tops slope precision cutoff weight K gap j c x)
    level (stop t) (slope (assigned t))
  have hB (t : σ) : 0 ≤ B t := norm_nonneg _
  have hQ (t : σ) : 0 ≤ Q t := g.pathLogSize_nonneg _ _ _ _ _
  change Q s ≤ ∑ t ∈ g.packetSet packets (fun t => slope (assigned t)) stop level cell, (B t+Q t)
  exact (le_add_of_nonneg_left (hB s)).trans (Finset.single_le_sum
    (fun t _ => add_nonneg (hB t) (hQ t)) hs)

theorem sourcePacketAmplitude_integral_entire_on_exhaustion
    (μ : Measure X) [IsFiniteMeasure μ] (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (hv : ∀ s, Measurable (fun x => value x s))
    (a : ℝ) (level : ℕ) (cell : ℤ) (n : ℕ) (offset direction : ℕ → ℂ)
    (b : X → EuclideanSpace ℂ κ) (hb : Measurable b) (T : ℝ) (hbT : ∀ x, ‖b x‖ ≤ T) :
    Differentiable ℂ (fun z => ∫ x in sourceExhaustion
      (g.sourceAmplitudeRadius tops slope precision cutoff weight K gap packets assigned stop value a level cell) n,
      ⟪b x,g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) (fun j => offset j+z*direction j) a x level cell⟫_ℂ ∂μ) := by
  let R := g.sourceAmplitudeRadius tops slope precision cutoff weight K gap packets assigned stop value a level cell
  let P := fun (phase : ℕ → ℂ) (s : σ) => ∑ j ∈ Finset.Ico level (stop s), ‖phase j‖
  have hP (phase : ℕ → ℂ) (s : σ) : 0 ≤ P phase s := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hlog (phase : ℕ → ℂ) (s : σ)
      (hs : s ∈ g.packetSet packets (fun s => slope (assigned s)) stop level cell)
      (x : X) (hx : x ∈ sourceExhaustion R n) :
      ‖g.sourcePathLog tops slope precision cutoff weight K gap phase level (stop s)
        (slope (assigned s)) x‖ ≤ P phase s*(n:ℝ) := by
    apply (g.pathLogCombination_norm_le _ _ phase level (stop s) (slope (assigned s))).trans
    apply mul_le_mul_of_nonneg_left _ (hP phase s)
    exact (g.sourceAmplitudeRadius_log_le tops slope precision cutoff weight K gap packets
      assigned stop value a level cell s hs x).trans hx
  apply g.sourcePacketAmplitude_integral_affine_entire_on μ tops slope precision cutoff weight hw
    K gap packets assigned stop value hv offset direction a level cell (sourceExhaustion R n)
    (sourceExhaustion_measurable R (g.measurable_sourceAmplitudeRadius tops slope precision cutoff
      weight hw K gap packets assigned stop value hv a level cell) n)
    (fun _ => (n:ℝ)) (fun s => (P offset s+P direction s)*(n:ℝ))
    (fun _ _ => Nat.cast_nonneg _) (fun s _ => mul_nonneg (add_nonneg (hP offset s) (hP direction s)) (Nat.cast_nonneg _))
    _ _ _ b hb T hbT
  · intro s hs x hx
    exact (g.sourceAmplitudeRadius_base_le tops slope precision cutoff weight K gap packets
      assigned stop value a level cell s hs x).trans hx
  · intro s hs x hx
    exact (hlog offset s hs x hx).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (hP direction s)) (Nat.cast_nonneg _))
  · intro s hs x hx
    exact (hlog direction s hs x hx).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (hP offset s)) (Nat.cast_nonneg _))

end LipschitzHilbert.AngularGrid

end

end OAI
