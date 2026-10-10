import OAI.Geometry.QuadricBundles.TraceMetrics

namespace OAI

noncomputable section

namespace QuadricCounterexample
open Set Filter Topology Metric MeasureTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
noncomputable section
local instance : TopologicalSpace.PseudoMetrizableSpace TwoMatrix :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))

abbrev TraceIndex := StandardChart × ℕ
abbrev CoefficientSpace := EuclideanSpace ℂ (Fin 2 × Fin 2)
abbrev CoefficientL2 := Lp CoefficientSpace 2 (volume : Measure BaseCoordinates)
def traceInterior (a : TraceIndex) : Set BaseCoordinates := ball 0 ((a.2:ℝ)+2)
def traceDomain (a : TraceIndex) : Set BaseCoordinates := ball 0 ((a.2:ℝ)+3)
def traceSupport (a : TraceIndex) : Set BaseCoordinates := closedBall 0 ((a.2:ℝ)+4)
def traceBound (D : EqualizerData) (a : TraceIndex) : ℝ :=
  (TwistedPshForm.local_bound D a.1 ((a.2:ℝ)+4)).choose
lemma traceBound_nonneg (D : EqualizerData) (a : TraceIndex) : 0≤traceBound D a :=
  (TwistedPshForm.local_bound D a.1 ((a.2:ℝ)+4)).choose_spec.1
lemma traceBound_spec (D : EqualizerData) (a : TraceIndex) (m : ℕ) (hm : 0 < m)
    (P : TwistedPshForm D m) (hP : ∀ i z, ‖z‖≤1 → ∀ v, P.value i (z,v)≤‖v‖^2)
    (z : BaseCoordinates) (hz : z∈traceSupport a) (v : FiberCoordinates) :
    P.value a.1 (z,v)≤traceBound D a*‖v‖^2 :=
  (TwistedPshForm.local_bound D a.1 ((a.2:ℝ)+4)).choose_spec.2 m hm P hP z
    (by simpa only [traceSupport,mem_closedBall,dist_zero_right] using hz) v

def cutoffTrace {D : EqualizerData} {m : ℕ} (P : TwistedPshForm D m) (a : TraceIndex) :
    BaseCoordinates → TwoMatrix := (traceSupport a).indicator (P.matrix a.1)

lemma cutoffTrace_eq {D : EqualizerData} {m : ℕ} (P : TwistedPshForm D m) (a : TraceIndex)
    {z : BaseCoordinates} (hz : z∈traceSupport a) : cutoffTrace P a z=P.matrix a.1 z :=
  indicator_of_mem hz _
lemma traceDomain_subset_support (a : TraceIndex) : traceDomain a ⊆ traceSupport a :=
  ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
lemma traceInterior_subset_domain (a : TraceIndex) : traceInterior a ⊆ traceDomain a :=
  ball_subset_ball (by linarith)

structure ExtractedTrace {D : EqualizerData} (ex : ℕ → ℕ) (P : ∀ k, TwistedPshForm D (ex k)) where
  matrix : TraceIndex → BaseCoordinates → TwoMatrix
  f : ℕ → TraceIndex → CoefficientL2
  w : TraceIndex → CoefficientL2
  subsequence : ℕ → ℕ
  strictMono : StrictMono subsequence
  coefficients : ∀ k a, (fun x ↦ coefficientsToMatrix (f k a x)) =ᵐ[volume] cutoffTrace (P k) a
  bound : ∀ k a, ∀ᵐ x ∂volume, ‖f k a x‖≤8*traceBound D a ∧
    (x∉traceSupport a → f k a x=0)
  representative : ∀ a, matrix a =ᵐ[volume.restrict (traceInterior a)]
    fun x ↦ coefficientsToMatrix (w a x)
  weak : ∀ a v, Tendsto (fun k ↦ inner ℂ (f (subsequence k) a) v) atTop (𝓝 (inner ℂ (w a) v))
  positive : ∀ a x, x∈traceInterior a → (matrix a x).PosSemidef
  psh : ∀ a, DiskPshOn (traceInterior a ×ˢ univ)
    (fun p : BaseCoordinates × FiberCoordinates ↦ quadraticValue (matrix a p.1) p.2)
  averages : ∀ a x r v, ball x r ⊆ traceInterior a →
    Tendsto (fun k ↦ ⨍ y in ball x r, quadraticValue (cutoffTrace (P (subsequence k)) a y) v)
      atTop (𝓝 (⨍ y in ball x r, quadraticValue (matrix a y) v))

lemma exists_extractedTrace {D : EqualizerData} {ex : ℕ → ℕ} (hex : ∀ k, 0 < ex k)
    (P : ∀ k, TwistedPshForm D (ex k))
    (hP : ∀ k i z, ‖z‖≤1 → ∀ v, (P k).value i (z,v)≤‖v‖^2) :
    Nonempty (ExtractedTrace ex P) := by
  let H (k : ℕ) (a : TraceIndex) := cutoffTrace (P k) a
  have heq (k : ℕ) (a : TraceIndex) : EqOn
      (fun p : BaseCoordinates × FiberCoordinates ↦ quadraticValue (H k a p.1) p.2)
      ((P k).value a.1) (traceDomain a ×ˢ univ) := by
    intro p hp
    change quadraticValue (H k a p.1) p.2 = quadraticValue ((P k).matrix a.1 p.1) p.2
    rw [show H k a p.1=(P k).matrix a.1 p.1 from cutoffTrace_eq _ _ (traceDomain_subset_support a hp.1)]
  have hmeas (k : ℕ) (a : TraceIndex) : AEStronglyMeasurable (H k a) :=
    ((P k).continuous a.1).aestronglyMeasurable.indicator measurableSet_closedBall
  have hpos (k : ℕ) (a : TraceIndex) : ∀ᵐ x ∂volume, (H k a x).PosSemidef := by
    apply Eventually.of_forall; intro x
    by_cases hx : x∈traceSupport a
    · rw [show H k a x=(P k).matrix a.1 x from cutoffTrace_eq _ _ hx]
      exact ((P k).positive a.1 x).posSemidef
    · simp only [H,cutoffTrace,indicator_of_notMem hx]
      exact Matrix.PosSemidef.zero
  have hcont (k : ℕ) (a : TraceIndex) : ContinuousOn
      (fun p : BaseCoordinates × FiberCoordinates ↦ quadraticValue (H k a p.1) p.2)
      (traceDomain a ×ˢ univ) := ((P k).value_continuous a.1).continuousOn.congr (heq k a)
  have hpsh (k : ℕ) (a : TraceIndex) : DiskPshOn (traceDomain a ×ˢ univ)
      (fun p : BaseCoordinates × FiberCoordinates ↦ quadraticValue (H k a p.1) p.2) :=
    (((P k).psh a.1).mono (subset_univ _)).congr (heq k a).symm
  have hb (k : ℕ) (a : TraceIndex) : ∀ᵐ x ∂volume,
      ‖matrixToCoefficients (H k a x)‖≤8*traceBound D a ∧ (x∉traceSupport a → H k a x=0) := by
    apply Eventually.of_forall; intro x
    by_cases hx : x∈traceSupport a
    · rw [show H k a x=(P k).matrix a.1 x from cutoffTrace_eq _ _ hx]
      exact ⟨norm_coefficients_of_quadratic_bound ((P k).positive a.1 x).posSemidef
        (traceBound_nonneg D a) (traceBound_spec D a (ex k) (hex k) (P k) (hP k) x hx),
        fun hn ↦ (hn hx).elim⟩
    · simp only [H,cutoffTrace,indicator_of_notMem hx,map_zero,norm_zero]
      exact ⟨mul_nonneg (by norm_num) (traceBound_nonneg D a),fun _ ↦ trivial⟩
  let r (_ : TraceIndex) (k : ℕ) : ℝ := 1/(k+1)
  have hr (a : TraceIndex) (k : ℕ) : 0 < r a k := by dsimp [r]; positivity
  have hr0 (a : TraceIndex) : Tendsto (r a) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hballs (a : TraceIndex) (k : ℕ) : ∀ x∈traceInterior a, closedBall x (r a k) ⊆ traceDomain a := by
    intro x hx
    apply closedBall_subset_ball'
    have hxr : dist x 0 < (a.2:ℝ)+2 := hx
    have hrle : r a k≤1 := by
      dsimp [r]
      rw [div_le_one (by positivity)]
      exact le_add_of_nonneg_left (Nat.cast_nonneg k)
    linarith
  have hbound (k : ℕ) (a : TraceIndex) : ∀ x∈traceDomain a, ∀ v,
      quadraticValue (H k a x) v≤traceBound D a*‖v‖^2 := by
    intro x hx v
    rw [show H k a x=(P k).matrix a.1 x from cutoffTrace_eq _ _ (traceDomain_subset_support a hx)]
    exact traceBound_spec D a (ex k) (hex k) (P k) (hP k) x (traceDomain_subset_support a hx) v
  obtain ⟨M,f,w,φ,hφ,hf,hfb,hlim⟩ := countable_local_quadratic_compactness_with_weak
    (fun _ ↦ isOpen_ball) (fun _ ↦ isOpen_ball) (fun _ ↦ measurableSet_closedBall)
    (fun _ ↦ measure_closedBall_lt_top.ne) hmeas hpos hcont hpsh
    (fun a ↦ mul_nonneg (by norm_num) (traceBound_nonneg D a)) hb hr hr0 hballs hbound
  exact ⟨{
    matrix := M, f := f, w := w, subsequence := φ, strictMono := hφ
    coefficients := hf, bound := hfb, representative := fun a ↦ (hlim a).1
    weak := fun a ↦ (hlim a).2.1, positive := fun a ↦ (hlim a).2.2.1
    psh := fun a ↦ (hlim a).2.2.2.1, averages := fun a ↦ (hlim a).2.2.2.2 }⟩
end
end QuadricCounterexample

end

end OAI
