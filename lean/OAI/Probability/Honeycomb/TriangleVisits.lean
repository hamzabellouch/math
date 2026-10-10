import Mathlib

namespace OAI

/-! Honeycomb triangle chords, visit sums and positive finite means. -/

noncomputable section

open scoped ENNReal Topology
open Filter MeasureTheory

namespace DiskBoundary

structure Vertex where
  j : ℤ
  k : ℤ
  b : Bool
  deriving DecidableEq, Countable

structure Port where
  j : ℤ
  k : ℤ
  dir : Fin 3
  deriving DecidableEq, Countable

def direction : Fin 3 → ℂ
  | 0 => ⟨Real.sqrt 3 / 2, 1 / 2⟩
  | 1 => ⟨-(Real.sqrt 3 / 2), 1 / 2⟩
  | 2 => ⟨0, -1⟩

def U : ℂ := direction 0 - direction 1

def V : ℂ := direction 0 - direction 2

def position (v : Vertex) : ℂ :=
  (v.j : ℂ) * U + (v.k : ℂ) * V + if v.b then direction 0 else 0

def edgeA (p : Port) : Vertex := ⟨p.j, p.k, false⟩

def edgeB (p : Port) : Vertex :=
  match p.dir with
  | 0 => ⟨p.j, p.k, true⟩
  | 1 => ⟨p.j - 1, p.k, true⟩
  | 2 => ⟨p.j, p.k - 1, true⟩

def portPosition (p : Port) : ℂ := (position (edgeA p) + position (edgeB p)) / 2

def Incident (p : Port) (v : Vertex) : Prop := v = edgeA p ∨ v = edgeB p

def Adj (v w : Vertex) : Prop :=
  ∃ p : Port, (v = edgeA p ∧ w = edgeB p) ∨ (v = edgeB p ∧ w = edgeA p)

def BoundaryPort (D : Set Vertex) (p : Port) : Prop :=
  (edgeA p ∈ D ∧ edgeB p ∉ D) ∨ (edgeB p ∈ D ∧ edgeA p ∉ D)

structure PortPath where
  source : Port
  target : Port
  vertices : List Vertex
  nonempty : vertices ≠ []
  nodup : vertices.Nodup
  chain : vertices.IsChain Adj
  first_incident : Incident source (vertices.head nonempty)
  last_incident : Incident target (vertices.getLast nonempty)
  distinct_ports : source ≠ target

namespace PortPath

def length (γ : PortPath) : ℕ := γ.vertices.length

def joints (γ : PortPath) : List ℂ :=
  portPosition γ.source :: (γ.vertices.map position ++ [portPosition γ.target])

def trace (γ : PortPath) : Set ℂ :=
  {z | z ∈ γ.joints} ∪
  {z | ∃ p ∈ γ.joints.zip γ.joints.tail, z ∈ segment ℝ p.1 p.2}

def diameter (γ : PortPath) : ℝ := Metric.diam γ.trace

def height (γ : PortPath) : ℝ :=
  sSup ((fun z : ℂ => |z.im + 1 / 2|) '' γ.trace)

end PortPath

instance : MeasurableSpace PortPath := ⊤
instance : MeasurableSingletonClass PortPath := ⟨fun _ => trivial⟩

def IsChord (D : Set Vertex) (γ : PortPath) : Prop :=
  (∀ v ∈ γ.vertices, v ∈ D) ∧ BoundaryPort D γ.source ∧ BoundaryPort D γ.target

abbrev Chord (D : Set Vertex) := {γ : PortPath // IsChord D γ}

def criticalPoint : ℝ := (Real.sqrt (2 + Real.sqrt 2))⁻¹

def weight (γ : PortPath) : ℝ≥0∞ := ENNReal.ofReal (criticalPoint ^ γ.length)

def pathMeasure {Ω : Type*} [MeasurableSpace Ω] (path : Ω → PortPath) : Measure Ω :=
  Measure.sum (fun γ => weight (path γ) • Measure.dirac γ)

def Normalizable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (E : Set Ω) : Prop :=
  0 < μ E ∧ μ E < ∞

def normalize {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (E : Set Ω) : Measure Ω :=
  (μ E)⁻¹ • μ.restrict E

def dot (z w : ℂ) : ℝ := z.re * w.re + z.im * w.im

def halfPlane : Set Vertex := {v | dot (direction 2) (position v) < 1 / 2}

def wallPort (m : ℤ) : Port := ⟨m, 0, 2⟩

abbrev Arch := {γ : Chord halfPlane //
  γ.val.source = wallPort 0 ∧ ∃ m : ℤ, m ≠ 0 ∧ γ.val.target = wallPort m}

def Arch.path (γ : Arch) : PortPath := γ.val.val

def μ : Measure Arch := pathMeasure Arch.path

def archKernel (m : ℕ) : ℝ≥0∞ :=
  μ {γ | γ.path.target = wallPort (m : ℤ)}

def heightTail (R : ℝ) : ℝ≥0∞ := μ {γ | R < γ.path.height}

def diameterTail (R : ℝ) : ℝ≥0∞ := μ {γ | R < γ.path.diameter}

def diameterWindow (C R : ℝ) : Set Arch :=
  {γ | R ≤ γ.path.diameter ∧ γ.path.diameter ≤ C * R}

def heightWindow (C R : ℝ) : Set Arch :=
  {γ | R ≤ γ.path.height ∧ γ.path.diameter ≤ C * R}

def archMean (E : Set Arch) : ℝ≥0∞ :=
  ∫⁻ γ, (γ.path.length : ℝ≥0∞) ∂normalize μ E

def triangle (R : ℝ) : Set ℂ := {z | ∀ i : Fin 3, dot (direction i) z < R}

def triangleVertices (R : ℝ) : Set Vertex := position ⁻¹' triangle R

def innerVertices (ε R : ℝ) : Set Vertex := triangleVertices ((1 - ε) * R)

def triangleMeasure (R : ℝ) : Measure (Chord (triangleVertices R)) :=
  pathMeasure Subtype.val

def hitsInner (ε R : ℝ) : Set (Chord (triangleVertices R)) :=
  {γ | ∃ v ∈ γ.val.vertices, v ∈ innerVertices ε R}

def triangleLaw (ε R : ℝ) : Measure (Chord (triangleVertices R)) :=
  normalize (triangleMeasure R) (hitsInner ε R)

def visitProbability (ε R : ℝ) (v : Vertex) : ℝ≥0∞ :=
  triangleLaw ε R {γ | v ∈ γ.val.vertices}

def triangleMean (ε R : ℝ) : ℝ≥0∞ :=
  ∫⁻ γ, (γ.val.length : ℝ≥0∞) ∂triangleLaw ε R

def innerCount (ε R : ℝ) (γ : PortPath) : ℕ := by
  classical
  exact (γ.vertices.toFinset.filter (fun v => v ∈ innerVertices ε R)).card

def triangleInnerMean (ε R : ℝ) : ℝ≥0∞ :=
  ∫⁻ γ, (innerCount ε R γ.val : ℝ≥0∞) ∂triangleLaw ε R

def admissibleLevels : Set ℝ := {R | ∃ n : ℤ, R = 1 / 2 + (3 / 2) * n}

def wallFilter : Filter ℝ := atTop ⊓ Filter.principal admissibleLevels

def ComparablePower {ι : Type*} (L : Filter ι) (scale : ι → ℝ)
    (f : ι → ℝ≥0∞) (a : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
    ∀ᶠ t in L, ENNReal.ofReal (c * (scale t) ^ a) ≤ f t ∧
      f t ≤ ENNReal.ofReal (C * (scale t) ^ a)

def HasExponent {ι : Type*} (L : Filter ι) (scale : ι → ℝ)
    (f : ι → ℝ≥0∞) (a : ℝ) : Prop :=
  (∀ᶠ t in L, 0 < f t ∧ f t < ∞) ∧
  Tendsto (fun t => Real.log (f t).toReal / Real.log (scale t)) L (𝓝 a)

def UniformVisitExponent (ε a : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ R in wallFilter, ∀ v ∈ innerVertices ε R,
    0 < visitProbability ε R v ∧ visitProbability ε R v < ∞ ∧
    |Real.log (visitProbability ε R v).toReal / Real.log R - a| < δ

def SharpBoundaryMassAndAnnealedChordLaws : Prop :=
  (AntitoneOn archKernel (Set.Ici 1) ∧
    ComparablePower atTop (fun m : ℕ => (m : ℝ)) archKernel (-(5 / 4 : ℝ)) ∧
    ComparablePower atTop id heightTail (-(1 / 4 : ℝ)) ∧
    ComparablePower atTop id diameterTail (-(1 / 4 : ℝ))) ∧
  (∃ C₀ : ℝ, 1 < C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
    (∀ᶠ R : ℝ in atTop,
      Normalizable μ (diameterWindow C R) ∧ Normalizable μ (heightWindow C R)) ∧
    HasExponent atTop id (fun R => archMean (diameterWindow C R)) (4 / 3) ∧
    HasExponent atTop id (fun R => archMean (heightWindow C R)) (4 / 3)) ∧
  (∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    (∀ᶠ R in wallFilter, Normalizable (triangleMeasure R) (hitsInner ε R)) ∧
    UniformVisitExponent ε (-(2 / 3 : ℝ)) ∧
    HasExponent wallFilter id (triangleMean ε) (4 / 3) ∧
    HasExponent wallFilter id (triangleInnerMean ε) (4 / 3))

@[ext]
theorem Vertex.ext {v w : Vertex} (hj : v.j = w.j)
    (hk : v.k = w.k) (hb : v.b = w.b) : v = w := by
  cases v
  cases w
  cases hj
  cases hk
  cases hb
  rfl

@[ext]
theorem PortPath.ext {γ η : PortPath} (hs : γ.source = η.source)
    (ht : γ.target = η.target) (hv : γ.vertices = η.vertices) : γ = η := by
  cases γ
  cases η
  cases hs
  cases ht
  cases hv
  rfl

instance : Countable PortPath := by
  apply Function.Injective.countable
    (f := fun γ : PortPath => (γ.source, γ.target, γ.vertices))
  intro γ η h
  exact PortPath.ext (congrArg (fun x => x.1) h)
    (congrArg (fun x => x.2.1) h) (congrArg (fun x => x.2.2) h)

theorem PortPath.length_pos (γ : PortPath) : 0 < γ.length := by
  exact List.length_pos_iff.mpr γ.nonempty

theorem criticalPoint_pos : 0 < criticalPoint := by
  unfold criticalPoint
  positivity

theorem criticalPoint_lt_one : criticalPoint < 1 := by
  unfold criticalPoint
  have h : 1 < Real.sqrt (2 + Real.sqrt 2) := by
    apply (Real.lt_sqrt (by norm_num)).mpr
    have := Real.sqrt_nonneg 2
    linarith
  exact (inv_lt_one₀ (by positivity)).mpr h

theorem weight_pos (γ : PortPath) : 0 < weight γ := by
  exact ENNReal.ofReal_pos.mpr (pow_pos criticalPoint_pos _)

theorem weight_lt_top (γ : PortPath) : weight γ < ∞ := ENNReal.ofReal_lt_top

theorem weight_le_one (γ : PortPath) : weight γ ≤ 1 := by
  unfold weight
  rw [ENNReal.ofReal_le_one]
  exact pow_le_one₀ criticalPoint_pos.le criticalPoint_lt_one.le

theorem pathMeasure_apply {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [Countable Ω] (path : Ω → PortPath) (E : Set Ω) :
    pathMeasure path E = ∑' γ, E.indicator (fun γ => weight (path γ)) γ := by
  classical
  rw [pathMeasure, Measure.sum_apply_of_countable]
  apply tsum_congr
  intro γ
  by_cases h : γ ∈ E <;> simp [Measure.smul_apply, Measure.dirac_apply, h]

theorem pathMeasure_singleton {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [Countable Ω] (path : Ω → PortPath) (γ : Ω) :
    pathMeasure path {γ} = weight (path γ) := by
  classical
  rw [pathMeasure_apply]
  simp

theorem lintegral_pathMeasure {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (path : Ω → PortPath) (f : Ω → ℝ≥0∞) :
    ∫⁻ γ, f γ ∂pathMeasure path = ∑' γ, weight (path γ) * f γ := by
  simp [pathMeasure, lintegral_sum_measure, lintegral_smul_measure, lintegral_dirac]

theorem normalize_apply {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (E F : Set Ω) (hF : MeasurableSet F) :
    normalize ν E F = (ν E)⁻¹ * ν (F ∩ E) := by
  simp [normalize, Measure.restrict_apply hF, smul_eq_mul]

theorem normalize_univ {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (E : Set Ω) (hE : Normalizable ν E) :
    normalize ν E Set.univ = 1 := by
  rw [normalize_apply _ _ _ MeasurableSet.univ, Set.univ_inter]
  exact ENNReal.inv_mul_cancel hE.1.ne' hE.2.ne

theorem normalize_isProbabilityMeasure {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (E : Set Ω) (hE : Normalizable ν E) :
    IsProbabilityMeasure (normalize ν E) := ⟨normalize_univ ν E hE⟩

theorem normalized_atom {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [Countable Ω] (path : Ω → PortPath)
    (E : Set Ω) {γ : Ω} (hγ : γ ∈ E) :
    normalize (pathMeasure path) E {γ} =
      (pathMeasure path E)⁻¹ * weight (path γ) := by
  rw [normalize_apply _ _ _ (measurableSet_singleton γ),
    Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr hγ), pathMeasure_singleton]

theorem position_re (v : Vertex) :
    (position v).re = (v.j : ℝ) * Real.sqrt 3 +
      (v.k : ℝ) * (Real.sqrt 3 / 2) + if v.b then Real.sqrt 3 / 2 else 0 := by
  cases v with
  | mk j k b =>
    cases b <;> simp [position, U, V, direction, Complex.mul_re]

theorem position_im (v : Vertex) :
    (position v).im = (v.k : ℝ) * (3 / 2) + if v.b then 1 / 2 else 0 := by
  cases v with
  | mk j k b =>
    cases b <;> norm_num [position, U, V, direction, Complex.mul_im]

theorem edge_displacement (p : Port) :
    position (edgeB p) - position (edgeA p) = direction p.dir := by
  rcases p with ⟨j, k, d⟩
  fin_cases d <;> simp [edgeA, edgeB, position, U, V, direction] <;> ring

theorem direction_normSq (i : Fin 3) : Complex.normSq (direction i) = 1 := by
  have h : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases i <;> norm_num [direction, Complex.normSq_apply] <;> nlinarith

theorem direction_norm (i : Fin 3) : ‖direction i‖ = 1 := by
  have := direction_normSq i
  rw [← Complex.sq_norm] at this
  have := norm_nonneg (direction i)
  nlinarith

theorem edge_length (p : Port) : dist (position (edgeA p)) (position (edgeB p)) = 1 := by
  rw [dist_comm, dist_eq_norm, edge_displacement, direction_norm]

theorem position_injective : Function.Injective position := by
  intro v w h
  rcases v with ⟨j, k, b⟩
  rcases w with ⟨j', k', b'⟩
  have hi := congrArg Complex.im h
  have hr := congrArg Complex.re h
  rw [position_im, position_im] at hi
  rw [position_re, position_re] at hr
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  cases b <;> cases b' <;> simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hi hr ⊢
  · have hk : k = k' := by exact_mod_cast (show (k : ℝ) = k' by linarith)
    subst k'
    have hj : j = j' := by
      exact_mod_cast (show (j : ℝ) = j' by nlinarith)
    subst j'
    rfl
  · have hk : 3 * k = 3 * k' + 1 := by
      exact_mod_cast (show (3 : ℝ) * k = 3 * k' + 1 by linarith)
    omega
  · have hk : 3 * k + 1 = 3 * k' := by
      exact_mod_cast (show (3 : ℝ) * k + 1 = 3 * k' by linarith)
    omega
  · have hk : k = k' := by exact_mod_cast (show (k : ℝ) = k' by linarith)
    subst k'
    have hj : j = j' := by
      exact_mod_cast (show (j : ℝ) = j' by nlinarith)
    subst j'
    rfl

theorem mem_halfPlane_iff (v : Vertex) : v ∈ halfPlane ↔ -1 / 2 < (position v).im := by
  simp only [halfPlane, Set.mem_ofPred_eq, dot, direction, zero_mul, neg_mul,
    one_mul, zero_add]
  constructor <;> intro h <;> linarith

theorem wallPort_position (m : ℤ) :
    portPosition (wallPort m) = ⟨(m : ℝ) * Real.sqrt 3, -1 / 2⟩ := by
  apply Complex.ext <;>
    simp [portPosition, wallPort, edgeA, edgeB, position_re, position_im]
  ring

theorem wallPort_boundary (m : ℤ) : BoundaryPort halfPlane (wallPort m) := by
  left
  norm_num [wallPort, edgeA, edgeB, mem_halfPlane_iff, position_im]

theorem PortPath.source_mem_trace (γ : PortPath) : portPosition γ.source ∈ γ.trace := by
  left
  simp [joints]

theorem PortPath.target_mem_trace (γ : PortPath) : portPosition γ.target ∈ γ.trace := by
  left
  simp [joints]

theorem PortPath.vertex_mem_trace (γ : PortPath) {v : Vertex} (hv : v ∈ γ.vertices) :
    position v ∈ γ.trace := by
  left
  simp only [joints, List.mem_cons, List.mem_append, List.mem_map]
  exact Or.inr (Or.inl ⟨v, hv, rfl⟩)

theorem PortPath.trace_isCompact (γ : PortPath) : IsCompact γ.trace := by
  refine γ.joints.finite_toSet.isCompact.union ?_
  have h := (γ.joints.zip γ.joints.tail).finite_toSet.isCompact_biUnion
    (fun p _ => ?_ : ∀ p ∈ γ.joints.zip γ.joints.tail, IsCompact (segment ℝ p.1 p.2))
  · convert h using 1
    ext z
    simp
  · rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous

theorem PortPath.trace_nonempty (γ : PortPath) : γ.trace.Nonempty :=
  ⟨_, γ.source_mem_trace⟩

theorem Arch.height_le_diameter (γ : Arch) : γ.path.height ≤ γ.path.diameter := by
  have hs : (portPosition γ.path.source).im = -1 / 2 := by
    rw [show γ.path.source = wallPort 0 from γ.property.1, wallPort_position]
  apply csSup_le (γ.path.trace_nonempty.image _)
  rintro _ ⟨z, hz, rfl⟩
  calc
    |z.im + 1 / 2| = |(z - portPosition γ.path.source).im| := by
      congr 1
      simp only [Complex.sub_im, hs]
      ring
    _ ≤ ‖z - portPosition γ.path.source‖ := Complex.abs_im_le_norm _
    _ = dist z (portPosition γ.path.source) := (dist_eq_norm _ _).symm
    _ ≤ γ.path.diameter := Metric.dist_le_diam_of_mem γ.path.trace_isCompact.isBounded
      hz γ.path.source_mem_trace

theorem heightTail_le_diameterTail (R : ℝ) : heightTail R ≤ diameterTail R := by
  apply measure_mono
  intro γ h
  exact lt_of_lt_of_le h (Arch.height_le_diameter γ)

theorem heightTail_antitone : Antitone heightTail := by
  intro R S hRS
  exact measure_mono (fun _ h => lt_of_le_of_lt hRS h)

theorem diameterTail_antitone : Antitone diameterTail := by
  intro R S hRS
  exact measure_mono (fun _ h => lt_of_le_of_lt hRS h)

theorem dot_zero_position (v : Vertex) :
    dot (direction 0) (position v) =
      (3 / 2 : ℝ) * ((v.j : ℝ) + (v.k : ℝ)) + if v.b then 1 else 0 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rcases v with ⟨j, k, b⟩
  cases b <;> simp [dot, direction, position_re, position_im] <;> ring_nf <;>
    simp [hs] <;> ring

theorem dot_one_position (v : Vertex) :
    dot (direction 1) (position v) =
      -((3 / 2 : ℝ) * (v.j : ℝ) + if v.b then 1 / 2 else 0) := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rcases v with ⟨j, k, b⟩
  cases b <;> simp [dot, direction, position_re, position_im] <;> ring_nf <;>
    simp [hs] <;> ring

theorem dot_two_position (v : Vertex) :
    dot (direction 2) (position v) =
      -((3 / 2 : ℝ) * (v.k : ℝ) + if v.b then 1 / 2 else 0) := by
  simp [dot, direction, position_im, mul_comm]

theorem triangle_coordinate_bounds {R : ℝ} {v : Vertex}
    (hv : v ∈ triangleVertices R) :
    -(⌈2 * |R| + 2⌉ : ℤ) ≤ v.j ∧ v.j ≤ ⌈2 * |R| + 2⌉ ∧
    -(⌈2 * |R| + 2⌉ : ℤ) ≤ v.k ∧ v.k ≤ ⌈2 * |R| + 2⌉ := by
  have h0 := hv (0 : Fin 3)
  have h1 := hv (1 : Fin 3)
  have h2 := hv (2 : Fin 3)
  rw [dot_zero_position] at h0
  rw [dot_one_position] at h1
  rw [dot_two_position] at h2
  have hN := Int.le_ceil (2 * |R| + 2)
  have hR := le_abs_self R
  have ha := abs_nonneg R
  have hb : -(⌈2 * |R| + 2⌉ : ℝ) ≤ (v.j : ℝ) ∧
      (v.j : ℝ) ≤ (⌈2 * |R| + 2⌉ : ℤ) ∧
      -(⌈2 * |R| + 2⌉ : ℝ) ≤ (v.k : ℝ) ∧
      (v.k : ℝ) ≤ (⌈2 * |R| + 2⌉ : ℤ) := by
    cases h : v.b <;> simp only [h, Bool.false_eq_true, ↓reduceIte, add_zero] at h0 h1 h2
    all_goals repeat' constructor
    all_goals linarith
  exact_mod_cast hb

theorem triangleVertices_finite (R : ℝ) : (triangleVertices R).Finite := by
  let N : ℤ := ⌈2 * |R| + 2⌉
  let f : triangleVertices R → Set.Icc (-N) N × Set.Icc (-N) N × Bool := fun v =>
    let h := triangle_coordinate_bounds v.property
    (⟨v.val.j, h.1, h.2.1⟩, ⟨v.val.k, h.2.2.1, h.2.2.2⟩, v.val.b)
  have hf : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    have hj : v.val.j = w.val.j := congrArg (fun x => x.1.val) h
    have hk : v.val.k = w.val.k := congrArg (fun x => x.2.1.val) h
    have hb : v.val.b = w.val.b := congrArg (fun x => x.2.2) h
    exact Vertex.ext hj hk hb
  have : Finite (triangleVertices R) := Finite.of_injective f hf
  exact Set.toFinite _

def incidentPorts (v : Vertex) : Finset Port :=
  if v.b then {⟨v.j, v.k, 0⟩, ⟨v.j + 1, v.k, 1⟩, ⟨v.j, v.k + 1, 2⟩}
  else {⟨v.j, v.k, 0⟩, ⟨v.j, v.k, 1⟩, ⟨v.j, v.k, 2⟩}

theorem incident_iff_mem (p : Port) (v : Vertex) :
    Incident p v ↔ p ∈ incidentPorts v := by
  rcases v with ⟨j, k, b⟩
  rcases p with ⟨j', k', d⟩
  cases b <;> fin_cases d <;>
    simp [Incident, edgeA, edgeB, incidentPorts, Vertex.mk.injEq, Port.mk.injEq] <;> omega

theorem boundaryPorts_finite {D : Set Vertex} (hD : D.Finite) :
    {p | BoundaryPort D p}.Finite := by
  apply (hD.biUnion (fun v _ => (incidentPorts v).finite_toSet)).subset
  intro p hp
  rcases hp with ⟨hA, _⟩ | ⟨hB, _⟩
  · simp only [Set.mem_iUnion]
    exact ⟨edgeA p, hA, (incident_iff_mem p _).mp (Or.inl rfl)⟩
  · simp only [Set.mem_iUnion]
    exact ⟨edgeB p, hB, (incident_iff_mem p _).mp (Or.inr rfl)⟩

def Chord.domainList {D : Set Vertex} (γ : Chord D) : List D :=
  γ.val.vertices.attach.map (fun v => ⟨v.val, γ.property.1 v.val v.property⟩)

theorem Chord.domainList_map_val {D : Set Vertex} (γ : Chord D) :
    γ.domainList.map Subtype.val = γ.val.vertices := by
  simp [Chord.domainList, List.map_map]

theorem Chord.domainList_nodup {D : Set Vertex} (γ : Chord D) :
    γ.domainList.Nodup := by
  apply List.Nodup.of_map Subtype.val
  rw [γ.domainList_map_val]
  exact γ.val.nodup

theorem finite_chord {D : Set Vertex} (hD : D.Finite) : Finite (Chord D) := by
  let := hD.fintype
  let : Fintype {p // BoundaryPort D p} := (boundaryPorts_finite hD).fintype
  let f : Chord D → {p // BoundaryPort D p} × {p // BoundaryPort D p} ×
      {l : List D // l.Nodup} := fun γ =>
    (⟨γ.val.source, γ.property.2.1⟩, ⟨γ.val.target, γ.property.2.2⟩,
      ⟨γ.domainList, γ.domainList_nodup⟩)
  apply Finite.of_injective f
  intro γ η h
  apply Subtype.ext
  apply PortPath.ext
  · exact congrArg (fun x => x.1.val) h
  · exact congrArg (fun x => x.2.1.val) h
  · have hL : γ.domainList = η.domainList := congrArg (fun x => x.2.2.val) h
    rw [← γ.domainList_map_val, ← η.domainList_map_val, hL]

theorem Chord.length_le_card {D : Set Vertex} (hD : D.Finite) (γ : Chord D) :
    γ.val.length ≤ hD.toFinset.card := by
  rw [PortPath.length, ← List.toFinset_card_of_nodup γ.val.nodup]
  apply Finset.card_le_card
  intro v hv
  exact hD.mem_toFinset.mpr (γ.property.1 v (List.mem_toFinset.mp hv))

theorem finite_pathMeasure {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [Finite Ω] (path : Ω → PortPath) :
    IsFiniteMeasure (pathMeasure path) := by
  classical
  let := Fintype.ofFinite Ω
  constructor
  rw [pathMeasure_apply]
  simp only [Set.indicator_univ, tsum_fintype]
  exact ENNReal.sum_lt_top.mpr (fun γ _ => weight_lt_top (path γ))

theorem triangleMeasure_finite (R : ℝ) : IsFiniteMeasure (triangleMeasure R) := by
  have := finite_chord (triangleVertices_finite R)
  exact finite_pathMeasure _

theorem admissibleLevels_tendsto :
    Tendsto (fun n : ℕ => (1 / 2 : ℝ) + (3 / 2) * n) atTop wallFilter := by
  apply tendsto_inf.mpr
  constructor
  · have h : Tendsto (fun n : ℕ => (3 / 2 : ℝ) * n) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
    simpa [add_comm] using tendsto_atTop_add_const_right atTop (1 / 2 : ℝ) h
  · apply tendsto_principal.mpr
    exact Eventually.of_forall (fun n => ⟨(n : ℤ), by norm_cast⟩)

instance : NeBot wallFilter := admissibleLevels_tendsto.neBot

theorem PortPath.length_eq_tsum_visits (γ : PortPath) :
    (γ.length : ℝ≥0∞) = ∑' v : Vertex, if v ∈ γ.vertices then 1 else 0 := by
  classical
  symm
  rw [tsum_eq_sum (s := γ.vertices.toFinset) (fun v hv => by simpa using hv)]
  calc
    _ = ∑ _v ∈ γ.vertices.toFinset, (1 : ℝ≥0∞) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [ite_eq_left (List.mem_toFinset.mp hv)]
    _ = _ := by simp [List.toFinset_card_of_nodup γ.nodup, PortPath.length]

theorem innerCount_eq_tsum_visits (ε R : ℝ) (γ : PortPath) :
    (innerCount ε R γ : ℝ≥0∞) =
      ∑' v : Vertex, (innerVertices ε R).indicator
        (fun v => if v ∈ γ.vertices then (1 : ℝ≥0∞) else 0) v := by
  classical
  let S := γ.vertices.toFinset.filter (fun v => v ∈ innerVertices ε R)
  symm
  rw [tsum_eq_sum (s := S) (fun v hv => ?_)]
  · calc
      _ = ∑ _v ∈ S, (1 : ℝ≥0∞) := by
        apply Finset.sum_congr rfl
        intro v hv
        obtain ⟨hγ, hI⟩ := Finset.mem_filter.mp hv
        simp [Set.indicator_of_mem hI, List.mem_toFinset.mp hγ]
      _ = _ := by simp [S, innerCount]
  · by_cases hI : v ∈ innerVertices ε R
    · have hγ : v ∉ γ.vertices := by
        intro hγ
        exact hv (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hγ, hI⟩)
      simp [hI, hγ]
    · simp [hI]

theorem lintegral_length_eq_tsum_visits {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [Countable Ω]
    (path : Ω → PortPath) (ν : Measure Ω) :
    (∫⁻ γ, ((path γ).length : ℝ≥0∞) ∂ν) = ∑' v : Vertex,
      ν {γ | v ∈ (path γ).vertices} := by
  classical
  calc
    _ = ∫⁻ γ, ∑' v : Vertex, if v ∈ (path γ).vertices then (1 : ℝ≥0∞) else 0 ∂ν :=
      lintegral_congr (fun γ => (path γ).length_eq_tsum_visits)
    _ = ∑' v : Vertex, ∫⁻ γ, if v ∈ (path γ).vertices then (1 : ℝ≥0∞) else 0 ∂ν :=
      lintegral_tsum (fun _ => (measurable_of_countable _).aemeasurable)
    _ = _ := by
      apply tsum_congr
      intro v
      simpa only [Set.indicator_apply, Set.mem_ofPred_eq, one_mul] using
        lintegral_indicator_const
          (MeasurableSet.of_discrete : MeasurableSet {γ | v ∈ (path γ).vertices}) (1 : ℝ≥0∞)

theorem lintegral_innerCount_eq_tsum_visits {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [Countable Ω]
    (path : Ω → PortPath) (ν : Measure Ω) (ε R : ℝ) :
    (∫⁻ γ, (innerCount ε R (path γ) : ℝ≥0∞) ∂ν) =
      ∑' v : Vertex, (innerVertices ε R).indicator
        (fun v => ν {γ | v ∈ (path γ).vertices}) v := by
  classical
  calc
    _ = ∫⁻ γ, ∑' v : Vertex, (innerVertices ε R).indicator
        (fun v => if v ∈ (path γ).vertices then (1 : ℝ≥0∞) else 0) v ∂ν :=
      lintegral_congr (fun γ => innerCount_eq_tsum_visits ε R (path γ))
    _ = ∑' v : Vertex, ∫⁻ γ, (innerVertices ε R).indicator
        (fun v => if v ∈ (path γ).vertices then (1 : ℝ≥0∞) else 0) v ∂ν :=
      lintegral_tsum (fun _ => (measurable_of_countable _).aemeasurable)
    _ = _ := by
      apply tsum_congr
      intro v
      by_cases h : v ∈ innerVertices ε R
      · simp only [Set.indicator_of_mem h]
        simpa only [Set.indicator_apply, Set.mem_ofPred_eq, one_mul] using
          lintegral_indicator_const
            (MeasurableSet.of_discrete : MeasurableSet {γ | v ∈ (path γ).vertices}) (1 : ℝ≥0∞)
      · simp [h]

theorem triangleMean_eq_sum_visitProbability (ε R : ℝ) :
    triangleMean ε R = ∑' v : Vertex, visitProbability ε R v :=
  lintegral_length_eq_tsum_visits Subtype.val (triangleLaw ε R)

theorem triangleInnerMean_eq_sum_visitProbability (ε R : ℝ) :
    triangleInnerMean ε R = ∑' v : Vertex,
      (innerVertices ε R).indicator (visitProbability ε R) v :=
  lintegral_innerCount_eq_tsum_visits Subtype.val (triangleLaw ε R) ε R

theorem innerCount_le_length (ε R : ℝ) (γ : PortPath) : innerCount ε R γ ≤ γ.length := by
  classical
  unfold innerCount PortPath.length
  rw [← List.toFinset_card_of_nodup γ.nodup]
  exact Finset.card_filter_le _ _

theorem triangleInnerMean_le_triangleMean (ε R : ℝ) :
    triangleInnerMean ε R ≤ triangleMean ε R := by
  apply lintegral_mono
  intro γ
  exact Nat.cast_le.mpr (innerCount_le_length ε R γ.val)

theorem finite_chord_event_normalizable {D : Set Vertex} (hD : D.Finite)
    (E : Set (Chord D)) (hE : E.Nonempty) : Normalizable (pathMeasure Subtype.val) E := by
  have := finite_chord hD
  have := finite_pathMeasure (Subtype.val : Chord D → PortPath)
  constructor
  · obtain ⟨γ, hγ⟩ := hE
    calc
      0 < weight γ.val := weight_pos _
      _ = pathMeasure Subtype.val {γ} := (pathMeasure_singleton _ _).symm
      _ ≤ pathMeasure Subtype.val E := measure_mono (Set.singleton_subset_iff.mpr hγ)
  · exact measure_lt_top _ _

theorem triangleMean_le_card (ε R : ℝ)
    (hN : Normalizable (triangleMeasure R) (hitsInner ε R)) :
    triangleMean ε R ≤ (triangleVertices_finite R).toFinset.card := by
  calc
    _ ≤ ∫⁻ _γ : Chord (triangleVertices R),
        ((triangleVertices_finite R).toFinset.card : ℝ≥0∞) ∂triangleLaw ε R := by
      apply lintegral_mono
      intro γ
      exact Nat.cast_le.mpr (γ.length_le_card (triangleVertices_finite R))
    _ = _ := by rw [lintegral_const, triangleLaw, normalize_univ _ _ hN, mul_one]

theorem triangleMean_lt_top (ε R : ℝ)
    (hN : Normalizable (triangleMeasure R) (hitsInner ε R)) :
    triangleMean ε R < ∞ :=
  (triangleMean_le_card ε R hN).trans_lt (ENNReal.natCast_lt_top _)

theorem mem_halfPlane_iff_k_nonneg (v : Vertex) : v ∈ halfPlane ↔ 0 ≤ v.k := by
  rw [mem_halfPlane_iff, position_im]
  cases v.b <;> simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
  all_goals constructor
  all_goals intro h
  · have h' : (-1 : ℝ) < (v.k : ℝ) := by linarith
    have : (-1 : ℤ) < v.k := by exact_mod_cast h'
    omega
  · have : (0 : ℝ) ≤ (v.k : ℝ) := by exact_mod_cast h
    linarith
  · have h' : (-1 : ℝ) < (v.k : ℝ) := by linarith
    have : (-1 : ℤ) < v.k := by exact_mod_cast h'
    omega
  · have : (0 : ℝ) ≤ (v.k : ℝ) := by exact_mod_cast h
    linarith

theorem boundaryPort_halfPlane_coords (p : Port) :
    BoundaryPort halfPlane p ↔ p.k = 0 ∧ p.dir = 2 := by
  rcases p with ⟨j, k, d⟩
  fin_cases d <;> simp [BoundaryPort, edgeA, edgeB, mem_halfPlane_iff_k_nonneg]
  omega

theorem boundaryPort_halfPlane_iff (p : Port) :
    BoundaryPort halfPlane p ↔ ∃ m : ℤ, p = wallPort m := by
  constructor
  · rw [boundaryPort_halfPlane_coords]
    rintro ⟨hk, hd⟩
    refine ⟨p.j, ?_⟩
    cases p
    simp_all [wallPort]
  · rintro ⟨m, rfl⟩
    exact wallPort_boundary m

theorem lintegral_normalized_pathMeasure {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [Countable Ω]
    (path : Ω → PortPath) (E : Set Ω) (f : Ω → ℝ≥0∞) :
    (∫⁻ γ, f γ ∂normalize (pathMeasure path) E) =
      (pathMeasure path E)⁻¹ *
        ∑' γ, E.indicator (fun γ => weight (path γ) * f γ) γ := by
  classical
  rw [normalize, lintegral_smul_measure, smul_eq_mul,
    ← lintegral_indicator MeasurableSet.of_discrete, lintegral_pathMeasure]
  congr 1
  apply tsum_congr
  intro γ
  by_cases h : γ ∈ E <;> simp [h]

theorem archMean_eq_weighted_ratio (E : Set Arch) :
    archMean E = (μ E)⁻¹ *
      ∑' γ : Arch, E.indicator (fun γ => weight γ.path * γ.path.length) γ :=
  lintegral_normalized_pathMeasure Arch.path E _

theorem triangleMean_eq_weighted_ratio (ε R : ℝ) :
    triangleMean ε R = (triangleMeasure R (hitsInner ε R))⁻¹ *
      ∑' γ : Chord (triangleVertices R), (hitsInner ε R).indicator
        (fun γ => weight γ.val * γ.val.length) γ :=
  lintegral_normalized_pathMeasure Subtype.val (hitsInner ε R) _

def row (a k : ℤ) : ℕ → List Vertex
  | 0 => [⟨a, k, false⟩]
  | n + 1 => ⟨a, k, false⟩ :: ⟨a, k, true⟩ :: row (a + 1) k n

theorem row_ne_nil (a k : ℤ) (n : ℕ) : row a k n ≠ [] := by
  cases n <;> simp [row]

theorem row_head (a k : ℤ) (n : ℕ) :
    (row a k n).head (row_ne_nil a k n) = ⟨a, k, false⟩ := by
  cases n <;> rfl

theorem row_head? (a k : ℤ) (n : ℕ) :
    (row a k n).head? = some ⟨a, k, false⟩ := by
  rw [List.head?_eq_some_head (row_ne_nil a k n), row_head]

theorem row_last (a k : ℤ) (n : ℕ) :
    (row a k n).getLast (row_ne_nil a k n) = ⟨a + n, k, false⟩ := by
  induction n generalizing a with
  | zero => simp [row]
  | succ n ih =>
    simp only [row, List.getLast_cons_cons, List.getLast_cons (row_ne_nil _ _ _), ih]
    congr 1
    push_cast
    omega

theorem mem_row (a k : ℤ) (n : ℕ) (v : Vertex) :
    v ∈ row a k n ↔
      v.k = k ∧ a ≤ v.j ∧ v.j ≤ a + n ∧ (v.b = true → v.j < a + n) := by
  rcases v with ⟨j, k', b⟩
  induction n generalizing a with
  | zero => cases b <;> simp [row, Vertex.mk.injEq] <;> omega
  | succ n ih => cases b <;> simp [row, ih, Vertex.mk.injEq] <;> omega

theorem row_nodup (a k : ℤ) (n : ℕ) : (row a k n).Nodup := by
  induction n generalizing a with
  | zero => simp [row]
  | succ n ih => simp [row, List.nodup_cons, mem_row, Vertex.mk.injEq, ih]

theorem row_chain (a k : ℤ) (n : ℕ) : (row a k n).IsChain Adj := by
  induction n generalizing a with
  | zero => simp [row]
  | succ n ih =>
    rw [row, List.isChain_cons_cons]
    constructor
    · exact ⟨⟨a, k, 0⟩, Or.inl ⟨rfl, rfl⟩⟩
    · apply List.IsChain.cons (ih (a + 1))
      intro v hv
      rw [row_head?] at hv
      have hv' : v = ⟨a + 1, k, false⟩ := (Option.mem_some_iff.mp hv).symm
      subst v
      refine ⟨⟨a + 1, k, 1⟩, Or.inr ⟨?_, rfl⟩⟩
      simp [edgeB]

def rowPath (a k : ℤ) (n : ℕ) : PortPath where
  source := ⟨a, k, 1⟩
  target := ⟨a + n, k, 0⟩
  vertices := row a k n
  nonempty := row_ne_nil a k n
  nodup := row_nodup a k n
  chain := row_chain a k n
  first_incident := by rw [row_head]; exact Or.inl rfl
  last_incident := by rw [row_last]; exact Or.inl rfl
  distinct_ports := by simp [Port.mk.injEq]

theorem a_mem_triangle_level (N j k : ℤ) :
    (⟨j, k, false⟩ : Vertex) ∈ triangleVertices (1 / 2 + (3 / 2) * N) ↔
      -N ≤ j ∧ -N ≤ k ∧ j + k ≤ N := by
  constructor
  · intro h
    have h0 := h (0 : Fin 3)
    have h1 := h (1 : Fin 3)
    have h2 := h (2 : Fin 3)
    rw [dot_zero_position] at h0
    rw [dot_one_position] at h1
    rw [dot_two_position] at h2
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at h0 h1 h2
    have h0' : (3 : ℤ) * (j + k) < 1 + 3 * N := by
      exact_mod_cast (show (3 : ℝ) * ((j : ℝ) + (k : ℝ)) < 1 + 3 * (N : ℝ) by linarith)
    have h1' : -(3 : ℤ) * j < 1 + 3 * N := by
      exact_mod_cast (show -(3 : ℝ) * (j : ℝ) < 1 + 3 * (N : ℝ) by linarith)
    have h2' : -(3 : ℤ) * k < 1 + 3 * N := by
      exact_mod_cast (show -(3 : ℝ) * (k : ℝ) < 1 + 3 * (N : ℝ) by linarith)
    omega
  · rintro ⟨hj, hk, hjk⟩
    have hj' : -(N : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hk' : -(N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hjk' : (j : ℝ) + (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hjk
    intro i
    fin_cases i
    · change dot (direction 0) (position ⟨j, k, false⟩) < _
      rw [dot_zero_position]; norm_num; linarith
    · change dot (direction 1) (position ⟨j, k, false⟩) < _
      rw [dot_one_position]; norm_num; linarith
    · change dot (direction 2) (position ⟨j, k, false⟩) < _
      rw [dot_two_position]; norm_num; linarith

theorem b_mem_triangle_level (N j k : ℤ) :
    (⟨j, k, true⟩ : Vertex) ∈ triangleVertices (1 / 2 + (3 / 2) * N) ↔
      -N ≤ j ∧ -N ≤ k ∧ j + k < N := by
  constructor
  · intro h
    have h0 := h (0 : Fin 3)
    have h1 := h (1 : Fin 3)
    have h2 := h (2 : Fin 3)
    rw [dot_zero_position] at h0
    rw [dot_one_position] at h1
    rw [dot_two_position] at h2
    simp only [↓reduceIte] at h0 h1 h2
    have h0' : (3 : ℤ) * (j + k) + 2 < 1 + 3 * N := by
      exact_mod_cast (show (3 : ℝ) * ((j : ℝ) + (k : ℝ)) + 2 < 1 + 3 * (N : ℝ) by linarith)
    have h1' : -(3 : ℤ) * j - 1 < 1 + 3 * N := by
      exact_mod_cast (show -(3 : ℝ) * (j : ℝ) - 1 < 1 + 3 * (N : ℝ) by linarith)
    have h2' : -(3 : ℤ) * k - 1 < 1 + 3 * N := by
      exact_mod_cast (show -(3 : ℝ) * (k : ℝ) - 1 < 1 + 3 * (N : ℝ) by linarith)
    omega
  · rintro ⟨hj, hk, hjk⟩
    have hj' : -(N : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hk' : -(N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hjk' : (j : ℝ) + (k : ℝ) + 1 ≤ (N : ℝ) := by
      exact_mod_cast (show j + k + 1 ≤ N by omega)
    intro i
    fin_cases i
    · change dot (direction 0) (position ⟨j, k, true⟩) < _
      rw [dot_zero_position]; norm_num; linarith
    · change dot (direction 1) (position ⟨j, k, true⟩) < _
      rw [dot_one_position]; norm_num; linarith
    · change dot (direction 2) (position ⟨j, k, true⟩) < _
      rw [dot_two_position]; norm_num; linarith

theorem mem_triangle_level (N : ℤ) (v : Vertex) :
    v ∈ triangleVertices (1 / 2 + (3 / 2) * N) ↔
      -N ≤ v.j ∧ -N ≤ v.k ∧ v.j + v.k ≤ N ∧
        (v.b = true → v.j + v.k < N) := by
  rcases v with ⟨j, k, b⟩
  cases b <;> simp only [a_mem_triangle_level, b_mem_triangle_level,
    Bool.false_eq_true, false_implies, and_true, true_implies]
  omega

def triangleRow (N k : ℤ) (hlo : -N ≤ k) (hhi : k ≤ 2 * N) :
    Chord (triangleVertices (1 / 2 + (3 / 2) * N)) := by
  have hn : ((2 * N - k).toNat : ℤ) = 2 * N - k :=
    Int.toNat_of_nonneg (by omega)
  refine ⟨rowPath (-N) k (2 * N - k).toNat, ?_, ?_, ?_⟩
  · intro v hv
    have h := (mem_row (-N) k (2 * N - k).toNat v).mp hv
    apply (mem_triangle_level N v).mpr
    refine ⟨h.2.1, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro hb
      have := h.2.2.2 hb
      omega
  · left
    change (⟨-N, k, false⟩ : Vertex) ∈ _ ∧ (⟨-N - 1, k, true⟩ : Vertex) ∉ _
    simp only [a_mem_triangle_level, b_mem_triangle_level]
    omega
  · left
    change (⟨-N + (2 * N - k).toNat, k, false⟩ : Vertex) ∈ _ ∧
      (⟨-N + (2 * N - k).toNat, k, true⟩ : Vertex) ∉ _
    simp only [a_mem_triangle_level, b_mem_triangle_level, hn]
    omega

theorem exists_chord_through {R : ℝ} (hR : R ∈ admissibleLevels)
    (v : Vertex) (hv : v ∈ triangleVertices R) :
    ∃ γ : Chord (triangleVertices R), v ∈ γ.val.vertices := by
  obtain ⟨N, rfl⟩ := hR
  have h := (mem_triangle_level N v).mp hv
  have hk : v.k ≤ 2 * N := by omega
  refine ⟨triangleRow N v.k h.2.1 hk, ?_⟩
  have hn : ((2 * N - v.k).toNat : ℤ) = 2 * N - v.k :=
    Int.toNat_of_nonneg (by omega)
  apply (mem_row (-N) v.k (2 * N - v.k).toNat v).mpr
  refine ⟨rfl, h.1, ?_, ?_⟩
  · omega
  · intro hb
    have := h.2.2.2 hb
    omega

theorem origin_mem_triangle {R : ℝ} (hR : 0 < R) :
    (⟨0, 0, false⟩ : Vertex) ∈ triangleVertices R := by
  intro i
  simpa [dot, position] using hR

theorem innerVertices_subset {ε R : ℝ} (hε : 0 ≤ ε) (hR : 0 ≤ R) :
    innerVertices ε R ⊆ triangleVertices R := by
  intro v hv i
  exact (hv i).trans_le (by nlinarith)

theorem hitsInner_nonempty {ε R : ℝ} (hε : ε < 1) (hR : 0 < R)
    (hg : R ∈ admissibleLevels) : (hitsInner ε R).Nonempty := by
  have hI : (⟨0, 0, false⟩ : Vertex) ∈ innerVertices ε R :=
    origin_mem_triangle (mul_pos (sub_pos.mpr hε) hR)
  obtain ⟨γ, hγ⟩ := exists_chord_through hg ⟨0, 0, false⟩ (origin_mem_triangle hR)
  exact ⟨γ, ⟨_, hγ, hI⟩⟩

theorem triangle_normalizable {ε R : ℝ} (hε : ε < 1) (hR : 0 < R)
    (hg : R ∈ admissibleLevels) : Normalizable (triangleMeasure R) (hitsInner ε R) :=
  finite_chord_event_normalizable (triangleVertices_finite R) _
    (hitsInner_nonempty hε hR hg)

theorem eventually_triangle_normalizable {ε : ℝ} (hε : ε < 1) :
    ∀ᶠ R in wallFilter, Normalizable (triangleMeasure R) (hitsInner ε R) := by
  rw [wallFilter, eventually_inf_principal]
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR hg
  exact triangle_normalizable hε hR hg

theorem triangleLaw_isProbabilityMeasure {ε R : ℝ} (hε : ε < 1) (hR : 0 < R)
    (hg : R ∈ admissibleLevels) : IsProbabilityMeasure (triangleLaw ε R) :=
  normalize_isProbabilityMeasure _ _ (triangle_normalizable hε hR hg)

theorem visitProbability_pos {ε R : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε < 1)
    (hR : 0 < R) (hg : R ∈ admissibleLevels) (v : Vertex)
    (hv : v ∈ innerVertices ε R) : 0 < visitProbability ε R v := by
  obtain ⟨γ, hγ⟩ := exists_chord_through hg v (innerVertices_subset hε₀ hR.le hv)
  have hE : γ ∈ hitsInner ε R := ⟨v, hγ, hv⟩
  have hn := triangle_normalizable hε₁ hR hg
  calc
    0 < (triangleMeasure R (hitsInner ε R))⁻¹ * weight γ.val :=
      ENNReal.mul_pos_iff.mpr ⟨ENNReal.inv_pos.mpr hn.2.ne, weight_pos _⟩
    _ = triangleLaw ε R {γ} := (normalized_atom Subtype.val _ hE).symm
    _ ≤ visitProbability ε R v := measure_mono (Set.singleton_subset_iff.mpr hγ)

theorem visitProbability_le_one {ε R : ℝ} (hε : ε < 1) (hR : 0 < R)
    (hg : R ∈ admissibleLevels) (v : Vertex) : visitProbability ε R v ≤ 1 := by
  have : IsProbabilityMeasure (triangleLaw ε R) := triangleLaw_isProbabilityMeasure hε hR hg
  exact prob_le_one

theorem triangleMean_pos {ε R : ℝ} (hε : ε < 1) (hR : 0 < R)
    (hg : R ∈ admissibleLevels) : 0 < triangleMean ε R := by
  have hn := triangle_normalizable hε hR hg
  have hm : (1 : ℝ≥0∞) ≤ triangleMean ε R := by
    calc
      1 = ∫⁻ _γ : Chord (triangleVertices R), (1 : ℝ≥0∞) ∂triangleLaw ε R := by
        rw [lintegral_const, triangleLaw, normalize_univ _ _ hn, mul_one]
      _ ≤ triangleMean ε R := by
        apply lintegral_mono
        intro γ
        change (1 : ℝ≥0∞) ≤ (γ.val.length : ℝ≥0∞)
        exact_mod_cast (show 1 ≤ γ.val.length from Nat.succ_le_of_lt γ.val.length_pos)
  exact zero_lt_one.trans_le hm

theorem eventually_triangleMean_pos_finite {ε : ℝ} (hε : ε < 1) :
    ∀ᶠ R in wallFilter, 0 < triangleMean ε R ∧ triangleMean ε R < ∞ := by
  rw [wallFilter, eventually_inf_principal]
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR hg
  exact ⟨triangleMean_pos hε hR hg,
    triangleMean_lt_top ε R (triangle_normalizable hε hR hg)⟩

theorem triangleInnerMean_pos {ε R : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε < 1)
    (hR : 0 < R) (hg : R ∈ admissibleLevels) : 0 < triangleInnerMean ε R := by
  have hv : (⟨0, 0, false⟩ : Vertex) ∈ innerVertices ε R :=
    origin_mem_triangle (mul_pos (sub_pos.mpr hε₁) hR)
  rw [triangleInnerMean_eq_sum_visitProbability]
  calc
    0 < visitProbability ε R ⟨0, 0, false⟩ :=
      visitProbability_pos hε₀ hε₁ hR hg _ hv
    _ = (innerVertices ε R).indicator (visitProbability ε R) ⟨0, 0, false⟩ :=
      (Set.indicator_of_mem hv _).symm
    _ ≤ _ := ENNReal.le_tsum _

theorem eventually_triangleInnerMean_pos_finite {ε : ℝ}
    (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    ∀ᶠ R in wallFilter, 0 < triangleInnerMean ε R ∧ triangleInnerMean ε R < ∞ := by
  rw [wallFilter, eventually_inf_principal]
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR hg
  exact ⟨triangleInnerMean_pos hε₀ hε₁ hR hg,
    (triangleInnerMean_le_triangleMean ε R).trans_lt
      (triangleMean_lt_top ε R (triangle_normalizable hε₁ hR hg))⟩

end DiskBoundary

end

end OAI
