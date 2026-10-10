import Mathlib

namespace OAI

/-!
# Normalized finite-volume Lipschitz laws on the triangular lattice

This file proves well-definedness of the normalized Lebesgue law in the free
coordinates and the almost-sure nonzero-vertex statement. It contains no SLE
or GFF convergence theorem and assumes no limiting law, effective stiffness,
or tangent-flux coefficient.
-/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace TriangularSurface
namespace FiniteModel

attribute [local instance] Classical.propDecidable

variable {V : Type*}

/-- Coordinates are only the unpinned vertices; Lebesgue measure is on this
space, not on the lower-dimensional subset of all-vertex height space. -/
abbrev Free (pins : Set V) := {x : V // x ∉ pins}

noncomputable instance freeFintype [Fintype V] (pins : Set V) : Fintype (Free pins) :=
  Fintype.ofFinite _

/-- Restore the prescribed boundary values. -/
def restore (pins : Set V) (b : V → ℝ) (h : Free pins → ℝ) (x : V) : ℝ :=
  if hx : x ∈ pins then b x else h ⟨x, hx⟩

/-- The actual unit nearest-neighbor Lipschitz polytope in its free coordinates.
The graph and pinned set are arbitrary here; the finite lattice polygon is a
special case. Fixed--fixed inequalities are retained. -/
def body (G : SimpleGraph V) (pins : Set V) (b : V → ℝ) : Set (Free pins → ℝ) :=
  {h | ∀ x y, G.Adj x y → |restore pins b h x - restore pins b h y| ≤ 1}

/-- Literal normalized Lebesgue restriction. It is proved to be a probability
measure below under the finite-volume model hypotheses. -/
def law [Fintype V] (G : SimpleGraph V) (pins : Set V) (b : V → ℝ) :
    Measure (Free pins → ℝ) :=
  (volume (body G pins b))⁻¹ • volume.restrict (body G pins b)

@[simp] theorem restore_pin (pins : Set V) (b : V → ℝ)
    (h : Free pins → ℝ) {x : V} (hx : x ∈ pins) : restore pins b h x = b x := by
  simp [restore, hx]

@[simp] theorem restore_free (pins : Set V) (b : V → ℝ)
    (h : Free pins → ℝ) (x : Free pins) : restore pins b h x = h x := by
  simp [restore, x.property]

lemma continuous_restore [Fintype V] (pins : Set V) (b : V → ℝ) (x : V) :
    Continuous (fun h : Free pins → ℝ => restore pins b h x) := by
  by_cases hx : x ∈ pins
  · simpa [restore, hx] using
      (continuous_const : Continuous (fun _ : Free pins → ℝ => b x))
  · simpa [restore, hx] using
      (continuous_apply (⟨x, hx⟩ : Free pins) :
        Continuous (fun h : Free pins → ℝ => h ⟨x, hx⟩))

lemma closed_body [Fintype V] (G : SimpleGraph V) (pins : Set V) (b : V → ℝ) :
    IsClosed (body G pins b) := by
  simp only [body, ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _ =>
    isClosed_le ((continuous_restore pins b x).sub (continuous_restore pins b y)).abs
      continuous_const

lemma bound_along_walk (G : SimpleGraph V) (h : V → ℝ)
    (hh : ∀ x y, G.Adj x y → |h x - h y| ≤ 1) {x y : V} (p : G.Walk x y) :
    |h x - h y| ≤ p.length := by
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
    calc
      |h u - h w| ≤ |h u - h v| + |h v - h w| := abs_sub_le _ _ _
      _ ≤ 1 + p.length := add_le_add (hh u v huv) ih
      _ = _ := by simp; ring

/-- Every vertex has a graph path to a prescribed vertex, exactly the anchoring
condition used for boundedness in the source model. -/
lemma compact_body [Fintype V] (G : SimpleGraph V) (pins : Set V)
    (ha : ∀ x : V, ∃ p ∈ pins, G.Reachable x p) (b : V → ℝ) :
    IsCompact (body G pins b) := by
  choose p hp path using ha
  let walk (x : V) : G.Walk x (p x) := Classical.choice (path x)
  let R (x : Free pins) : ℝ := |b (p x)| + (walk x).length
  apply isCompact_Icc.of_isClosed_subset (closed_body G pins b) (s := Icc (-R) R)
  intro h hh
  have hb (x : Free pins) : |h x| ≤ R x := by
    have hbnd := bound_along_walk G (restore pins b h) hh (walk x)
    have hx : restore pins b h x = h x := restore_free pins b h x
    have hp' : restore pins b h (p x) = b (p x) := restore_pin pins b h (hp x)
    rw [hx, hp'] at hbnd
    have ht : |h x| ≤ |h x - b (p x)| + |b (p x)| := by
      simpa only [sub_add_cancel] using abs_add_le (h x - b (p x)) (b (p x))
    dsimp [R]
    linarith
  exact ⟨fun x => (abs_le.mp (hb x)).1, fun x => (abs_le.mp (hb x)).2⟩

/-- A concrete unit-volume cube lies in the model whenever all fixed heights
are at most 1/2 in absolute value. This includes the fixed--fixed edges. -/
lemma cube_subset_body (G : SimpleGraph V) (pins : Set V) (b : V → ℝ)
    (hb : ∀ x ∈ pins, |b x| ≤ 1 / 2) :
    Icc (fun _ : Free pins => -(1 / 2 : ℝ)) (fun _ => 1 / 2) ⊆ body G pins b := by
  intro h hh x y _
  have hbound (z : V) : |restore pins b h z| ≤ 1 / 2 := by
    by_cases hz : z ∈ pins
    · simpa [restore, hz] using hb z hz
    · simpa [restore, hz] using abs_le.mpr ⟨hh.1 ⟨z, hz⟩, hh.2 ⟨z, hz⟩⟩
  calc
    |restore pins b h x - restore pins b h y| ≤
        |restore pins b h x| + |restore pins b h y| := abs_sub _ _
    _ ≤ 1 := by linarith [hbound x, hbound y]

lemma ball_subset_body [Fintype V] (G : SimpleGraph V) (pins : Set V) (b : V → ℝ)
    (hb : ∀ x ∈ pins, |b x| ≤ 1 / 2) :
    Metric.ball (0 : Free pins → ℝ) (1 / 2) ⊆ body G pins b := by
  apply Subset.trans _ (cube_subset_body G pins b hb)
  intro h hh
  have hn : ‖h‖ < (1 / 2 : ℝ) := by simpa [Metric.mem_ball, dist_zero_right] using hh
  have hbound (x : Free pins) : |h x| ≤ 1 / 2 :=
    (show |h x| ≤ ‖h‖ by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm h x).trans hn.le
  exact ⟨fun x => (abs_le.mp (hbound x)).1, fun x => (abs_le.mp (hbound x)).2⟩

lemma zero_mem_interior [Fintype V] (G : SimpleGraph V) (pins : Set V) (b : V → ℝ)
    (hb : ∀ x ∈ pins, |b x| ≤ 1 / 2) :
    (0 : Free pins → ℝ) ∈ interior (body G pins b) := by
  apply (Metric.isOpen_ball.subset_interior_iff.mpr (ball_subset_body G pins b hb))
  simp

lemma one_le_volume_body [Fintype V] (G : SimpleGraph V) (pins : Set V) (b : V → ℝ)
    (hb : ∀ x ∈ pins, |b x| ≤ 1 / 2) : 1 ≤ volume (body G pins b) := by
  let C : Set (Free pins → ℝ) :=
    Icc (fun _ => -(1 / 2 : ℝ)) (fun _ => 1 / 2)
  have hC : volume C = 1 := by
    rw [show C = Set.pi Set.univ (fun _ : Free pins => Icc (-(1 / 2 : ℝ)) (1 / 2)) by
      ext h
      simp [C, Set.mem_Icc, Pi.le_def], MeasureTheory.volume_pi_pi]
    norm_num [Real.volume_Icc]
  rw [← hC]
  exact measure_mono (cube_subset_body G pins b hb)

lemma law_probability [Fintype V] (G : SimpleGraph V) (pins : Set V)
    (ha : ∀ x : V, ∃ p ∈ pins, G.Reachable x p) (b : V → ℝ)
    (hb : ∀ x ∈ pins, |b x| ≤ 1 / 2) : IsProbabilityMeasure (law G pins b) := by
  constructor
  simp only [law, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    ((zero_lt_one.trans_le (one_le_volume_body G pins b hb)).ne')
    (compact_body G pins ha b).measure_ne_top

lemma ae_mem_body [Fintype V] (G : SimpleGraph V) (pins : Set V) (b : V → ℝ) :
    ∀ᵐ h ∂law G pins b, h ∈ body G pins b := by
  exact Measure.ae_smul_measure (ae_restrict_mem (closed_body G pins b).measurableSet) _

/-- Coordinate hyperplanes have zero volume, hence no free vertex has a given
height with positive probability. This does not assert pointwise tightness
as the mesh decreases. -/
lemma ae_free_ne [Fintype V] (G : SimpleGraph V) (pins : Set V) (b : V → ℝ)
    (c : ℝ) : ∀ᵐ h ∂law G pins b, ∀ x : Free pins, h x ≠ c := by
  have hvol : ∀ᵐ h ∂(volume : Measure (Free pins → ℝ)), ∀ x : Free pins, h x ≠ c := by
    rw [ae_all_iff]
    intro x
    exact Measure.ae_eval_ne (fun _ : Free pins => (volume : Measure ℝ)) x c
  exact Measure.ae_smul_measure (ae_restrict_of_ae hvol) _

/-- The two boundary arcs; vertices in `plus` get `lam`, the other pinned
vertices get `-lam`. Membership outside `pins` has no effect on `body` or `law`.
Each pinned vertex receives exactly one prescribed value. -/
def boundaryHeight (plus : Set V) (lam : ℝ) (x : V) : ℝ :=
  if x ∈ plus then lam else -lam

lemma abs_boundaryHeight (plus : Set V) {lam : ℝ} (hlam : 0 ≤ lam) (x : V) :
    |boundaryHeight plus lam x| = lam := by
  by_cases hx : x ∈ plus <;> simp [boundaryHeight, hx, abs_of_nonneg hlam]

/-- Finite-volume well-definedness of the normalized law. The hypotheses do not
contain any limiting, cell, or stochastic identification statement. The
normalized law is exactly normalized Lebesgue measure on the polytope. -/
theorem finite_model_well_defined [Fintype V] (G : SimpleGraph V) (pins plus : Set V)
    (ha : ∀ x : V, ∃ p ∈ pins, G.Reachable x p)
    (lam : ℝ) (hlam : 0 < lam) (hlamhalf : lam ≤ 1 / 2) :
    IsCompact (body G pins (boundaryHeight plus lam)) ∧
    (0 : Free pins → ℝ) ∈ interior (body G pins (boundaryHeight plus lam)) ∧
    0 < volume (body G pins (boundaryHeight plus lam)) ∧
    volume (body G pins (boundaryHeight plus lam)) < ⊤ ∧
    IsProbabilityMeasure (law G pins (boundaryHeight plus lam)) ∧
    (∀ᵐ h ∂law G pins (boundaryHeight plus lam),
      h ∈ body G pins (boundaryHeight plus lam) ∧
      ∀ x : Free pins, h x ≠ 0) := by
  have hb (x : V) (_ : x ∈ pins) : |boundaryHeight plus lam x| ≤ 1 / 2 := by
    rw [abs_boundaryHeight plus hlam.le x]
    exact hlamhalf
  refine ⟨compact_body G pins ha _, zero_mem_interior G pins _ hb,
    zero_lt_one.trans_le (one_le_volume_body G pins _ hb),
    (compact_body G pins ha _).measure_lt_top, law_probability G pins ha _ hb, ?_⟩
  exact (ae_mem_body G pins _).and (ae_free_ne G pins _ 0)

end FiniteModel

namespace Lattice

/-- The integer coordinates in the triangular-lattice basis
`e₁ = (1,0)`, `e₂ = (1/2, sqrt(3)/2)`. -/
abbrev Vertex := ℤ × ℤ

/-- The six triangular-lattice steps, not square-lattice adjacency. -/
def Adj (x y : Vertex) : Prop :=
  y = (x.1 + 1, x.2) ∨ y = (x.1 - 1, x.2) ∨
  y = (x.1, x.2 + 1) ∨ y = (x.1, x.2 - 1) ∨
  y = (x.1 + 1, x.2 - 1) ∨ y = (x.1 - 1, x.2 + 1)

theorem adj_symm {x y : Vertex} (h : Adj x y) : Adj y x := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  simp only [Adj, Prod.mk.injEq] at h ⊢
  omega

theorem adj_irrefl (x : Vertex) : ¬ Adj x x := by
  rcases x with ⟨a, b⟩
  simp only [Adj, Prod.mk.injEq]
  omega

/-- The induced nearest-neighbor graph on the vertices of a finite polygon
(or, more generally, any finite set of lattice vertices). -/
def graph (vertices : Finset Vertex) : SimpleGraph vertices where
  Adj x y := Adj x.val y.val
  symm := ⟨fun _ _ h => adj_symm h⟩
  loopless := ⟨fun x => adj_irrefl x.val⟩

/-- The physical embedding at mesh `delta`. -/
def embed (delta : ℝ) (x : Vertex) : ℝ × ℝ :=
  (delta * ((x.1 : ℝ) + (x.2 : ℝ) / 2),
   delta * ((x.2 : ℝ) * Real.sqrt 3 / 2))

/-- The preceding finite-dimensional result specialized to the actual
triangular-lattice graph. No assertion about a scaling limit is made. -/
theorem triangular_finite_model_well_defined (vertices : Finset Vertex)
    (pins plus : Set vertices)
    (ha : ∀ x : vertices, ∃ p ∈ pins, (graph vertices).Reachable x p)
    (lam : ℝ) (hlam : 0 < lam) (hlamhalf : lam ≤ 1 / 2) :
    IsCompact (FiniteModel.body (graph vertices) pins (FiniteModel.boundaryHeight plus lam)) ∧
    (0 : FiniteModel.Free pins → ℝ) ∈
      interior (FiniteModel.body (graph vertices) pins (FiniteModel.boundaryHeight plus lam)) ∧
    0 < volume (FiniteModel.body (graph vertices) pins (FiniteModel.boundaryHeight plus lam)) ∧
    volume (FiniteModel.body (graph vertices) pins (FiniteModel.boundaryHeight plus lam)) < ⊤ ∧
    IsProbabilityMeasure
      (FiniteModel.law (graph vertices) pins (FiniteModel.boundaryHeight plus lam)) ∧
    (∀ᵐ h ∂FiniteModel.law (graph vertices) pins (FiniteModel.boundaryHeight plus lam),
      h ∈ FiniteModel.body (graph vertices) pins (FiniteModel.boundaryHeight plus lam) ∧
      ∀ x : FiniteModel.Free pins, h x ≠ 0) :=
  FiniteModel.finite_model_well_defined (graph vertices) pins plus ha lam hlam hlamhalf

end Lattice
end TriangularSurface

end

end OAI
