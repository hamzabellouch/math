import OAI.Geometry.RCD.Metric.RescalingSampleLimit

namespace OAI

/-! # Countable samples with moving centers and bounded rescaled curvature

Finite nets are padded by the base point, so their labels do not change
with the sequence index. Their distance matrices therefore admit one
common convergent subsequence.
-/

open Set Metric Filter
open scoped Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X]

omit [MetricSpace X] in
private theorem enumerate_finite_net (p : X) {A : Set X} (hp : p ∈ A)
    (s : Finset X) (hs : (s : Set X) ⊆ A) {N : ℕ} (hN : s.card ≤ N) :
    ∃ f : Fin (N+1) → X, (∀ j, f j ∈ A) ∧ (s : Set X) ⊆ range f := by
  classical
  let e := Fintype.equivFin s
  have hcard : Fintype.card s ≤ N := by simpa only [Fintype.card_coe] using hN
  let f (j : Fin (N+1)) : X :=
    if h : j.val < Fintype.card s then (e.symm ⟨j.val,h⟩).val else p
  refine ⟨f, ?_, ?_⟩
  · intro j
    dsimp only [f]
    split_ifs with h
    · exact hs (e.symm ⟨j.val,h⟩).property
    · exact hp
  · intro x hx
    let y : s := ⟨x,hx⟩
    let j : Fin (N+1) := ⟨(e y).val, by have h := (e y).isLt; omega⟩
    refine ⟨j, ?_⟩
    have hj : j.val < Fintype.card s := (e y).isLt
    dsimp only [f]
    rw [dite_eq_left hj]
    exact congrArg Subtype.val (e.symm_apply_apply y)

/-- Every radius and accuracy has a fixed finite label type across the
whole sequence. The point at infinity is not introduced at this stage. -/
structure MovingRescalingNetFamily (p : ℕ → X) (r : ℕ → ℝ) where
  size : ℕ → ℕ → ℕ
  point : ℕ → ∀ R k, Fin (size R k) → X
  bounded : ∀ (i R k : ℕ) j, dist (point i R k j) (p i) ≤ ((R:ℝ)+1)*r i
  covers : ∀ (i R k : ℕ) x, dist x (p i) ≤ ((R:ℝ)+1)*r i →
    ∃ j, dist x (point i R k j) < r i / ((k:ℝ)+1)

variable [MeasurableSpace X] [BorelSpace X]

/-- CD supplies the countably many finite nets needed by the pointed
compactness construction, with no compactness assumption on rescalings. -/
theorem NoncollapsedRCD.movingRescalingNetFamily {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : ℕ → X)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hcurv : ∀ i, -1 ≤ K*(r i)^2) :
    Nonempty (MovingRescalingNetFamily p r) := by
  classical
  have havail (R k : ℕ) : ∃ N : ℕ, ∀ (p : X) (r : ℝ), 0 < r → -1 ≤ K*r^2 →
      ∃ s : Finset X, s.card ≤ N ∧ (s : Set X) ⊆ closedBall p (((R:ℝ)+1)*r) ∧
        ∀ x ∈ closedBall p (((R:ℝ)+1)*r), ∃ y ∈ s,
          dist x y < (1/((k:ℝ)+1))*r :=
    hX.rescaled_finite_nets hn (by positivity) (by positivity)
  choose N hN using havail
  have hdata (i R k : ℕ) : ∃ f : Fin (N R k+1) → X,
      (∀ j, dist (f j) (p i) ≤ ((R:ℝ)+1)*r i) ∧
      ∀ x, dist x (p i) ≤ ((R:ℝ)+1)*r i → ∃ j, dist x (f j) < r i/((k:ℝ)+1) := by
    obtain ⟨s, hsN, hs, hcover⟩ := hN R k (p i) (r i) (hr i) (hcurv i)
    have hp : p i ∈ closedBall (p i) (((R:ℝ)+1)*r i) := mem_closedBall_self (mul_nonneg (by positivity) (hr i).le)
    obtain ⟨f, hf, hsf⟩ := enumerate_finite_net (p i) hp s hs hsN
    refine ⟨f, hf, ?_⟩
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcover x hx
    obtain ⟨j, rfl⟩ := hsf hy
    refine ⟨j, ?_⟩
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hxy
  choose f hf hcover using hdata
  exact ⟨{ size := fun R k => N R k+1, point := f, bounded := hf, covers := hcover }⟩

namespace MovingRescalingNetFamily

variable {p : ℕ → X} {r : ℕ → ℝ} (s : MovingRescalingNetFamily p r)

/-- The base point and all finite-net labels form one countable index set. -/
abbrev Index := Option (Σ R : ℕ, Σ k : ℕ, Fin (s.size R k))

def sample (i : ℕ) : s.Index → X
  | none => p i
  | some a => s.point i a.1 a.2.1 a.2.2

def radius : s.Index → ℝ
  | none => 0
  | some a => (a.1:ℝ)+1

omit [MeasurableSpace X] [BorelSpace X] in
theorem sample_bound (i : ℕ) (a : s.Index) :
    dist (s.sample i a) (p i) ≤ s.radius a*r i := by
  cases a with
  | none => simp only [sample, radius, dist_self, zero_mul, le_refl]
  | some a => exact s.bounded i a.1 a.2.1 a.2.2

omit [MeasurableSpace X] [BorelSpace X] in
/-- One subsequence makes all distances between these actual sample points
converge. The limit pseudometric uses the same countable labels. -/
theorem exists_limit (hr : ∀ i, 0 < r i) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ d : PseudoMetricSpace s.Index,
      ∀ a b, Tendsto (fun k => dist (s.sample (phi k) a) (s.sample (phi k) b) / r (phi k))
        atTop (𝓝 (@dist s.Index d.toDist a b)) := by
  apply exists_rescaling_sample_limit r hr s.sample s.radius
  intro k a b
  apply (div_le_iff₀ (hr k)).mpr
  calc
    _ ≤ dist (s.sample k a) (p k) + dist (p k) (s.sample k b) := dist_triangle _ _ _
    _ ≤ s.radius a*r k + s.radius b*r k := by
      apply add_le_add (s.sample_bound k a)
      rw [dist_comm]
      exact s.sample_bound k b
    _ = _ := by ring

end MovingRescalingNetFamily
end RegularPointCoordinates

end

end OAI
