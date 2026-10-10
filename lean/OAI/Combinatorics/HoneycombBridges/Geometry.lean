import Mathlib
import OAI.Combinatorics.HoneycombBridges.Factorization

namespace OAI

/-! Geometry of concatenation and vertex-port conventions. -/

noncomputable section
open scoped ENNReal
open Filter

namespace HoneycombActual

def BridgeGeometryLaw : Prop :=
  (∀ b : Bridge, rowSpacing * (b.height : ℝ) ≤ b.endpointDistance) ∧
  (∀ b c : Bridge,
    max b.diameter c.diameter ≤ (b.concat c).diameter ∧
    (b.concat c).diameter ≤ b.diameter + c.diameter) ∧
  (∀ (bs : List Bridge) (b : Bridge), bridgeProduct bs = some b →
    rowSpacing * (bs.map (fun a => (a.height : ℝ))).sum ≤ b.endpointDistance ∧
    b.diameter ≤ (bs.map Bridge.diameter).sum ∧
    ∀ a ∈ bs, a.diameter ≤ b.diameter)



def shiftPoint (i j : ℤ) (z : ℂ) : ℂ := z + (port i j - port 0 0)

@[simp] theorem shiftPoint_port (i j a b : ℤ) :
    shiftPoint i j (port a b) = port (a+i) (b+j) := by
  apply Complex.ext <;> simp [shiftPoint, port] <;> ring

@[simp] theorem position_shiftVertex (i j : ℤ) (v : Vertex) :
    position (shiftVertex i j v) = shiftPoint i j (position v) := by
  cases hv : v.up <;> apply Complex.ext <;>
    simp [position, shiftVertex, hv, shiftPoint, port] <;> ring

theorem shiftPoint_isometry (i j : ℤ) : Isometry (shiftPoint i j) := by
  apply Isometry.of_dist_eq
  intro x y
  simp [shiftPoint]

theorem port_eq_midpoint (i j : ℤ) :
    port i j = midpoint ℝ (position (down i (j-1))) (position (up i j)) := by
  rw [midpoint_eq_smul_add]
  apply Complex.ext <;> simp [position, up, down, port] <;> ring

namespace Bridge

theorem height_le_endpointDistance (b : Bridge) :
    rowSpacing * (b.height : ℝ) ≤ b.endpointDistance := by
  have h := Complex.abs_im_le_norm (port b.terminal b.height - port 0 0)
  have he : (port b.terminal b.height - port 0 0).im = rowSpacing * (b.height : ℝ) := by
    simp [port]
  rw [he, abs_of_nonneg (by unfold rowSpacing; positivity)] at h
  simpa [endpointDistance, dist_eq_norm, norm_sub_rev] using h

theorem concat_trace_subset (b c : Bridge) :
    (b.concat c).trace ⊆ b.trace ∪ shiftPoint b.terminal b.height '' c.trace := by
  intro z hz
  rcases hz with hp | ⟨v, hv, rfl⟩
  · rcases hp with he | he
    · exact Or.inl (Or.inl (Or.inl he))
    · right
      refine ⟨port c.terminal c.height, by simp [trace], ?_⟩
      simpa [concat_terminal, concat_height, add_comm] using he.symm
  · rcases List.mem_append.mp hv with hb | hc
    · exact Or.inl (Or.inr ⟨v, hb, rfl⟩)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc
      right
      exact ⟨position w, Or.inr ⟨w, hw, rfl⟩, (position_shiftVertex _ _ _).symm⟩

theorem concat_diameter_le (b c : Bridge) :
    (b.concat c).diameter ≤ b.diameter + c.diameter := by
  have hb : Bornology.IsBounded (b.trace ∪ shiftPoint b.terminal b.height '' c.trace) :=
    (b.trace_finite.union (c.trace_finite.image _)).isBounded
  have hm : (b.trace ∩ shiftPoint b.terminal b.height '' c.trace).Nonempty := by
    refine ⟨port b.terminal b.height, by simp [trace], ?_⟩
    exact ⟨port 0 0, by simp [trace], by simp⟩
  calc
    (b.concat c).diameter ≤ Metric.diam (b.trace ∪ shiftPoint b.terminal b.height '' c.trace) :=
      Metric.diam_mono (concat_trace_subset b c) hb
    _ ≤ Metric.diam b.trace + Metric.diam (shiftPoint b.terminal b.height '' c.trace) :=
      Metric.diam_union' hm
    _ = b.diameter + c.diameter := by rw [(shiftPoint_isometry _ _).diam_image]; rfl

end Bridge
end HoneycombActual

namespace HoneycombActual.Bridge

theorem concat_cut_mem_convexHull (b c : Bridge) :
    port b.terminal b.height ∈ convexHull ℝ (b.concat c).trace := by
  rw [port_eq_midpoint]
  apply (convex_convexHull ℝ _).midpoint_mem
  · apply subset_convexHull ℝ _
    right
    refine ⟨down b.terminal ((b.height : ℤ)-1), ?_, rfl⟩
    exact List.mem_append_left _ (List.mem_of_getLast? b.terminates)
  · apply subset_convexHull ℝ _
    right
    refine ⟨up b.terminal b.height, ?_, rfl⟩
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨up 0 0, List.mem_of_head? c.initiates, by simp⟩

theorem left_trace_subset_convexHull_concat (b c : Bridge) :
    b.trace ⊆ convexHull ℝ (b.concat c).trace := by
  intro z hz
  rcases hz with hp | ⟨v, hv, rfl⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact subset_convexHull ℝ _ (by simp [trace])
    · exact concat_cut_mem_convexHull b c
  · apply subset_convexHull ℝ _
    exact Or.inr ⟨v, List.mem_append_left _ hv, rfl⟩

theorem right_trace_subset_convexHull_concat (b c : Bridge) :
    shiftPoint b.terminal b.height '' c.trace ⊆ convexHull ℝ (b.concat c).trace := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := hz
  rcases hw with hp | ⟨v, hv, rfl⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · simpa using concat_cut_mem_convexHull b c
    · apply subset_convexHull ℝ _
      left
      right
      simp [concat_height, concat_terminal, add_comm]
  · apply subset_convexHull ℝ _
    right
    exact ⟨shiftVertex b.terminal b.height v,
      List.mem_append_right _ (List.mem_map.mpr ⟨v, hv, rfl⟩),
      position_shiftVertex _ _ _⟩

theorem le_concat_diameter (b c : Bridge) :
    max b.diameter c.diameter ≤ (b.concat c).diameter := by
  have hb : Bornology.IsBounded (convexHull ℝ (b.concat c).trace) :=
    isBounded_convexHull.mpr (b.concat c).trace_finite.isBounded
  apply max_le
  · calc
      b.diameter ≤ Metric.diam (convexHull ℝ (b.concat c).trace) :=
        Metric.diam_mono (left_trace_subset_convexHull_concat b c) hb
      _ = (b.concat c).diameter := convexHull_diam _
  · calc
      c.diameter = Metric.diam (shiftPoint b.terminal b.height '' c.trace) :=
        ((shiftPoint_isometry _ _).diam_image _).symm
      _ ≤ Metric.diam (convexHull ℝ (b.concat c).trace) :=
        Metric.diam_mono (right_trace_subset_convexHull_concat b c) hb
      _ = (b.concat c).diameter := convexHull_diam _

end HoneycombActual.Bridge

namespace HoneycombActual

theorem bridgeProduct_height_sum {bs : List Bridge} {b : Bridge}
    (h : bridgeProduct bs = some b) :
    (b.height : ℝ) = (bs.map (fun a => (a.height : ℝ))).sum := by
  induction bs generalizing b with
  | nil => simp at h
  | cons a as ih =>
    cases he : bridgeProduct as with
    | none =>
      have hn := (bridgeProduct_eq_none_iff _).mp he
      subst as
      have heq : a = b := by simpa using h
      simp [← heq]
    | some c =>
      have heq : a.concat c = b := by simpa [bridgeProduct, he] using h
      rw [← heq]
      simpa using congrArg (fun x : ℝ => (a.height : ℝ) + x) (ih he)

theorem bridgeProduct_diameter {bs : List Bridge} {b : Bridge}
    (h : bridgeProduct bs = some b) :
    b.diameter ≤ (bs.map Bridge.diameter).sum ∧
    ∀ a ∈ bs, a.diameter ≤ b.diameter := by
  induction bs generalizing b with
  | nil => simp at h
  | cons a as ih =>
    cases he : bridgeProduct as with
    | none =>
      have hn := (bridgeProduct_eq_none_iff _).mp he
      subst as
      have heq : a = b := by simpa using h
      simp [← heq]
    | some c =>
      have heq : a.concat c = b := by simpa [bridgeProduct, he] using h
      rw [← heq]
      obtain ⟨hupper, hlower⟩ := ih he
      constructor
      · simpa using (a.concat_diameter_le c).trans (add_le_add le_rfl hupper)
      · intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact (le_max_left _ _).trans (Bridge.le_concat_diameter _ _)
        · exact (hlower d hd).trans ((le_max_right _ _).trans (a.le_concat_diameter c))

theorem bridgeGeometry : BridgeGeometryLaw := by
  refine ⟨Bridge.height_le_endpointDistance, ?_, ?_⟩
  · intro b c
    exact ⟨b.le_concat_diameter c, b.concat_diameter_le c⟩
  · intro bs b hb
    refine ⟨?_, bridgeProduct_diameter hb⟩
    rw [← bridgeProduct_height_sum hb]
    exact b.height_le_endpointDistance



namespace Bridge

def vertexEndpointDistance (b : Bridge) : ℝ :=
  dist (position (up 0 0)) (position (down b.terminal ((b.height : ℤ) - 1)))

def vertexTrace (b : Bridge) : Set ℂ := position '' {v | v ∈ b.vertices}

def vertexDiameter (b : Bridge) : ℝ := Metric.diam b.vertexTrace

end Bridge

def BoundedVertexConventions : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ b : Bridge,
    |b.endpointDistance - b.vertexEndpointDistance| ≤ C ∧
    |b.diameter - b.vertexDiameter| ≤ C

theorem rowSpacing_nonneg : 0 ≤ rowSpacing := by
  unfold rowSpacing
  positivity

theorem port_dist_up (i j : ℤ) :
    dist (port i j) (position (up i j)) = rowSpacing / 3 := by
  rw [Complex.dist_of_re_eq (by simp [port, position, up]), Real.dist_eq]
  have he : (port i j).im - (position (up i j)).im = -(rowSpacing / 3) := by
    simp [port, position, up]
    ring
  rw [he, abs_neg, abs_of_nonneg (div_nonneg rowSpacing_nonneg (by norm_num))]

theorem port_dist_down (i j : ℤ) :
    dist (port i j) (position (down i (j-1))) = rowSpacing / 3 := by
  rw [Complex.dist_of_re_eq (by simp [port, position, down]; ring), Real.dist_eq]
  have he : (port i j).im - (position (down i (j-1))).im = rowSpacing / 3 := by
    simp [port, position, down]
    ring
  rw [he, abs_of_nonneg (div_nonneg rowSpacing_nonneg (by norm_num))]

namespace Bridge

theorem endpointDistance_vertex_change (b : Bridge) :
    |b.endpointDistance - b.vertexEndpointDistance| ≤ 2 * rowSpacing / 3 := by
  have h₁ := dist_triangle4_right (port 0 0) (port b.terminal b.height)
    (position (up 0 0)) (position (down b.terminal ((b.height : ℤ)-1)))
  have h₂ := dist_triangle4_left (port 0 0) (port b.terminal b.height)
    (position (up 0 0)) (position (down b.terminal ((b.height : ℤ)-1)))
  rw [port_dist_up, port_dist_down] at h₁ h₂
  dsimp [endpointDistance, vertexEndpointDistance]
  apply abs_sub_le_iff.mpr
  constructor <;> linarith

theorem vertexTrace_finite (b : Bridge) : b.vertexTrace.Finite :=
  b.vertices.finite_toSet.image position

theorem first_vertex_mem_vertexTrace (b : Bridge) :
    position (up 0 0) ∈ b.vertexTrace :=
  ⟨up 0 0, List.mem_of_head? b.initiates, rfl⟩

theorem last_vertex_mem_vertexTrace (b : Bridge) :
    position (down b.terminal ((b.height : ℤ)-1)) ∈ b.vertexTrace :=
  ⟨down b.terminal ((b.height : ℤ)-1), List.mem_of_getLast? b.terminates, rfl⟩

theorem vertexEndpointDistance_le_vertexDiameter (b : Bridge) :
    b.vertexEndpointDistance ≤ b.vertexDiameter :=
  Metric.dist_le_diam_of_mem b.vertexTrace_finite.isBounded
    b.first_vertex_mem_vertexTrace b.last_vertex_mem_vertexTrace

theorem vertexDiameter_le_diameter (b : Bridge) : b.vertexDiameter ≤ b.diameter :=
  Metric.diam_mono (fun _ hz => Or.inr hz) b.trace_finite.isBounded

theorem trace_near_vertexTrace (b : Bridge) (z : ℂ) (hz : z ∈ b.trace) :
    ∃ w ∈ b.vertexTrace, dist z w ≤ rowSpacing / 3 := by
  rcases hz with hp | hv
  · rcases hp with rfl | rfl
    · exact ⟨_, b.first_vertex_mem_vertexTrace, (port_dist_up 0 0).le⟩
    · exact ⟨_, b.last_vertex_mem_vertexTrace, (port_dist_down b.terminal b.height).le⟩
  · exact ⟨z, hv, by simpa using div_nonneg rowSpacing_nonneg (by norm_num : (0 : ℝ) ≤ 3)⟩

theorem diameter_le_vertexDiameter_add (b : Bridge) :
    b.diameter ≤ b.vertexDiameter + 2 * rowSpacing / 3 := by
  apply Metric.diam_le_of_forall_dist_le
    (add_nonneg Metric.diam_nonneg (by positivity [rowSpacing_nonneg]))
  intro x hx y hy
  obtain ⟨v, hv, hxv⟩ := b.trace_near_vertexTrace x hx
  obtain ⟨w, hw, hyw⟩ := b.trace_near_vertexTrace y hy
  have hdist := dist_triangle4_right x y v w
  have hdiam := Metric.dist_le_diam_of_mem b.vertexTrace_finite.isBounded hv hw
  linarith

theorem diameter_vertex_change (b : Bridge) :
    |b.diameter - b.vertexDiameter| ≤ 2 * rowSpacing / 3 := by
  rw [abs_of_nonneg (sub_nonneg.mpr b.vertexDiameter_le_diameter)]
  linarith [b.diameter_le_vertexDiameter_add]

end Bridge

theorem boundedVertexConventions : BoundedVertexConventions := by
  refine ⟨2 * rowSpacing / 3, by positivity [rowSpacing_nonneg], ?_⟩
  intro b
  exact ⟨b.endpointDistance_vertex_change, b.diameter_vertex_change⟩

end HoneycombActual

end

end OAI
