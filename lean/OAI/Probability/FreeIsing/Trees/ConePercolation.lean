import OAI.Probability.FreeIsing.Trees.ConeCoding
import OAI.Probability.FreeIsing.Trees.SubcriticalClusters

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.TreeConeCoding

def rootedPathOpen {b : ℕ} (p : ℝ) (U : List (Fin b) → ℝ) (w : List (Fin b)) : Prop :=
  ∀ k : ℕ, 0 < k → k ≤ w.length → U (w.take k) ≤ p

theorem measurableSet_rootedPathOpen {b : ℕ} (p : ℝ) (w : List (Fin b)) :
    MeasurableSet {U : List (Fin b) → ℝ | rootedPathOpen p U w} := by
  simp only [rootedPathOpen, Set.ofPred_forall]
  exact MeasurableSet.iInter fun k : ℕ =>
    MeasurableSet.iInter fun _ : 0 < k =>
      MeasurableSet.iInter fun _ : k ≤ w.length =>
        measurableSet_le (measurable_pi_apply _) measurable_const

theorem downwardOpen_vertex_iff {b : ℕ} (p : ℝ)
    (U : TreeVertex (b + 1) → ℝ) (r : TreeVertex (b + 1)) (hr : r.1 ≠ [])
    (w : List (Fin b)) :
    SubcriticalClusters.DownwardOpen p U r (vertex r hr w) ↔
      rootedPathOpen p (labels r hr U) w := by
  constructor
  · intro h k hk hklen
    have hc := h.2 (r.1.length + k) (by omega) (by simp; omega)
    simpa only [← vertex_take, labels] using hc
  · intro h
    refine ⟨vertex_prefix r hr w, fun k hk hklen => ?_⟩
    have hkle : k - r.1.length ≤ w.length := by
      rw [length_vertex] at hklen
      omega
    have hpos : 0 < k - r.1.length := by omega
    have hc := h (k - r.1.length) hpos hkle
    have he : r.1.length + (k - r.1.length) = k := Nat.add_sub_of_le hk.le
    simpa only [labels, vertex_take, he] using hc

theorem survival_iff {b : ℕ} (p : ℝ)
    (U : TreeVertex (b + 1) → ℝ) (r : TreeVertex (b + 1)) (hr : r.1 ≠ []) (n : ℕ) :
    (∃ v : TreeVertex (b + 1), v.1.length = r.1.length + n ∧
      SubcriticalClusters.DownwardOpen p U r v) ↔
    ∃ w : List (Fin b), w.length = n ∧ rootedPathOpen p (labels r hr U) w := by
  constructor
  · rintro ⟨v, hvlen, hv⟩
    obtain ⟨w, rfl⟩ := vertex_surjective_cone r hr v hv.1
    refine ⟨w, ?_, (downwardOpen_vertex_iff p U r hr w).mp hv⟩
    rw [length_vertex] at hvlen
    exact Nat.add_left_cancel hvlen
  · rintro ⟨w, hwlen, hw⟩
    refine ⟨vertex r hr w, ?_, (downwardOpen_vertex_iff p U r hr w).mpr hw⟩
    rw [length_vertex, hwlen]

theorem measurableSet_rootedSurvival {b : ℕ} (p : ℝ) (n : ℕ) :
    MeasurableSet {U : List (Fin b) → ℝ |
      ∃ w : List (Fin b), w.length = n ∧ rootedPathOpen p U w} := by
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro w
  by_cases hw : w.length = n
  · simpa only [hw, true_and] using measurableSet_rootedPathOpen p w
  · simp only [hw, false_and, Set.ofPred_false, MeasurableSet.empty]

theorem survival_probability {b : ℕ} (p : ℝ)
    (r : TreeVertex (b + 1)) (hr : r.1 ≠ []) (n : ℕ) :
    labelMeasure (b + 1) {U | ∃ v : TreeVertex (b + 1),
      v.1.length = r.1.length + n ∧ SubcriticalClusters.DownwardOpen p U r v} =
    (Measure.infinitePi (fun _ : List (Fin b) => uniform01))
      {W | ∃ w : List (Fin b), w.length = n ∧ rootedPathOpen p W w} := by
  have he : {U : TreeVertex (b + 1) → ℝ | ∃ v : TreeVertex (b + 1),
      v.1.length = r.1.length + n ∧ SubcriticalClusters.DownwardOpen p U r v} =
      (labels r hr) ⁻¹' {W | ∃ w : List (Fin b),
        w.length = n ∧ rootedPathOpen p W w} := by
    ext U
    exact survival_iff p U r hr n
  rw [he]
  exact (measurePreserving_labels uniform01 r hr).measure_preimage
    (measurableSet_rootedSurvival p n).nullMeasurableSet

theorem ae_finite_downwardOpen_of_rooted {b : ℕ} (p : ℝ)
    (r : TreeVertex (b + 1)) (hr : r.1 ≠ [])
    (hfin : ∀ᵐ W ∂Measure.infinitePi (fun _ : List (Fin b) => uniform01),
      {w | rootedPathOpen p W w}.Finite) :
    ∀ᵐ U ∂labelMeasure (b + 1),
      {v | SubcriticalClusters.DownwardOpen p U r v}.Finite := by
  filter_upwards [(measurePreserving_labels uniform01 r hr).quasiMeasurePreserving.ae hfin]
    with U hU
  apply (hU.image (vertex r hr)).subset
  intro v hv
  obtain ⟨w, hw⟩ := vertex_surjective_cone r hr v hv.1
  refine ⟨w, ?_, hw⟩
  apply (downwardOpen_vertex_iff p U r hr w).mp
  rwa [hw]

end Problem367.TreeConeCoding

end

end OAI
