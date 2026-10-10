import Mathlib
import OAI.Analysis.AffineBernstein.TriangularGraph
import OAI.Analysis.AffineBernstein.AmbientStraightening
import OAI.Analysis.AffineBernstein.FiniteAreaCover

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter
open scoped Topology

open Filter Metric
open scoped Topology

lemma continuous_ambientCoordinate {n : ℕ} (i : Fin n ⊕ Unit) :
    Continuous (fun z : Space n × ℝ => ambientCoordinates n z i) := by
  cases i with
  | inl i => simpa only [ambientCoordinates_inl,Function.comp_def] using
      (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).comp continuous_fst
  | inr i => simpa only [ambientCoordinates_inr] using continuous_snd

def ambientOrthant (n : ℕ) : Set (Space n × ℝ) :=
  {z | ∀ i, 0 ≤ ambientCoordinates n z i}

lemma isClosed_ambientOrthant (n : ℕ) : IsClosed (ambientOrthant n) := by
  unfold ambientOrthant
  rw [ofPred_forall]
  exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_ambientCoordinate i)

lemma pos_mem_interior_ambientOrthant {n : ℕ} {z : Space n × ℝ}
    (hz : ∀ i, 0 < ambientCoordinates n z i) : z ∈ interior (ambientOrthant n) := by
  have hopen : IsOpen {z : Space n × ℝ | ∀ i, 0 < ambientCoordinates n z i} := by
    rw [ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_ambientCoordinate i)
  exact (hopen.subset_interior_iff.mpr (fun p hp i => (hp i).le)) hz

lemma graph_not_mem_interior_epigraph {n : ℕ} (Ω : Set (Space n))
    (u : Space n → ℝ) (x : Space n) : (x,u x) ∉ interior (sourceEpigraph Ω u) := by
  intro hi
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hi)
  have hy : (x,u x-r/2) ∈ Metric.ball (x,u x) r := by
    rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
    constructor
    · simpa using hr
    · rw [Real.dist_eq]
      have : u x-r/2-u x = -(r/2) := by ring
      rw [this,abs_neg,abs_of_pos (half_pos hr)]
      linarith
  have hh := (hball hy).2
  dsimp at hh
  linarith

lemma affineGraph_not_mem_interior_epigraph {n : ℕ} (Ω : Set (Space n))
    (u : Space n → ℝ) (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ))
    (v : Space n × ℝ) (x : Space n) :
    L (x,u x)+v ∉ interior ((fun z => L z+v) '' sourceEpigraph Ω u) := by
  let F := L.toHomeomorph.trans (Homeomorph.addRight v)
  change F (x,u x) ∉ interior (F '' sourceEpigraph Ω u)
  rw [← F.image_interior]
  simpa only [F.injective.mem_set_image] using graph_not_mem_interior_epigraph Ω u x

/- Under local-set convergence to the orthant, every bounded boundary
point eventually lies in a thin coordinate strip. -/
theorem orthant_limit_boundary_strips {n : ℕ} {Cj : ℕ → Set (Space n × ℝ)}
    (h : LocalDistanceConverges Cj (ambientOrthant n))
    (hclj : ∀ j, IsClosed (Cj j)) (hcvj : ∀ j, Convex ℝ (Cj j))
    (hnej : ∀ j, (Cj j).Nonempty) {R ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ z ∈ Cj j, z ∉ interior (Cj j) → ‖z‖ ≤ R →
      ∃ i, |ambientCoordinates n z i| ≤ ε := by
  classical
  let S := Metric.closedBall (0 : Space n × ℝ) R ∩
    {z | ∀ i, ε ≤ ambientCoordinates n z i}
  have hS : IsCompact S := (isCompact_closedBall _ _).inter_right (by
    rw [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_ambientCoordinate i))
  have hSC : S ⊆ interior (ambientOrthant n) := fun z hz =>
    pos_mem_interior_ambientOrthant (fun i => hε.trans_le (hz.2 i))
  have he (i : Fin n ⊕ Unit) : ∀ᶠ j in atTop,
      Disjoint (Cj j) (Metric.closedBall (0 : Space n × ℝ) R ∩
        {z | ambientCoordinates n z i ≤ -ε}) := by
    apply h.eventually_disjoint_compact (isClosed_ambientOrthant n)
      ⟨0,by simp [ambientOrthant]⟩
      ((isCompact_closedBall _ _).inter_right
        (isClosed_le (continuous_ambientCoordinate i) continuous_const))
    rw [disjoint_left]
    intro z hz hz'
    have hh := hz i
    have hn : ambientCoordinates n z i ≤ -ε := hz'.2
    linarith
  filter_upwards [h.eventually_normed_compact_interior hclj hcvj hnej hS hSC,
    Filter.eventually_all.mpr he] with j hj he
  intro z hz hzi hzR
  have hzB : z ∈ Metric.closedBall (0 : Space n × ℝ) R := by simpa using hzR
  by_contra hn
  have hall : ∀ i, ε ≤ ambientCoordinates n z i := by
    intro i
    have hlo : -ε < ambientCoordinates n z i := by
      by_contra hh
      exact Set.disjoint_left.mp (he i) hz ⟨hzB,le_of_not_gt hh⟩
    have habs : ε < |ambientCoordinates n z i| := lt_of_not_ge (fun hh => hn ⟨i,hh⟩)
    have : ε < ambientCoordinates n z i := by
      rcases (lt_abs).mp habs with hh | hh
      · exact hh
      · linarith
    exact this.le
  exact hzi (hj ⟨hzB,hall⟩)

end AffineBernstein

end

end OAI
