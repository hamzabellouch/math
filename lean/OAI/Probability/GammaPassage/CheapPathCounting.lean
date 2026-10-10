import OAI.Probability.GammaPassage.CheapPath
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.BigOperators

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Finset
open scoped ENNReal

/-- There are four possible nearest-neighbor steps on the square lattice. -/
local instance cheapStepFintype : Fintype Step where
  elems := {Step.east, Step.west, Step.north, Step.south}
  complete d := by cases d <;> simp

private lemma cheapStep_card : Fintype.card Step = 4 := by decide

/-- Includes every actual step list of length n, without a simplicity restriction. -/
noncomputable def fixedStepLists (n : ℕ) : Finset (List Step) :=
  Finset.univ.image (fun f : Fin n → Step => List.ofFn f)

lemma mem_fixedStepLists (n : ℕ) (ds : List Step) :
    ds ∈ fixedStepLists n ↔ ds.length = n := by
  classical
  constructor
  · intro h
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp h
    exact List.length_ofFn
  · intro h
    subst n
    apply Finset.mem_image.mpr
    exact ⟨ds.get, Finset.mem_univ _, List.ofFn_get ds⟩

lemma card_fixedStepLists_le (n : ℕ) : (fixedStepLists n).card ≤ 4 ^ n := by
  classical
  calc
    (fixedStepLists n).card ≤ (Finset.univ : Finset (Fin n → Step)).card :=
      Finset.card_image_le
    _ = 4 ^ n := by rw [Finset.card_univ, Fintype.card_fun, cheapStep_card, Fintype.card_fin]

/-- The probability bound uses only the subfamily with distinct undirected edges. -/
noncomputable def fixedTrailLists (p : Vertex) (n : ℕ) : Finset (List Step) := by
  classical
  exact (fixedStepLists n).filter (fun ds => ((trace p ds).map traversalEdge).Nodup)

lemma mem_fixedTrailLists (p : Vertex) (n : ℕ) (ds : List Step) :
    ds ∈ fixedTrailLists p n ↔
      ds.length = n ∧ ((trace p ds).map traversalEdge).Nodup := by
  classical
  simp only [fixedTrailLists, Finset.mem_filter, mem_fixedStepLists]

lemma card_fixedTrailLists_le (p : Vertex) (n : ℕ) :
    (fixedTrailLists p n).card ≤ 4 ^ n := by
  classical
  exact (Finset.card_filter_le _ _).trans (card_fixedStepLists_le n)

/-- Exact event equality; there is no hidden restriction to a selected optimizer. -/
lemma fixedTrail_event_eq {Ω : Type*} (τ : Edge → Ω → ℝ)
    (p : Vertex) (n : ℕ) (t : ℝ) :
    {ω | ∃ ds : List Step, ds.length = n ∧
      ((trace p ds).map traversalEdge).Nodup ∧ pathCost (fun e => τ e ω) p ds ≤ t} =
    {ω | ∃ ds ∈ fixedTrailLists p n, pathCost (fun e => τ e ω) p ds ≤ t} := by
  ext ω
  simp only [Set.mem_ofPred_eq, mem_fixedTrailLists]
  constructor
  · rintro ⟨ds, hl, hn, hc⟩
    exact ⟨ds, ⟨hl, hn⟩, hc⟩
  · rintro ⟨ds, ⟨hl, hn⟩, hc⟩
    exact ⟨ds, hl, hn, hc⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- All actual fixed-length trails, with a proved four-way exponential count. -/
theorem GammaEnvironment.cheap_fixed_length_probability
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (s : ℝ) (hsp : 0 < s) (p : Vertex) (n : ℕ) (t : ℝ) :
    P {ω | ∃ ds : List Step, ds.length = n ∧
      ((trace p ds).map traversalEdge).Nodup ∧ pathCost (fun e => τ e ω) p ds ≤ t} ≤
      ((4 ^ n : ℕ) : ℝ≥0∞) *
        ((ENNReal.ofReal ((rate / (rate + s)) ^ shape)) ^ n /
          ENNReal.ofReal (Real.exp (-s * t))) := by
  rw [fixedTrail_event_eq]
  have hb := h.cheap_path_family_probability hs hr s hsp p (fixedTrailLists p n) n
    (fun ds hds => ((mem_fixedTrailLists p n ds).mp hds).symm) t
  refine hb.trans (mul_le_mul_left ?_ _)
  exact_mod_cast card_fixedTrailLists_le p n

end GammaFPP

end OAI
