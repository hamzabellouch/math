import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportVisitImage
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CenteredProfilePaths

namespace OAI

/-! # Controlled image paths along the selected finite generator chains -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

/-- Concatenate the actual selected edges. Both the metric constants and
the common image restriction are retained with a fixed finite loss. -/
theorem exists_finite_chain_path
    {X : Type*} [PseudoMetricSpace X] (L κ : ℝ) (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (S : Set X) :
    ∀ (N : ℕ) (vertex : Fin (N + 1) → X)
      (edge : ∀ j : Fin N, Path (vertex j.castSucc) (vertex j.succ)),
      vertex 0 ∈ S →
      (∀ j, PathMetricBound (edge j) L κ) →
      (∀ j t, edge j t ∈ S) →
      ∃ path : Path (vertex 0) (vertex (Fin.last N)),
        PathMetricBound path (L * 2 ^ N) (κ * 2 ^ N) ∧ ∀ t, path t ∈ S := by
  intro N
  induction N with
  | zero =>
      intro vertex edge hzero hbound hmem
      refine ⟨Path.refl (vertex 0), ?_, ?_⟩
      · intro s t
        simp only [Path.refl_apply, dist_self, pow_zero, mul_one]
        positivity
      · intro t
        exact hzero
  | succ N ih =>
      intro vertex edge hzero hbound hmem
      obtain ⟨path, hp, hpath⟩ := ih (fun j => vertex j.castSucc)
        (fun j => edge j.castSucc) hzero (fun j => hbound j.castSucc)
        (fun j => hmem j.castSucc)
      have hpow : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
      have he : PathMetricBound (edge (Fin.last N)) (L * 2 ^ N) (κ * 2 ^ N) :=
        (hbound _).mono (le_mul_of_one_le_right hL hpow) (le_mul_of_one_le_right hκ hpow)
      refine ⟨path.trans (edge (Fin.last N)), ?_, path_trans_range_mem hpath (hmem _)⟩
      have hb := hp.trans (mul_nonneg hκ (pow_nonneg (by norm_num) _)) he
      have hL' : L * 2 ^ (N + 1) = 2 * (L * 2 ^ N) := by rw [pow_succ]; ring
      have hκ' : κ * 2 ^ (N + 1) = 2 * (κ * 2 ^ N) := by rw [pow_succ]; ring
      rw [hL', hκ']
      exact hb

/-- Good profile bounds on both endpoint sheets control each outward and
return leg. A short switch costs only its Lipschitz error; concatenating
all selected switches yields one path with a controlled image. -/
theorem exists_profile_controlled_support_chain
    {G W : Type*} [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {N : ℕ} (vertex : Fin (N + 1) → G) (d₀ : G)
    (d f : Fin N → ℝ → G) (hd : ∀ j, Continuous (d j)) (hd₀ : ∀ j, d j 0 = 1)
    (hf : ∀ j, Continuous (f j)) (hf₀ : ∀ j, f j 0 = 1)
    (b : Fin N → ℝ) (hstep : ∀ j, vertex j.succ = vertex j.castSucc * f j (b j))
    (J : G → W) {K : ℝ≥0} (hJ : LipschitzWith K J)
    (center w₀ : W) (E : Set W) (r B B₀ L κ δ : ℝ)
    (hL : 0 ≤ L) (hκ : 0 ≤ κ) (hδ : 0 ≤ δ)
    (hstart : ‖J (vertex 0 * d₀) - center - r • w₀‖ ≤ B₀)
    (hbase : ∀ j, ∃ w ∈ E, ‖J (vertex j * d₀) - center - r • w‖ ≤ B)
    (hout : ∀ j t, ∃ w ∈ E,
      ‖J ((vertex j.castSucc * d₀) * d j (r * (t : unitInterval))) - center - r • w‖ ≤ B)
    (hback : ∀ j t, ∃ w ∈ E,
      ‖J ((vertex j.succ * d₀) * d j (r * (t : unitInterval))) - center - r • w‖ ≤ B)
    (hmetric : ∀ j, PathMetricBound
      (supportVisitPath (d j) (hd j) (hd₀ j) (f j) (hf j) (hf₀ j)
        (vertex j.castSucc) d₀ r (b j)) L κ)
    (hswitch : ∀ j t, dist
      (vertex j.castSucc * f j ((t : unitInterval) * b j) * (d₀ * d j r))
      ((vertex j.castSucc * d₀) * d j r) ≤ δ) :
    ∃ path : Path (vertex 0 * d₀) (vertex (Fin.last N) * d₀),
      PathMetricBound path (L * 2 ^ N) (κ * 2 ^ N) ∧
      ∀ t, ∃ w ∈ (fun z => z - w₀) '' E,
        ‖J (path t) - J (vertex 0 * d₀) - r • w‖ ≤ B + K * δ + B₀ := by
  let region := {g : G | ∃ w ∈ E, ‖J g - center - r • w‖ ≤ B + K * δ}
  let edge : ∀ j : Fin N, Path (vertex j.castSucc * d₀) (vertex j.succ * d₀) := fun j =>
    (supportVisitPath (d j) (hd j) (hd₀ j) (f j) (hf j) (hf₀ j)
      (vertex j.castSucc) d₀ r (b j)).cast rfl (congrArg (fun g => g * d₀) (hstep j))
  have hedge (j) : ∀ t, edge j t ∈ region := by
    have hreturn := hback j
    rw [hstep j] at hreturn
    exact supportVisitPath_image_bound (d j) (hd j) (hd₀ j) (f j) (hf j) (hf₀ j)
      J hJ (vertex j.castSucc) d₀ r (b j) center E hδ (hout j) hreturn (hswitch j)
  obtain ⟨path, hp, himage⟩ := exists_finite_chain_path L κ hL hκ region N
    (fun j => vertex j * d₀) edge (by
      obtain ⟨w, hw, hb⟩ := hbase 0
      exact ⟨w, hw, hb.trans (le_add_of_nonneg_right (mul_nonneg K.coe_nonneg hδ))⟩)
    hmetric hedge
  exact ⟨path, hp, centered_path_height_bound path J center w₀ E r (B + K * δ) B₀
    hstart himage⟩

end PolycyclicRecognition

end

end OAI
