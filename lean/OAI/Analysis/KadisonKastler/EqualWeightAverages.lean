import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators

namespace OAI

/-! # Equal-weight approximation of closed convex hulls

Natural multiplicities approximate any finite convex combination: round
scaled weights down, normalize their total, and repeat the corresponding
points. No compactness or dimension restriction on the normed space is used.
-/

namespace KadisonKastler

open Filter Set
open scoped BigOperators Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A natural-weight mean is literally an equal-weight mean with repetitions. -/
theorem exists_equalWeightAverage_of_natWeights {ι : Type*} [Fintype ι]
    (c : ι → ℕ) (f : ι → E) (hc : 0 < ∑ i, c i) :
    ∃ n : ℕ, 0 < n ∧ ∃ g : Fin n → E,
      (∀ j, g j ∈ Set.range f) ∧
      (n : ℝ)⁻¹ • ∑ j, g j = ((∑ i, c i : ℕ) : ℝ)⁻¹ • ∑ i, (c i : ℝ) • f i := by
  let K := Σ i, Fin (c i)
  have hcard : Fintype.card K = ∑ i, c i := by simp [K]
  have hK : 0 < Fintype.card K := hcard.symm ▸ hc
  let σ : Fin (Fintype.card K) ≃ K := (Fintype.equivFin K).symm
  refine ⟨Fintype.card K, hK, fun j => f (σ j).1, ?_, ?_⟩
  · intro j
    exact ⟨(σ j).1, rfl⟩
  · have hsum : (∑ j : Fin (Fintype.card K), f (σ j).1) =
        ∑ i, (c i : ℝ) • f i := by
      calc
        _ = ∑ k : K, f k.1 := σ.sum_comp (fun k : K => f k.1)
        _ = _ := by
          rw [Fintype.sum_sigma]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            Nat.cast_smul_eq_nsmul ℝ]
    rw [hsum, hcard]

private theorem rounded_mean_eq {ι : Type*} [Fintype ι]
    (c : ι → ℕ) (f : ι → E) {t : ℝ} (ht : t ≠ 0) (hc : 0 < ∑ i, c i) :
    (∑ i, (c i : ℝ) / t)⁻¹ • ∑ i, ((c i : ℝ) / t) • f i =
      ((∑ i, c i : ℕ) : ℝ)⁻¹ • ∑ i, (c i : ℝ) • f i := by
  have hsum : (∑ i, (c i : ℝ) / t) = ((∑ i, c i : ℕ) : ℝ) / t := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul, Nat.cast_sum]
  have hnum : (∑ i, ((c i : ℝ) / t) • f i) =
      t⁻¹ • ∑ i, (c i : ℝ) • f i := by
    simp only [Finset.smul_sum, smul_smul, div_eq_mul_inv]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]
  rw [hsum, hnum, smul_smul]
  congr 1
  have hc0 : (((∑ i, c i : ℕ) : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  field_simp

/-- Finite convex combinations can be approximated by means with repeated points. -/
theorem exists_equalWeightAverage_of_convexCombination {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (f : ι → E) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ g : Fin n → E,
      (∀ j, g j ∈ Set.range f) ∧
      ‖(n : ℝ)⁻¹ • ∑ j, g j - ∑ i, w i • f i‖ < ε := by
  let c (t : ℝ) (i : ι) : ℕ := ⌊w i * t⌋₊
  let r (t : ℝ) (i : ι) : ℝ := (c t i : ℝ) / t
  have hr (i : ι) : Tendsto (fun t : ℝ => r t i) atTop (𝓝 (w i)) :=
    tendsto_nat_floor_mul_div_atTop (hw i)
  have hs : Tendsto (fun t : ℝ => ∑ i, r t i) atTop (𝓝 1) := by
    simpa only [hw1] using tendsto_finsetSum Finset.univ (fun i _ => hr i)
  have hf : Tendsto (fun t : ℝ => ∑ i, r t i • f i) atTop (𝓝 (∑ i, w i • f i)) :=
    tendsto_finsetSum Finset.univ (fun i _ => (hr i).smul tendsto_const_nhds)
  have hv : Tendsto (fun t : ℝ => (∑ i, r t i)⁻¹ • ∑ i, r t i • f i)
      atTop (𝓝 (∑ i, w i • f i)) := by
    simpa only [inv_one, one_smul] using (hs.inv₀ (by norm_num)).smul hf
  have hpos : ∀ᶠ t : ℝ in atTop, 0 < ∑ i, r t i :=
    hs.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hnear := (Metric.tendsto_nhds.mp hv) ε hε
  obtain ⟨t, ht, hcpos, hclose⟩ :=
    ((eventually_gt_atTop (0 : ℝ)).and (hpos.and hnear)).exists
  have hcount : 0 < ∑ i, c t i := by
    apply Nat.pos_iff_ne_zero.mpr
    intro hz
    have he : (∑ i, r t i) = 0 := by
      change (∑ i, (c t i : ℝ) / t) = 0
      simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum, hz]
      simp
    linarith
  obtain ⟨n, hn, g, hg, heq⟩ := exists_equalWeightAverage_of_natWeights (c t) f hcount
  refine ⟨n, hn, g, hg, ?_⟩
  rw [heq, ← rounded_mean_eq (c t) f ht.ne' hcount]
  change ‖(∑ i, r t i)⁻¹ • ∑ i, r t i • f i - ∑ i, w i • f i‖ < ε
  simpa only [dist_eq_norm] using hclose

/-- Equal-weight means of points of a set are dense in its convex hull. -/
theorem exists_equalWeightAverage_of_mem_convexHull {S : Set E} {z : E}
    (hz : z ∈ convexHull ℝ S) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ f : Fin n → E,
      (∀ i, f i ∈ S) ∧ ‖(n : ℝ)⁻¹ • ∑ i, f i - z‖ < ε := by
  obtain ⟨ι, hι, w, f, hw, hw1, hf, heq⟩ := mem_convexHull_iff_exists_fintype.mp hz
  let : Fintype ι := hι
  obtain ⟨n, hn, g, hg, hclose⟩ :=
    exists_equalWeightAverage_of_convexCombination w f hw hw1 hε
  refine ⟨n, hn, g, ?_, ?_⟩
  · intro i
    obtain ⟨j, hj⟩ := hg i
    exact hj ▸ hf j
  · simpa only [heq] using hclose

/-- Every point of the closed convex hull is approximated by a finite
nonempty equal-weight average of points of the original set. -/
theorem exists_equalWeightAverage_of_mem_closedConvexHull {S : Set E} {z : E}
    (hz : z ∈ closure (convexHull ℝ S)) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ f : Fin n → E,
      (∀ i, f i ∈ S) ∧ ‖(n : ℝ)⁻¹ • ∑ i, f i - z‖ < ε := by
  obtain ⟨x, hx, hzx⟩ := Metric.mem_closure_iff.mp hz (ε / 2) (by positivity)
  obtain ⟨n, hn, f, hf, hfx⟩ :=
    exists_equalWeightAverage_of_mem_convexHull hx (show 0 < ε / 2 by positivity)
  refine ⟨n, hn, f, hf, ?_⟩
  have hxz : ‖x - z‖ < ε / 2 := by simpa only [dist_eq_norm, norm_sub_rev] using hzx
  calc
    _ ≤ ‖(n : ℝ)⁻¹ • ∑ i, f i - x‖ + ‖x - z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε := by linarith

end

end KadisonKastler

end OAI
