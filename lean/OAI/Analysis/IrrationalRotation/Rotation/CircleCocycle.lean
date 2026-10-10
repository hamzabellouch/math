import OAI.Analysis.IrrationalRotation.Model.CircleWeights
import OAI.Analysis.IrrationalRotation.Rotation.CircleWeightSupport
import OAI.Analysis.IrrationalRotation.Sampling.CircleCharacterDynamics
import OAI.Analysis.IrrationalRotation.Rotation.FiniteSupportCocycle

namespace OAI

open MeasureTheory Set Function

namespace Invariant233.CircleWeights

variable {ι : Type*}

theorem phase_nonneg (θ : ℝ) (q : ι → ℤ) (i : ι) : 0 ≤ phase θ q i :=
  Int.fract_nonneg _

theorem coordinate_mem_Ico (q : ι → ℤ) (i : ι) (x : UnitAddCircle) :
    coordinate q i x ∈ Ico (0 : ℝ) 1 := by
  simpa only [coordinate, representative, zero_add] using
    (AddCircle.equivIco (1 : ℝ) 0 (q i • x)).property

theorem coordinate_rotate (θ : ℝ) (q : ι → ℤ) (i : ι)
    (k : ℤ) (x : UnitAddCircle) :
    coordinate q i (rotate θ k x) =
      Int.fract (coordinate q i x + (k : ℝ) * phase θ q i) := by
  exact CircleCharacterDynamics.character_orbit_representative (q i) k θ x

theorem cocycle_pos (θ : ℝ) (q : ι → ℤ) (c : ι → ℝ)
    (k : ℤ) (x : UnitAddCircle) : 0 < cocycle θ q c k x := Real.exp_pos _

theorem cocycle_zero (θ : ℝ) (q : ι → ℤ) (c : ι → ℝ) (x : UnitAddCircle) :
    cocycle θ q c 0 x = 1 := by
  simp only [cocycle, floorCost, Int.cast_zero, zero_mul, add_zero]
  exact FiniteSupportCocycle.exp_tsum_floor_zero
    (fun i => coordinate q i x) c (fun i => coordinate_mem_Ico q i x)

theorem exists_cocycle_set [Countable ι]
    (θ : ℝ) (q : ι → ℤ) (hq : ∀ i, q i ≠ 0) (c : ι → ℝ)
    (hphase : Summable (phase θ q)) :
    ∃ s : Set UnitAddCircle, MeasurableSet s ∧ (∀ᵐ x ∂volume, x ∈ s) ∧
      (∀ (k : ℤ) x, rotate θ k x ∈ s ↔ x ∈ s) ∧
      (∀ x ∈ s, ∀ k : ℤ,
        HasFiniteSupport (fun i => Int.floor (coordinate q i x + (k : ℝ) * phase θ q i))) ∧
      (∀ x ∈ s, ∀ k n : ℤ,
        cocycle θ q c (k + n) x =
          cocycle θ q c n (rotate θ k x) * cocycle θ q c k x) := by
  obtain ⟨s, hs, hfull, hinv, hfinite⟩ :=
    CircleWeightSupport.exists_invariant_conull_floor_support θ q hq
      (phase θ q) (phase_nonneg θ q) hphase
  refine ⟨s, hs, hfull, hinv, hfinite, ?_⟩
  intro x hx k n
  have hk : HasFiniteSupport
      (fun i => Int.floor (coordinate q i x + (k : ℝ) * phase θ q i)) := hfinite x hx k
  have hn : HasFiniteSupport (fun i =>
      Int.floor (Int.fract (coordinate q i x + (k : ℝ) * phase θ q i) +
        (n : ℝ) * phase θ q i)) := by
    have h := hfinite (rotate θ k x) ((hinv k x).mpr hx) n
    change HasFiniteSupport (fun i =>
      Int.floor (coordinate q i (rotate θ k x) + (n : ℝ) * phase θ q i)) at h
    simpa only [coordinate_rotate] using h
  simpa only [cocycle, floorCost, coordinate_rotate] using
    FiniteSupportCocycle.exp_tsum_floor_cocycle
      (fun i => coordinate q i x) (phase θ q) c k n hk hn

theorem measurable_cocycle [Countable ι] (θ : ℝ) (q : ι → ℤ)
    (hq : ∀ i, q i ≠ 0) (c : ι → ℝ) (k : ℤ) :
    Measurable (cocycle θ q c k) := by
  exact CircleWeightSupport.measurable_exp_weight q hq
    (fun i => (k : ℝ) * phase θ q i) c

theorem weight_mem_Ioc (θ : ℝ) (q : ι → ℤ) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (x : UnitAddCircle) : weight θ q c x ∈ Ioc (0 : ℝ) 1 := by
  simpa only [weight, cocycle, floorCost, Int.cast_one, one_mul, coordinate, representative] using
    CircleWeightSupport.exp_weight_mem_Ioc q (phase θ q) c (phase_nonneg θ q) hc x

theorem cocycle_antitone_of_finite_support (θ : ℝ) (q : ι → ℤ) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (x : UnitAddCircle)
    (hx : ∀ k : ℤ, HasFiniteSupport
      (fun i => Int.floor (coordinate q i x + (k : ℝ) * phase θ q i))) :
    Antitone (fun k : ℤ => cocycle θ q c k x) := by
  intro k n hkn
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply Summable.tsum_le_tsum _
    (FiniteSupportCocycle.summable_weighted_int c (hx k))
    (FiniteSupportCocycle.summable_weighted_int c (hx n))
  intro i
  apply mul_le_mul_of_nonneg_left _ (hc i)
  apply Int.cast_le.mpr
  apply Int.floor_mono
  exact add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_right (Int.cast_le.mpr hkn) (phase_nonneg θ q i))

theorem cocycle_le_one_of_nonneg (θ : ℝ) (q : ι → ℤ) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) {n : ℤ} (hn : 0 ≤ n) (x : UnitAddCircle) :
    cocycle θ q c n x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  apply neg_nonpos.mpr
  apply tsum_nonneg
  intro i
  apply mul_nonneg (hc i)
  apply Int.cast_nonneg
  apply Int.floor_nonneg.mpr
  exact add_nonneg (coordinate_mem_Ico q i x).1
    (mul_nonneg (Int.cast_nonneg hn) (phase_nonneg θ q i))

theorem orbit_ratio_of_cocycle_identities (θ : ℝ) (q : ι → ℤ) (c : ι → ℝ)
    (x : UnitAddCircle) (v n : ℤ)
    (hvn : cocycle θ q c (v + n) x =
      cocycle θ q c n (rotate θ v x) * cocycle θ q c v x)
    (hnv : cocycle θ q c (n + v) x =
      cocycle θ q c v (rotate θ n x) * cocycle θ q c n x) :
    cocycle θ q c n (rotate θ v x) / cocycle θ q c n x =
      cocycle θ q c v (rotate θ n x) / cocycle θ q c v x := by
  apply (div_eq_div_iff (ne_of_gt (cocycle_pos θ q c n x))
    (ne_of_gt (cocycle_pos θ q c v x))).mpr
  rw [← hvn, ← hnv, add_comm v n]

theorem positive_orbit_ratio_cap (θ : ℝ) (q : ι → ℤ) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (x : UnitAddCircle) (v n : ℤ) (hn : 0 ≤ n)
    (hvn : cocycle θ q c (v + n) x =
      cocycle θ q c n (rotate θ v x) * cocycle θ q c v x)
    (hnv : cocycle θ q c (n + v) x =
      cocycle θ q c v (rotate θ n x) * cocycle θ q c n x) :
    cocycle θ q c v (rotate θ n x) / cocycle θ q c v x ≤
      1 / cocycle θ q c n x := by
  rw [← orbit_ratio_of_cocycle_identities θ q c x v n hvn hnv]
  exact div_le_div_of_nonneg_right
    (cocycle_le_one_of_nonneg θ q c hc hn (rotate θ v x))
    (le_of_lt (cocycle_pos θ q c n x))

end Invariant233.CircleWeights

end OAI
