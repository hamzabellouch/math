import OAI.Analysis.Brenier.AffineCertificate
import OAI.Analysis.Brenier.Argmax
import OAI.Analysis.Brenier.SharpTargets

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators symmDiff

namespace Problem358.Sharpness

variable {d : ℕ}

/-- The central cell of the three-plane example. -/
def centralCell (i j : Fin d) (a b : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | |x i| ≤ a + b * x j}

/-- A fixed measurable choice of the outer slope. -/
def outerSlope (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  if x i < 0 then EuclideanSpace.single i (-1) else EuclideanSpace.single i 1

/-- A transport map selected from the maximum of -xᵢ, xᵢ and a+b*xⱼ. -/
def slabMap (i j : Fin d) (a b : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) := by
  classical
  exact if x ∈ centralCell i j a b then EuclideanSpace.single j b else outerSlope i x

lemma measurableSet_centralCell (i j : Fin d) (a b : ℝ) :
    MeasurableSet (centralCell i j a b) := by
  exact isClosed_le (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).abs
    (continuous_const.add (continuous_const.mul (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) j))) |>.measurableSet

lemma measurable_outerSlope (i : Fin d) : Measurable (outerSlope i) := by
  apply Measurable.ite
  · exact isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i) continuous_const |>.measurableSet
  · exact measurable_const
  · exact measurable_const

lemma measurable_slabMap (i j : Fin d) (a b : ℝ) : Measurable (slabMap i j a b) := by
  exact Measurable.ite (measurableSet_centralCell i j a b) measurable_const
    (measurable_outerSlope i)

lemma norm_outerSlope (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    ‖outerSlope i x‖ = 1 := by
  unfold outerSlope
  split_ifs <;> simp

lemma norm_sq_single_sub_single (i j : Fin d) (hij : i ≠ j) (r s : ℝ) :
    ‖EuclideanSpace.single i r - EuclideanSpace.single j s‖ ^ 2 = r ^ 2 + s ^ 2 := by
  rw [norm_sub_sq_real]
  simp [EuclideanSpace.inner_single_left, hij, Real.norm_eq_abs, sq_abs]

lemma norm_sq_outerSlope_sub_single (i j : Fin d) (hij : i ≠ j)
    (b : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖outerSlope i x - EuclideanSpace.single j b‖ ^ 2 = 1 + b ^ 2 := by
  unfold outerSlope
  split_ifs <;> rw [norm_sq_single_sub_single i j hij] <;> norm_num

lemma single_zero (j : Fin d) : (EuclideanSpace.single j (0 : ℝ)) = 0 := by
  ext k
  simp [PiLp.single_apply]

/-- The exact pointwise cost identity for the sharpness construction. -/
lemma slabMap_norm_sq_difference (i j : Fin d) (hij : i ≠ j)
    (a b : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖slabMap i j a 0 x - slabMap i j a b x‖ ^ 2 =
      (centralCell i j a 0 ∆ centralCell i j a b).indicator (fun _ => (1 : ℝ)) x +
      (centralCell i j a b).indicator (fun _ => b ^ 2) x := by
  classical
  by_cases hA : x ∈ centralCell i j a 0 <;>
    by_cases hB : x ∈ centralCell i j a b
  · simp [slabMap, single_zero, Set.indicator, hA, hB, Set.mem_symmDiff, Real.norm_eq_abs, sq_abs]
  · simp [slabMap, single_zero, Set.indicator, hA, hB, Set.mem_symmDiff, norm_outerSlope]
  · simp [slabMap, Set.indicator, hA, hB, Set.mem_symmDiff,
      norm_sq_outerSlope_sub_single i j hij]
  · simp [slabMap, Set.indicator, hA, hB, Set.mem_symmDiff]

/-- The three site vectors, ordered negative/positive/central. -/
def sites (i j : Fin d) (b : ℝ) : Fin 3 → EuclideanSpace ℝ (Fin d) :=
  ![EuclideanSpace.single i (-1), EuclideanSpace.single i 1, EuclideanSpace.single j b]

/-- The corresponding affine intercepts. -/
def intercepts (a : ℝ) : Fin 3 → ℝ := ![0, 0, a]

/-- The maximum of the three affine branches. -/
def potential (i j : Fin d) (a b : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  max |x i| (a + b * x j)

lemma inner_outerSlope (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (outerSlope i x) x = |x i| := by
  unfold outerSlope
  split_ifs with h
  · simp [EuclideanSpace.inner_single_left, abs_of_neg h]
  · simp [EuclideanSpace.inner_single_left, abs_of_nonneg (le_of_not_gt h)]

lemma site_affine_le_potential (i j : Fin d) (a b : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (k : Fin 3) :
    inner ℝ (sites i j b k) x + intercepts a k ≤ potential i j a b x := by
  fin_cases k
  · simpa [sites, intercepts, EuclideanSpace.inner_single_left, potential] using
      (neg_le_abs (x i)).trans (le_max_left |x i| (a + b * x j))
  · simpa [sites, intercepts, EuclideanSpace.inner_single_left, potential] using
      (le_abs_self (x i)).trans (le_max_left |x i| (a + b * x j))
  · simp [sites, intercepts, EuclideanSpace.inner_single_left, potential, add_comm]

/-- Everywhere, the selected slope is one of the three active affine branches. -/
lemma exists_active_site (i j : Fin d) (a b : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    ∃ k : Fin 3, slabMap i j a b x = sites i j b k ∧
      potential i j a b x = inner ℝ (sites i j b k) x + intercepts a k := by
  classical
  by_cases h : x ∈ centralCell i j a b
  · refine ⟨2, ?_, ?_⟩
    · simp [slabMap, h, sites]
    · have hc : |x i| ≤ a + b * x j := h
      simp [potential, max_eq_right hc, sites, intercepts,
        EuclideanSpace.inner_single_left, add_comm]
  · have hc : a + b * x j ≤ |x i| := le_of_lt (lt_of_not_ge h)
    by_cases hs : x i < 0
    · refine ⟨0, ?_, ?_⟩
      · simp [slabMap, h, outerSlope, hs, sites]
      · rw [potential, max_eq_left hc]
        simp [sites, intercepts, EuclideanSpace.inner_single_left, abs_of_neg hs]
    · refine ⟨1, ?_, ?_⟩
      · simp [slabMap, h, outerSlope, hs, sites]
      · rw [potential, max_eq_left hc]
        simp [sites, intercepts, EuclideanSpace.inner_single_left, abs_of_nonneg (le_of_not_gt hs)]

lemma slabMap_supporting (i j : Fin d) (a b : ℝ)
    (x z : EuclideanSpace ℝ (Fin d)) :
    potential i j a b x + inner ℝ (slabMap i j a b x) (z - x) ≤
      potential i j a b z := by
  obtain ⟨k, hk, ha⟩ := exists_active_site i j a b x
  rw [hk, ha, inner_sub_right]
  have h := site_affine_le_potential i j a b z k
  linarith

/-- The three sites are distinct whenever the coordinate directions are distinct. -/
lemma sites_injective (i j : Fin d) (hij : i ≠ j) (b : ℝ) :
    Function.Injective (sites i j b) := by
  intro k l h
  fin_cases k <;> fin_cases l <;> try rfl
  all_goals
    have he := congrArg (fun y : EuclideanSpace ℝ (Fin d) => y i) h
    norm_num [sites, EuclideanSpace.single, PiLp.single_apply, hij] at he

/-- Away from the two slanted boundary hyperplanes, the active slope is unique.
The positive-threshold assumption excludes the tie between the two outer branches. -/
lemma site_eq_slabMap_of_active (i j : Fin d) (a b : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (hq : 0 < a + b * x j)
    (htie : |x i| ≠ a + b * x j) (k : Fin 3)
    (hk : inner ℝ (sites i j b k) x + intercepts a k = potential i j a b x) :
    sites i j b k = slabMap i j a b x := by
  classical
  by_cases h : x ∈ centralCell i j a b
  · have hc : |x i| < a + b * x j := lt_of_le_of_ne h htie
    rw [potential, max_eq_right hc.le] at hk
    fin_cases k
    · simp [sites, intercepts, EuclideanSpace.inner_single_left] at hk
      exfalso
      linarith [neg_le_abs (x i)]
    · simp [sites, intercepts, EuclideanSpace.inner_single_left] at hk
      exfalso
      linarith [le_abs_self (x i)]
    · simp [sites, slabMap, h]
  · have hc : a + b * x j < |x i| := lt_of_not_ge h
    rw [potential, max_eq_left hc.le] at hk
    by_cases hs : x i < 0
    · rw [abs_of_neg hs] at hk
      fin_cases k
      · simp [sites, slabMap, h, outerSlope, hs]
      · simp [sites, intercepts, EuclideanSpace.inner_single_left] at hk
        exfalso
        linarith
      · simp [sites, intercepts, EuclideanSpace.inner_single_left] at hk
        exfalso
        rw [abs_of_neg hs] at hc
        linarith
    · have hs0 : 0 ≤ x i := le_of_not_gt hs
      rw [abs_of_nonneg hs0] at hk hc
      fin_cases k
      · simp [sites, intercepts, EuclideanSpace.inner_single_left] at hk
        exfalso
        linarith
      · simp [sites, slabMap, h, outerSlope, hs]
      · simp [sites, intercepts, EuclideanSpace.inner_single_left] at hk
        exfalso
        linarith

/-- A finite label for the cell partition and its pushforward law. -/
def slabIndex (i j : Fin d) (a b : ℝ) (x : EuclideanSpace ℝ (Fin d)) : Fin 3 := by
  classical
  exact if x ∈ centralCell i j a b then 2 else if x i < 0 then 0 else 1

lemma slabMap_eq_sites_slabIndex (i j : Fin d) (a b : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    slabMap i j a b x = sites i j b (slabIndex i j a b x) := by
  classical
  unfold slabMap slabIndex outerSlope
  split_ifs <;> simp [sites]

lemma slabMap_eq_site_iff (i j : Fin d) (hij : i ≠ j) (a b : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (k : Fin 3) :
    slabMap i j a b x = sites i j b k ↔ slabIndex i j a b x = k := by
  rw [slabMap_eq_sites_slabIndex]
  exact (sites_injective i j hij b).eq_iff

lemma slabMap_mem_range_sites (i j : Fin d) (a b : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    slabMap i j a b x ∈ Set.range (sites i j b) := by
  exact ⟨slabIndex i j a b x, (slabMap_eq_sites_slabIndex i j a b x).symm⟩

lemma slabIndex_eq_two_iff (i j : Fin d) (a b : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    slabIndex i j a b x = 2 ↔ |x i| ≤ a + b * x j := by
  classical
  unfold slabIndex
  by_cases hc : x ∈ centralCell i j a b <;> by_cases hs : x i < 0 <;>
    simp [hs, centralCell] at *

lemma slabIndex_eq_zero_iff (i j : Fin d) (a b : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (hq : 0 ≤ a + b * x j) :
    slabIndex i j a b x = 0 ↔ x i < -(a + b * x j) := by
  classical
  unfold slabIndex
  by_cases hc : x ∈ centralCell i j a b
  · have ha : |x i| ≤ a + b * x j := hc
    have hx : -(a + b * x j) ≤ x i := (abs_le.mp ha).1
    simp [hc]
    linarith
  · have ha : a + b * x j < |x i| := lt_of_not_ge hc
    by_cases hs : x i < 0
    · have hx : x i < -(a + b * x j) := by
        rw [abs_of_neg hs] at ha
        linarith
      simp [hc, hs]
      linarith
    · have hx : -(a + b * x j) ≤ x i := by linarith
      simp [hc, hs]
      linarith

lemma slabIndex_eq_one_iff (i j : Fin d) (a b : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (hq : 0 ≤ a + b * x j) :
    slabIndex i j a b x = 1 ↔ a + b * x j < x i := by
  classical
  unfold slabIndex
  by_cases hc : x ∈ centralCell i j a b
  · have ha : |x i| ≤ a + b * x j := hc
    have hx : x i ≤ a + b * x j := (abs_le.mp ha).2
    simp [hc]
    linarith
  · have ha : a + b * x j < |x i| := lt_of_not_ge hc
    by_cases hs : x i < 0
    · have hx : x i ≤ a + b * x j := by linarith
      simp [hc, hs]
      linarith
    · have hx : a + b * x j < x i := by
        simpa [abs_of_nonneg (le_of_not_gt hs)] using ha
      simp [hc, hs]
      linarith

lemma threshold_bounds (a t : ℝ) (ha : 0 ≤ a) (ht : |t| ≤ 1) :
    a / 2 ≤ a + (a / 2) * t ∧ a + (a / 2) * t ≤ 3 * a / 2 := by
  have ht' := abs_le.mp ht
  constructor <;> nlinarith

lemma norm_sites_le_one (i j : Fin d) (b : ℝ) (hb : |b| ≤ 1) (k : Fin 3) :
    ‖sites i j b k‖ ≤ 1 := by
  fin_cases k
  · simp [sites]
  · simp [sites]
  · simpa [sites, Real.norm_eq_abs] using hb

lemma abs_sites_coordinate_le_one (i j : Fin d) (b : ℝ) (hb : |b| ≤ 1)
    (k : Fin 3) (l : Fin d) : |sites i j b k l| ≤ 1 := by
  fin_cases k <;> simp [sites, EuclideanSpace.single, PiLp.single_apply]
  all_goals split_ifs <;> simp_all

lemma continuous_potential (i j : Fin d) (a b : ℝ) :
    Continuous (potential i j a b) := by
  exact (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).abs.max
    (continuous_const.add (continuous_const.mul
      (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) j)))

/-- Integration reduces the map-distance computation to the masses of two cells. -/
lemma integral_slabMap_norm_sq_difference (i j : Fin d) (hij : i ≠ j) (a b : ℝ)
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ρ] :
    (∫ x, ‖slabMap i j a 0 x - slabMap i j a b x‖ ^ 2 ∂ρ) =
      (ρ (centralCell i j a 0 ∆ centralCell i j a b)).toReal +
        b ^ 2 * (ρ (centralCell i j a b)).toReal := by
  have hA := measurableSet_centralCell i j a 0
  have hB := measurableSet_centralCell i j a b
  simp_rw [slabMap_norm_sq_difference i j hij]
  rw [integral_add ((integrable_const (1 : ℝ)).indicator (hA.symmDiff hB))
    ((integrable_const (b ^ 2)).indicator hB)]
  rw [integral_indicator_const _ (hA.symmDiff hB), integral_indicator_const _ hB]
  simp [Measure.real, mul_comm]

end Problem358.Sharpness

end

noncomputable section
namespace Problem358.Sharpness
variable {d : ℕ}

lemma potential_eq_finiteAffine (i j : Fin d) (a b : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    potential i j a b x = FiniteAffine.potential (sites i j b) (intercepts a) x := by
  apply le_antisymm
  · obtain ⟨k, _, hk⟩ := exists_active_site i j a b x
    rw [hk, real_inner_comm]
    exact FiniteAffine.affine_le_potential _ _ _ _
  · apply FiniteAffine.potential_le_of_affine_le
    intro k
    rw [real_inner_comm]
    exact site_affine_le_potential i j a b x k

lemma exists_maximizes_site (i j : Fin d) (a b : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    ∃ k : Fin 3, slabMap i j a b x = sites i j b k ∧
      FiniteAffine.Maximizes (sites i j b) (intercepts a) x k := by
  obtain ⟨k, hk, ha⟩ := exists_active_site i j a b x
  refine ⟨k, hk, ?_⟩
  apply (FiniteAffine.potential_eq_iff_maximizes _ _ _ _).mp
  rw [← potential_eq_finiteAffine, ha, real_inner_comm]

lemma slabIndex_maximizes (i j : Fin d) (hij : i ≠ j) (a b : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    FiniteAffine.Maximizes (sites i j b) (intercepts a) x (slabIndex i j a b x) := by
  obtain ⟨k, hk, ha⟩ := exists_maximizes_site i j a b x
  have hk' := (slabMap_eq_site_iff i j hij a b x k).mp hk
  rw [hk']
  exact ha

lemma eq_slabMap_of_maximizes (i j : Fin d) (a b : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (hq : 0 < a + b * x j)
    (htie : |x i| ≠ a + b * x j) (k : Fin 3)
    (hk : FiniteAffine.Maximizes (sites i j b) (intercepts a) x k) :
    sites i j b k = slabMap i j a b x := by
  apply site_eq_slabMap_of_active i j a b x hq htie k
  have h := (FiniteAffine.potential_eq_iff_maximizes _ _ _ _).mpr hk
  rw [← potential_eq_finiteAffine] at h
  rw [real_inner_comm]
  exact h.symm

end Problem358.Sharpness

open MeasureTheory
open scoped BigOperators ENNReal

namespace Problem358.Sharpness

variable {d : ℕ}

/-- The selected branch, with central branches taking precedence on ties. -/
def slabSelector (i j : Fin d) (a b : ℝ) (x : E d) : Fin 3 := by
  classical
  exact if x ∈ centralCell i j a b then 2 else if x i < 0 then 0 else 1

lemma measurable_slabSelector (i j : Fin d) (a b : ℝ) :
    Measurable (slabSelector i j a b) := by
  apply Measurable.ite (measurableSet_centralCell i j a b) measurable_const
  apply Measurable.ite _ measurable_const measurable_const
  exact isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i)
    continuous_const |>.measurableSet

lemma slabMap_eq_sites_selector (i j : Fin d) (a b : ℝ) (x : E d) :
    slabMap i j a b x = sites i j b (slabSelector i j a b x) := by
  classical
  by_cases hc : x ∈ centralCell i j a b <;>
    by_cases hn : x i < 0 <;>
    simp [slabMap, slabSelector, outerSlope, sites, hc, hn]

lemma slabSelector_preimage_zero (i j : Fin d) (a b : ℝ) :
    slabSelector i j a b ⁻¹' {0} = {x | x ∉ centralCell i j a b ∧ x i < 0} := by
  classical
  ext x
  by_cases hc : x ∈ centralCell i j a b <;>
    by_cases hn : x i < 0 <;> simp [slabSelector, hc, hn]

lemma slabSelector_preimage_one (i j : Fin d) (a b : ℝ) :
    slabSelector i j a b ⁻¹' {1} = {x | x ∉ centralCell i j a b ∧ 0 ≤ x i} := by
  classical
  ext x
  by_cases hc : x ∈ centralCell i j a b <;>
    simp [slabSelector, hc, not_lt]

lemma slabSelector_preimage_two (i j : Fin d) (a b : ℝ) :
    slabSelector i j a b ⁻¹' {2} = centralCell i j a b := by
  classical
  ext x
  by_cases hc : x ∈ centralCell i j a b <;>
    by_cases hn : x i < 0 <;> simp [slabSelector, hc, hn]

/-- Exact cell masses immediately determine the pushforward law of the slab map. -/
lemma map_slabMap_of_cell_masses (ρ : Measure (E d)) (i j : Fin d) (a b : ℝ)
    (hneg : ρ {x | x ∉ centralCell i j a b ∧ x i < 0} = ENNReal.ofReal ((1-a)/2))
    (hpos : ρ {x | x ∉ centralCell i j a b ∧ 0 ≤ x i} = ENNReal.ofReal ((1-a)/2))
    (hcent : ρ (centralCell i j a b) = ENNReal.ofReal a) :
    Measure.map (slabMap i j a b) ρ =
      ∑ k, sharpWeights a k • Measure.dirac (sites i j b k) := by
  have hm : ∀ k, ρ (slabSelector i j a b ⁻¹' {k}) = sharpWeights a k := by
    intro k
    fin_cases k
    · change ρ (slabSelector i j a b ⁻¹' {0}) = ENNReal.ofReal ((1-a)/2)
      rw [slabSelector_preimage_zero]
      exact hneg
    · change ρ (slabSelector i j a b ⁻¹' {1}) = ENNReal.ofReal ((1-a)/2)
      rw [slabSelector_preimage_one]
      exact hpos
    · change ρ (slabSelector i j a b ⁻¹' {2}) = ENNReal.ofReal a
      rw [slabSelector_preimage_two]
      exact hcent
  have heq : slabMap i j a b = fun x => sites i j b (slabSelector i j a b x) := by
    funext x
    exact slabMap_eq_sites_selector i j a b x
  rw [heq]
  exact map_finite_selector_of_masses ρ (slabSelector i j a b)
    (measurable_slabSelector i j a b) (sites i j b) (sharpWeights a) hm

end Problem358.Sharpness

namespace Problem358

lemma sharpAtoms_eq_sites (d : ℕ) (hd : 2 ≤ d) (b : ℝ) :
    sharpAtoms d hd b = Sharpness.sites (sharpAxis0 d hd) (sharpAxis1 d hd) b := rfl

lemma sharpAxis_ne (d : ℕ) (hd : 2 ≤ d) : sharpAxis0 d hd ≠ sharpAxis1 d hd := by
  simp [sharpAxis0, sharpAxis1]

/-- The branch law in the target-family notation used by the sharpness theorem. -/
lemma map_slabMap_eq_sharpTarget_of_cell_masses (d : ℕ) (hd : 2 ≤ d)
    (ρ : Measure (E d)) (a b : ℝ)
    (hneg : ρ {x | x ∉ Sharpness.centralCell (sharpAxis0 d hd) (sharpAxis1 d hd) a b ∧
      x (sharpAxis0 d hd) < 0} = ENNReal.ofReal ((1-a)/2))
    (hpos : ρ {x | x ∉ Sharpness.centralCell (sharpAxis0 d hd) (sharpAxis1 d hd) a b ∧
      0 ≤ x (sharpAxis0 d hd)} = ENNReal.ofReal ((1-a)/2))
    (hcent : ρ (Sharpness.centralCell (sharpAxis0 d hd) (sharpAxis1 d hd) a b) =
      ENNReal.ofReal a) :
    Measure.map (Sharpness.slabMap (sharpAxis0 d hd) (sharpAxis1 d hd) a b) ρ =
      sharpTarget d hd a b := by
  exact Sharpness.map_slabMap_of_cell_masses ρ (sharpAxis0 d hd) (sharpAxis1 d hd)
    a b hneg hpos hcent

end Problem358

end

end OAI
