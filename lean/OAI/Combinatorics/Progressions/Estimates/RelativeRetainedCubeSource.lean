import OAI.Combinatorics.Progressions.Estimates.RelativeCoefficientGeometry
import OAI.Combinatorics.Progressions.Lattices.RetainedResidueSources
import OAI.Combinatorics.Progressions.Probability.ScalarCubeWeightMassComparison

namespace OAI

section

namespace Erdos3

open scoped NNReal

def scalarCubeWeightPullbackMap {I : Type*} (c ρ : ℝ) (x : Option I → ℝ) : Option I → ℝ
  | none => c + ρ * x none
  | some i => ρ * x (some i)

theorem scalarCubeWeightPullbackMap_lipschitz {I : Type*} [Fintype I]
    (c : ℝ) (ρ : ℝ≥0) : LipschitzWith ρ (scalarCubeWeightPullbackMap (I := I) c ρ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (mul_nonneg ρ.coe_nonneg dist_nonneg)).mpr
  intro i
  have hi := mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) ρ.coe_nonneg
  rw [Real.dist_eq] at hi
  cases i with
  | none =>
      rw [Real.dist_eq]
      change |(c + (ρ : ℝ) * x none) - (c + (ρ : ℝ) * y none)| ≤ _
      calc
        _ = (ρ : ℝ) * |x none - y none| := by
          rw [show (c + (ρ : ℝ) * x none) - (c + (ρ : ℝ) * y none) =
            (ρ : ℝ) * (x none - y none) by ring, abs_mul, abs_of_nonneg ρ.coe_nonneg]
        _ ≤ _ := hi
  | some i =>
      rw [Real.dist_eq]
      change |(ρ : ℝ) * x (some i) - (ρ : ℝ) * y (some i)| ≤ _
      simpa only [← mul_sub, abs_mul, abs_of_nonneg ρ.coe_nonneg] using hi

theorem scalarCubeWeightPullback_lipschitz {I : Type*} [Fintype I]
    (w : (Option I → ℝ) → ℝ) {T : ℝ≥0} (hw : LipschitzWith T w) (c : ℝ) (ρ : ℝ≥0) :
    LipschitzWith (T * ρ) (fun x => w (scalarCubeWeightPullbackMap c ρ x)) :=
  hw.comp (scalarCubeWeightPullbackMap_lipschitz c ρ)

theorem scalarCubeWeightPullbackMap_sample {I : Type*} (parent root : ℤ) {N L : ℕ}
    (hN : 0 < N) (hL : 0 < L) (y : Option I → ℤ) :
    scalarCubeWeightPullbackMap (((root - parent : ℤ) : ℝ) / N) ((L : ℝ) / N)
      (fun i => (shiftScalarCube (-root) y i : ℝ) / L) =
        (fun i => (shiftScalarCube (-parent) y i : ℝ) / N) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  funext i
  cases i <;> simp only [scalarCubeWeightPullbackMap, shiftScalarCube, Int.cast_add,
    Int.cast_neg, Int.cast_sub]
  all_goals field_simp [hN', hL']
  all_goals ring

theorem translatedCubeWeight_pullback {I : Type*} (w : (Option I → ℝ) → ℝ)
    (parent root : ℤ) {N L : ℕ} (hN : 0 < N) (hL : 0 < L) (y : Option I → ℤ) :
    translatedCubeWeight L root
      (fun x => w (scalarCubeWeightPullbackMap (((root - parent : ℤ) : ℝ) / N) ((L : ℝ) / N) x)) y =
        translatedCubeWeight N parent w y := by
  unfold translatedCubeWeight
  exact congrArg w (scalarCubeWeightPullbackMap_sample parent root hN hL y)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem scalarCubeWeightPullbackMap_lipschitz_of_width {I : Type*} [Fintype I]
    (c : ℝ) {N L : ℕ} (hN : 0 < N) (R : ℝ≥0) (hwidth : (L : ℝ) ≤ R * N) :
    LipschitzWith R (scalarCubeWeightPullbackMap (I := I) c ((L : ℝ) / N)) := by
  let ρ : ℝ≥0 := ⟨(L : ℝ) / N, div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)⟩
  apply (scalarCubeWeightPullbackMap_lipschitz (I := I) c ρ).weaken
  change (L : ℝ) / N ≤ R
  exact (div_le_iff₀ (by exact_mod_cast hN : (0 : ℝ) < N)).mpr hwidth

theorem parentSliceWeight_lipschitz {I : Type*} [Fintype I]
    (w : (Option I → ℝ) → ℝ) {T : ℝ≥0} (hw : LipschitzWith T w)
    (c : ℝ) {N L : ℕ} (hN : 0 < N) (R : ℝ≥0) (hwidth : (L : ℝ) ≤ R * N) :
    LipschitzWith (T * R) (fun x => w (scalarCubeWeightPullbackMap c ((L : ℝ) / N) x)) :=
  hw.comp (scalarCubeWeightPullbackMap_lipschitz_of_width c hN R hwidth)

theorem coefficientWeightPullbackMap_sample (offset : ℤ) (stride : ℕ) {N L : ℕ}
    (hN : 0 < N) (hL : 0 < L) (z : ℤ) :
    scalarCubeWeightPullbackMap ((offset : ℝ) / N) (((stride * L : ℕ) : ℝ) / N)
      (fun _ : Option Empty => (z : ℝ) / L) =
        (fun _ => ((offset + (stride : ℤ) * z : ℤ) : ℝ) / N) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  funext i
  cases i with
  | none =>
      simp only [scalarCubeWeightPullbackMap, Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
      field_simp [hN', hL']
  | some a => exact a.elim

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal Classical

section Cube

variable {q M : ℕ} (L : ℕ) (root : ℤ) (m : Option (Fin q) → ℕ) (r : ∀ i, ZMod (m i))
  (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (w : (Option (Fin q) → ℝ) → ℝ)
  (B T η : ℝ≥0) (hη : 0 < η) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
  (hmass : (η : ℝ) ≤ ∫ x, w x ∂scalarCubeMeasure (Fin q))

noncomputable def smoothCubeSliceOfPositiveIntegral : SmoothCubeSlice q M (B / η) (T / η) where
  length := L
  root := root
  modulus := m
  residue := r
  modulus_pos := hm
  modulus_le := hmM
  weight x := w x / ∫ y, w y ∂scalarCubeMeasure (Fin q)
  weight_range := weight_div_range_of_lower w hη hmass hw
  weight_lipschitz := weight_div_lipschitz_of_lower w hη hmass hLip
  weight_integral := integral_weight_div_self _ w ((show (0 : ℝ) < η from hη).trans_le hmass).ne'

theorem smoothCubeSliceOfPositiveIntegral_law :
    let s := smoothCubeSliceOfPositiveIntegral L root m r hm hmM w B T η hη hw hLip hmass
    let v : s.Domain → ℝ := fun x => translatedCubeWeight L root w (s.finiteSlice.coordinates x)
    ∀ hv : 0 < ∑ x, v x,
      s.law (by
        change 0 < ∑ x, v x / ∫ y, w y ∂scalarCubeMeasure (Fin q)
        rw [← Finset.sum_div]
        exact div_pos hv ((show (0 : ℝ) < η from hη).trans_le hmass)) =
      FiniteProbabilityWeights.ofPositiveWeights v (fun x => (hw _).1) hv := by
  dsimp only
  intro hv
  exact FiniteProbabilityWeights.ofPositiveWeights_div _ _ hv
    ((show (0 : ℝ) < η from hη).trans_le hmass)

end Cube

section Coefficient

variable {M : ℕ} (L m : ℕ) (r : ZMod m) (hm : 0 < m) (hmM : m ≤ M)
  (w : (Option Empty → ℝ) → ℝ) (B T η : ℝ≥0) (hη : 0 < η)
  (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
  (hmass : (η : ℝ) ≤ ∫ x, w x ∂scalarCubeMeasure Empty)

noncomputable def smoothCoefficientSliceOfPositiveIntegral : SmoothCoefficientSlice M (B / η) (T / η) where
  length := L
  modulus := m
  residue := r
  modulus_pos := hm
  modulus_le := hmM
  weight x := w x / ∫ y, w y ∂scalarCubeMeasure Empty
  weight_range := weight_div_range_of_lower w hη hmass hw
  weight_lipschitz := weight_div_lipschitz_of_lower w hη hmass hLip
  weight_integral := integral_weight_div_self _ w ((show (0 : ℝ) < η from hη).trans_le hmass).ne'

theorem smoothCoefficientSliceOfPositiveIntegral_law :
    let s := smoothCoefficientSliceOfPositiveIntegral L m r hm hmM w B T η hη hw hLip hmass
    let v : s.Domain → ℝ := fun x => w (fun _ => (x.val : ℝ) / L)
    ∀ hv : 0 < ∑ x, v x,
      s.law (by
        change 0 < ∑ x, v x / ∫ y, w y ∂scalarCubeMeasure Empty
        rw [← Finset.sum_div]
        exact div_pos hv ((show (0 : ℝ) < η from hη).trans_le hmass)) =
      FiniteProbabilityWeights.ofPositiveWeights v (fun x => (hw _).1) hv := by
  dsimp only
  intro hv
  exact FiniteProbabilityWeights.ofPositiveWeights_div _ _ hv
    ((show (0 : ℝ) < η from hη).trans_le hmass)

end Coefficient

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal Classical

noncomputable def retainedSmoothCubeSlice {q M : ℕ} (L : ℕ) (root : ℤ)
    (m : Option (Fin q) → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (w : (Option (Fin q) → ℝ) → ℝ)
    (B T η : ℝ≥0) (hη : 0 < η) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hcut : scalarCubeNormalizationThreshold (Fin q) M (B / η) (T / η) ≤ L)
    (hretained : (η : ℝ) ≤
      𝔼 x : TranslatedResidueSupportedCube q L root m (shiftScalarCubeResidues (-root) m r),
        translatedCubeWeight L root w (supportedCubeCoordinates x.val.val)) :
    SmoothCubeSlice q M (B / (η / 2)) (T / (η / 2)) := by
  have hs := scalarCubeNormalizationThreshold_spec (Fin q) hcut
  have hmean : (η : ℝ) ≤ (scalarCubeResidueWeights (Fin q) L M hs.1 m r hm hmM hs.2.1).mean
      (fun z => w (fun i => (z i : ℝ) / L)) := by
    rw [scalarCube_translated_weight_mean q L M root hs.1 m r hm hmM hs.2.1 w]
    exact hretained
  have hmass : ((η / 2 : ℝ≥0) : ℝ) ≤ ∫ x, w x ∂scalarCubeMeasure (Fin q) := by
    simpa only [NNReal.coe_div, NNReal.coe_ofNat] using
      scalarCube_continuous_mass_of_discrete (Fin q) L M m r hm hmM w hη hw hLip hcut hmean
  exact smoothCubeSliceOfPositiveIntegral L root m r hm hmM w B T (η / 2) (half_pos hη) hw hLip hmass

noncomputable def retainedSmoothCoefficientSlice {M : ℕ} (L m : ℕ) (r : ZMod m)
    (hm : 0 < m) (hmM : m ≤ M) (w : (Option Empty → ℝ) → ℝ)
    (B T η : ℝ≥0) (hη : 0 < η) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hcut : scalarCubeNormalizationThreshold Empty M (B / η) (T / η) ≤ L)
    (hretained : (η : ℝ) ≤ 𝔼 x : ↥(coefficientResidueSet L m r), w (fun _ => (x.val : ℝ) / L)) :
    SmoothCoefficientSlice M (B / (η / 2)) (T / (η / 2)) := by
  have hs := scalarCubeNormalizationThreshold_spec Empty hcut
  have hsize : M ≤ L := by simpa only [Fintype.card_empty, zero_add, one_mul] using hs.2.1
  have hmean : (η : ℝ) ≤ (scalarCubeResidueWeights Empty L M hs.1 (fun _ => m) (fun _ => r)
      (fun _ => hm) (fun _ => hmM) hs.2.1).mean (fun z => w (fun i => (z i : ℝ) / L)) := by
    rw [scalarCube_coefficient_weight_mean L M hs.1 m r hm hmM hsize w]
    exact hretained
  have hmass : ((η / 2 : ℝ≥0) : ℝ) ≤ ∫ x, w x ∂scalarCubeMeasure Empty := by
    simpa only [NNReal.coe_div, NNReal.coe_ofNat] using
      scalarCube_continuous_mass_of_discrete Empty L M (fun _ => m) (fun _ => r)
        (fun _ => hm) (fun _ => hmM) w hη hw hLip hcut hmean
  exact smoothCoefficientSliceOfPositiveIntegral L m r hm hmM w B T (η / 2) (half_pos hη) hw hLip hmass

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def parentRetainedSmoothCubeSlice {q M : ℕ} (N L : ℕ) (parent root : ℤ)
    (m : Option (Fin q) → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (w : (Option (Fin q) → ℝ) → ℝ)
    (B T η : ℝ≥0) (hη : 0 < η) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hN : 0 < N) (hL : 0 < L) (hwidth : L ≤ 2 * N)
    (hcut : scalarCubeNormalizationThreshold (Fin q) M (B / η) ((T * 2) / η) ≤ L)
    (hretained : (η : ℝ) ≤
      𝔼 x : TranslatedResidueSupportedCube q L root m (shiftScalarCubeResidues (-root) m r),
        translatedCubeWeight N parent w (supportedCubeCoordinates x.val.val)) :
    SmoothCubeSlice q M (B / (η / 2)) ((T * 2) / (η / 2)) := by
  let v := fun x => w (scalarCubeWeightPullbackMap (((root - parent : ℤ) : ℝ) / N) ((L : ℝ) / N) x)
  have hv : LipschitzWith (T * 2) v := parentSliceWeight_lipschitz w hLip
    (((root - parent : ℤ) : ℝ) / N) hN 2 (by exact_mod_cast hwidth)
  apply retainedSmoothCubeSlice L root m r hm hmM v B (T * 2) η hη (fun x => hw _) hv hcut
  have he : (𝔼 x : TranslatedResidueSupportedCube q L root m (shiftScalarCubeResidues (-root) m r),
      translatedCubeWeight L root v (supportedCubeCoordinates x.val.val)) =
      𝔼 x : TranslatedResidueSupportedCube q L root m (shiftScalarCubeResidues (-root) m r),
        translatedCubeWeight N parent w (supportedCubeCoordinates x.val.val) := by
    apply Finset.expect_congr rfl
    intro x _
    exact translatedCubeWeight_pullback w parent root hN hL _
  exact hretained.trans_eq he.symm

noncomputable def parentRetainedSmoothCoefficientSlice {M : ℕ} (N L m : ℕ) (r : ZMod m)
    (hm : 0 < m) (hmM : m ≤ M) (offset : ℤ) (stride : ℕ) (w : (Option Empty → ℝ) → ℝ)
    (B T η : ℝ≥0) (hη : 0 < η) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hN : 0 < N) (hL : 0 < L) (hwidth : stride * L ≤ 2 * N)
    (hcut : scalarCubeNormalizationThreshold Empty M (B / η) ((T * 2) / η) ≤ L)
    (hretained : (η : ℝ) ≤ 𝔼 x : ↥(coefficientResidueSet L m r),
      w (fun _ => ((offset + (stride : ℤ) * x.val : ℤ) : ℝ) / N)) :
    SmoothCoefficientSlice M (B / (η / 2)) ((T * 2) / (η / 2)) := by
  let v := fun x => w (scalarCubeWeightPullbackMap ((offset : ℝ) / N) (((stride * L : ℕ) : ℝ) / N) x)
  have hv : LipschitzWith (T * 2) v := parentSliceWeight_lipschitz w hLip
    ((offset : ℝ) / N) hN 2 (by exact_mod_cast hwidth)
  apply retainedSmoothCoefficientSlice L m r hm hmM v B (T * 2) η hη (fun x => hw _) hv hcut
  have he : (𝔼 x : ↥(coefficientResidueSet L m r), v (fun _ => (x.val : ℝ) / L)) =
      𝔼 x : ↥(coefficientResidueSet L m r), w (fun _ => ((offset + (stride : ℤ) * x.val : ℤ) : ℝ) / N) := by
    apply Finset.expect_congr rfl
    intro x _
    exact congrArg w (coefficientWeightPullbackMap_sample offset stride hN hL x.val)
  exact hretained.trans_eq he.symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def parentRetainedCubeSource {q M : ℕ} (s : FiniteCubeSlice q)
    (N : ℕ) (parent : ℤ) (hm : ∀ i, 0 < s.modulus i) (hmM : ∀ i, s.modulus i ≤ M)
    (w : (Option (Fin q) → ℝ) → ℝ) (B T η : ℝ≥0)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hN : 0 < N) (hL : 0 < s.length) (hwidth : (s.length : ℝ) ≤ 2 * N)
    (hmean : (η : ℝ) ≤ 𝔼 x : s.Domain, translatedCubeWeight N parent w (s.coordinates x)) :
    RetainedCubeSlice q M B (T * 2) η := by
  let v := fun x => w (scalarCubeWeightPullbackMap (((s.root - parent : ℤ) : ℝ) / N) ((s.length : ℝ) / N) x)
  have hv : LipschitzWith (T * 2) v := parentSliceWeight_lipschitz w hLip
    (((s.root - parent : ℤ) : ℝ) / N) hN 2 hwidth
  apply retainedCubeSliceOfFinite s hm hmM v B (T * 2) η (fun x => hw _) hv
  have he : (𝔼 x : s.Domain, translatedCubeWeight s.length s.root v (s.coordinates x)) =
      𝔼 x : s.Domain, translatedCubeWeight N parent w (s.coordinates x) := by
    apply Finset.expect_congr rfl
    intro x _
    exact translatedCubeWeight_pullback w parent s.root hN hL _
  exact hmean.trans_eq he.symm

theorem parentRetainedCubeSource_finiteSlice {q M : ℕ} (s : FiniteCubeSlice q)
    (N : ℕ) (parent : ℤ) (hm : ∀ i, 0 < s.modulus i) (hmM : ∀ i, s.modulus i ≤ M)
    (w : (Option (Fin q) → ℝ) → ℝ) (B T η : ℝ≥0)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hN : 0 < N) (hL : 0 < s.length) (hwidth : (s.length : ℝ) ≤ 2 * N)
    (hmean : (η : ℝ) ≤ 𝔼 x : s.Domain, translatedCubeWeight N parent w (s.coordinates x)) :
    (parentRetainedCubeSource s N parent hm hmM w B T η hw hLip hN hL hwidth hmean).finiteSlice = s := by
  change (⟨s.length, s.root, s.modulus,
    shiftScalarCubeResidues (-s.root) s.modulus
      (shiftScalarCubeResidues s.root s.modulus s.residue)⟩ : FiniteCubeSlice q) = s
  have hres := shiftScalarCubeResidues_neg_cancel (-s.root) s.modulus s.residue
  simp only [neg_neg] at hres
  rw [hres]

theorem parentRetainedCubeSource_sliceWeight {q M : ℕ} (s : FiniteCubeSlice q)
    (N : ℕ) (parent : ℤ) (hm : ∀ i, 0 < s.modulus i) (hmM : ∀ i, s.modulus i ≤ M)
    (w : (Option (Fin q) → ℝ) → ℝ) (B T η : ℝ≥0)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hN : 0 < N) (hL : 0 < s.length) (hwidth : (s.length : ℝ) ≤ 2 * N)
    (hmean : (η : ℝ) ≤ 𝔼 x : s.Domain, translatedCubeWeight N parent w (s.coordinates x)) :
    let t := parentRetainedCubeSource s N parent hm hmM w B T η hw hLip hN hL hwidth hmean
    ∀ x : t.Domain, t.sliceWeight x = translatedCubeWeight N parent w (t.finiteSlice.coordinates x) := by
  intro t x
  exact translatedCubeWeight_pullback w parent s.root hN hL _

noncomputable def parentRetainedCoefficientSource {M : ℕ} (N L m : ℕ) (r : ZMod m)
    (offset : ℤ) (stride : ℕ) (hm : 0 < m) (hmM : m ≤ M)
    (w : (Option Empty → ℝ) → ℝ) (B T η : ℝ≥0)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hN : 0 < N) (hL : 0 < L) (hwidth : ((stride * L : ℕ) : ℝ) ≤ 2 * N)
    (hmean : (η : ℝ) ≤ 𝔼 x : ↥(coefficientResidueSet L m r),
      w (fun _ => ((offset + (stride : ℤ) * x.val : ℤ) : ℝ) / N)) :
    RetainedCoefficientSlice M B (T * 2) η := by
  let v := fun x => w (scalarCubeWeightPullbackMap ((offset : ℝ) / N) (((stride * L : ℕ) : ℝ) / N) x)
  have hv : LipschitzWith (T * 2) v := parentSliceWeight_lipschitz w hLip ((offset : ℝ) / N) hN 2 hwidth
  apply retainedCoefficientSliceOfFinite ⟨L, offset, stride, m, r⟩ hm hmM v B (T * 2) η (fun x => hw _) hv
  have he : (𝔼 x : ↥(coefficientResidueSet L m r), v (fun _ => (x.val : ℝ) / L)) =
      𝔼 x : ↥(coefficientResidueSet L m r), w (fun _ => ((offset + (stride : ℤ) * x.val : ℤ) : ℝ) / N) := by
    apply Finset.expect_congr rfl
    intro x _
    exact congrArg w (coefficientWeightPullbackMap_sample offset stride hN hL x.val)
  exact hmean.trans_eq he.symm

theorem parentRetainedCoefficientSource_finiteSlice {M : ℕ} (N L m : ℕ) (r : ZMod m)
    (offset : ℤ) (stride : ℕ) (hm : 0 < m) (hmM : m ≤ M)
    (w : (Option Empty → ℝ) → ℝ) (B T η : ℝ≥0)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hN : 0 < N) (hL : 0 < L) (hwidth : ((stride * L : ℕ) : ℝ) ≤ 2 * N)
    (hmean : (η : ℝ) ≤ 𝔼 x : ↥(coefficientResidueSet L m r),
      w (fun _ => ((offset + (stride : ℤ) * x.val : ℤ) : ℝ) / N)) :
    (parentRetainedCoefficientSource N L m r offset stride hm hmM w B T η hw hLip hN hL hwidth hmean).finiteSlice
      offset stride = ⟨L, offset, stride, m, r⟩ := rfl

theorem parentRetainedCoefficientSource_sliceWeight {M : ℕ} (N L m : ℕ) (r : ZMod m)
    (offset : ℤ) (stride : ℕ) (hm : 0 < m) (hmM : m ≤ M)
    (w : (Option Empty → ℝ) → ℝ) (B T η : ℝ≥0)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hN : 0 < N) (hL : 0 < L) (hwidth : ((stride * L : ℕ) : ℝ) ≤ 2 * N)
    (hmean : (η : ℝ) ≤ 𝔼 x : ↥(coefficientResidueSet L m r),
      w (fun _ => ((offset + (stride : ℤ) * x.val : ℤ) : ℝ) / N)) :
    let t := parentRetainedCoefficientSource N L m r offset stride hm hmM w B T η hw hLip hN hL hwidth hmean
    ∀ x : t.Domain, t.sliceWeight x = w (fun _ => ((offset + (stride : ℤ) * x.val : ℤ) : ℝ) / N) := by
  intro t x
  exact congrArg w (coefficientWeightPullbackMap_sample offset stride hN hL x.val)

end Erdos3

end

section

namespace Erdos3.RelativeProgression

open scoped BigOperators NNReal Classical

variable {δ : ℝ} (P : RelativeProgression δ)

def coefficientSlice : FiniteCoefficientSlice := ⟨P.length, P.root, P.canonicalStep, 1, 0⟩

theorem coefficientSlice_nonempty (hδ : 0 < δ) : Nonempty P.coefficientSlice.Domain := by
  refine ⟨⟨0, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨le_rfl, ?_⟩, ?_⟩⟩⟩
  · exact_mod_cast P.length_pos hδ
  · change (0 : ZMod 1) = 0
    rfl

noncomputable def coefficientReference (hδ : 0 < δ) : FiniteProbabilityWeights P.coefficientSlice.Domain := by
  let := P.coefficientSlice_nonempty hδ
  exact FiniteProbabilityWeights.uniform _

abbrev CoefficientResidueLabel (R : ℕ) := P.coefficientSlice.ResidueLabel R

noncomputable def retainedCoefficientSource (R : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (r : P.CoefficientResidueLabel R) (w : (Option Empty → ℝ) → ℝ) (B T η : ℝ≥0)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hr : r ∉ (P.coefficientReference hδ).lowWeightFibers (P.coefficientSlice.residueLabelMap R)
      (fun x => w (fun _ => ((P.coefficientSlice.value x : ℤ) : ℝ) / P.parentLength)) η) :
    RetainedCoefficientSlice (⌈2 / δ⌉₊ * R) B (T * 2) η := by
  let := P.coefficientSlice_nonempty hδ
  have hmean := P.coefficientSlice.retained_refineResidues_mean_ge R (one_dvd R) r
    (fun z => w (fun _ => (z : ℝ) / P.parentLength)) η hr
  have hV : 0 < ⌈2 / δ⌉₊ := P.canonicalStep_pos.trans_le (P.geometric_bounds hδ).2.2.1
  exact parentRetainedCoefficientSource P.parentLength P.length R r.val P.root P.canonicalStep
    hR (Nat.le_mul_of_pos_left R hV) w B T η hw hLip P.parent_pos (P.length_pos hδ)
    (P.geometric_bounds hδ).2.1.le hmean

theorem retainedCoefficientSource_length (R : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (r : P.CoefficientResidueLabel R) (w : (Option Empty → ℝ) → ℝ) (B T η : ℝ≥0)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hr : r ∉ (P.coefficientReference hδ).lowWeightFibers (P.coefficientSlice.residueLabelMap R)
      (fun x => w (fun _ => ((P.coefficientSlice.value x : ℤ) : ℝ) / P.parentLength)) η) :
    (P.retainedCoefficientSource R hδ hR r w B T η hw hLip hr).length = P.length := rfl

theorem retainedCoefficientSource_finiteSlice (R : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (r : P.CoefficientResidueLabel R) (w : (Option Empty → ℝ) → ℝ) (B T η : ℝ≥0)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hr : r ∉ (P.coefficientReference hδ).lowWeightFibers (P.coefficientSlice.residueLabelMap R)
      (fun x => w (fun _ => ((P.coefficientSlice.value x : ℤ) : ℝ) / P.parentLength)) η) :
    (P.retainedCoefficientSource R hδ hR r w B T η hw hLip hr).finiteSlice P.root P.canonicalStep =
      P.coefficientSlice.refineResidues R r := rfl

theorem retainedCoefficientSource_sliceWeight (R : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (r : P.CoefficientResidueLabel R) (w : (Option Empty → ℝ) → ℝ) (B T η : ℝ≥0)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hr : r ∉ (P.coefficientReference hδ).lowWeightFibers (P.coefficientSlice.residueLabelMap R)
      (fun x => w (fun _ => ((P.coefficientSlice.value x : ℤ) : ℝ) / P.parentLength)) η) :
    let t := P.retainedCoefficientSource R hδ hR r w B T η hw hLip hr
    ∀ x : t.Domain, t.sliceWeight x =
      w (fun _ => ((P.root + (P.canonicalStep : ℤ) * x.val : ℤ) : ℝ) / P.parentLength) := by
  intro t x
  exact congrArg w (coefficientWeightPullbackMap_sample P.root P.canonicalStep P.parent_pos (P.length_pos hδ) x.val)

end Erdos3.RelativeProgression

end

section

namespace Erdos3.RelativeProgression

open scoped BigOperators NNReal Classical

variable {δ : ℝ} (P : RelativeProgression δ)

noncomputable def cubeReference (q : ℕ) (hδ : 0 < δ) : FiniteProbabilityWeights (P.cubeSlice q).Domain := by
  let := P.cubeSlice_nonempty q hδ
  exact FiniteProbabilityWeights.uniform _

abbrev CubeResidueLabel (q R : ℕ) := (P.cubeSlice q).ResidueLabel (fun _ => P.canonicalStep * R)

noncomputable def retainedCubeSource (q R : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (r : P.CubeResidueLabel q R) (w : (Option (Fin q) → ℝ) → ℝ) (B T η : ℝ≥0)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hr : r ∉ (P.cubeReference q hδ).lowWeightFibers
      ((P.cubeSlice q).residueLabelMap (fun _ => P.canonicalStep * R))
      (fun x => translatedCubeWeight P.parentLength 0 w ((P.cubeSlice q).coordinates x)) η) :
    RetainedCubeSlice q (⌈2 / δ⌉₊ * R) B (T * 2) η := by
  let := P.cubeSlice_nonempty q hδ
  have hmean := (P.cubeSlice q).retained_refineResidues_mean_ge (fun _ => P.canonicalStep * R)
    (fun _ => ⟨R, rfl⟩) r (translatedCubeWeight P.parentLength 0 w) η hr
  exact parentRetainedCubeSource ((P.cubeSlice q).refineResidues (fun _ => P.canonicalStep * R) r)
    P.parentLength 0 (fun _ => Nat.mul_pos P.canonicalStep_pos hR)
    (fun _ => Nat.mul_le_mul_right R (P.geometric_bounds hδ).2.2.1)
    w B T η hw hLip P.parent_pos (P.width_pos hδ) (P.geometric_bounds hδ).2.1.le hmean

theorem retainedCubeSource_length (q R : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (r : P.CubeResidueLabel q R) (w : (Option (Fin q) → ℝ) → ℝ) (B T η : ℝ≥0)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hr : r ∉ (P.cubeReference q hδ).lowWeightFibers
      ((P.cubeSlice q).residueLabelMap (fun _ => P.canonicalStep * R))
      (fun x => translatedCubeWeight P.parentLength 0 w ((P.cubeSlice q).coordinates x)) η) :
    (P.retainedCubeSource q R hδ hR r w B T η hw hLip hr).length = P.width := rfl

theorem retainedCubeSource_root (q R : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (r : P.CubeResidueLabel q R) (w : (Option (Fin q) → ℝ) → ℝ) (B T η : ℝ≥0)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hr : r ∉ (P.cubeReference q hδ).lowWeightFibers
      ((P.cubeSlice q).residueLabelMap (fun _ => P.canonicalStep * R))
      (fun x => translatedCubeWeight P.parentLength 0 w ((P.cubeSlice q).coordinates x)) η) :
    (P.retainedCubeSource q R hδ hR r w B T η hw hLip hr).root = P.root := rfl

theorem retainedCubeSource_finiteSlice (q R : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (r : P.CubeResidueLabel q R) (w : (Option (Fin q) → ℝ) → ℝ) (B T η : ℝ≥0)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hr : r ∉ (P.cubeReference q hδ).lowWeightFibers
      ((P.cubeSlice q).residueLabelMap (fun _ => P.canonicalStep * R))
      (fun x => translatedCubeWeight P.parentLength 0 w ((P.cubeSlice q).coordinates x)) η) :
    (P.retainedCubeSource q R hδ hR r w B T η hw hLip hr).finiteSlice =
      (P.cubeSlice q).refineResidues (fun _ => P.canonicalStep * R) r := by
  change (⟨P.width, P.root, (fun _ => P.canonicalStep * R),
    shiftScalarCubeResidues (-P.root) (fun _ => P.canonicalStep * R)
      (shiftScalarCubeResidues P.root (fun _ => P.canonicalStep * R) r.val)⟩ : FiniteCubeSlice q) = _
  have he := shiftScalarCubeResidues_neg_cancel (-P.root) (fun _ => P.canonicalStep * R) r.val
  simp only [neg_neg] at he
  rw [he]
  rfl

theorem retainedCubeSource_sliceWeight (q R : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (r : P.CubeResidueLabel q R) (w : (Option (Fin q) → ℝ) → ℝ) (B T η : ℝ≥0)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hr : r ∉ (P.cubeReference q hδ).lowWeightFibers
      ((P.cubeSlice q).residueLabelMap (fun _ => P.canonicalStep * R))
      (fun x => translatedCubeWeight P.parentLength 0 w ((P.cubeSlice q).coordinates x)) η) :
    let t := P.retainedCubeSource q R hδ hR r w B T η hw hLip hr
    ∀ x : t.Domain, t.sliceWeight x = translatedCubeWeight P.parentLength 0 w (t.finiteSlice.coordinates x) := by
  intro t x
  exact translatedCubeWeight_pullback w 0 P.root P.parent_pos (P.width_pos hδ) _

end Erdos3.RelativeProgression

end

end OAI
