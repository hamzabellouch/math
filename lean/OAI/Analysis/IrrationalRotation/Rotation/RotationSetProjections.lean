import OAI.Analysis.IrrationalRotation.Rotation.RotationMeasurableLaws
import OAI.Analysis.IrrationalRotation.Rotation.RotationDiffuse

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace Invariant233.Rotation

def setCoefficient (s : Set Circle) : Circle → ℂ := s.indicator (fun _ => 1)

theorem measurable_setCoefficient {s : Set Circle} (hs : MeasurableSet s) :
    Measurable (setCoefficient s) := measurable_const.indicator hs

theorem norm_setCoefficient_le (s : Set Circle) (x : Circle) :
    ‖setCoefficient s x‖ ≤ 1 := by
  classical
  by_cases hx : x ∈ s <;> simp [setCoefficient, hx]

abbrev setProjection (θ : ℝ) (s : Set Circle) (hs : MeasurableSet s) :
    Hilbert →L[ℂ] Hilbert := borelSetProjection θ s hs

theorem setProjection_mem_algebra (θ : ℝ) (s : Set Circle) (hs : MeasurableSet s) :
    setProjection θ s hs ∈ algebra θ :=
  measurableRepresentation_mem_algebra θ _ _ _ _ _

theorem norm_setProjection_le (θ : ℝ) (s : Set Circle) (hs : MeasurableSet s) :
    ‖setProjection θ s hs‖ ≤ 1 :=
  measurableRepresentation_norm_le θ _ _ _ _ _

theorem setProjection_coordinates_ae (θ : ℝ) (s : Set Circle)
    (hs : MeasurableSet s) (v : Hilbert) :
    ∀ᵐ x ∂circleMeasure, ∀ k : ℤ,
      setProjection θ s hs v x k = setCoefficient s (action θ k x) * v x k :=
  measurableRepresentation_coordinates_ae θ _ _ _ _ _ v

theorem setProjection_inter (θ : ℝ) (s t : Set Circle)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    setProjection θ (s ∩ t) (hs.inter ht) = setProjection θ s hs * setProjection θ t ht := by
  unfold setProjection borelSetProjection
  rw [← measurableRepresentation_mul]
  apply measurableRepresentation_congr_ae θ
  exact Eventually.of_forall fun x => by
    classical
    by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;>
      simp [hxs, hxt]

theorem star_setProjection (θ : ℝ) (s : Set Circle) (hs : MeasurableSet s) :
    star (setProjection θ s hs) = setProjection θ s hs := by
  unfold setProjection borelSetProjection
  rw [← measurableRepresentation_star]
  apply measurableRepresentation_congr_ae θ
  exact Eventually.of_forall fun x => by
    classical
    by_cases hx : x ∈ s <;> simp [hx]

theorem isStarProjection_setProjection (θ : ℝ) (s : Set Circle)
    (hs : MeasurableSet s) : IsStarProjection (setProjection θ s hs) := by
  constructor
  · change setProjection θ s hs * setProjection θ s hs = setProjection θ s hs
    simpa only [Set.inter_self] using (setProjection_inter θ s s hs hs).symm
  · exact star_setProjection θ s hs

theorem setProjection_empty (θ : ℝ) : setProjection θ ∅ MeasurableSet.empty = 0 := by
  apply operator_ext_of_coordinates
  intro v
  filter_upwards [setProjection_coordinates_ae θ ∅ MeasurableSet.empty v,
    Lp.coeFn_zero Fiber 2 circleMeasure] with x hx hz k
  change setProjection θ ∅ MeasurableSet.empty v x k = (0 : Hilbert) x k
  rw [hx, hz]
  simp [setCoefficient]

theorem setProjection_mul_eq_zero_of_disjoint (θ : ℝ) (s t : Set Circle)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : Disjoint s t) :
    setProjection θ s hs * setProjection θ t ht = 0 := by
  rw [← setProjection_inter]
  simpa only [Set.disjoint_iff_inter_eq_empty.mp hst] using setProjection_empty θ

theorem vacuumFunctional_setProjection (θ : ℝ) (s : Set Circle)
    (hs : MeasurableSet s) :
    vacuumFunctional (setProjection θ s hs) = ((circleMeasure s).toReal : ℂ) := by
  unfold setProjection borelSetProjection
  rw [vacuumFunctional_measurableRepresentation]
  simp [integral_indicator hs, MeasureTheory.measureReal_def]

theorem setProjection_univ (θ : ℝ) : setProjection θ Set.univ MeasurableSet.univ = 1 := by
  apply operator_ext_of_coordinates
  intro v
  filter_upwards [setProjection_coordinates_ae θ Set.univ MeasurableSet.univ v] with x hx k
  change setProjection θ Set.univ MeasurableSet.univ v x k = v x k
  rw [hx]
  simp [setCoefficient]

theorem setProjection_union (θ : ℝ) (s t : Set Circle)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : Disjoint s t) :
    setProjection θ (s ∪ t) (hs.union ht) =
      setProjection θ s hs + setProjection θ t ht := by
  apply operator_ext_of_coordinates
  intro v
  filter_upwards [setProjection_coordinates_ae θ (s ∪ t) (hs.union ht) v,
      setProjection_coordinates_ae θ s hs v, setProjection_coordinates_ae θ t ht v,
      Lp.coeFn_add (setProjection θ s hs v) (setProjection θ t ht v)]
      with x hstx hsx htx hadd k
  change setProjection θ (s ∪ t) (hs.union ht) v x k =
    (setProjection θ s hs v + setProjection θ t ht v) x k
  rw [hstx, hadd]
  change setCoefficient (s ∪ t) (action θ k x) * v x k =
    setProjection θ s hs v x k + setProjection θ t ht v x k
  rw [hsx, htx]
  classical
  by_cases hxs : action θ k x ∈ s
  · have hxt : action θ k x ∉ t := fun ht' => Set.disjoint_left.mp hst hxs ht'
    simp [setCoefficient, hxs, hxt]
  · by_cases hxt : action θ k x ∈ t <;> simp [setCoefficient, hxs, hxt]

theorem setProjection_biUnion {ι : Type*} (θ : ℝ) (t : Finset ι)
    (s : ι → Set Circle) (hs : ∀ i, MeasurableSet (s i))
    (hdisj : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Disjoint (s i) (s j)) :
    setProjection θ (⋃ i ∈ t, s i) (Finset.measurableSet_biUnion t (fun i _ => hs i)) =
      ∑ i ∈ t, setProjection θ (s i) (hs i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using setProjection_empty θ
  | @insert a t ha ih =>
    have hdisjt : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Disjoint (s i) (s j) := by
      intro i hi j hj hij
      exact hdisj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have had : Disjoint (s a) (⋃ i ∈ t, s i) := by
      rw [Set.disjoint_iUnion_right]
      intro i
      rw [Set.disjoint_iUnion_right]
      intro hi
      exact hdisj a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
        (by intro h; exact ha (h ▸ hi))
    have hu : (⋃ i ∈ insert a t, s i) = s a ∪ ⋃ i ∈ t, s i := by simp
    simp only [hu, Finset.sum_insert ha]
    rw [setProjection_union θ (s a) (⋃ i ∈ t, s i) (hs a)
      (Finset.measurableSet_biUnion t (fun i _ => hs i)) had, ih hdisjt]

theorem sum_setProjection_eq_one {ι : Type*} (θ : ℝ) (t : Finset ι)
    (s : ι → Set Circle) (hs : ∀ i, MeasurableSet (s i))
    (hdisj : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Disjoint (s i) (s j))
    (hcover : (⋃ i ∈ t, s i) = Set.univ) :
    (∑ i ∈ t, setProjection θ (s i) (hs i)) = 1 := by
  rw [← setProjection_biUnion θ t s hs hdisj]
  simpa only [hcover] using setProjection_univ θ

theorem U_pow_coordinates_ae (n : ℕ) (v : Hilbert) :
    ∀ᵐ x ∂circleMeasure, ∀ k : ℤ, (U ^ n) v x k = v x (k - (n : ℤ)) := by
  induction n generalizing v with
  | zero => exact Eventually.of_forall fun x k => by simp
  | succ n ih =>
    filter_upwards [ih (U v), U_coordinates_ae v] with x hn hu k
    change (U ^ (n + 1)) v x k = _
    rw [pow_succ]
    change (U ^ n) (U v) x k = _
    rw [hn, hu]
    simp [Nat.cast_add, sub_sub]

theorem U_pow_mul_setProjection (θ : ℝ) (n : ℕ) (s : Set Circle)
    (hs : MeasurableSet s) :
    U ^ n * setProjection θ s hs =
      setProjection θ ((action θ (-(n : ℤ))) ⁻¹' s)
        (hs.preimage (action_continuous θ (-(n : ℤ))).measurable) * U ^ n := by
  apply operator_ext_of_coordinates
  intro v
  filter_upwards [U_pow_coordinates_ae n (setProjection θ s hs v),
      setProjection_coordinates_ae θ s hs v,
      setProjection_coordinates_ae θ ((action θ (-(n : ℤ))) ⁻¹' s)
        (hs.preimage (action_continuous θ (-(n : ℤ))).measurable) ((U ^ n) v),
      U_pow_coordinates_ae n v] with x hleft hsx hright hu k
  change (U ^ n) (setProjection θ s hs v) x k =
    setProjection θ ((action θ (-(n : ℤ))) ⁻¹' s)
      (hs.preimage (action_continuous θ (-(n : ℤ))).measurable) ((U ^ n) v) x k
  rw [hleft, hsx, hright, hu]
  congr 1
  have ha : action θ (k - (n : ℤ)) x =
      action θ (-(n : ℤ)) (action θ k x) := by
    rw [action_add]
    congr 1
    omega
  rw [ha]
  rfl

theorem U_pow_setProjection_star (θ : ℝ) (n : ℕ) (s : Set Circle)
    (hs : MeasurableSet s) :
    U ^ n * setProjection θ s hs * star (U ^ n) =
      setProjection θ ((action θ (-(n : ℤ))) ⁻¹' s)
        (hs.preimage (action_continuous θ (-(n : ℤ))).measurable) := by
  rw [U_pow_mul_setProjection, mul_assoc,
    Unitary.mul_star_self_of_mem ((unitary _).pow_mem U_mem_unitary n), mul_one]

theorem action_neg_preimage_eq_image (θ : ℝ) (n : ℤ) (s : Set Circle) :
    (action θ (-n)) ⁻¹' s = action θ n '' s := by
  ext x
  constructor
  · intro hx
    refine ⟨action θ (-n) x, hx, ?_⟩
    simp
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

theorem U_pow_setProjection_star_image (θ : ℝ) (n : ℕ) (s : Set Circle)
    (hs : MeasurableSet s) :
    ∃ ht : MeasurableSet (action θ (n : ℤ) '' s),
      U ^ n * setProjection θ s hs * star (U ^ n) =
        setProjection θ (action θ (n : ℤ) '' s) ht := by
  have ht := hs.preimage (action_continuous θ (-(n : ℤ))).measurable
  rw [action_neg_preimage_eq_image] at ht
  refine ⟨ht, ?_⟩
  simpa only [action_neg_preimage_eq_image] using U_pow_setProjection_star θ n s hs

end Invariant233.Rotation

end

end OAI
