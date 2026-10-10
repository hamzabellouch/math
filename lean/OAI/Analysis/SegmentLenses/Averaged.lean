import OAI.Analysis.SegmentLenses.Completed

namespace OAI

/-!
# All-radius averaged estimates and asymptotic moduli
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section AveragedFiniteHead
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V]
  [LocallyFiniteOrderBot V] [TreeOrder V] [SegmentSystem V] [IntervalSegments V]


theorem finite_head_average {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (x y : FullDual V) (hx : head H x = x) (hxn : ‖x‖ = 1)
    (hy : head H y = 0) (hyn : 1 ≤ ‖y‖) {t : ℝ} (ht : 0 < t) :
    (Real.sqrt (1 + t ^ 2 / 4) - 1) / 2 ≤
      (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1 := by
  let R := max ‖x + t • y‖ ‖x - t • y‖
  have hR : 0 ≤ R := le_trans (norm_nonneg _) (le_max_left _ _)
  have hp : ‖x + t • y‖ ≤ R := le_max_left _ _
  have hm : ‖x - t • y‖ ≤ R := le_max_right _ _
  have hc : 1 ≤ R := by simpa only [hxn] using norm_center_le x (t • y) R hp hm
  have hty : tail H (t • y) = t • y := by
    change t • y - headLinear H (t • y) = t • y
    rw [map_smul, headLinear_apply, hy, smul_zero, sub_zero]
  have htail := completed_main_tail hH x (t • y) hx R hR hp hm
  rw [hty, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hxn] at htail
  have htn : t ≤ t * ‖y‖ := le_mul_of_one_le_right ht.le hyn
  have hd : 0 ≤ R ^ 2 - 1 ^ 2 := by nlinarith
  have hs := Real.sq_sqrt hd
  have hroot : Real.sqrt (1 + t ^ 2 / 4) ≤ R := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨hR, ?_⟩
    nlinarith [Real.sqrt_nonneg (R ^ 2 - 1 ^ 2)]
  have hph : head H (x + t • y) = x := by
    change headLinear H (x + t • y) = x
    simp only [map_add, map_smul, headLinear_apply, hx, hy, smul_zero, add_zero]
  have hmh : head H (x - t • y) = x := by
    change headLinear H (x - t • y) = x
    simp only [map_sub, map_smul, headLinear_apply, hx, hy, smul_zero, sub_zero]
  have hpl : 1 ≤ ‖x + t • y‖ := by
    have h := norm_head_le hH (x + t • y)
    rwa [hph, hxn] at h
  have hml : 1 ≤ ‖x - t • y‖ := by
    have h := norm_head_le hH (x - t • y)
    rwa [hmh, hxn] at h
  have hsum : R ≤ ‖x + t • y‖ + ‖x - t • y‖ - 1 := max_le (by linarith) (by linarith)
  linarith


theorem predual_unit_approx (x : CoordinatePredual V) (hx : ‖x‖ = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Finset V, Ancestral (· ≤ ·) H ∧ ∃ z : FullDual V,
      head H z = z ∧ ‖z‖ = 1 ∧ ‖x.val - z‖ < ε := by
  obtain ⟨H, hH, z, hz, he⟩ := predual_finite_approx x
    (lt_min (half_pos hε) (by norm_num : (0 : ℝ) < 1 / 2))
  have he1 : ‖x.val - z‖ < 1 / 2 := he.trans_le (min_le_right _ _)
  have heε : ‖x.val - z‖ < ε / 2 := he.trans_le (min_le_left _ _)
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, sub_zero, show ‖x.val‖ = 1 from hx] at he1
    norm_num at he1
  let q := ‖z‖⁻¹ • z
  have hqn : ‖q‖ = 1 := by
    simp only [q, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz0)]
  have hzq : z = ‖z‖ • q := by
    simp only [q, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz0), one_smul]
  have hqz : ‖q - z‖ = |1 - ‖z‖| := by
    calc
      ‖q - z‖ = ‖(1 - ‖z‖) • q‖ := by
        apply congrArg norm
        calc q - z = q - ‖z‖ • q := congrArg (q - ·) hzq
             _ = (1 - ‖z‖) • q := by module
      _ = |1 - ‖z‖| := by rw [norm_smul, Real.norm_eq_abs, hqn, mul_one]
  have hnorm : |1 - ‖z‖| ≤ ‖x.val - z‖ := by
    simpa only [show ‖x.val‖ = 1 from hx] using abs_norm_sub_norm_le x.val z
  refine ⟨H, hH, q, ?_, hqn, ?_⟩
  · change headLinear H (‖z‖⁻¹ • z) = ‖z‖⁻¹ • z
    rw [map_smul, headLinear_apply, hz]
  · have htriangle : ‖x.val - q‖ ≤ ‖x.val - z‖ + ‖z - q‖ := by
      simpa only [dist_eq_norm] using dist_triangle x.val z q
    rw [norm_sub_rev z q, hqz] at htriangle
    linarith



theorem predual_averaged_witness (x : CoordinatePredual V) (hx : ‖x‖ = 1)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    ∃ H : Finset V, Ancestral (· ≤ ·) H ∧
      ∀ y : CoordinatePredual V, head H y.val = 0 → 1 ≤ ‖y‖ →
        (Real.sqrt (1 + t ^ 2 / 4) - 1) / 2 - ε ≤
          (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1 := by
  obtain ⟨H, hH, z, hz, hzn, he⟩ := predual_unit_approx x hx hε
  refine ⟨H, hH, ?_⟩
  intro y hy hyn
  have h := finite_head_average hH z y.val hz hzn hy hyn ht
  have hp : ‖z + t • y.val‖ ≤ ‖x.val + t • y.val‖ + ‖x.val - z‖ := by
    have heq : z + t • y.val = (x.val + t • y.val) + (z - x.val) := by module
    rw [heq]
    exact (norm_add_le _ _).trans_eq (by rw [norm_sub_rev z x.val])
  have hm : ‖z - t • y.val‖ ≤ ‖x.val - t • y.val‖ + ‖x.val - z‖ := by
    have heq : z - t • y.val = (x.val - t • y.val) + (z - x.val) := by module
    rw [heq]
    exact (norm_add_le _ _).trans_eq (by rw [norm_sub_rev z x.val])
  change (Real.sqrt (1 + t ^ 2 / 4) - 1) / 2 - ε ≤
    (‖x.val + t • y.val‖ + ‖x.val - t • y.val‖) / 2 - 1
  linarith

end AveragedFiniteHead

section IndependentCoordinates
variable {V : Type*} [DecidableEq V] [SegmentSystem V]

theorem coordinate_independent : LinearIndependent ℝ (coordinate (V := V)) := by
  classical
  rw [linearIndependent_iff']
  intro s a ha v hv
  have h := congrArg (fun z : FullDual V => z (unitVector v)) ha
  simpa [_root_.sum_apply, _root_.smul_apply, coordinate_unitVector, hv] using h

theorem predualCoordinate_independent : LinearIndependent ℝ (predualCoordinate (V := V)) :=
  LinearIndependent.of_comp (coordinateSpan V).subtype coordinate_independent

theorem predual_not_finite [Infinite V] : ¬ FiniteDimensional ℝ (CoordinatePredual V) := by
  intro h
  let := h
  have : Finite V := predualCoordinate_independent.finite
  exact not_finite V

theorem fullDual_not_finite [Infinite V] : ¬ FiniteDimensional ℝ (FullDual V) := by
  intro h
  let := h
  have : Finite V := coordinate_independent.finite
  exact not_finite V

end IndependentCoordinates

instance : Infinite ForestVertex := by
  let f : ℕ → ForestVertex := fun n => ⟨(1, [n]), by simp⟩
  apply Infinite.of_injective f
  intro n m h
  have he := congrArg (fun v : ForestVertex => v.val.2) h
  simpa only [f, List.cons.injEq, and_true] using he


section Modulus
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]


structure CofiniteSubspace where
  space : Submodule ℝ E
  closed : IsClosed (space : Set E)
  finite : FiniteDimensional ℝ (E ⧸ space)

attribute [instance] CofiniteSubspace.finite

abbrev SphereOne := {x : E // ‖x‖ = 1}
abbrev CofiniteSphere (F : CofiniteSubspace E) := {y : E // y ∈ F.space ∧ ‖y‖ = 1}

variable {E}

def CofiniteSubspace.ofMap {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] (f : E →L[ℝ] D) : CofiniteSubspace E where
  space := f.toLinearMap.ker
  closed := f.isClosed_ker
  finite := FiniteDimensional.of_injective
    f.toLinearMap.quotKerEquivRange.toLinearMap f.toLinearMap.quotKerEquivRange.injective

instance : Nonempty (CofiniteSubspace E) :=
  ⟨CofiniteSubspace.ofMap (0 : E →L[ℝ] ℝ)⟩

theorem CofiniteSubspace.sphere_nonempty (hE : ¬ FiniteDimensional ℝ E)
    (F : CofiniteSubspace E) : Nonempty (CofiniteSphere E F) := by
  have hn : F.space ≠ ⊥ := by
    intro he
    exact hE (F.space.quotEquivOfEqBot he).finiteDimensional
  let : Nontrivial F.space := Submodule.nontrivial_iff_ne_bot.mpr hn
  obtain ⟨y, hy⟩ := exists_ne (0 : F.space)
  have hy0 : (y : E) ≠ 0 := by
    intro he
    exact hy (Subtype.ext he)
  refine ⟨⟨‖(y : E)‖⁻¹ • (y : E), F.space.smul_mem _ y.property, ?_⟩⟩
  simp only [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy0)]

theorem sphereOne_nonempty (hE : ¬ FiniteDimensional ℝ E) : Nonempty (SphereOne E) := by
  obtain ⟨y⟩ := (CofiniteSubspace.ofMap (0 : E →L[ℝ] ℝ)).sphere_nonempty hE
  exact ⟨⟨y.val, y.property.2⟩⟩


def averagedOn (x : SphereOne E) (t : ℝ) (F : CofiniteSubspace E) : ℝ :=
  ⨅ y : CofiniteSphere E F, (‖x.val + t • y.val‖ + ‖x.val - t • y.val‖) / 2 - 1

def averagedAt (x : SphereOne E) (t : ℝ) : ℝ :=
  ⨆ F : CofiniteSubspace E, averagedOn x t F


def averagedModulus (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℝ) : ℝ :=
  ⨅ x : SphereOne E, averagedAt x t

theorem average_bounds (x y : E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1 ∧
      (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1 ≤ t := by
  have hsum := norm_add_le (x + t • y) (x - t • y)
  have he : (x + t • y) + (x - t • y) = (2 : ℝ) • x := by module
  rw [he, norm_smul, hx, mul_one] at hsum
  have hp := norm_add_le x (t • y)
  have hm := norm_sub_le x (t • y)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hy, mul_one, hx] at hp hm
  norm_num at hsum
  constructor <;> linarith

theorem averagedOn_bounds (hE : ¬ FiniteDimensional ℝ E) (x : SphereOne E)
    {t : ℝ} (ht : 0 ≤ t) (F : CofiniteSubspace E) :
    0 ≤ averagedOn x t F ∧ averagedOn x t F ≤ t := by
  have := F.sphere_nonempty hE
  have hb : BddBelow (Set.range (fun y : CofiniteSphere E F =>
      (‖x.val + t • y.val‖ + ‖x.val - t • y.val‖) / 2 - 1)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact (average_bounds _ _ x.property y.property.2 ht).1
  constructor
  · exact le_ciInf (fun y => (average_bounds _ _ x.property y.property.2 ht).1)
  · let y : CofiniteSphere E F := Classical.choice (F.sphere_nonempty hE)
    exact (ciInf_le hb y).trans (average_bounds _ _ x.property y.property.2 ht).2

theorem averagedAt_bdd (hE : ¬ FiniteDimensional ℝ E) (x : SphereOne E)
    {t : ℝ} (ht : 0 ≤ t) :
    BddAbove (Set.range (fun F : CofiniteSubspace E => averagedOn x t F)) := by
  refine ⟨t, ?_⟩
  rintro _ ⟨F, rfl⟩
  exact (averagedOn_bounds hE x ht F).2



theorem averagedModulus_lower (hE : ¬ FiniteDimensional ℝ E) {t c : ℝ} (ht : 0 ≤ t)
    (hw : ∀ x : SphereOne E, ∀ ε : ℝ, 0 < ε → ∃ F : CofiniteSubspace E,
      ∀ y : CofiniteSphere E F,
        c - ε ≤ (‖x.val + t • y.val‖ + ‖x.val - t • y.val‖) / 2 - 1) :
    c ≤ averagedModulus E t := by
  have := sphereOne_nonempty hE
  apply le_ciInf
  intro x
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨F, hF⟩ := hw x ε hε
  have := F.sphere_nonempty hE
  have hon : c - ε ≤ averagedOn x t F := le_ciInf hF
  have hs : averagedOn x t F ≤ averagedAt x t := le_ciSup (averagedAt_bdd hE x ht) F
  linarith

end Modulus

section PredualModulus
variable {V : Type*} [decidableEqV : DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V]
  [locallyFiniteOrderBotV : LocallyFiniteOrderBot V] [treeOrderV : TreeOrder V] [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]


def predualHeadValues (H : Finset V) : CoordinatePredual V →L[ℝ] (H → ℝ) :=
  ContinuousLinearMap.pi (fun v =>
    (ContinuousLinearMap.apply ℝ ℝ (unitVector v.val)).comp (coordinateSpan V).subtypeL)

theorem predualHeadValues_zero (H : Finset V) (y : CoordinatePredual V)
    (hy : predualHeadValues H y = 0) : head H y.val = 0 := by
  have _ := decidableEqV
  have _ := partialOrderV
  have _ := locallyFiniteOrderV
  have _ := locallyFiniteOrderBotV
  have _ := treeOrderV
  have _ := intervalSegmentsV
  apply Finset.sum_eq_zero
  intro v hv
  have he := congrFun hy (⟨v, hv⟩ : H)
  change y.val (unitVector v) = 0 at he
  rw [he, zero_smul]


theorem predual_all_radius_average [Infinite V] {t : ℝ} (ht : 0 < t) :
    (Real.sqrt (1 + t ^ 2 / 4) - 1) / 2 ≤ averagedModulus (CoordinatePredual V) t := by
  apply averagedModulus_lower predual_not_finite ht.le
  intro x ε hε
  obtain ⟨H, hH, hw⟩ := predual_averaged_witness x.val x.property ht hε
  refine ⟨CofiniteSubspace.ofMap (predualHeadValues H), ?_⟩
  intro y
  exact hw y.val (predualHeadValues_zero H y.val y.property.1) y.property.2.ge


theorem infinite_all_radius_average {t : ℝ} (ht : 0 < t) :
    (Real.sqrt (1 + t ^ 2 / 4) - 1) / 2 ≤ averagedModulus BInfinite t := by
  classical
  exact predual_all_radius_average ht

end PredualModulus


end SegmentLenses

end

end OAI
