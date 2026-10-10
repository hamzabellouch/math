import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootWindows

namespace OAI

/-!
# Locally finite conditional measures on complete upper-root leaves

The finite-box conditionals have compatible normalized restrictions.
Their increasing limit is a locally finite measure on all real root
coordinates, uniquely determined by the countable long-box atlas.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma subgroup_free_of_free_translate {n : ℕ} (H : Subgroup (G n)) (x : X n)
    (w : G n) (hw : w ∈ H)
    (hf : ∀ v ∈ H, rightAction (rightAction x w) v = rightAction x w → v = 1) :
    ∀ v ∈ H, rightAction x v = x → v = 1 := by
  intro v hv hfix
  have he : rightAction (rightAction x w) (w⁻¹ * v * w) = rightAction x w := by
    rw [rightAction_mul]
    have hm : w * (w⁻¹ * v * w) = v * w := by group
    rw [hm, ←rightAction_mul, hfix]
  have hh := hf (w⁻¹ * v * w) (H.mul_mem (H.mul_mem (H.inv_mem hw) hv) hw) he
  have heq := congrArg (fun a : G n => w * a * w⁻¹) hh
  simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, mul_one,
    mul_inv_cancel] using heq

namespace UpperRootBox
variable {n : ℕ} {g : G n}

theorem ae_injective_upperRoot_slice_of_ae_free (B : UpperRootBox n g)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst,
      Function.Injective (fun t => upperRootQuotientParam n g (s, t)) := by
  have hf := B.ae_coordinate_of_ambient μ hfree
  have hf' : ∀ᵐ z ∂((B.coordinateMeasure μ).fst ⊗ₘ B.conditionalKernel μ),
      ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
        rightAction (upperRootQuotientParam n g z) v = upperRootQuotientParam n g z → v = 1 := by
    simpa only [conditionalKernel, Measure.disintegrate] using hf
  have H := Measure.ae_ae_of_ae_compProd hf'
  filter_upwards [H] with s hs
  obtain ⟨t, ht⟩ := hs.exists
  apply upperRootQuotientParam_injective_of_free
  apply subgroup_free_of_free_translate (positiveRootGeneratedGroup (allPositiveRoots n))
    (Quotient.mk _ (g * s.val)) ((completeRootChain n).word t) (upperRootWord_mem n t)
  simpa only [upperRootQuotientParam_eq_action] using ht

theorem ae_exists_upperRootLeafMeasure (A : UpperRootBox n g) (R : ℝ)
    (hAR : A.time ⊆ upperRootWindow n R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∃ ν : Measure (UpperRootTime n),
      IsLocallyFiniteMeasure ν ∧ ν A.time = 1 ∧
      ν.restrict A.time = A.conditionalKernel μ s ∧
      ∀ (m : ℕ) (B : UpperRootBox n g), B ∈ upperRootLongBoxFamily n g R m →
        s ∈ B.transverse →
        ν.restrict (upperRootWindow n R m) =
          (anchorNormalize (B.conditionalKernel μ s) A.time).restrict (upperRootWindow n R m) := by
  let C := upperRootLongBoxFamily n g R
  have hCc (m : ℕ) : (C m).Countable := upperRootLongBoxFamily_countable n g R m
  let (m : ℕ) : Countable (C m) := (hCc m).to_subtype
  have hT (m : ℕ) (B : C m) : B.val.time = upperRootWindow n R m :=
    upperRootLongBoxFamily_time n g R m B.val B.prop
  have hinc (m : ℕ) (B : C m) : A.time ⊆ B.val.time := by
    rw [hT m B]
    exact hAR.trans (upperRootWindow_mono n R (Nat.zero_le m))
  have hp : ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      ∀ (a b : ℕ) (B : C a) (D : C b), s ∈ B.val.transverse → s ∈ D.val.transverse →
        B.val.conditionalKernel μ s A.time ≠ 0 ∧ D.val.conditionalKernel μ s A.time ≠ 0 ∧
        (anchorNormalize (B.val.conditionalKernel μ s) A.time).restrict (B.val.time ∩ D.val.time) =
          (anchorNormalize (D.val.conditionalKernel μ s) A.time).restrict (B.val.time ∩ D.val.time) := by
    apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro b
    apply ae_all_iff.mpr
    intro B
    apply ae_all_iff.mpr
    intro D
    exact base_overlap_anchorNormalize A B.val D.val (hinc a B) (hinc b D) μ
  have ha : ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      ∀ (m : ℕ) (B : C m), s ∈ B.val.transverse →
        B.val.conditionalKernel μ s A.time ≠ 0 ∧
        (anchorNormalize (B.val.conditionalKernel μ s) A.time).restrict A.time =
          A.conditionalKernel μ s := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro B
    exact base_anchor_restrict A B.val (hinc m B) μ
  filter_upwards [A.ae_injective_upperRoot_slice_of_ae_free μ hfree,hp,ha] with s hs hp ha
  have hcover (m : ℕ) : ∃ B : C m, s ∈ B.val.transverse := by
    obtain ⟨B,hB,hsB⟩ := upperRootLongBoxFamily_covers n g R m s hs
    exact ⟨⟨B,hB⟩,hsB⟩
  choose B hB using hcover
  let N (m : ℕ) : Measure (UpperRootTime n) :=
    (anchorNormalize ((B m).val.conditionalKernel μ s) A.time).restrict (upperRootWindow n R m)
  have hpos (m : ℕ) : (B m).val.conditionalKernel μ s A.time ≠ 0 := (ha m (B m) (hB m)).1
  let (m : ℕ) : IsFiniteMeasure (anchorNormalize ((B m).val.conditionalKernel μ s) A.time) :=
    anchorNormalize_finite _ _ (hpos m)
  let (m : ℕ) : IsFiniteMeasure (N m) := by dsimp [N]; infer_instance
  have hc : ∀ a b, a ≤ b → (N b).restrict (upperRootWindow n R a) = N a := by
    intro a b hab
    have H := (hp a b (B a) (B b) (hB a) (hB b)).2.2
    rw [hT a (B a),hT b (B b),inter_eq_left.mpr (upperRootWindow_mono n R hab)] at H
    dsimp [N]
    rw [Measure.restrict_restrict (upperRootWindow_open n R a).measurableSet,
      inter_eq_left.mpr (upperRootWindow_mono n R hab)]
    exact H.symm
  let ν := increasingMeasureLimit N (restrictionChain_monotone N (upperRootWindow n R) hc)
  have hν (m : ℕ) : ν.restrict (upperRootWindow n R m) = N m :=
    increasingMeasureLimit_restrict N (upperRootWindow n R)
      (fun m => (upperRootWindow_open n R m).measurableSet) hc m
  have hνA : ν.restrict A.time = A.conditionalKernel μ s := by
    have H := congrArg (fun ξ : Measure (UpperRootTime n) => ξ.restrict A.time) (hν 0)
    dsimp [N] at H
    rw [Measure.restrict_restrict A.time_open.measurableSet,inter_eq_left.mpr hAR,
      Measure.restrict_restrict A.time_open.measurableSet,inter_eq_left.mpr hAR] at H
    exact H.trans (ha 0 (B 0) (hB 0)).2
  refine ⟨ν,increasingMeasureLimit_locallyFinite N (upperRootWindow n R)
    (upperRootWindow_open n R) (fun m => (upperRootWindow_open n R m).measurableSet)
    (upperRootWindow_cover n R) hc,?_,hνA,?_⟩
  · have H := congrArg (fun ξ : Measure (UpperRootTime n) => ξ univ) hνA
    simpa only [Measure.restrict_apply MeasurableSet.univ,univ_inter,measure_univ] using H
  · intro m D hD hsD
    let D' : C m := ⟨D,hD⟩
    have H := (hp m m (B m) D' (hB m) hsD).2.2
    rw [hT m (B m),hT m D',inter_self] at H
    exact (hν m).trans H



theorem upperRootLeafMeasure_unique (A : UpperRootBox n g) (R : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (s : UpperRootTransverse n)
    (hs : Function.Injective (fun t : UpperRootTime n => upperRootQuotientParam n g (s,t)))
    (ν ρ : Measure (UpperRootTime n))
    (hν : ∀ (m : ℕ) (B : UpperRootBox n g), B ∈ upperRootLongBoxFamily n g R m →
      s ∈ B.transverse → ν.restrict (upperRootWindow n R m) =
        (anchorNormalize (B.conditionalKernel μ s) A.time).restrict (upperRootWindow n R m))
    (hρ : ∀ (m : ℕ) (B : UpperRootBox n g), B ∈ upperRootLongBoxFamily n g R m →
      s ∈ B.transverse → ρ.restrict (upperRootWindow n R m) =
        (anchorNormalize (B.conditionalKernel μ s) A.time).restrict (upperRootWindow n R m)) : ν = ρ := by
  apply measure_eq_of_restrictionChain (upperRootWindow n R) (upperRootWindow_mono n R)
    (upperRootWindow_cover n R)
  intro m
  obtain ⟨B,hB,hsB⟩ := upperRootLongBoxFamily_covers n g R m s hs
  exact (hν m B hB hsB).trans (hρ m B hB hsB).symm


end UpperRootBox
end DukePrimeDegree

end

end OAI
