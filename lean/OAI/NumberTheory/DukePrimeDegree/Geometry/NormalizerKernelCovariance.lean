import OAI.NumberTheory.DukePrimeDegree.Dynamics.NormalizerInvariantSigma

namespace OAI

/-!
# Covariance of the component kernel under a normalizer

The normalizer moves the component parameter as well as the component
measure. The proof compares the two actual joint laws and uses uniqueness
of disintegration. In particular, it does not replace covariance by the
stronger assertion that every component is fixed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem condExpKernel_equivariant
    {Y : Type*} (m : MeasurableSpace Y)
    [mY : MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (hm : m ≤ mY)
    (μ : @Measure Y mY) [IsProbabilityMeasure μ]
    (T : @MeasurableEquiv Y Y mY mY)
    (hT : @MeasurePreserving Y Y mY mY T μ μ)
    (hmT : @Measurable Y Y m m T)
    (hmTi : @Measurable Y Y m m T.symm) :
    ∀ᵐ x ∂μ.trim hm,
      (condExpKernel μ m x).map T = condExpKernel μ m (T x) := by
  let κ := condExpKernel μ m
  let τ := μ.trim hm
  let κT := Kernel.comap κ T hmT
  let : IsMarkovKernel (κ.map T) := Kernel.IsMarkovKernel.map κ T.measurable
  let : IsMarkovKernel κT := inferInstance
  have hτT : @MeasurePreserving Y Y m m T τ τ :=
    measurePreserving_trim_of_measurable m hm μ T hT hmT
  have hdiag : τ ⊗ₘ κ =
      @Measure.map Y (Y × Y) mY (m.prod mY) Function.diag μ :=
    compProd_trim_condExpKernel hm
  have hδ : @Measurable Y (Y × Y) mY (m.prod mY) Function.diag :=
    (measurable_id'' hm).prodMk measurable_id
  have hrectangle (A B : Set Y) (hA : @MeasurableSet Y m A)
      (hB : @MeasurableSet Y mY B) :
      (τ ⊗ₘ κ) (A ×ˢ B) = μ (A ∩ B) := by
    rw [hdiag, Measure.map_apply hδ (hA.prod hB)]
    rfl
  have hprod : τ ⊗ₘ κ.map T = τ ⊗ₘ κT := by
    apply Measure.ext_prod
    intro A B hA hB
    have hleft : (τ ⊗ₘ κ.map T) (A ×ˢ B) = μ (A ∩ T ⁻¹' B) := by
      rw [Measure.compProd_apply_prod hA hB]
      simp_rw [Kernel.map_apply' _ T.measurable _ hB]
      rw [← Measure.compProd_apply_prod hA (T.measurable hB),
        hrectangle A (T ⁻¹' B) hA (T.measurable hB)]
    have hright : (τ ⊗ₘ κT) (A ×ˢ B) = μ (T.symm ⁻¹' A ∩ B) := by
      let F : Y → ℝ≥0∞ := (T.symm ⁻¹' A).indicator (fun x => κ x B)
      have hF : @Measurable Y ℝ≥0∞ m _ F :=
        (Kernel.measurable_coe κ hB).indicator (hmTi hA)
      have hFE : (fun x => F (T x)) = A.indicator (fun x => κ (T x) B) := by
        funext x
        by_cases hx : x ∈ A
        · have hTx : T x ∈ T.symm ⁻¹' A := by simpa only [mem_preimage,
            T.symm_apply_apply] using hx
          simp only [F, Set.indicator_of_mem hx, Set.indicator_of_mem hTx]
        · have hTx : T x ∉ T.symm ⁻¹' A := by simpa only [mem_preimage,
            T.symm_apply_apply] using hx
          simp only [F, Set.indicator_of_notMem hx, Set.indicator_of_notMem hTx]
      calc
        (τ ⊗ₘ κT) (A ×ˢ B) = ∫⁻ x in A, κ (T x) B ∂τ := by
          rw [Measure.compProd_apply_prod hA hB]
          rfl
        _ = ∫⁻ x, F (T x) ∂τ := by
          rw [hFE, lintegral_indicator hA]
        _ = ∫⁻ x, F x ∂τ := by
          let : MeasurableSpace Y := m
          exact hτT.lintegral_comp hF
        _ = ∫⁻ x in T.symm ⁻¹' A, κ x B ∂τ := lintegral_indicator (hmTi hA) _
        _ = (τ ⊗ₘ κ) ((T.symm ⁻¹' A) ×ˢ B) :=
          (Measure.compProd_apply_prod (hmTi hA) hB).symm
        _ = μ (T.symm ⁻¹' A ∩ B) := hrectangle _ _ (hmTi hA) hB
    rw [hleft, hright]
    have he : A ∩ T ⁻¹' B = T ⁻¹' (T.symm ⁻¹' A ∩ B) := by
      ext x
      simp only [mem_inter_iff, mem_preimage, T.symm_apply_apply]
    rw [he]
    exact hT.measure_preimage (((T.symm.measurable (hm A hA)).inter hB).nullMeasurableSet)
  have hfirst := condKernel_compProd τ (κ.map T)
  have hsecond := condKernel_compProd τ κT
  have hfirst' : (τ ⊗ₘ κT).condKernel =ᵐ[τ] κ.map T := by
    simpa only [hprod] using hfirst
  have heq := hfirst'.symm.trans hsecond
  filter_upwards [heq] with x hx
  change (κ.map T) x = κT x at hx
  simpa only [κT, Kernel.map_apply _ T.measurable, Kernel.comap_apply, κ] using hx

/-- For the actual lattice action, a normalizer sends each conditional
measure to the conditional measure at the moved parameter. -/
theorem lattice_normalizer_component_covariance {n : ℕ}
    (H : Subgroup (G n)) (a : G n)
    (ha : a ∈ Subgroup.normalizer (H : Set (G n)))
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (hμ : μ.map (fun x => rightAction x a) = μ) :
    ∀ᵐ x ∂μ.trim (actionInvariantSigma_le H (X n)),
      (condExpKernel μ (actionInvariantSigma H (X n)) x).map
        (fun y => rightAction y a) =
      condExpKernel μ (actionInvariantSigma H (X n)) (rightAction x a) := by
  let T : X n ≃ᵐ X n :=
    { toEquiv :=
        { toFun := fun x => rightAction x a
          invFun := fun x => rightAction x a⁻¹
          left_inv := by intro x; simp only [rightAction_mul, mul_inv_cancel, rightAction_one]
          right_inv := by intro x; simp only [rightAction_mul, inv_mul_cancel, rightAction_one] }
      measurable_toFun := (continuous_rightAction a).measurable
      measurable_invFun := (continuous_rightAction a⁻¹).measurable }
  exact condExpKernel_equivariant (actionInvariantSigma H (X n))
    (actionInvariantSigma_le H (X n)) μ T ⟨T.measurable, hμ⟩
    (lattice_normalizer_measurable_invariantSigma H a ha)
    (lattice_normalizer_measurable_invariantSigma H a⁻¹
      ((Subgroup.normalizer (H : Set (G n))).inv_mem ha))

end DukePrimeDegree

end

end OAI
