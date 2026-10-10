import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingRootProductBoxes

namespace OAI

/-! # Normalized conditional products on actual rectangles -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma probability_eq_prod_marginals_of_prod
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (ρ : Measure (A × B)) [IsProbabilityMeasure ρ]
    (ν : Measure A) (η : Measure B) [SFinite ν] [SFinite η]
    (h : ρ = ν.prod η) : ρ = ρ.fst.prod ρ.snd := by
  have hm : ν univ * η univ = 1 := by
    rw [←Measure.prod_prod,univ_prod_univ,←h,measure_univ]
  rw [h,Measure.fst,Measure.snd,Measure.map_fst_prod,Measure.map_snd_prod,
    Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,mul_comm,hm,one_smul]

theorem conditional_restrict_rectangle_product
    {T B : Type*} [MeasurableSpace T] [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B]
    (σ : Measure (T × (B × ℝ))) [IsFiniteMeasure σ]
    (J : Set ℝ) (hJ : MeasurableSet J)
    (hprod : ∀ᵐ s ∂σ.fst, ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
      (σ.condKernel s).restrict (univ ×ˢ J) =
        ((σ.condKernel s).restrict (univ ×ˢ J)).fst.prod ν) :
    let ρ := σ.restrict (univ ×ˢ (univ ×ˢ J))
    ∀ᵐ s ∂ρ.fst, ρ.condKernel s = (ρ.condKernel s).fst.prod (ρ.condKernel s).snd := by
  intro ρ
  have hbase : ρ.fst ≪ σ.fst :=
    Measure.absolutelyContinuous_of_le (Measure.fst_mono Measure.restrict_le_self)
  have hc := conditional_restrict_normalized σ (univ ×ˢ (univ ×ˢ J))
    (MeasurableSet.univ.prod (MeasurableSet.univ.prod hJ))
  filter_upwards [hc,hbase.ae_le hprod] with s hs hp
  have hfiber : Prod.mk s ⁻¹' (univ ×ˢ (univ ×ˢ J) : Set (T × (B × ℝ))) =
      univ ×ˢ J := by ext z; simp
  rw [hfiber] at hs
  obtain ⟨ν,hν,hp⟩ := hp
  let : IsFiniteMeasure ν := hν
  have he : ρ.condKernel s =
      ((σ.condKernel s) (univ ×ˢ J))⁻¹ •
        (((σ.condKernel s).restrict (univ ×ˢ J)).fst.prod ν) := by
    calc
      _ = ((σ.condKernel s) (univ ×ˢ J))⁻¹ •
          ((σ.condKernel s).restrict (univ ×ˢ J)) := by
        rw [hs.2,anchorNormalize,Measure.restrict_smul]
      _ = _ := congrArg (fun θ : Measure (B × ℝ) =>
        ((σ.condKernel s) (univ ×ˢ J))⁻¹ • θ) hp
  rw [←Measure.prod_smul_left] at he
  exact probability_eq_prod_marginals_of_prod _ _ _ he

theorem exists_remainingRoot_independent_box
    (d : ℕ) (q : InitialRootStep (d+1))
    {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))
    (z : C.factorPivotDomain q g k) (t : ℝ)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ Q : RootTransverseRectangle (C.factorPivotDomain q g k), ∃ hQ : Nonempty Q.second,
      letI := hQ
      haveI : StandardBorelSpace Q.second := Q.second_open.measurableSet.standardBorel
      ∃ (A : RootBox q.distinct k) (R : ℝ) (J : Set ℝ),
        IsOpen J ∧ z.val ∈ Q.first ×ˢ Q.second ∧ t ∈ J ∧
        A.time ⊆ rootLeafWindow R 0 ∧
        let σ := shiftedRootFactorPullback q.distinct A μ
          (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)
        haveI := shiftedRootFactorPullback_finite q.distinct A μ
          (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
          (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
        let ρ := σ.restrict (univ ×ˢ (univ ×ˢ J))
        ∀ᵐ s ∂ρ.fst, ρ.condKernel s = (ρ.condKernel s).fst.prod (ρ.condKernel s).snd := by
  obtain ⟨Q,hQ,h⟩ := exists_remainingRoot_product_box d q C g k z t μ hA
  let : Nonempty Q.second := hQ
  let : StandardBorelSpace Q.second := Q.second_open.measurableSet.standardBorel
  obtain ⟨A,R,J,hJ,hz,ht,hR,hprod⟩ := h
  refine ⟨Q,hQ,A,R,J,hJ,hz,ht,hR,?_⟩
  let σ := shiftedRootFactorPullback q.distinct A μ
    (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)
  let := shiftedRootFactorPullback_finite q.distinct A μ
    (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
    (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
  exact conditional_restrict_rectangle_product σ J hJ.measurableSet hprod

end DukePrimeDegree

end

end OAI
