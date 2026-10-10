import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixWindows

namespace OAI

/-! # Locally finite leaf measures on each remaining subgroup

The actual prefix-box kernels glue through their normalized restrictions
on a countable long-box exhaustion. No root-product identity is assumed.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    {Pfx : RootPrefixCoordinates n P T} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hfinal : c.finalEntries = allPositiveRoots n} {g : G n}

theorem ae_exists_prefixLeafMeasure (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∃ ν : Measure (c.Time),
      IsLocallyFiniteMeasure ν ∧ ν A.time = 1 ∧
      ν.restrict A.time = A.conditionalKernel μ s ∧
      ∀ (m : ℕ) (B : RootPrefixBox Pfx c hP hfinal g), B ∈ Pfx.longBoxFamily c hP hfinal g R m →
        s ∈ B.transverse →
        ν.restrict (c.remainingWindow R m) =
          (anchorNormalize (B.conditionalKernel μ s) A.time).restrict (c.remainingWindow R m) := by
  let C := Pfx.longBoxFamily c hP hfinal g R
  have hCc (m : ℕ) : (C m).Countable := Pfx.longBoxFamily_countable c hP hfinal g R m
  let (m : ℕ) : Countable (C m) := (hCc m).to_subtype
  have hT (m : ℕ) (B : C m) : B.val.time = c.remainingWindow R m :=
    Pfx.longBoxFamily_time c hP hfinal g R m B.val B.prop
  have hinc (m : ℕ) (B : C m) : A.time ⊆ B.val.time := by
    rw [hT m B]
    exact hAR.trans (c.remainingWindow_mono R (Nat.zero_le m))
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
  filter_upwards [A.ae_injective_slice_of_ae_free μ hfree,hp,ha] with s hs hp ha
  have hcover (m : ℕ) : ∃ B : C m, s ∈ B.val.transverse := by
    obtain ⟨B,hB,hsB⟩ := Pfx.longBoxFamily_covers c hP hfinal g R m s hs
    exact ⟨⟨B,hB⟩,hsB⟩
  choose B hB using hcover
  let N (m : ℕ) : Measure (c.Time) :=
    (anchorNormalize ((B m).val.conditionalKernel μ s) A.time).restrict (c.remainingWindow R m)
  have hpos (m : ℕ) : (B m).val.conditionalKernel μ s A.time ≠ 0 := (ha m (B m) (hB m)).1
  let (m : ℕ) : IsFiniteMeasure (anchorNormalize ((B m).val.conditionalKernel μ s) A.time) :=
    anchorNormalize_finite _ _ (hpos m)
  let (m : ℕ) : IsFiniteMeasure (N m) := by dsimp [N]; infer_instance
  have hc : ∀ a b, a ≤ b → (N b).restrict (c.remainingWindow R a) = N a := by
    intro a b hab
    have H := (hp a b (B a) (B b) (hB a) (hB b)).2.2
    rw [hT a (B a),hT b (B b),inter_eq_left.mpr (c.remainingWindow_mono R hab)] at H
    dsimp [N]
    rw [Measure.restrict_restrict (c.remainingWindow_open R a).measurableSet,
      inter_eq_left.mpr (c.remainingWindow_mono R hab)]
    exact H.symm
  let ν := increasingMeasureLimit N (restrictionChain_monotone N (c.remainingWindow R) hc)
  have hν (m : ℕ) : ν.restrict (c.remainingWindow R m) = N m :=
    increasingMeasureLimit_restrict N (c.remainingWindow R)
      (fun m => (c.remainingWindow_open R m).measurableSet) hc m
  have hνA : ν.restrict A.time = A.conditionalKernel μ s := by
    have H := congrArg (fun ξ : Measure (c.Time) => ξ.restrict A.time) (hν 0)
    dsimp [N] at H
    rw [Measure.restrict_restrict A.time_open.measurableSet,inter_eq_left.mpr hAR,
      Measure.restrict_restrict A.time_open.measurableSet,inter_eq_left.mpr hAR] at H
    exact H.trans (ha 0 (B 0) (hB 0)).2
  refine ⟨ν,increasingMeasureLimit_locallyFinite N (c.remainingWindow R)
    (c.remainingWindow_open R) (fun m => (c.remainingWindow_open R m).measurableSet)
    (c.remainingWindow_cover R) hc,?_,hνA,?_⟩
  · have H := congrArg (fun ξ : Measure (c.Time) => ξ univ) hνA
    simpa only [Measure.restrict_apply MeasurableSet.univ,univ_inter,measure_univ] using H
  · intro m D hD hsD
    let D' : C m := ⟨D,hD⟩
    have H := (hp m m (B m) D' (hB m) hsD).2.2
    rw [hT m (B m),hT m D',inter_self] at H
    exact (hν m).trans H



theorem prefixLeafMeasure_unique (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (s : (UpperRootTransverse n × T))
    (hs : Function.Injective (fun t : c.Time => Pfx.timeParam c hP hfinal g (s,t)))
    (ν ρ : Measure (c.Time))
    (hν : ∀ (m : ℕ) (B : RootPrefixBox Pfx c hP hfinal g), B ∈ Pfx.longBoxFamily c hP hfinal g R m →
      s ∈ B.transverse → ν.restrict (c.remainingWindow R m) =
        (anchorNormalize (B.conditionalKernel μ s) A.time).restrict (c.remainingWindow R m))
    (hρ : ∀ (m : ℕ) (B : RootPrefixBox Pfx c hP hfinal g), B ∈ Pfx.longBoxFamily c hP hfinal g R m →
      s ∈ B.transverse → ρ.restrict (c.remainingWindow R m) =
        (anchorNormalize (B.conditionalKernel μ s) A.time).restrict (c.remainingWindow R m)) : ν = ρ := by
  apply measure_eq_of_restrictionChain (c.remainingWindow R) (c.remainingWindow_mono R)
    (c.remainingWindow_cover R)
  intro m
  obtain ⟨B,hB,hsB⟩ := Pfx.longBoxFamily_covers c hP hfinal g R m s hs
  exact (hν m B hB hsB).trans (hρ m B hB hsB).symm



end RootPrefixBox
end DukePrimeDegree

end

end OAI
