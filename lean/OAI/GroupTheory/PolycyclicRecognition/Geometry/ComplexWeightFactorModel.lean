import OAI.GroupTheory.PolycyclicRecognition.Algebra.ClosedIntegrationOverLinearQuotient
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexWeightKernel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealCartanQuotient
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanLocalProduct
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConnectedIdealNormality
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialTangentUniqueness

namespace OAI

/-! # Nilpotent and Cartan factors for a solvable group with complex weights -/

noncomputable section
namespace PolycyclicRecognition
open Set Filter
open scoped Manifold ContDiff Topology

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
  (ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G)

/-- The concrete group part of the complex-weight Cartan model. The ambient
overlap is retained, and all lifting conclusions refer to the actual map. -/
structure ComplexWeightFactorModel where
  N : NilpotentLieModel T.kernelIdeal
  D : NilpotentLieModel H
  weightCharacter : G →* Multiplicative T.weightMap.range
  continuousWeightCharacter : Continuous weightCharacter
  weightCharacter_exp : ∀ x, (weightCharacter (ExpG x)).toAdd = T.weightMap.rangeRestrict x
  ExpN : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → N.carrier
  ExpD : GroupLieAlgebra (𝓘(ℝ, D.modelSpace)) D.carrier → D.carrier
  isExpN : IsGroupExponential ExpN
  isExpD : IsGroupExponential ExpD
  inclusionN : N.carrier →* G
  inclusionD : D.carrier →* G
  action : D.carrier →* MulAut N.carrier
  closedN : Topology.IsClosedEmbedding inclusionN
  closedD : Topology.IsClosedEmbedding inclusionD
  compatibleN : ∀ x : T.kernelIdeal, inclusionN (ExpN (N.equiv x)) = ExpG x
  compatibleD : ∀ x : H, inclusionD (ExpD (D.equiv x)) = ExpG x
  normalN : inclusionN.range.Normal
  conjugation : ∀ d n, inclusionN (action d n) =
    inclusionD d * inclusionN n * (inclusionD d)⁻¹
  surjective : Function.Surjective (fun p : N.carrier × D.carrier =>
    inclusionN p.1 * inclusionD p.2)
  openProduct : IsOpenMap (fun p : N.carrier × D.carrier =>
    inclusionN p.1 * inclusionD p.2)
  compactLifts : ∀ K : Set G, IsCompact K → ∃ C : Set (N.carrier × D.carrier),
    IsCompact C ∧ K ⊆ (fun p => inclusionN p.1 * inclusionD p.2) '' C
  overlap : Set.range inclusionN ∩ Set.range inclusionD = ExpG ''
    ((T.kernelIdeal : Set (GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∩
      (H : Set (GroupLieAlgebra (𝓘(ℝ, EG)) G)))


include T in
theorem nonempty_complexWeightFactorModel (hExp : IsGroupExponential ExpG) :
    Nonempty (ComplexWeightFactorModel T H ExpG) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  obtain ⟨π, hπ, hπExp, N, ExpN, hExpN, ι, hι, hιsmooth, heι, hrι⟩ :=
    exists_closed_complex_weight_kernel T ExpG hExp
  obtain ⟨D⟩ := nilpotentPublishedInputs.existsModel H inferInstance
  let : IsTopologicalGroup N.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, N.modelSpace)) ⊤
  let : IsTopologicalGroup D.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, D.modelSpace)) ⊤
  let : LocallyCompactSpace N.carrier := ChartedSpace.locallyCompactSpace N.modelSpace N.carrier
  let : LocallyCompactSpace D.carrier := ChartedSpace.locallyCompactSpace D.modelSpace D.carrier
  obtain ⟨cN, hcN⟩ := ((nilpotentPublishedInputs.haar T.kernelIdeal N).2
    ExpN hExpN (N.tangent_nilpotent T.kernelIdeal_nilpotent)).1
  obtain ⟨ExpD, hExpD, cD, hcD⟩ := D.exists_exponential_chart inferInstance
    (nilpotentPublishedInputs.haar H D)
  let d := T.weightMap.rangeRestrict
  have hker (x : GroupLieAlgebra (𝓘(ℝ, EG)) G) : d x = 0 ↔ x ∈ T.kernelIdeal := by
    constructor
    · exact fun h => congrArg Subtype.val h
    · exact fun h => Subtype.ext h
  let jD := H.incl.comp D.equiv.symm.toLieHom
  have hjD : Function.Injective jD := Subtype.val_injective.comp D.equiv.symm.injective
  have hsurj : Function.Surjective (d.comp jD.toLinearMap) :=
    (T.cartan_weightRange_surjective H).comp D.equiv.symm.surjective
  obtain ⟨κ, hκ, hκsmooth, heκall⟩ := exists_closed_nilpotent_integration_over_linear_quotient
    T.kernelIdeal T.kernelIdeal_nilpotent d T.weightMap.surjective_rangeRestrict hker
    ExpG hExp π hπ hπExp H D inferInstance jD hjD hsurj
  have heκ (x : H) : κ (ExpD (D.equiv x)) = ExpG x := by
    simpa only [jD, LieHom.comp_apply, LieEquiv.coe_toLieHom, LieEquiv.symm_apply_apply,
      LieSubalgebra.coe_incl] using
      heκall ExpD hExpD (D.equiv x)
  have hiExp (x : N.modelSpace) : ι (ExpN x) = ExpG (T.kernelIdeal.incl (N.equiv.symm x)) := by
    exact (congrArg (fun y : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier =>
      ι (ExpN y)) (N.equiv.apply_symm_apply x)).symm.trans (heι (N.equiv.symm x))
  have hkExp (x : D.modelSpace) : κ (ExpD x) = ExpG (H.incl (D.equiv.symm x)) := by
    exact (congrArg (fun y : GroupLieAlgebra (𝓘(ℝ, D.modelSpace)) D.carrier =>
      κ (ExpD y)) (D.equiv.apply_symm_apply x)).symm.trans (heκ (D.equiv.symm x))
  have hiRange : Set.range ι = ExpG '' (T.kernelIdeal : Set (GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
    ext g
    constructor
    · rintro ⟨n, rfl⟩
      obtain ⟨x, hx⟩ := cN.surjective n
      rw [hcN] at hx
      exact ⟨N.equiv.symm x, (N.equiv.symm x).property, (hiExp x).symm.trans (congrArg ι hx)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨ExpN (N.equiv ⟨x, hx⟩), heι ⟨x, hx⟩⟩
  have hkRange : Set.range κ = ExpG '' (H : Set (GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
    ext g
    constructor
    · rintro ⟨d, rfl⟩
      obtain ⟨x, hx⟩ := cD.surjective d
      rw [hcD] at hx
      exact ⟨D.equiv.symm x, (D.equiv.symm x).property, (hkExp x).symm.trans (congrArg κ hx)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨ExpD (D.equiv ⟨x, hx⟩), heκ ⟨x, hx⟩⟩
  have hnormal : ι.range.Normal := by
    have he : ι.range = π.ker := SetLike.coe_injective hrι
    rw [he]
    infer_instance
  let φ := conjugationLiftOfNormal ι κ hι.injective hnormal
  have hconj (d : D.carrier) (n : N.carrier) :
      ι (φ d n) = κ d * ι n * (κ d)⁻¹ :=
    conjugationLiftOfNormal_spec ι κ hι.injective hnormal d n
  have hiDiff := mfderiv_eq_of_exponential_compatibility hExpN hExp ι
    (hιsmooth.mdifferentiable (by simp))
    (T.kernelIdeal.incl.comp N.equiv.symm.toLieHom).toLinearMap hiExp
  have hkDiff := mfderiv_eq_of_exponential_compatibility hExpD hExp κ
    (hκsmooth.mdifferentiable (by simp)) jD.toLinearMap hkExp
  have hiVal (x : T.kernelIdeal) :
      (tangentSpaceCast (𝓘(ℝ, EG)) (ι 1) 1)
        (mfderiv (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, EG)) ι 1 (N.equiv x)) =
          (x : GroupLieAlgebra (𝓘(ℝ, EG)) G) := by
    change mfderiv (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, EG)) ι 1 (N.equiv x) =
      (x : GroupLieAlgebra (𝓘(ℝ, EG)) G)
    exact (hiDiff (N.equiv x)).trans
      (congrArg (fun z : T.kernelIdeal => (z : GroupLieAlgebra (𝓘(ℝ, EG)) G))
        (N.equiv.symm_apply_apply x))
  have hkVal (x : H) :
      (tangentSpaceCast (𝓘(ℝ, EG)) (κ 1) 1)
        (mfderiv (𝓘(ℝ, D.modelSpace)) (𝓘(ℝ, EG)) κ 1 (D.equiv x)) =
          (x : GroupLieAlgebra (𝓘(ℝ, EG)) G) := by
    change mfderiv (𝓘(ℝ, D.modelSpace)) (𝓘(ℝ, EG)) κ 1 (D.equiv x) =
      (x : GroupLieAlgebra (𝓘(ℝ, EG)) G)
    exact (hkDiff (D.equiv x)).trans
      (congrArg (fun z : H => (z : GroupLieAlgebra (𝓘(ℝ, EG)) G))
        (D.equiv.symm_apply_apply x))
  have hlocal : Filter.map (fun p : N.carrier × D.carrier => ι p.1 * κ p.2)
      (𝓝 (1 : N.carrier × D.carrier)) = 𝓝 (1 : G) := by
    apply factorProduct_map_nhds_one ι κ hιsmooth hκsmooth
    intro x
    obtain ⟨h, hh⟩ := T.exists_real_cartan_representative H x
    have hu : x - (h : GroupLieAlgebra (𝓘(ℝ, EG)) G) ∈ T.kernelIdeal := by
      change T.weightMap (x - (h : GroupLieAlgebra (𝓘(ℝ, EG)) G)) = 0
      rw [map_sub, hh, sub_self]
    refine ⟨N.equiv ⟨x - h, hu⟩, D.equiv h, ?_⟩
    rw [hiVal, hkVal]
    exact sub_add_cancel x h
  obtain ⟨hprod, hlifts⟩ := factorProduct_surjective_and_compact_lifts ι κ φ hconj hlocal
  have hexpinj {x y : GroupLieAlgebra (𝓘(ℝ, EG)) G} (hx : x ∈ T.kernelIdeal)
      (he : ExpG x = ExpG y) : x = y := by
    have hy : y ∈ T.kernelIdeal := by
      apply (hker y).mp
      rw [← hπExp, ← he, hπExp]
      exact (hker x).mpr hx
    have hn : ExpN (N.equiv ⟨x, hx⟩) = ExpN (N.equiv ⟨y, hy⟩) :=
      hι.injective ((heι ⟨x, hx⟩).trans (he.trans (heι ⟨y, hy⟩).symm))
    have hn' : N.equiv ⟨x, hx⟩ = N.equiv ⟨y, hy⟩ :=
      cN.injective (by simpa only [hcN] using hn)
    exact congrArg Subtype.val (N.equiv.injective hn')
  have hoverlap : Set.range ι ∩ Set.range κ = ExpG ''
      ((T.kernelIdeal : Set (GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∩ H) := by
    rw [hiRange, hkRange]
    ext g
    constructor
    · rintro ⟨⟨x, hx, he⟩, ⟨y, hy, he'⟩⟩
      have hxy := hexpinj hx (he.trans he'.symm)
      exact ⟨x, ⟨hx, hxy ▸ hy⟩, he⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
  exact ⟨{
    N := N, D := D, weightCharacter := π, continuousWeightCharacter := hπ,
    weightCharacter_exp := hπExp, ExpN := ExpN, ExpD := ExpD, isExpN := hExpN, isExpD := hExpD,
    inclusionN := ι, inclusionD := κ, action := φ, closedN := hι, closedD := hκ,
    compatibleN := heι, compatibleD := heκ, normalN := hnormal, conjugation := hconj,
    surjective := hprod, openProduct := isOpenMap_factorProduct_of_map_nhds_one ι κ hlocal,
    compactLifts := hlifts, overlap := hoverlap }⟩

end PolycyclicRecognition

end

end OAI
