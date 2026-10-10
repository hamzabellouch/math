import OAI.GroupTheory.PolycyclicRecognition.Geometry.ClosedIntegrationInHeightKernel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ClosedIntegrationOverHeight
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConnectedIdealNormality
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialTangentUniqueness

namespace OAI

/-! # Cartan factors from the intrinsic height kernel

Both nilpotent factor inclusions are closed without the ambient exponential
chart. Their product and exact overlap follow from local multiplication
coordinates and uniqueness of exponential preimages in the height kernel.
-/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped Manifold ContDiff

variable {E G W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
  (q : HeightSpace T.character ≃ₗ[ℝ] W)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
  (π : G →* Multiplicative W) (hπ : Continuous π)
  (hπExp : ∀ v, (π (Exp v)).toAdd = q (heightProjection T.character v))
  (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) [H.IsCartanSubalgebra]

include q hExp hπ hπExp in
theorem nonempty_intrinsic_cartanFactorModel : Nonempty (CartanFactorModel H Exp) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  have hn := cartanRootIdeal_nilpotent H T
  obtain ⟨N⟩ := nilpotentPublishedInputs.existsModel (cartanRootIdeal H) hn
  obtain ⟨D⟩ := nilpotentPublishedInputs.existsModel H inferInstance
  let : IsTopologicalGroup N.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, N.modelSpace)) ⊤
  let : IsTopologicalGroup D.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, D.modelSpace)) ⊤
  let : LocallyCompactSpace N.carrier := ChartedSpace.locallyCompactSpace N.modelSpace N.carrier
  let : LocallyCompactSpace D.carrier := ChartedSpace.locallyCompactSpace D.modelSpace D.carrier
  obtain ⟨ExpN, hExpN, cN, hcN⟩ := N.exists_exponential_chart hn
    (nilpotentPublishedInputs.haar (cartanRootIdeal H) N)
  obtain ⟨ExpD, hExpD, cD, hcD⟩ := D.exists_exponential_chart inferInstance
    (nilpotentPublishedInputs.haar H D)
  obtain ⟨ι, hι, hιsmooth, heι⟩ := exists_closed_integration_in_height_kernel T q Exp hExp
    π hπ hπExp (cartanRootIdeal H) (cartanRootIdeal_le_kernel H T) hn N ExpN hExpN
  let jD := H.incl.comp D.equiv.symm.toLieHom
  have hjD : Function.Injective jD := Subtype.val_injective.comp D.equiv.symm.injective
  have hsurj : Function.Surjective
      ((q.toLinearMap.comp (heightProjection T.character)).comp jD.toLinearMap) := by
    exact q.surjective.comp ((cartan_height_surjective T H).comp D.equiv.symm.surjective)
  obtain ⟨κ, hκ, hκsmooth, heκall⟩ := exists_closed_nilpotent_integration_over_height T q Exp
    hExp π hπ hπExp H D inferInstance jD hjD hsurj
  have heκ (x : H) : κ (ExpD (D.equiv x)) = Exp x := by
    simpa [jD] using heκall ExpD hExpD (D.equiv x)
  have hiExp (x : N.modelSpace) : ι (ExpN x) = Exp ((cartanRootIdeal H).incl (N.equiv.symm x)) := by
    change ι (ExpN x) = Exp (N.equiv.symm x)
    exact (congrArg (fun y : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier =>
      ι (ExpN y)) (N.equiv.apply_symm_apply x)).symm.trans (heι (N.equiv.symm x))
  have hkExp (x : D.modelSpace) : κ (ExpD x) = Exp (H.incl (D.equiv.symm x)) := by
    change κ (ExpD x) = Exp (D.equiv.symm x)
    exact (congrArg (fun y : GroupLieAlgebra (𝓘(ℝ, D.modelSpace)) D.carrier =>
      κ (ExpD y)) (D.equiv.apply_symm_apply x)).symm.trans (heκ (D.equiv.symm x))
  have hiRange : Set.range ι = Exp '' (cartanRootIdeal H : Set (GroupLieAlgebra (𝓘(ℝ, E)) G)) := by
    ext g
    constructor
    · rintro ⟨n, rfl⟩
      obtain ⟨x, hx⟩ := cN.surjective n
      rw [hcN] at hx
      exact ⟨N.equiv.symm x, (N.equiv.symm x).property, (hiExp x).symm.trans (congrArg ι hx)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨ExpN (N.equiv ⟨x, hx⟩), heι ⟨x, hx⟩⟩
  have hkRange : Set.range κ = Exp '' (H : Set (GroupLieAlgebra (𝓘(ℝ, E)) G)) := by
    ext g
    constructor
    · rintro ⟨d, rfl⟩
      obtain ⟨x, hx⟩ := cD.surjective d
      rw [hcD] at hx
      exact ⟨D.equiv.symm x, (D.equiv.symm x).property, (hkExp x).symm.trans (congrArg κ hx)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨ExpD (D.equiv ⟨x, hx⟩), heκ ⟨x, hx⟩⟩
  have hnormal : ι.range.Normal := normal_of_exponential_ideal_connected hExp
    (cartanRootIdeal H) ι.range hiRange
  let φ := conjugationLiftOfNormal ι κ hι.injective hnormal
  have hconj (d : D.carrier) (n : N.carrier) :
      ι (φ d n) = κ d * ι n * (κ d)⁻¹ :=
    conjugationLiftOfNormal_spec ι κ hι.injective hnormal d n
  have hiDiff := mfderiv_eq_of_exponential_compatibility hExpN hExp ι
    (hιsmooth.mdifferentiable (by simp))
    ((cartanRootIdeal H).incl.comp N.equiv.symm.toLieHom).toLinearMap hiExp
  have hkDiff := mfderiv_eq_of_exponential_compatibility hExpD hExp κ
    (hκsmooth.mdifferentiable (by simp)) jD.toLinearMap hkExp
  have hlocal := cartanFactorProduct_map_nhds_one ι κ T H N.equiv D.equiv hιsmooth hκsmooth
    (fun x => by
      change mfderiv (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, E)) ι 1 (N.equiv x) = (x : GroupLieAlgebra (𝓘(ℝ, E)) G)
      exact (hiDiff (N.equiv x)).trans
        (congrArg (fun z : cartanRootIdeal H => (z : GroupLieAlgebra (𝓘(ℝ, E)) G))
          (N.equiv.symm_apply_apply x)))
    (fun x => by
      change mfderiv (𝓘(ℝ, D.modelSpace)) (𝓘(ℝ, E)) κ 1 (D.equiv x) = (x : GroupLieAlgebra (𝓘(ℝ, E)) G)
      exact (hkDiff (D.equiv x)).trans
        (congrArg (fun z : H => (z : GroupLieAlgebra (𝓘(ℝ, E)) G))
          (D.equiv.symm_apply_apply x)))
  obtain ⟨hprod, hlifts⟩ := factorProduct_surjective_and_compact_lifts ι κ φ hconj hlocal
  have hoverlap : Set.range ι ∩ Set.range κ = Exp ''
      ((cartanRootIdeal H : Set (GroupLieAlgebra (𝓘(ℝ, E)) G)) ∩ H) := by
    rw [hiRange, hkRange]
    ext g
    constructor
    · rintro ⟨⟨x, hx, hxe⟩, ⟨y, hy, hye⟩⟩
      have hxy := exponential_eq_of_mem_intrinsic_height_kernel T q Exp hExp π hπ hπExp
        (cartanRootIdeal_le_kernel H T hx) (hxe.trans hye.symm)
      exact ⟨x, ⟨hx, hxy ▸ hy⟩, hxe⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
  exact ⟨{
    N := N, D := D, ExpN := ExpN, ExpD := ExpD, isExpN := hExpN, isExpD := hExpD,
    inclusionN := ι, inclusionD := κ, action := φ, closedN := hι, closedD := hκ,
    compatibleN := heι, compatibleD := heκ, normalN := hnormal, conjugation := hconj,
    surjective := hprod, compactLifts := hlifts, overlap := hoverlap }⟩

end PolycyclicRecognition

end

end OAI
