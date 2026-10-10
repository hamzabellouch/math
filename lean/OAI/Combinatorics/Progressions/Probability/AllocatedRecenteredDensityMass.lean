import OAI.Combinatorics.Progressions.Estimates.AllocatedSlicedCoarseSource

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]

variable (wholeReference : ((PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod ((residueRefinedPeriod modulus q)))) → ((PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) ((allocatedPrincipalSides B U b S))))) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (N : X → ℕ) {W τ ξ : ℝ} (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)

noncomputable def allocatedRecenteredFiberReconstruction
    (wholeReference : ((PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod ((residueRefinedPeriod modulus q)))) → ((PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) ((allocatedPrincipalSides B U b S))))) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (base : X → ℤ) (u : ((PrincipalAxisTuples (α := Fin dim) ((allocatedGridAxis (I := I) U b S.value)) ((allocatedPrincipalSides B U b S))))) (r : ((PrincipalTupleIndex (fun a : {a // ¬((allocatedGridAxis (I := I) U b S.value)) a} => B (Subtype.val a))
  (fun a => layerSamplerDegree I n (Subtype.val a)) → Option (Fin dim) → ZMod ((residueRefinedPeriod modulus q))))) :
    ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q →
      (X → (Unit ⊕ Fin dim) → ℤ) → (X → (Unit ⊕ Fin dim) → ℤ) := by
  exact
  allocatedWholeResidueReconstruction (G := G) (dim := dim) B U b S X modulus q wholeReference x base
    (principalAxisResidueJoin ((allocatedGridAxis (I := I) U b S.value)) u ((residueRefinedPeriod modulus q)) r)

noncomputable def allocatedRecenteredFiberMass
    (wholeReference : ((PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod ((residueRefinedPeriod modulus q)))) → ((PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) ((allocatedPrincipalSides B U b S))))) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (N : X → ℕ) {W τ ξ : ℝ} (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
    (profile : ((PrincipalAxisTuples (α := Fin dim) ((allocatedGridAxis (I := I) U b S.value)) ((allocatedPrincipalSides B U b S)))) → ((PrincipalTupleIndex (fun a : {a // ¬((allocatedGridAxis (I := I) U b S.value)) a} => B (Subtype.val a))
  (fun a => layerSamplerDegree I n (Subtype.val a)) → Option (Fin dim) → ZMod ((residueRefinedPeriod modulus q)))) → EuclideanJetLayers U O → ℝ) : ℝ := by
  let V := narrowTrimmedSpatialWidths (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
  let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
    (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i
  exact (((allocatedFrozenTupleWeights (α := Fin dim) B U b S))).mean (fun u => ((((allocatedLongTupleWeights (α := Fin dim) B U b S))).fiberLaw (principalResidueLabel ((residueRefinedPeriod modulus q)))).mean (fun r =>
    ∑ a : cells, selectedResidueCellWeight q cells V a *
      ((∑ v ∈ spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4,
        |profile u r (point (allocatedRecenteredFiberReconstruction (G := G) (dim := dim)
          B U b S X modulus q wholeReference x base u r a.val v))|) / A)))

theorem allocatedRecenteredProfileMass_fiber
    (profile : ((PrincipalAxisTuples (α := Fin dim) ((allocatedGridAxis (I := I) U b S.value)) ((allocatedPrincipalSides B U b S)))) → ((PrincipalTupleIndex (fun a : {a // ¬((allocatedGridAxis (I := I) U b S.value)) a} => B (Subtype.val a))
  (fun a => layerSamplerDegree I n (Subtype.val a)) → Option (Fin dim) → ZMod ((residueRefinedPeriod modulus q)))) → EuclideanJetLayers U O → ℝ) :
    (((principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) ((allocatedPrincipalSides B U b S))
  (allocatedPrincipalSides_pos B U b S)))).mean (allocatedRecenteredProfileMass (G := G) (dim := dim) (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point
        (fun y z => (profile (principalAxisRestrict ((allocatedGridAxis (I := I) U b S.value)) y)
          (principalResidueLabel ((residueRefinedPeriod modulus q)) (principalAxisRestrict (fun a => ¬((allocatedGridAxis (I := I) U b S.value)) a) y)) z : ℂ))) =
      allocatedRecenteredFiberMass (G := G) (dim := dim) (W := W) (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x N base cells point profile := by
  have h := congrArg Complex.re (principalTupleWeights_partition ((allocatedGridAxis (I := I) U b S.value)) ((allocatedPrincipalSides B U b S))
    (allocatedPrincipalSides_pos B U b S)
    (fun y => ((allocatedRecenteredProfileMass (G := G) (dim := dim) (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point
        (fun y z => (profile (principalAxisRestrict ((allocatedGridAxis (I := I) U b S.value)) y)
          (principalResidueLabel ((residueRefinedPeriod modulus q)) (principalAxisRestrict (fun a => ¬((allocatedGridAxis (I := I) U b S.value)) a) y)) z : ℂ)) y : ℝ) : ℂ)))
  simp only [FiniteProbabilityWeights.complexMean_re, Complex.ofReal_re] at h
  calc
    _ = (((allocatedFrozenTupleWeights (α := Fin dim) B U b S))).mean (fun u => (((allocatedLongTupleWeights (α := Fin dim) B U b S))).mean (fun v =>
      allocatedRecenteredProfileMass (G := G) (dim := dim) (W := W) (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x N base cells point
        (fun y z => (profile (principalAxisRestrict ((allocatedGridAxis (I := I) U b S.value)) y)
          (principalResidueLabel ((residueRefinedPeriod modulus q)) (principalAxisRestrict (fun a => ¬((allocatedGridAxis (I := I) U b S.value)) a) y)) z : ℂ))
        (principalAxisJoin ((allocatedGridAxis (I := I) U b S.value)) u v))) := by
      simpa only [allocatedFrozenTupleWeights, allocatedLongTupleWeights] using h
    _ = _ := by
      unfold allocatedRecenteredFiberMass
      simp only [FiniteProbabilityWeights.fiberLaw_mean]
      apply congrArg ((((allocatedFrozenTupleWeights (α := Fin dim) B U b S))).mean)
      funext u
      apply congrArg ((((allocatedLongTupleWeights (α := Fin dim) B U b S))).mean)
      funext v
      simp only [allocatedRecenteredProfileMass, principalAxisRestrict_join_left,
        principalAxisRestrict_join_right, principalResidueLabel_join,
        allocatedRecenteredFiberReconstruction, Complex.norm_real, Real.norm_eq_abs]

variable (weights : ((PrincipalTupleIndex (fun a : {a // ¬((allocatedGridAxis (I := I) U b S.value)) a} => B (Subtype.val a))
  (fun a => layerSamplerDegree I n (Subtype.val a)) → Option (Fin dim) → ZMod ((residueRefinedPeriod modulus q)))) → FiniteProbabilityWeights ((PrincipalAxisTuples (α := Fin dim) (fun a => ¬((allocatedGridAxis (I := I) U b S.value)) a) ((allocatedPrincipalSides B U b S)))))
variable (g : ((PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) ((allocatedPrincipalSides B U b S)))) → EuclideanJetLayers U O → ℝ)

theorem allocatedRecenteredFiberMass_le
    (profile error : ((PrincipalAxisTuples (α := Fin dim) ((allocatedGridAxis (I := I) U b S.value)) ((allocatedPrincipalSides B U b S)))) → ((PrincipalTupleIndex (fun a : {a // ¬((allocatedGridAxis (I := I) U b S.value)) a} => B (Subtype.val a))
  (fun a => layerSamplerDegree I n (Subtype.val a)) → Option (Fin dim) → ZMod ((residueRefinedPeriod modulus q)))) → EuclideanJetLayers U O → ℝ)
    (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ) (hN : ∀ t, 0 < N t) (hq : ∀ t, 0 < q t)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells ((narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)) z)
    (C Etail : ℝ) (hg : ∀ y z, 0 ≤ g y z)
    (hcompare : ∀ u r z, |(weights r).mean (fun v => g (principalAxisJoin ((allocatedGridAxis (I := I) U b S.value)) u v) z) - profile u r z| ≤ error u r z)
    (hprojected : ∀ u r v, (weights r).weight v ≠ 0 → ∀ a : cells,
      (∑ z ∈ ((spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4)), g (principalAxisJoin ((allocatedGridAxis (I := I) U b S.value)) u v) (point (allocatedRecenteredFiberReconstruction (G := G) (dim := dim)
        B U b S X modulus q wholeReference x base u r a.val z))) ≤ C * ((∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i)))
    (htail : ∀ u r, (∑ a : cells, selectedResidueCellWeight q cells ((narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)) a *
      ((∑ v ∈ ((spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4)), error u r (point (allocatedRecenteredFiberReconstruction (G := G) (dim := dim)
        B U b S X modulus q wholeReference x base u r a.val v))) / ((∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i)))) ≤ Etail) :
    allocatedRecenteredFiberMass (G := G) (dim := dim) (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point profile ≤ C + Etail := by
  let index := cells × ((spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4))
  let F := allocatedRecenteredFiberReconstruction (G := G) (dim := dim) B U b S X modulus q wholeReference x base
  have hA : 0 < ((∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i)) := Finset.prod_pos (fun t _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim)
      (trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)).1
      (trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)).2 (Nat.cast_pos.mpr S.positive) i))
  have hwidths := narrowTrimmedSpatialWidths_pos (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n)) hW hτ hξ N hN
  have hlocal (u : ((PrincipalAxisTuples (α := Fin dim) ((allocatedGridAxis (I := I) U b S.value)) ((allocatedPrincipalSides B U b S))))) (r : ((PrincipalTupleIndex (fun a : {a // ¬((allocatedGridAxis (I := I) U b S.value)) a} => B (Subtype.val a))
  (fun a => layerSamplerDegree I n (Subtype.val a)) → Option (Fin dim) → ZMod ((residueRefinedPeriod modulus q))))) :
      (∑ a : cells, selectedResidueCellWeight q cells ((narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)) a *
        ((∑ v ∈ ((spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4)), |profile u r (point (F u r a.val v))|) / ((∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i)))) ≤ C + Etail := by
    have hm (v : ((PrincipalAxisTuples (α := Fin dim) (fun a => ¬((allocatedGridAxis (I := I) U b S.value)) a) ((allocatedPrincipalSides B U b S))))) (hv : (weights r).weight v ≠ 0) :
        (∑ t : index, (selectedResidueCellWeight q cells ((narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)) t.1 / ((∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i))) *
          g (principalAxisJoin ((allocatedGridAxis (I := I) U b S.value)) u v) (point (F u r t.1.val t.2.val))) ≤ C := by
      apply partition_weighted_mass_le (fun a : cells => selectedResidueCellWeight q cells ((narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)) a)
        (fun a (z : ((spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4))) => g (principalAxisJoin ((allocatedGridAxis (I := I) U b S.value)) u v) (point (F u r a.val z.val)))
        (fun _ => selectedResidueCellWeight_nonneg _ _ _ _)
        (selectedResidueCellWeight_sum q cells ((narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)) hwidths hmass) hA
      intro a
      rw [← Finset.sum_subtype
        (spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4)
        (fun _ => Iff.rfl)
        (fun z => g (principalAxisJoin (allocatedGridAxis (I := I) U b S.value) u v)
          (point (F u r a.val z)))]
      exact hprojected u r v hv a
    have h := (weights r).weighted_proxy_abs_mass_le
      (fun t : index => selectedResidueCellWeight q cells ((narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)) t.1 / ((∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i)))
      (fun v (t : index) => g (principalAxisJoin ((allocatedGridAxis (I := I) U b S.value)) u v) (point (F u r t.1.val t.2.val)))
      (fun t : index => profile u r (point (F u r t.1.val t.2.val)))
      (fun t : index => error u r (point (F u r t.1.val t.2.val)))
      (fun _ => div_nonneg (selectedResidueCellWeight_nonneg _ _ _ _) hA.le)
      (fun _ _ => hg _ _) (fun _ => hcompare u r _) hm
    have hsum (f : cells → (X → (Unit ⊕ Fin dim) → ℤ) → ℝ) :
        (∑ t : index, selectedResidueCellWeight q cells ((narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)) t.1 / ((∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i)) * f t.1 t.2.val) =
        ∑ a : cells, selectedResidueCellWeight q cells ((narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)) a * ((∑ v ∈ ((spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4)), f a v) / ((∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i))) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      dsimp only
      rw [← Finset.mul_sum, ← Finset.sum_subtype
        (spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4)
        (fun _ => Iff.rfl) (f a)]
      ring
    rw [hsum (fun a v => |profile u r (point (F u r a.val v))|),
      hsum (fun a v => error u r (point (F u r a.val v)))] at h
    exact h.trans (add_le_add le_rfl (htail u r))
  unfold allocatedRecenteredFiberMass
  exact ((((allocatedFrozenTupleWeights (α := Fin dim) B U b S))).mean_mono (fun u =>
    (((((allocatedLongTupleWeights (α := Fin dim) B U b S))).fiberLaw (principalResidueLabel ((residueRefinedPeriod modulus q)))).mean_mono (hlocal u)).trans_eq
      (FiniteProbabilityWeights.mean_const _ _))).trans_eq ((((allocatedFrozenTupleWeights (α := Fin dim) B U b S))).mean_const _)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset (Fin dim))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Module.Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

variable (modulus : ℕ)
variable (f : ((Σ a : {a // ¬((allocatedGridAxis (I := I) U b S.value)) a}, O a.val.1) → ℝ) → ℝ)
variable (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)

include hperiod in
theorem allocatedWholeMaskedCoveredProfile_long_residue_eq
    (u : ((PrincipalAxisTuples (α := Fin dim) ((allocatedGridAxis (I := I) U b S.value)) ((allocatedPrincipalSides B U b S))))) (v w : ((PrincipalAxisTuples (α := Fin dim) (fun a => ¬((allocatedGridAxis (I := I) U b S.value)) a) ((allocatedPrincipalSides B U b S)))))
    (hlabel : principalResidueLabel modulus v = principalResidueLabel modulus w) :
    allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d (principalAxisJoin ((allocatedGridAxis (I := I) U b S.value)) u v) modulus f =
      allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d (principalAxisJoin ((allocatedGridAxis (I := I) U b S.value)) u w) modulus f := by
  simp only [allocatedWholeMaskedCoveredProfile, principalAxisRestrict_join_left, principalAxisRestrict_join_right]
  rw [show (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) modulus) =
      (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j w) modulus) from
    funext (fun j => allocatedNonkernelJetMatrix_residue_of_label B U b S x rows u v w modulus hlabel j)]
  exact allocatedCoveredProfileDensity_long_residue_eq B U b hR hσ S x rows hb o bW d
    u v w modulus hperiod hlabel _

variable (X : Type*) [Fintype X] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (reference : ((PrincipalAxisTuples (α := Fin dim) ((allocatedGridAxis (I := I) U b S.value)) ((allocatedPrincipalSides B U b S)))) → ((PrincipalTupleIndex (fun a : {a // ¬((allocatedGridAxis (I := I) U b S.value)) a} => B (Subtype.val a))
  (fun a => layerSamplerDegree I n (Subtype.val a)) → Option (Fin dim) → ZMod ((residueRefinedPeriod modulus q)))) → ((PrincipalAxisTuples (α := Fin dim) (fun a => ¬((allocatedGridAxis (I := I) U b S.value)) a) ((allocatedPrincipalSides B U b S)))))
variable (wholeReference : ((PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod ((residueRefinedPeriod modulus q)))) → ((PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) ((allocatedPrincipalSides B U b S)))))
variable (N : X → ℕ) {W τ ξ : ℝ} (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)

include hperiod in
theorem allocatedRecenteredMaskedProfileMass_fiber
    (href : ∀ u r, principalResidueLabel ((residueRefinedPeriod modulus q)) (reference u r) = r) :
    (((principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) ((allocatedPrincipalSides B U b S))
  (allocatedPrincipalSides_pos B U b S)))).mean (allocatedRecenteredProfileMass (G := G) (dim := dim) (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point
      (fun y z => (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y modulus f z : ℂ))) =
    allocatedRecenteredFiberMass (G := G) (dim := dim) (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point
      (fun u r => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
        (principalAxisJoin ((allocatedGridAxis (I := I) U b S.value)) u (reference u r)) modulus f) := by
  let profile := fun u r => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
    (principalAxisJoin ((allocatedGridAxis (I := I) U b S.value)) u (reference u r)) modulus f
  have hfun : (fun y z => (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y modulus f z : ℂ)) =
      (fun y z => (profile (principalAxisRestrict ((allocatedGridAxis (I := I) U b S.value)) y)
        (principalResidueLabel ((residueRefinedPeriod modulus q)) (principalAxisRestrict (fun a => ¬((allocatedGridAxis (I := I) U b S.value)) a) y)) z : ℂ)) := by
    funext y z
    let u := principalAxisRestrict ((allocatedGridAxis (I := I) U b S.value)) y
    let v := principalAxisRestrict (fun a => ¬((allocatedGridAxis (I := I) U b S.value)) a) y
    let r := principalResidueLabel ((residueRefinedPeriod modulus q)) v
    have hlabel : principalResidueLabel modulus (reference u r) = principalResidueLabel modulus v :=
      principalResidueLabel_eq_of_dvd _ _ ⟨∏ t, q t, rfl⟩ (href u r)
    have heq := allocatedWholeMaskedCoveredProfile_long_residue_eq B U b hR hσ S x rows hb o bW d
      modulus f hperiod u (reference u r) v hlabel
    have hj : principalAxisJoin ((allocatedGridAxis (I := I) U b S.value)) u v = y := principalAxisJoin_restrict ((allocatedGridAxis (I := I) U b S.value)) y
    rw [hj] at heq
    exact congrArg Complex.ofReal (congrFun heq z).symm
  rw [hfun]
  exact allocatedRecenteredProfileMass_fiber B U b S X modulus q wholeReference x N base cells point profile

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset (Fin dim))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Module.Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

variable (modulus : ℕ)
variable (f : ((Σ a : {a // ¬((allocatedGridAxis (I := I) U b S.value)) a}, O a.val.1) → ℝ) → ℝ)
variable (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)

variable (X : Type*) [Fintype X] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (reference : ((PrincipalAxisTuples (α := Fin dim) ((allocatedGridAxis (I := I) U b S.value)) ((allocatedPrincipalSides B U b S)))) → ((PrincipalTupleIndex (fun a : {a // ¬((allocatedGridAxis (I := I) U b S.value)) a} => B (Subtype.val a))
  (fun a => layerSamplerDegree I n (Subtype.val a)) → Option (Fin dim) → ZMod ((residueRefinedPeriod modulus q)))) → ((PrincipalAxisTuples (α := Fin dim) (fun a => ¬((allocatedGridAxis (I := I) U b S.value)) a) ((allocatedPrincipalSides B U b S)))))
variable (wholeReference : ((PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod ((residueRefinedPeriod modulus q)))) → ((PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) ((allocatedPrincipalSides B U b S)))))
variable (N : X → ℕ) {W τ ξ : ℝ} (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)

include hperiod in
theorem allocatedRecenteredMaskedMass_of_comparison
    (href : ∀ u r, principalResidueLabel ((residueRefinedPeriod modulus q)) (reference u r) = r)
    (weights : ((PrincipalTupleIndex (fun a : {a // ¬((allocatedGridAxis (I := I) U b S.value)) a} => B (Subtype.val a))
  (fun a => layerSamplerDegree I n (Subtype.val a)) → Option (Fin dim) → ZMod ((residueRefinedPeriod modulus q)))) → FiniteProbabilityWeights ((PrincipalAxisTuples (α := Fin dim) (fun a => ¬((allocatedGridAxis (I := I) U b S.value)) a) ((allocatedPrincipalSides B U b S)))))
    (g : ((PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) ((allocatedPrincipalSides B U b S)))) → EuclideanJetLayers U O → ℝ)
    (error : ((PrincipalAxisTuples (α := Fin dim) ((allocatedGridAxis (I := I) U b S.value)) ((allocatedPrincipalSides B U b S)))) → ((PrincipalTupleIndex (fun a : {a // ¬((allocatedGridAxis (I := I) U b S.value)) a} => B (Subtype.val a))
  (fun a => layerSamplerDegree I n (Subtype.val a)) → Option (Fin dim) → ZMod ((residueRefinedPeriod modulus q)))) → EuclideanJetLayers U O → ℝ)
    (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ) (hN : ∀ t, 0 < N t) (hq : ∀ t, 0 < q t)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells ((narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)) z)
    (Etail : ℝ) (hg : ∀ y z, 0 ≤ g y z)
    (hcompare : ∀ u r z, |(weights r).mean (fun v => g (principalAxisJoin ((allocatedGridAxis (I := I) U b S.value)) u v) z) -
      allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
        (principalAxisJoin ((allocatedGridAxis (I := I) U b S.value)) u (reference u r)) modulus f z| ≤ error u r z)
    (hprojected : ∀ y y₀ (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q),
      (∑ v ∈ ((spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4)), g y (point (physicalResidueReconstruction
        (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y₀)
        (allocatedPhysicalCubeDirections B U b S x y₀) base
        (boundedColumnResidueRepresentative q a) q v))) ≤
      (4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X)) *
        (∏ t, ∏ _i : Unit ⊕ Fin dim, trimmedSpatialRootScale τ N q t))
    (htail : ∀ u r, (∑ a : cells, selectedResidueCellWeight q cells ((narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)) a *
      ((∑ v ∈ ((spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4)), error u r (point (allocatedRecenteredFiberReconstruction (G := G) (dim := dim)
        B U b S X modulus q wholeReference x base u r a.val v))) / ((∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i)))) ≤ Etail) :
    (((principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) ((allocatedPrincipalSides B U b S))
  (allocatedPrincipalSides_pos B U b S)))).mean (allocatedRecenteredProfileMass (G := G) (dim := dim) (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point
      (fun y z => (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y modulus f z : ℂ))) ≤
      coarseReferenceMassConstant dim X W S.value + Etail := by
  rw [allocatedRecenteredMaskedProfileMass_fiber B U b hR hσ S x rows hb o bW d
    modulus f hperiod X q reference wholeReference N base cells point href]
  apply allocatedRecenteredFiberMass_le B U b S X modulus q wholeReference x N base cells point
    weights g _ error hW hτ hξ hN hq hmass (coarseReferenceMassConstant dim X W S.value) Etail
    hg hcompare _ htail
  intro u r v _ a
  have h := hprojected (principalAxisJoin ((allocatedGridAxis (I := I) U b S.value)) u v)
    (wholeReference (principalAxisResidueJoin ((allocatedGridAxis (I := I) U b S.value)) u ((residueRefinedPeriod modulus q)) r)) a.val
  rw [physicalSpatial_uniform_volume (trimmedSpatialRootScale τ N q)
    (trimmedSpatialSlopeScale W τ N q) (Nat.cast_ne_zero.mpr S.positive.ne')
    (fun t => trimmedSpatial_scale_ratio hW N q t)] at h
  simpa only [allocatedRecenteredFiberReconstruction, allocatedWholeResidueReconstruction,
    coarseReferenceMassConstant, Fintype.card_fin, mul_assoc] using h

end Erdos3.VectorPolynomial

end

end OAI
