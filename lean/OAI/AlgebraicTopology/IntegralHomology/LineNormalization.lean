import OAI.AlgebraicTopology.IntegralHomology.AffineAvoidance

namespace OAI

noncomputable section

namespace Kaplansky

/-! Integral line normalization and finite-cover diagonal comparison. -/

section
open Bundle Topology CategoryTheory
variable {A S : Type} [TopologicalSpace A] [Fintype S] {d : S → ℕ}
  (p : ∀ s, C(A,projectionSpace (d s) 1))
  (v : ∀ s, A → EuclideanSpace ℂ (Fin (d s)))
  (hm : ∀ s a, v s a ∈ projectionLine (p s a))
  (hn : ∀ s a, v s a ≠ 0) (hc : ∀ s, Continuous (v s))

/-- Relative pair coordinates on the ACTUAL finite sum of hyperplane lines. -/
def finiteLineEvaluationRelativeIso (n : ℕ) :=
  relativeHomologyHomeomorphIso (finiteLineEvaluationHomeomorph p v hm hn hc)
    {z : TotalSpace (EuclideanSpace ℂ S)
      (finiteLineSumCore (fun s => evaluationPullbackCore (p s))).Fiber | z.2 ≠ 0}
    {z : A × (S → ℂ) | z.2 ≠ 0}
    (fun z => (not_congr (finiteLineEvaluationHomeomorph_zero_iff p v hm hn hc z)).symm) n

/-- Fiber normalization defined even when the base is not contractible. -/
def finiteLineEvaluationNormalization (n : ℕ) :=
  (finiteLineEvaluationRelativeIso p v hm hn hc n).hom ≫
    productPairProjection (B := A) ({0}ᶜ : Set (S → ℂ)) n

theorem finiteLineEvaluationNormalization_isIso [ContractibleSpace A] (n : ℕ) :
    IsIso (finiteLineEvaluationNormalization p v hm hn hc n) := by
  have hpiso := productPairProjection_isIso (B := A) ({0}ᶜ : Set (S → ℂ)) n
  unfold finiteLineEvaluationNormalization
  exact @IsIso.comp_isIso _ _ _ _ _ _ _
    (finiteLineEvaluationRelativeIso p v hm hn hc n).isIso_hom hpiso

variable (w : ∀ s, A → EuclideanSpace ℂ (Fin (d s)))
  (hwm : ∀ s a, w s a ∈ projectionLine (p s a))
  (hwn : ∀ s a, w s a ≠ 0) (hwc : ∀ s, Continuous (w s))

/-- The transition between these actual evaluation charts is diagonal
on each fiber, with explicitly invertible complex entries. -/
theorem finiteLineEvaluation_transition (a : A) (z : S → ℂ) :
    finiteLineEvaluationEquiv p w hwm hwn a
      ((finiteLineEvaluationEquiv p v hm hn a).symm z) =
    complexDiagonalMap (fun s => complexLineCoordinateUnit
      (pullbackEvaluationEquiv (p s) (v s) (hm s) (hn s) a)
      (pullbackEvaluationEquiv (p s) (w s) (hwm s) (hwn s) a)) z := by
  funext s
  exact complexLineCoordinate_change
    (pullbackEvaluationEquiv (p s) (v s) (hm s) (hn s) a)
    (pullbackEvaluationEquiv (p s) (w s) (hwm s) (hwn s) a) (z s)

/-- Genuine integral fiber normalizations from ANY two continuous,
nonvanishing line frames agree over a contractible base. No orientation,
transition degree, or homology compatibility premise is assumed. -/
theorem finiteLineEvaluationNormalization_eq [ContractibleSpace A] (n : ℕ) :
    finiteLineEvaluationNormalization p v hm hn hc n =
      finiteLineEvaluationNormalization p w hwm hwn hwc n := by
  let ev := finiteLineEvaluationHomeomorph p v hm hn hc
  let ew := finiteLineEvaluationHomeomorph p w hwm hwn hwc
  let f : C(A × (S → ℂ),(S → ℂ)) :=
    ⟨fun z => (ew (ev.symm z)).2, continuous_snd.comp (ew.continuous.comp ev.symm.continuous)⟩
  have hf : ∀ z : A × (S → ℂ), z.2 ≠ 0 → f z ≠ 0 := by
    intro z hz he
    have hw : (ev.symm z).2 = 0 :=
      (finiteLineEvaluationHomeomorph_zero_iff p w hwm hwn hwc _).mp he
    have hv := (finiteLineEvaluationHomeomorph_zero_iff p v hm hn hc (ev.symm z)).mpr hw
    change (ev (ev.symm z)).2 = 0 at hv
    rw [ev.apply_symm_apply] at hv
    exact hz hv
  let a : A := Classical.choice (inferInstance : Nonempty A)
  let c : S → ℂˣ := fun s => complexLineCoordinateUnit
    (pullbackEvaluationEquiv (p s) (v s) (hm s) (hn s) a)
    (pullbackEvaluationEquiv (p s) (w s) (hwm s) (hwn s) a)
  have he : ∀ z, f (a,z) = complexDiagonalMap c z :=
    finiteLineEvaluation_transition p v hm hn w hwm hwn a
  have hnorm := productPairCoordinateMap_eq_projection f hf a c he n
  have heq : finiteLineEvaluationNormalization p w hwm hwn hwc n =
      (finiteLineEvaluationRelativeIso p v hm hn hc n).hom ≫
        productPairCoordinateMap f hf n := by
    unfold finiteLineEvaluationNormalization finiteLineEvaluationRelativeIso
    rw [relativeHomologyHomeomorphIso_hom, relativeHomologyHomeomorphIso_hom]
    unfold productPairProjection productPairCoordinateMap
    erw [relativeHomologyMap_comp, relativeHomologyMap_comp]
    apply relativeHomologyMap_congr_ambient
    ext z : 1
    change (ew z).2 = (ew (ev.symm (ev z))).2
    rw [ev.symm_apply_apply]
  rw [heq, hnorm]
  rfl

end

section
open CategoryTheory Limits Set
variable {B ι J : Type} [TopologicalSpace B]

/-- A finite contractible cover detects the normalization of a varying
complex diagonal coordinate change. The whole base need not be contractible
or connected; the lower intersection groups are the actual relative groups. -/
theorem productPairCoordinateMap_eq_projection_of_finite_cover
    (S : Finset J) (U : J → Set B)
    (hopen : ∀ i ∈ S, IsOpen (U i)) (hcover : (⋃ i ∈ S, U i) = Set.univ)
    (hchart : ∀ i ∈ S, (U i).Nonempty → ContractibleSpace (U i))
    (n : ℕ)
    (hinter : ∀ T : Finset J, T.Nonempty → T ⊆ S → ∀ q < n+1,
      IsZero (relativeSingularHomology
        (subspaceInclusion {z : (⋂ i ∈ T, U i) × (ι → ℂ) | z.2 ≠ 0}) q))
    (f : C(B × (ι → ℂ),(ι → ℂ))) (hf : ∀ z, z.2 ≠ 0 → f z ≠ 0)
    (a : B → ι → ℂˣ) (he : ∀ b v, f (b,v) = complexDiagonalMap (a b) v) :
    productPairCoordinateMap f hf (n+1) =
      productPairProjection (B := B) ({0}ᶜ : Set (ι → ℂ)) (n+1) := by
  let C : J → Set (B × (ι → ℂ)) := fun i => {z | z.1 ∈ U i}
  let A : Set (B × (ι → ℂ)) := {z | z.2 ∈ ({0}ᶜ : Set (ι → ℂ))}
  have hC : (⋃ i ∈ S, C i) = Set.univ := by
    ext z
    have hb : z.1 ∈ ⋃ i ∈ S, U i := by rw [hcover]; trivial
    simpa only [mem_iUnion, C, mem_ofPred_eq, mem_univ, iff_true] using hb
  refine finiteRelativeOpenCover_hom_ext S C A
    (fun i hi => (hopen i hi).preimage continuous_fst) hC n ?_ _ _ ?_
  · intro T ht hts q hq
    have heC : (⋂ i ∈ T, C i) = {point : B × (ι → ℂ) | point.1 ∈ ⋂ i ∈ T, U i} := by
      ext point
      simp [C]
    rw [heC]
    exact (hinter T ht hts q hq).of_iso
      (productPairBaseSubsetIso (⋂ i ∈ T, U i) ({0}ᶜ : Set (ι → ℂ)) q)
  · intro i hi
    by_cases hne : (U i).Nonempty
    · let : ContractibleSpace (U i) := hchart i hi hne
      let b : U i := ⟨hne.choose,hne.choose_spec⟩
      have := productPairChartFiberMap_isIso (U i) b ({0}ᶜ : Set (ι → ℂ)) (n+1)
      apply (cancel_epi (productPairChartFiberMap (U i) b ({0}ᶜ : Set (ι → ℂ)) (n+1))).mp
      have hc : productPairFiberMap b.1 ({0}ᶜ : Set (ι → ℂ)) (n+1) ≫
          productPairCoordinateMap f hf (n+1) = complexDiagonalRelativeMap (a b.1) (n+1) := by
        unfold productPairFiberMap productPairCoordinateMap complexDiagonalRelativeMap
        erw [relativeHomologyMap_comp]
        apply relativeHomologyMap_congr_ambient
        ext v : 1
        exact he b.1 v
      have hincl := productPairChartFiberMap_inclusion (U i) b ({0}ᶜ : Set (ι → ℂ)) (n+1)
      have hc' := (congrArg (fun g => g ≫ productPairCoordinateMap f hf (n+1)) hincl).trans
        (hc.trans (complexDiagonalRelativeMap_eq_id (a b.1) (n+1)))
      have hp' := (congrArg (fun g => g ≫ productPairProjection (B := B) ({0}ᶜ : Set (ι → ℂ))
        (n+1)) hincl).trans (productPairFiberMap_projection b.1 ({0}ᶜ : Set (ι → ℂ)) (n+1))
      exact (Category.assoc _ _ _).symm.trans
        (hc'.trans (hp'.symm.trans (Category.assoc _ _ _)))
    · have : IsEmpty (C i) := ⟨fun z => hne ⟨z.1.1,z.2⟩⟩
      exact (relativeHomology_isZero_empty (Subtype.val ⁻¹' A : Set (C i)) (n+1)).eq_of_src _ _

end

section
open Bundle Topology CategoryTheory
variable {A S : Type} [TopologicalSpace A] [Fintype S] {d : S → ℕ}
  (p : ∀ s, C(A,projectionSpace (d s) 1))
  (v : ∀ s, A → EuclideanSpace ℂ (Fin (d s)))
  (hm : ∀ s a, v s a ∈ projectionLine (p s a))
  (hn : ∀ s a, v s a ≠ 0) (hc : ∀ s, Continuous (v s))

variable (w : ∀ s, A → EuclideanSpace ℂ (Fin (d s)))
  (hwm : ∀ s a, w s a ∈ projectionLine (p s a))
  (hwn : ∀ s a, w s a ≠ 0) (hwc : ∀ s, Continuous (w s))

/-- Normalization of the actual finite sum of hyperplane lines is independent
of the chosen continuous nonvanishing line frames on a finite contractible
cover with the stated lower intersection vanishing. No global contractibility
or connectedness hypothesis is required. -/
theorem finiteLineEvaluationNormalization_eq_of_finite_cover
    {J : Type} (T : Finset J) (U : J → Set A)
    (hopen : ∀ i ∈ T, IsOpen (U i)) (hcover : (⋃ i ∈ T, U i) = Set.univ)
    (hchart : ∀ i ∈ T, (U i).Nonempty → ContractibleSpace (U i))
    (n : ℕ)
    (hinter : ∀ I : Finset J, I.Nonempty → I ⊆ T → ∀ q < n+1,
      Limits.IsZero (relativeSingularHomology
        (subspaceInclusion {z : (⋂ i ∈ I, U i) × (S → ℂ) | z.2 ≠ 0}) q)) :
    finiteLineEvaluationNormalization p v hm hn hc (n+1) =
      finiteLineEvaluationNormalization p w hwm hwn hwc (n+1) := by
  let ev := finiteLineEvaluationHomeomorph p v hm hn hc
  let ew := finiteLineEvaluationHomeomorph p w hwm hwn hwc
  let f : C(A × (S → ℂ),(S → ℂ)) :=
    ⟨fun z => (ew (ev.symm z)).2, continuous_snd.comp (ew.continuous.comp ev.symm.continuous)⟩
  have hf : ∀ z : A × (S → ℂ), z.2 ≠ 0 → f z ≠ 0 := by
    intro z hz he
    have hw : (ev.symm z).2 = 0 :=
      (finiteLineEvaluationHomeomorph_zero_iff p w hwm hwn hwc _).mp he
    have hv := (finiteLineEvaluationHomeomorph_zero_iff p v hm hn hc (ev.symm z)).mpr hw
    change (ev (ev.symm z)).2 = 0 at hv
    rw [ev.apply_symm_apply] at hv
    exact hz hv
  let c : A → S → ℂˣ := fun a s => complexLineCoordinateUnit
    (pullbackEvaluationEquiv (p s) (v s) (hm s) (hn s) a)
    (pullbackEvaluationEquiv (p s) (w s) (hwm s) (hwn s) a)
  have he : ∀ a z, f (a,z) = complexDiagonalMap (c a) z :=
    finiteLineEvaluation_transition p v hm hn w hwm hwn
  have hnorm := productPairCoordinateMap_eq_projection_of_finite_cover
    T U hopen hcover hchart n hinter f hf c he
  have heq : finiteLineEvaluationNormalization p w hwm hwn hwc (n+1) =
      (finiteLineEvaluationRelativeIso p v hm hn hc (n+1)).hom ≫
        productPairCoordinateMap f hf (n+1) := by
    unfold finiteLineEvaluationNormalization finiteLineEvaluationRelativeIso
    rw [relativeHomologyHomeomorphIso_hom, relativeHomologyHomeomorphIso_hom]
    unfold productPairProjection productPairCoordinateMap
    erw [relativeHomologyMap_comp, relativeHomologyMap_comp]
    apply relativeHomologyMap_congr_ambient
    ext z : 1
    change (ew z).2 = (ew (ev.symm (ev z))).2
    rw [ev.symm_apply_apply]
  rw [heq, hnorm]
  rfl

end

open Bundle Topology CategoryTheory Set
section
variable {E F J S : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Fintype J] [Fintype S] {d : S → ℕ}

omit [FiniteDimensional ℝ E] in
/-- On the complement of any finite family of affine zero sets, the two
normalizations of the ACTUAL finite sum of hyperplane lines coincide in
fiber degree. Contractibility, connectivity, transition degree and homology
vanishing are not premises: the finite convex cover supplies the comparison. -/
theorem affineAvoidance_finiteLineEvaluationNormalization_eq
    (l : J → E →L[ℝ] F) (c : J → F)
    (p : ∀ s, C(affineAvoidanceSet l c,projectionSpace (d s) 1))
    (v : ∀ s, affineAvoidanceSet l c → EuclideanSpace ℂ (Fin (d s)))
    (hm : ∀ s a, v s a ∈ projectionLine (p s a))
    (hn : ∀ s a, v s a ≠ 0) (hc : ∀ s, Continuous (v s))
    (w : ∀ s, affineAvoidanceSet l c → EuclideanSpace ℂ (Fin (d s)))
    (hwm : ∀ s a, w s a ∈ projectionLine (p s a))
    (hwn : ∀ s a, w s a ≠ 0) (hwc : ∀ s, Continuous (w s))
    (hv : 2 ≤ Module.finrank ℝ (S → ℂ)) :
    finiteLineEvaluationNormalization p v hm hn hc (Module.finrank ℝ (S → ℂ)) =
      finiteLineEvaluationNormalization p w hwm hwn hwc (Module.finrank ℝ (S → ℂ)) := by
  classical
  let I := J → Fin (Module.finrank ℝ F) × Bool
  let U : I → Set (affineAvoidanceSet l c) := fun s => Subtype.val ⁻¹' affineAvoidanceChart l c s
  have hcover : (⋃ s ∈ (Finset.univ : Finset I), U s) = Set.univ := by
    ext x
    have hx : x.val ∈ ⋃ s : I, affineAvoidanceChart l c s := by
      rw [affineAvoidanceCharts_cover]; exact x.property
    simpa only [U, mem_iUnion, Finset.mem_univ, exists_true_left,
      mem_preimage, mem_univ, iff_true] using hx
  let n := Module.finrank ℝ (S → ℂ) - 1
  have hdim : n+1 = Module.finrank ℝ (S → ℂ) := by dsimp [n]; omega
  have h := finiteLineEvaluationNormalization_eq_of_finite_cover p v hm hn hc w hwm hwn hwc
    Finset.univ U
    (fun s _ => (affineAvoidanceChart_open l c s).preimage continuous_subtype_val) hcover
    (fun s _ hne => convexRestrictedBase_contractible _ _ (affineAvoidanceChart_subset l c s)
      (affineAvoidanceChart_convex l c s) hne) n
    (fun T ht hts q hq => convexCover_product_intersection_below_isZero
      (affineAvoidanceSet l c) Finset.univ (affineAvoidanceChart l c)
      (fun s _ => affineAvoidanceChart_subset l c s)
      (fun s _ => affineAvoidanceChart_convex l c s) T ht hts hv q (by omega))
  rwa [hdim] at h

end

end Kaplansky

end

end OAI
