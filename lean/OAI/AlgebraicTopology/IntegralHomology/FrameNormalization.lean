import OAI.AlgebraicTopology.IntegralHomology.LineNormalization
import OAI.Geometry.ComplexBundle.Tensor

namespace OAI

noncomputable section

namespace Kaplansky

/-! Integral normalization of finite-line frames over affine-avoidance covers. -/

section
open Bundle Topology CategoryTheory Set
variable {A S : Type} [TopologicalSpace A] [Fintype S] {I : S → Type}
  (C : ∀ s, VectorBundleCore ℂ A ℂ (I s))
  (v : ∀ s a, (C s).Fiber a) (hn : ∀ s a, v s a ≠ 0)
  (hc : ∀ s, Continuous (fun a => TotalSpace.mk' ℂ a (v s a)))

/-- Relative coordinates of any finite sum with genuine continuous line frames. -/
def finiteLineFrameRelativeIso (n : ℕ) :=
  relativeHomologyHomeomorphIso (finiteLineFrameHomeomorph C v hn hc)
    {z : TotalSpace (EuclideanSpace ℂ S) (finiteLineSumCore C).Fiber | z.2 ≠ 0}
    {z : A × (S → ℂ) | z.2 ≠ 0}
    (fun z => (not_congr (finiteLineFrameHomeomorph_zero_iff C v hn hc z)).symm) n

def finiteLineFrameNormalization (n : ℕ) :=
  (finiteLineFrameRelativeIso C v hn hc n).hom ≫
    productPairProjection (B := A) ({0}ᶜ : Set (S → ℂ)) n

variable (w : ∀ s a, (C s).Fiber a) (hwn : ∀ s a, w s a ≠ 0)
  (hwc : ∀ s, Continuous (fun a => TotalSpace.mk' ℂ a (w s a)))

theorem finiteLineFrame_transition (a : A) (z : S → ℂ) :
    finiteLineFrameEquiv C w hwn a ((finiteLineFrameEquiv C v hn a).symm z) =
      complexDiagonalMap (fun s => complexLineCoordinateUnit
        (lineFrameEquiv (C s) (v s) (hn s) a) (lineFrameEquiv (C s) (w s) (hwn s) a)) z := by
  funext s
  exact complexLineCoordinate_change
    (lineFrameEquiv (C s) (v s) (hn s) a) (lineFrameEquiv (C s) (w s) (hwn s) a) (z s)

/-- Normalization of the actual finite sum of actual line cores is independent
of the chosen continuous nonvanishing line frames on a finite contractible
cover with the stated lower intersection vanishing. No global contractibility
or connectedness hypothesis is required. -/
theorem finiteLineFrameNormalization_eq_of_finite_cover
    {J : Type} (T : Finset J) (U : J → Set A)
    (hopen : ∀ i ∈ T, IsOpen (U i)) (hcover : (⋃ i ∈ T, U i) = Set.univ)
    (hchart : ∀ i ∈ T, (U i).Nonempty → ContractibleSpace (U i))
    (n : ℕ)
    (hinter : ∀ I : Finset J, I.Nonempty → I ⊆ T → ∀ q < n+1,
      Limits.IsZero (relativeSingularHomology
        (subspaceInclusion {z : (⋂ i ∈ I, U i) × (S → ℂ) | z.2 ≠ 0}) q)) :
    finiteLineFrameNormalization C v hn hc (n+1) =
      finiteLineFrameNormalization C w hwn hwc (n+1) := by
  let ev := finiteLineFrameHomeomorph C v hn hc
  let ew := finiteLineFrameHomeomorph C w hwn hwc
  let f : C(A × (S → ℂ),(S → ℂ)) :=
    ⟨fun z => (ew (ev.symm z)).2, continuous_snd.comp (ew.continuous.comp ev.symm.continuous)⟩
  have hf : ∀ z : A × (S → ℂ), z.2 ≠ 0 → f z ≠ 0 := by
    intro z hz he
    have hw : (ev.symm z).2 = 0 :=
      (finiteLineFrameHomeomorph_zero_iff C w hwn hwc _).mp he
    have hv := (finiteLineFrameHomeomorph_zero_iff C v hn hc (ev.symm z)).mpr hw
    change (ev (ev.symm z)).2 = 0 at hv
    rw [ev.apply_symm_apply] at hv
    exact hz hv
  let c : A → S → ℂˣ := fun a s => complexLineCoordinateUnit
    (lineFrameEquiv (C s) (v s) (hn s) a)
    (lineFrameEquiv (C s) (w s) (hwn s) a)
  have he : ∀ a z, f (a,z) = complexDiagonalMap (c a) z :=
    finiteLineFrame_transition C v hn w hwn
  have hnorm := productPairCoordinateMap_eq_projection_of_finite_cover
    T U hopen hcover hchart n hinter f hf c he
  have heq : finiteLineFrameNormalization C w hwn hwc (n+1) =
      (finiteLineFrameRelativeIso C v hn hc (n+1)).hom ≫
        productPairCoordinateMap f hf (n+1) := by
    unfold finiteLineFrameNormalization finiteLineFrameRelativeIso
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
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Fintype J] [Fintype S] {I : S → Type}

/-- On the complement of any finite family of affine zero sets, the two
normalizations of the ACTUAL finite sum of line cores coincide in
fiber degree. Contractibility, connectivity, transition degree and homology
vanishing are not premises: the finite convex cover supplies the comparison. -/
theorem affineAvoidance_finiteLineFrameNormalization_eq
    (l : J → E →L[ℝ] F) (c : J → F)
    (C : ∀ s, VectorBundleCore ℂ (affineAvoidanceSet l c) ℂ (I s))
    (v : ∀ s a, (C s).Fiber a) (hn : ∀ s a, v s a ≠ 0)
    (hc : ∀ s, Continuous (fun a => TotalSpace.mk' ℂ a (v s a)))
    (w : ∀ s a, (C s).Fiber a) (hwn : ∀ s a, w s a ≠ 0)
    (hwc : ∀ s, Continuous (fun a => TotalSpace.mk' ℂ a (w s a)))
    (hv : 2 ≤ Module.finrank ℝ (S → ℂ)) :
    finiteLineFrameNormalization C v hn hc (Module.finrank ℝ (S → ℂ)) =
      finiteLineFrameNormalization C w hwn hwc (Module.finrank ℝ (S → ℂ)) := by
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
  have h := finiteLineFrameNormalization_eq_of_finite_cover C v hn hc w hwn hwc
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
