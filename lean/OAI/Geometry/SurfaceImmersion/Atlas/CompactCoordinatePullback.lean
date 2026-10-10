import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateTensorPullback
import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs

namespace OAI

/-! Fixed smooth representatives of the coordinate transitions on each
compact overlap, with exact local inverses and polynomial tensor transport. -/
noncomputable section
open Set
open scoped ContDiff Topology

namespace ClosedSurfaceR4.JetPolynomial

/-- Both coordinate maps can be extended off a compact overlap. Their
actual inverse identities continue to hold as germs on a smaller open set. -/
theorem compact_coordinate_representatives
    (e : OpenPartialHomeomorph Base Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {K : Set Base} (hK : IsCompact K) (hKe : K ⊆ e.source) :
    ∃ U : Set Base, IsOpen U ∧ K ⊆ U ∧ U ⊆ e.source ∧
      ∃ T S : Base → Base, ContDiff ℝ ∞ T ∧ ContDiff ℝ ∞ S ∧ EqOn T e U ∧
        (∀ x ∈ U, S (T x) = x) ∧
        (∀ x ∈ U, (T ∘ S) =ᶠ[𝓝 (T x)] id) := by
  obtain ⟨W,hW,hKW,hWe,T,hT,hTe⟩ :=
    CollarVelocity.compact_smooth_extension hK e.open_source hKe he
  have himage : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hKe)
  obtain ⟨V,hV,hKV,hVe,S,hS,hSe⟩ :=
    CollarVelocity.compact_smooth_extension himage e.open_target
      (by rintro y ⟨x,hx,rfl⟩; exact e.map_source (hKe hx)) hi
  let U := W ∩ T ⁻¹' V
  have hU : IsOpen U := hW.inter (hV.preimage hT.continuous)
  have hUK : K ⊆ U := by
    intro x hx
    refine ⟨hKW hx,?_⟩
    change T x ∈ V
    rw [hTe (hKW hx)]
    exact hKV (mem_image_of_mem e hx)
  have hST : ∀ x ∈ U, S (T x) = x := by
    intro x hx
    rw [hSe hx.2,hTe hx.1,e.left_inv (hWe hx.1)]
  refine ⟨U,hU,hUK,fun _ hx => hWe hx.1,T,S,hT,hS,
    fun _ hx => hTe hx.1,hST,?_⟩
  intro x hx
  have hn : T x ∈ S ⁻¹' W := by
    change S (T x) ∈ W
    rw [hST x hx]
    exact hx.1
  filter_upwards [hV.mem_nhds hx.2,(hW.preimage hS.continuous).mem_nhds hn] with y hy hsy
  change T (S y) = y
  rw [hTe hsy,hSe hy,e.right_inv (hVe hy)]

/-- Tensor polynomials have a fixed smooth expression on every compact
coordinate overlap; the expression is chosen before the map being evaluated. -/
theorem compact_tensor_polynomial_pullback {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k r, (P k r).SmoothCoeffs univ)
    (e : OpenPartialHomeomorph Base Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {K : Set Base} (hK : IsCompact K) (hKe : K ⊆ e.source) :
    ∃ U : Set Base, IsOpen U ∧ K ⊆ U ∧ U ⊆ e.source ∧
        ∃ P' : Fin 3 → Fin n → Expression, (∀ k r, (P' k r).SmoothCoeffs univ) ∧
          ∀ (G H : Base → Space), ContDiff ℝ ∞ G → ContDiff ℝ ∞ H →
            (∀ x ∈ U, H x = G (e x)) → ∀ (ε t : ℝ) (x : Base), x ∈ U →
              Perturbation.coordinatePolynomialValue P' ε H t (planeCoordinateIsometry x) =
                tensorCoordinatePullbackValue e x
                  (Perturbation.coordinatePolynomialValue P ε G t
                    (planeCoordinateIsometry (e x))) := by
  obtain ⟨U,hU,hKU,hUe,T,S,hT,hS,hTe,hST,hTS⟩ :=
    compact_coordinate_representatives e he hi hK hKe
  refine ⟨U,hU,hKU,hUe,
    Perturbation.tensorPolynomialCoordinatePullback P T S,
    Perturbation.tensorPolynomialCoordinatePullback_smooth hP hT hS,?_⟩
  intro G H hG hH hrel ε t x hx
  have hr : ∀ y ∈ U, H y = G (T y) := by
    intro y hy
    rw [hTe hy]
    exact hrel y hy
  have heq : T =ᶠ[𝓝 x] e := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hTe hy
  have hd : tensorCoordinatePullbackValue T x = tensorCoordinatePullbackValue e x := by
    unfold tensorCoordinatePullbackValue tensorCoordinateDerivative
    rw [heq.fderiv_eq]
  simpa only [hTe hx,hd] using
    Perturbation.tensorPolynomialCoordinatePullback_eval P hT hS hU hST hTS hG hH hr ε t hx

end ClosedSurfaceR4.JetPolynomial

end

end OAI
