import OAI.Combinatorics.Progressions.Estimates.AllocatedRefinedLongJetComparison
import OAI.Combinatorics.Progressions.Estimates.PrincipalRetainedIntegral
import OAI.Combinatorics.Progressions.Geometry.SpatialChoiceEnvelope

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides
local notation "longWeight" => allocatedLongTupleWeights (α := α) B U basis S
local notation "source" => allocatedLongCoefficientSource B U basis hR hσ S

variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {D N : Type*} [Fintype D] [Fintype N] [DecidableEq N]
variable (c : D → N → ℤ) (index : D → N → PrincipalTupleIndex B (layerSamplerDegree I n))
variable (x : G → IntegerScalarCubeBox α S.value) (root : G → ℤ) (selection : α ↪ G)
variable (hP : (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection).det ≠ 0)
variable (H : D → ℝ) (Q : D → N → ℝ) (hH : ∀ d, 0 < H d) (hQ : ∀ d j, 0 < Q d j)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "scale" => (∏ d, ∏ _i : Unit ⊕ α, H d : ℝ)
local notation "spatial" => allocatedSpatialOutputLaw B U basis S u c index x root H Q hH hQ

omit [∀ j, DecidableEq (O j)] in
theorem allocatedSpatial_integral_comparison {M : ℕ} (hM : 0 < M)
    (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hroot : ∀ j, |root j| ≤ (S.value : ℤ)) (modulus : ℕ) [NeZero modulus] (hm : 0 < modulus)
    (hp : integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection))
    (hsize : ∀ d, (Fintype.card α+1)*modulus ≤ lengths d)
    {ρ ξ mesh ε : ℝ} (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hwidth : ∀ d j, ((|c d j| : ℤ)+(sides (index d j) : ℤ) : ℝ)*Q d j ≤ ξ*H d)
    (hρ : 0 < ρ) (hscale : ∀ d, ρ ≤ H d/S.value) (hscaleQ : ∀ d j, ρ ≤ Q d j)
    (hlarge : smoothSpatialMeshThreshold α G N S.value ≤ ρ) (hmesh : 0 < mesh) (hε : 0 ≤ ε)
    (tv : Finset (D → (Unit ⊕ α) → ℤ))
    (hv : ∀ v ∈ tv, ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ)/H d| ≤ 1)
    (T : (PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
      (fun a => layerSamplerDegree I n a.val) → Option α → ZMod modulus) →
      (D → (Unit ⊕ α) → ℤ) → ℂ)
    (φ : (D → (Unit ⊕ α) → ℤ) → AllocatedLongJetRows B U basis S O → ℂ)
    (hφ : ∀ v ∈ tv, Measurable (φ v)) (hb : ∀ v ∈ tv, ∀ z, ‖φ v z‖ ≤ 1)
    (hcoeff : ∀ (r : PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option α → ZMod modulus)
        (v : D → (Unit ⊕ α) → ℤ), v ∈ tv →
      ‖(∫ a, (allocatedLongResidueWeights (α := α) B U basis S modulus hm r hsize).complexMean
        (fun y => φ v (allocatedLongJetMap B U basis S x u y rows a)) ∂source)-T r v‖ ≤ ε) :
    ‖(∫ a, (longWeight).complexMean
        (fun y => ∑ v ∈ tv, ((spatial y v).toReal : ℂ)*φ v (allocatedLongJetMap B U basis S x u y rows a))
        ∂source) -
      ((longWeight).fiberLaw (principalResidueLabel modulus)).complexMean
        (fun r => ∑ v ∈ tv,
          (allocatedSpatialProxy B U basis S u c index x root selection hP H hH modulus r mesh v /
            (scale : ℂ))*T r v)‖ ≤
      smoothVectorSpatialError D N selection M S.value modulus ρ ξ mesh/scale*tv.card +
        (1+smoothVectorSpatialError D N selection M S.value modulus ρ ξ mesh/scale*tv.card)*ε := by
  let : IsProbabilityMeasure source := allocatedLongCoefficientSource_probability B U basis hR hσ S
  have hscale0 : 0 < scale := Finset.prod_pos (fun d _ => Finset.prod_pos (fun _ _ => hH d))
  have hscaleC : (scale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hscale0)
  have hspatial (y) (_hy : (longWeight).weight y ≠ 0) (v) (hvt : v ∈ tv) :
      ‖((spatial y v).toReal : ℂ)-
        allocatedSpatialProxy B U basis S u c index x root selection hP H hH modulus
          (principalResidueLabel modulus y) mesh v/(scale : ℂ)‖ ≤
        smoothVectorSpatialError D N selection M S.value modulus ρ ξ mesh/scale := by
    have he := allocatedSpatial_site_error B U basis S u c index x root selection hP H Q hH hQ
      hM hx hroot modulus hp hξ0 hξ1 hwidth hρ hscale hscaleQ hlarge hmesh y v (hv v hvt)
    have hid (z : ℝ) (b : ℂ) : (z : ℂ)-b/(scale : ℂ) = ((scale*z : ℝ)-b)/(scale : ℂ) := by
      rw [Complex.ofReal_mul, sub_div, mul_div_cancel_left₀ _ hscaleC]
    rw [hid, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hscale0]
    exact div_le_div_of_nonneg_right he hscale0.le
  exact principalRetained_integral_comparison
    (fun a : {a // ¬grid a} => B a.val) (fun a => layerSamplerDegree I n a.val)
    lengths (fun j => allocatedPrincipalSides_pos B U basis S ⟨j.1.val, j.2⟩)
    modulus hm hsize tv spatial
    (fun r v => allocatedSpatialProxy B U basis S u c index x root selection hP H hH modulus r mesh v /
      (scale : ℂ)) source (fun y => allocatedLongJetMap B U basis S x u y rows)
    (fun y => allocatedLongJetMap_measurable B U basis S x u y rows) T
    (div_nonneg (smoothVectorSpatialError_nonneg D N selection M S.value modulus hρ.le hξ0 hmesh.le)
      hscale0.le) hε hspatial φ hφ hb hcoeff

end Erdos3.VectorPolynomial

end

end OAI
