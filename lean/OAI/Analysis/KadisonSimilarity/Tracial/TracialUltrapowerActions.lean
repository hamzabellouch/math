import OAI.Analysis.KadisonSimilarity.Tracial.TracialUltrapowerGNS

namespace OAI

/-! Bounded left-multiplier sequences reduce the tracial GNS subspace of
the Hilbert ultrapower. The compressed operator therefore inherits every
eventual coordinate commutator estimate. -/

noncomputable section
namespace KadisonSimilarity

open NuclearUltrapower HochschildUltrapower
open scoped ENNReal Topology BoundedContinuousFunction ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a * b) = τ (b * a))

/-- The actual uniformly bounded family of left multipliers. -/
def gnsLeftSequence (x : ℕ →ᵇ A) : lp (fun _ : ℕ => τ.GNS →L[ℂ] τ.GNS) ∞ :=
  ⟨fun i => τ.gnsStarAlgHom (x i), memℓp_infty ⟨‖x‖, by
    rintro _ ⟨i, rfl⟩
    exact (NonUnitalStarAlgHom.norm_apply_le τ.gnsStarAlgHom (x i)).trans
      (x.norm_coe_le_norm i)⟩⟩

@[simp] theorem gnsLeftSequence_apply (x : ℕ →ᵇ A) (i : ℕ) :
    gnsLeftSequence τ x i = τ.gnsStarAlgHom (x i) := rfl

@[simp] theorem gnsLeftSequence_star (x : ℕ →ᵇ A) :
    gnsLeftSequence τ (star x) = star (gnsLeftSequence τ x) := by
  apply Subtype.ext
  funext i
  exact map_star τ.gnsStarAlgHom (x i)

theorem gnsLeftSequence_vector (x y : ℕ →ᵇ A) :
    HilbertUltraproduct.map ω (gnsLeftSequence τ x)
      (algebraSequenceVectorLinear τ h1 ω y) =
      algebraSequenceVectorLinear τ h1 ω (x * y) := by
  change HilbertUltraproduct.map ω (gnsLeftSequence τ x)
    (algebraSequenceVector τ h1 ω y : HilbertUltraproduct (fun _ : ℕ => τ.GNS) ω) = _
  rw [HilbertUltraproduct.map_coe]
  congr 1
  apply Subtype.ext
  funext i
  change τ.gnsStarAlgHom (x i) (τ.toPreGNS (y i) : τ.GNS) =
    (τ.toPreGNS (x i * y i) : τ.GNS)
  simp [PositiveLinearMap.gnsStarAlgHom]

/-- The inclusion intertwines the quotient's left action and the coordinate action. -/
theorem tracialUltrapowerGNSInclusion_intertwines (x : ℕ →ᵇ A) :
    (HilbertUltraproduct.map ω (gnsLeftSequence τ x)).comp
      (tracialUltrapowerGNSInclusion τ h1 ω htr).toContinuousLinearMap =
    (tracialUltrapowerGNSInclusion τ h1 ω htr).toContinuousLinearMap.comp
      ((quotientTrace τ h1 ω htr).gnsStarAlgHom (quotientHom τ h1 ω htr x)) := by
  ext v
  induction v using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih v =>
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective
      ((quotientTrace τ h1 ω htr).ofPreGNS v)
    have hv : v = (quotientTrace τ h1 ω htr).toPreGNS
        (quotientHom τ h1 ω htr y) := by
      apply (quotientTrace τ h1 ω htr).ofPreGNS.injective
      exact hy.symm
    rw [hv]
    simpa [PositiveLinearMap.gnsStarAlgHom, ← map_mul] using
      gnsLeftSequence_vector τ h1 ω x y

/-- Compression of the constant Hilbert-ultrapower operator to the tracial
quotient's GNS space. No invariance of the original operator is needed. -/
def tracialUltrapowerCompression (T : τ.GNS →L[ℂ] τ.GNS) :
    (quotientTrace τ h1 ω htr).GNS →L[ℂ] (quotientTrace τ h1 ω htr).GNS :=
  (tracialUltrapowerGNSInclusion τ h1 ω htr).toContinuousLinearMap.adjoint.comp
    ((HilbertUltraproduct.map ω (boundedConstant T)).comp
      (tracialUltrapowerGNSInclusion τ h1 ω htr).toContinuousLinearMap)

/-- Eventual coordinate bounds survive the two constructions exactly. -/
theorem norm_tracialUltrapowerCompression_commutator_le
    (T : τ.GNS →L[ℂ] τ.GNS) (x : ℕ →ᵇ A) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ᶠ i in (ω : Filter ℕ), ‖commutator T (τ.gnsStarAlgHom (x i))‖ ≤ c) :
    ‖commutator (tracialUltrapowerCompression τ h1 ω htr T)
      ((quotientTrace τ h1 ω htr).gnsStarAlgHom (quotientHom τ h1 ω htr x))‖ ≤ c := by
  apply norm_reducing_compression_commutator_le
    (tracialUltrapowerGNSInclusion τ h1 ω htr)
    (HilbertUltraproduct.map ω (boundedConstant T))
    (HilbertUltraproduct.map ω (gnsLeftSequence τ x))
  · exact tracialUltrapowerGNSInclusion_intertwines τ h1 ω htr x
  · simpa only [← ContinuousLinearMap.star_eq_adjoint, gnsLeftSequence_star,
      HilbertUltraproduct.map_star, map_star] using
      tracialUltrapowerGNSInclusion_intertwines τ h1 ω htr (star x)
  · exact norm_hilbertUltraproduct_commutator_le ω _ _ hc hbound

end KadisonSimilarity

end

end OAI
