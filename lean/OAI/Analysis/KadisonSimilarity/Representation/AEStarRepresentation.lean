import OAI.Analysis.KadisonSimilarity.Representation.DenseStarRepresentation

namespace OAI

/-! # A common conull set for fiber representations

Countability of the dense subring lets all algebraic identities and norm
bounds hold on a single conull set. Each of those fibers then has the genuine
complex star representation constructed in `DenseStarRepresentation`.
Exceptional fibers are left out of the existence assertion.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter

variable {A : Type*} [CStarAlgebra A]
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  (K : Ω → Type*) [∀ x, NormedAddCommGroup (K x)]
  [∀ x, InnerProductSpace ℂ (K x)] [∀ x, CompleteSpace (K x)]

/-- Pointwise representatives on a countable dense star subring extend to
complex star representations almost everywhere. Each input identity is
required only almost everywhere for its fixed tuple of arguments. -/
theorem ae_exists_starRepresentation_of_countable_subring
    (S : Subring A) [Countable S] (hdense : Dense (S : Set A))
    (hstarS : ∀ a ∈ S, star a ∈ S) (hIS : algebraMap ℂ A Complex.I ∈ S)
    (f : ∀ _a : S, ∀ x, K x →L[ℂ] K x)
    (hzero : ∀ᵐ x ∂μ, f 0 x = 0)
    (hone : ∀ᵐ x ∂μ, f 1 x = 1)
    (hadd : ∀ a b : S, ∀ᵐ x ∂μ, f (a + b) x = f a x + f b x)
    (hmul : ∀ a b : S, ∀ᵐ x ∂μ, f (a * b) x = f a x * f b x)
    (hnorm : ∀ a : S, ∀ᵐ x ∂μ, ‖f a x‖ ≤ ‖a‖)
    (hstar : ∀ a : S, ∀ᵐ x ∂μ,
      f ⟨star a.val, hstarS a.val a.property⟩ x = star (f a x))
    (hI : ∀ᵐ x ∂μ, f ⟨algebraMap ℂ A Complex.I, hIS⟩ x =
      algebraMap ℂ (K x →L[ℂ] K x) Complex.I) :
    ∀ᵐ x ∂μ, ∃ σ : A →⋆ₐ[ℂ] (K x →L[ℂ] K x), ∀ a : S, σ a = f a x := by
  have hadd_all : ∀ᵐ x ∂μ, ∀ a b : S, f (a + b) x = f a x + f b x :=
    eventually_countable_forall.mpr fun a => eventually_countable_forall.mpr (hadd a)
  have hmul_all : ∀ᵐ x ∂μ, ∀ a b : S, f (a * b) x = f a x * f b x :=
    eventually_countable_forall.mpr fun a => eventually_countable_forall.mpr (hmul a)
  have hnorm_all : ∀ᵐ x ∂μ, ∀ a : S, ‖f a x‖ ≤ ‖a‖ :=
    eventually_countable_forall.mpr hnorm
  have hstar_all : ∀ᵐ x ∂μ, ∀ a : S,
      f ⟨star a.val, hstarS a.val a.property⟩ x = star (f a x) :=
    eventually_countable_forall.mpr hstar
  filter_upwards [hzero, hone, hadd_all, hmul_all, hnorm_all, hstar_all, hI]
    with x hz ho ha hm hn hs hi
  let F : S →+* (K x →L[ℂ] K x) := {
    toFun := fun a => f a x
    map_zero' := hz
    map_one' := ho
    map_add' := ha
    map_mul' := hm }
  exact exists_starRepresentation_of_dense_subring S hdense hstarS hIS F hn hs hi

end KadisonSimilarity

end

end OAI
