import OAI.Analysis.KadisonSimilarity.Representation.AEStarRepresentation
import OAI.Analysis.KadisonSimilarity.Representation.CountableDenseStarSubring
import Mathlib.Topology.Sequences

namespace OAI

/-! # Agreement of the reconstructed fiber representations

For each fixed algebra element, the genuine representations reconstructed
from a countable dense subring agree almost everywhere with the original
operator representatives. Only countably many approximants are used for
that element; no uncountable intersection of conull sets is taken.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology CStarAlgebra

variable {A : Type*} [CStarAlgebra A]
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  (K : Ω → Type*) [∀ x, NormedAddCommGroup (K x)]
  [∀ x, InnerProductSpace ℂ (K x)] [∀ x, CompleteSpace (K x)]

/-- Every extension of the dense-subring representatives has the correct
value at a fixed `a`, outside a null set that may depend on `a`. -/
theorem ae_starRepresentation_agrees_at
    (S : Subring A) (hdense : Dense (S : Set A))
    (f : ∀ _a : A, ∀ x, K x →L[ℂ] K x)
    (hsub : ∀ a b : A, ∀ᵐ x ∂μ, f (a - b) x = f a x - f b x)
    (hnorm : ∀ a : A, ∀ᵐ x ∂μ, ‖f a x‖ ≤ ‖a‖) (a : A) :
    ∀ᵐ x ∂μ, ∀ σ : A →⋆ₐ[ℂ] (K x →L[ℂ] K x),
      (∀ b : S, σ b = f b x) → σ a = f a x := by
  obtain ⟨b, hb, hlim⟩ := mem_closure_iff_seq_limit.mp (hdense a)
  have hsub_all : ∀ᵐ x ∂μ, ∀ n : ℕ, f (a - b n) x = f a x - f (b n) x :=
    eventually_countable_forall.mpr (fun n => hsub a (b n))
  have hnorm_all : ∀ᵐ x ∂μ, ∀ n : ℕ, ‖f (a - b n) x‖ ≤ ‖a - b n‖ :=
    eventually_countable_forall.mpr (fun n => hnorm (a - b n))
  filter_upwards [hsub_all, hnorm_all] with x hsubx hnormx
  intro σ hσ
  have hbound (n : ℕ) : ‖σ a - f a x‖ ≤ ‖a - b n‖ + ‖a - b n‖ := by
    calc
      ‖σ a - f a x‖ ≤ ‖σ a - σ (b n)‖ + ‖σ (b n) - f a x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖a - b n‖ + ‖a - b n‖ := add_le_add
        (by rw [← map_sub]; exact NonUnitalStarAlgHom.norm_apply_le σ _)
        (by
          rw [hσ ⟨b n, hb n⟩, norm_sub_rev, ← hsubx n]
          exact hnormx n)
  have hzero : Tendsto (fun n => ‖a - b n‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a)).sub hlim).norm
  have hle : ‖σ a - f a x‖ ≤ 0 := by
    simpa only [zero_add] using ge_of_tendsto' (hzero.add hzero) hbound
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hle (norm_nonneg _)))

/-- Countably many fiber relations suffice for genuine representations,
and their values agree almost everywhere with every fixed original section.
The statement leaves exceptional fibers unspecified. -/
theorem exists_dense_subring_ae_fiber_representations
    [TopologicalSpace.SeparableSpace A]
    (f : ∀ _a : A, ∀ x, K x →L[ℂ] K x)
    (hzero : ∀ᵐ x ∂μ, f 0 x = 0)
    (hone : ∀ᵐ x ∂μ, f 1 x = 1)
    (hadd : ∀ a b : A, ∀ᵐ x ∂μ, f (a + b) x = f a x + f b x)
    (hmul : ∀ a b : A, ∀ᵐ x ∂μ, f (a * b) x = f a x * f b x)
    (hnorm : ∀ a : A, ∀ᵐ x ∂μ, ‖f a x‖ ≤ ‖a‖)
    (hstar : ∀ a : A, ∀ᵐ x ∂μ, f (star a) x = star (f a x))
    (hI : ∀ᵐ x ∂μ, f (algebraMap ℂ A Complex.I) x =
      algebraMap ℂ (K x →L[ℂ] K x) Complex.I) :
    ∃ S : Subring A, Countable S ∧ Dense (S : Set A) ∧
      (∀ᵐ x ∂μ, ∃ σ : A →⋆ₐ[ℂ] (K x →L[ℂ] K x), ∀ b : S, σ b = f b x) ∧
      (∀ a : A, ∀ᵐ x ∂μ, ∀ σ : A →⋆ₐ[ℂ] (K x →L[ℂ] K x),
        (∀ b : S, σ b = f b x) → σ a = f a x) := by
  obtain ⟨S, hcount, hdense, hstarS, hIS⟩ := exists_countable_dense_star_subring A
  let : Countable S := hcount.to_subtype
  refine ⟨S, inferInstance, hdense, ?_, ?_⟩
  · exact ae_exists_starRepresentation_of_countable_subring μ K S hdense hstarS hIS
      (fun b x => f b x) hzero hone (fun a b => hadd a b) (fun a b => hmul a b)
      (fun a => hnorm a) (fun a => hstar a) hI
  · intro a
    apply ae_starRepresentation_agrees_at μ K S hdense f _ hnorm a
    intro b c
    filter_upwards [hadd (b - c) c] with x hx
    apply eq_sub_iff_add_eq.mpr
    simpa only [sub_add_cancel] using hx.symm

end KadisonSimilarity

end

end OAI
