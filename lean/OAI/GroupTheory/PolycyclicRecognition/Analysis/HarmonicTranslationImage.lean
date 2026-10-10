import OAI.GroupTheory.PolycyclicRecognition.Analysis.PolynomialHarmonicFiniteDimensional

namespace OAI

/-! # The maximum principle and the harmonic translation image

A nonconstant harmonic function has infinite translation image. This is the
algebraic conclusion needed after constructing a nonconstant Lipschitz
harmonic function; no such existence result is assumed here.
-/
noncomputable section
namespace PolycyclicRecognition
open Finset
variable {G : Type*} [Group G] [DecidableEq G]

theorem cayleyHarmonic_eq_maximum (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (f : G → ℝ) (hf : CayleyHarmonic S f)
    (x : G) (hmax : ∀ y, f y ≤ f x) : ∀ y, f y = f x := by
  have hstep (z : G) (hz : f z = f x) (s : G) (hs : s ∈ S) : f (z * s) = f x := by
    have hnon : ∀ t ∈ S, f (z * t) - f z ≤ 0 := by
      intro t _
      rw [hz]
      exact sub_nonpos.mpr (hmax _)
    have he : f (z * s) - f z = 0 := (sum_eq_zero_iff_of_nonpos hnon).mp (hf z) s hs
    exact (sub_eq_zero.mp he).trans hz
  have hword : ∀ (l : List G) (z : G), f z = f x →
      (∀ s ∈ l, s ∈ S) → f (z * l.prod) = f x := by
    intro l
    induction l with
    | nil => intro z hz _; simpa using hz
    | cons s l ih =>
      intro z hz hl
      have hz' := hstep z hz s (hl s (List.mem_cons_self ..))
      have ht := ih (z * s) hz' (fun t ht => hl t (List.mem_cons_of_mem s ht))
      simpa only [List.prod_cons, mul_assoc] using ht
  intro y
  obtain ⟨n, hn⟩ := wordBall_exhaustive S hS hgen (x⁻¹ * y)
  obtain ⟨l, _, hl, he⟩ := (mem_wordBall_iff S n (x⁻¹ * y)).mp hn
  simpa only [he, mul_inv_cancel_left] using hword l x rfl hl

theorem cayleyHarmonic_finite_range_constant (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (f : G → ℝ) (hf : CayleyHarmonic S f)
    (hfin : (Set.range f).Finite) : ∀ x, f x = f 1 := by
  classical
  obtain ⟨m, hm, hmax⟩ := exists_max_image hfin.toFinset id
    ⟨f 1, hfin.mem_toFinset.mpr ⟨1, rfl⟩⟩
  obtain ⟨z, hz⟩ := hfin.mem_toFinset.mp hm
  have hb : ∀ x, f x ≤ f z := by
    intro x
    rw [hz]
    exact hmax (f x) (hfin.mem_toFinset.mpr ⟨x, rfl⟩)
  have he := cayleyHarmonic_eq_maximum S hS hgen f hf z hb
  exact fun x => (he x).trans (he 1).symm

theorem polynomialHarmonicRepresentation_infinite_range (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set G) = ⊤)
    (d : ℕ) (f : polynomialHarmonicFunctions S d) (x : G) (hx : f.val x ≠ f.val 1) :
    (Set.range (polynomialHarmonicRepresentation S hS hgen d)).Infinite := by
  intro hfin
  let ρ := polynomialHarmonicRepresentation S hS hgen d
  have hf : (Set.range f.val).Finite := by
    apply (hfin.image (fun A => (A f).val 1)).subset
    rintro _ ⟨g, rfl⟩
    refine ⟨ρ g⁻¹, ⟨g⁻¹, rfl⟩, ?_⟩
    simp [ρ, polynomialHarmonicRepresentation, polynomialHarmonicLeftTranslation, cayleyLeftTranslate]
  exact hx (cayleyHarmonic_finite_range_constant S hS hgen f.val f.property.2 hf x)

end PolycyclicRecognition

end

end OAI
