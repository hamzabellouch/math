import OAI.Analysis.Nuclearity.PositiveFunctionalKernel

namespace OAI

/-! Positive functionals descend through surjective star homomorphisms
when they vanish on the kernel. Positivity is proved by lifting a square root. -/

noncomputable section
open scoped ComplexOrder

namespace WeakPureInfiniteness

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

theorem positiveFunctional_descends (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (f : A →ₚ[ℂ] ℂ) (hk : ∀ a, q a = 0 → f a = 0) :
    ∃ g : B →ₚ[ℂ] ℂ, ∀ a, g (q a) = f a := by
  classical
  have hcompat (a b : A) (h : q a = q b) : f a = f b := by
    have hzero : q (a - b) = 0 := by rw [map_sub, h, sub_self]
    have hf := hk (a - b) hzero
    rwa [map_sub, sub_eq_zero] at hf
  let s : B → A := fun b => Classical.choose (hq b)
  have hs (b : B) : q (s b) = b := Classical.choose_spec (hq b)
  let L : B →ₗ[ℂ] ℂ :=
    { toFun := fun b => f (s b)
      map_add' := fun x y => by
        rw [← map_add]
        exact hcompat _ _ (by rw [map_add, hs, hs, hs])
      map_smul' := fun c x => by
        rw [← map_smul]
        exact hcompat _ _ (by rw [map_smul, hs, hs]; rfl) }
  have he (a : A) : L (q a) = f a := hcompat _ _ (hs (q a))
  have hpos (b : B) (hb : 0 ≤ b) : 0 ≤ L b := by
    obtain ⟨a, ha⟩ := hq (CFC.sqrt b)
    have hqa : q (star a * a) = b := by
      rw [map_mul, map_star, ha, (CFC.sqrt_nonneg b).isSelfAdjoint.star_eq,
        CFC.sqrt_mul_sqrt_self b hb]
    rw [← hqa, he]
    exact f.map_nonneg (star_mul_self_nonneg a)
  exact ⟨PositiveLinearMap.mk₀ L hpos, he⟩

theorem state_descends (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1) (hk : ∀ a, q a = 0 → f a = 0) :
    ∃ g : B →ₚ[ℂ] ℂ, g 1 = 1 ∧ ∀ a, g (q a) = f a := by
  obtain ⟨g, hg⟩ := positiveFunctional_descends q hq f hk
  exact ⟨g, by simpa only [map_one, hf] using hg 1, hg⟩

/-- Each positive summand of a functional pulled back from a quotient also
passes through that quotient. -/
theorem positive_summands_descend (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (f : B →ₚ[ℂ] ℂ) (g h : A →ₚ[ℂ] ℂ)
    (hsum : ∀ a, g a + h a = f (q a)) :
    ∃ (g' h' : B →ₚ[ℂ] ℂ),
      (∀ a, g' (q a) = g a) ∧ (∀ a, h' (q a) = h a) ∧
      ∀ b, g' b + h' b = f b := by
  have hzero (a : A) (ha : q a = 0) : g (star a * a) + h (star a * a) = 0 := by
    rw [hsum, map_mul, map_star, ha, star_zero, zero_mul, map_zero]
  have hg (a : A) (ha : q a = 0) : g a = 0 := by
    apply positiveFunctional_eq_zero_of_square
    exact (add_eq_zero_iff_of_nonneg (g.map_nonneg (star_mul_self_nonneg a))
      (h.map_nonneg (star_mul_self_nonneg a))).mp (hzero a ha) |>.1
  have hh (a : A) (ha : q a = 0) : h a = 0 := by
    apply positiveFunctional_eq_zero_of_square
    exact (add_eq_zero_iff_of_nonneg (g.map_nonneg (star_mul_self_nonneg a))
      (h.map_nonneg (star_mul_self_nonneg a))).mp (hzero a ha) |>.2
  obtain ⟨g', hg'⟩ := positiveFunctional_descends q hq g hg
  obtain ⟨h', hh'⟩ := positiveFunctional_descends q hq h hh
  refine ⟨g', h', hg', hh', ?_⟩
  intro b
  obtain ⟨a, rfl⟩ := hq b
  rw [hg', hh', hsum]

end WeakPureInfiniteness

end

end OAI
