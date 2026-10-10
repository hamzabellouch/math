import OAI.Algebra.DepthFive.FourPathLocal

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335
namespace LayeredFourPath

/-- Signed occupations, retaining the layer coordinate explicitly. -/
def signedOccupation {T σ : Type*} (M : T → σ → ℕ) : T → σ → ℤ :=
  fun t x => M t x

/-- Every path chooses exactly one coordinate in every layer. -/
def signedShift {T σ : Type*} [DecidableEq σ]
    (side : T → Bool) (p : T → σ) : T → σ → ℤ :=
  fun t x => (if side t then -1 else 1) * (Finsupp.single (p t) (1 : ℤ)) x

/-- The Fock coefficient of a layered path. -/
def amplitude {T σ : Type*} [Fintype T]
    (side : T → Bool) (M : T → σ → ℕ) (p : T → σ) : ℝ :=
  ∏ t, LocalMoments.coefficient (side t) (M t (p t))

/-- Compatibility of global signed shifts gives the local pairing identity at every layer. -/
theorem coordinate_matching_of_signedShift {T σ : Type*} [DecidableEq σ]
    (side : T → Bool) (p q r s : T → σ)
    (h : signedShift side p - signedShift side q =
      signedShift side r - signedShift side s) (t : T) :
    Finsupp.single (p t) (1 : ℤ) - Finsupp.single (q t) 1 =
      Finsupp.single (r t) 1 - Finsupp.single (s t) 1 := by
  ext x
  have hx := congrArg (fun f : T → σ → ℤ => f t x) h
  change (Finsupp.single (p t) (1 : ℤ)) x - (Finsupp.single (q t) 1) x =
    (Finsupp.single (r t) 1) x - (Finsupp.single (s t) 1) x
  cases ht : side t <;> simp [signedShift, ht] at hx <;> omega

/-- An actual shifted source automatically satisfies the local occupation relation. -/
theorem local_shift_of_signedOccupation {T σ : Type*} [DecidableEq σ]
    (side : T → Bool) (M M' : T → σ → ℕ) (p q : T → σ)
    (h : signedOccupation M' =
      signedOccupation M + signedShift side p - signedShift side q) (t : T) :
    LocalMoments.ShiftRelation (side t) (M t) (M' t) (p t) (q t) := by
  intro x
  have hx := congrArg (fun f : T → σ → ℤ => f t x) h
  change (M' t x : ℤ) = (M t x : ℤ) +
    (if side t then -1 else 1) * (Finsupp.single (p t) (1 : ℤ)) x -
    (if side t then -1 else 1) * (Finsupp.single (q t) (1 : ℤ)) x at hx
  rw [Finsupp.sub_apply]
  rw [hx]
  ring

/-- The entire valid four-path coefficient is the product of the local occupation table. -/
theorem amplitude_four_eq_local_product {T σ : Type*} [Fintype T] [DecidableEq σ]
    (side : T → Bool) (M M' : T → σ → ℕ) (p q r s : T → σ)
    (hmatch : signedShift side p - signedShift side q =
      signedShift side r - signedShift side s)
    (hshift : signedOccupation M' =
      signedOccupation M + signedShift side p - signedShift side q) :
    amplitude side M p * amplitude side M' q * amplitude side M r * amplitude side M' s =
      ∏ t, LocalMoments.localPolynomial (side t) (M t) (p t) (q t) (r t) := by
  exact LocalMoments.four_path_products_eq_localPolynomial_product Finset.univ
    side M M' p q r s
    (fun t _ => coordinate_matching_of_signedShift side p q r s hmatch t)
    (fun t _ => local_shift_of_signedOccupation side M M' p q hshift t)

/-- Lift the valid-source identity to a zero extension. Missing shifted source occupations
contribute zero, so an upper estimate needs no source-validity-closure hypothesis. -/
theorem zeroExtended_amplitude_four_le_local_product
    {I T σ : Type*} [Fintype T] [DecidableEq σ]
    (side : T → Bool) (M : I → T → σ → ℕ)
    (hinj : Function.Injective (fun i => signedOccupation (M i)))
    (i : I) (p q r s : T → σ)
    (hmatch : signedShift side p - signedShift side q =
      signedShift side r - signedShift side s) :
    amplitude side (M i) p *
        Function.extend (fun k => signedOccupation (M k))
          (fun k => amplitude side (M k) q) (fun _ => 0)
          (signedOccupation (M i) + signedShift side p - signedShift side q) *
      amplitude side (M i) r *
        Function.extend (fun k => signedOccupation (M k))
          (fun k => amplitude side (M k) s) (fun _ => 0)
          (signedOccupation (M i) + signedShift side p - signedShift side q) ≤
      ∏ t, LocalMoments.localPolynomial (side t) (M i t) (p t) (q t) (r t) := by
  classical
  let x := signedOccupation (M i) + signedShift side p - signedShift side q
  by_cases hx : ∃ k, signedOccupation (M k) = x
  · obtain ⟨k, hk⟩ := hx
    change amplitude side (M i) p *
        Function.extend (fun k => signedOccupation (M k))
          (fun k => amplitude side (M k) q) (fun _ => 0) x *
      amplitude side (M i) r *
        Function.extend (fun k => signedOccupation (M k))
          (fun k => amplitude side (M k) s) (fun _ => 0) x ≤ _
    rw [← hk, hinj.extend_apply, hinj.extend_apply]
    exact (amplitude_four_eq_local_product side (M i) (M k) p q r s hmatch hk).le
  · have hz := Function.extend_apply' (f := fun k => signedOccupation (M k))
      (fun k => amplitude side (M k) q) (fun _ => (0 : ℝ)) x hx
    change amplitude side (M i) p *
        Function.extend (fun k => signedOccupation (M k))
          (fun k => amplitude side (M k) q) (fun _ => 0) x *
      amplitude side (M i) r *
        Function.extend (fun k => signedOccupation (M k))
          (fun k => amplitude side (M k) s) (fun _ => 0) x ≤ _
    rw [hz]
    simp only [mul_zero, zero_mul]
    exact Finset.prod_nonneg (fun t _ => LocalMoments.localPolynomial_nonneg _ _ _ _ _)

end LayeredFourPath
end Problem335

end

end OAI
