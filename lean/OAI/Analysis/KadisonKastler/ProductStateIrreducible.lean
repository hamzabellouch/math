import OAI.Analysis.KadisonKastler.ProductStateCentralizer
import OAI.Analysis.KadisonKastler.BoundaryFiniteIsomorphism

namespace OAI

/-! # Local independent swaps force scalar relative commutant -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace LocalProductSwaps

variable {D : VonNeumannAlgebra H} {Ω : H} (L : LocalProductSwaps D Ω)

/-- Factorization of the vector state against every local observable. -/
theorem local_factorization (hΩ : ‖Ω‖ = 1) (x : H →L[ℂ] H) (hx : x ∈ D)
    (hcomm : ∀ u : unitary (H →L[ℂ] H), (u : H →L[ℂ] H) ∈ D →
      ProductStateCentralizes D Ω u → (u : H →L[ℂ] H) * x = x * u)
    (k : ℕ) (a : L.localAlgebra k) :
    productVectorState Ω ((a : H →L[ℂ] H) * x) =
      productVectorState Ω a * productVectorState Ω x := by
  apply eq_of_sub_eq_zero
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  simp only [zero_add]
  let δ := ε / (2 * ‖(a : H →L[ℂ] H)‖ + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨_, ⟨p, rfl⟩, hp⟩ := Metric.mem_closure_iff.mp (L.dense (x Ω)) δ hδ
  have herr : ‖(x - (p.2 : H →L[ℂ] H)) Ω‖ < δ := by
    simpa only [dist_eq_norm, sub_apply, norm_sub_rev] using hp
  obtain ⟨u, hu, hc, hi⟩ := L.independent_swap k a p.1
  let b : H →L[ℂ] H := p.2
  let c : H →L[ℂ] H := unitaryConj u a
  have hs : productVectorState Ω (c * x) = productVectorState Ω (a * x) :=
    productVectorState_swap D Ω u hu hc a x (L.local_le k a.property) hx (hcomm u hu hc)
  have hi' : productVectorState Ω (c * b) =
      productVectorState Ω a * productVectorState Ω b := hi p.2
  have he : productVectorState Ω (a * x) -
      productVectorState Ω a * productVectorState Ω x =
      (productVectorState Ω (c * x) - productVectorState Ω (c * b)) +
        productVectorState Ω a * (productVectorState Ω b - productVectorState Ω x) := by
    rw [hs, hi']
    ring
  have hv : ‖productVectorState Ω b - productVectorState Ω x‖ ≤ ‖(x - b) Ω‖ := by
    calc
      _ = ‖inner ℂ Ω ((b - x) Ω)‖ := by
        simp only [productVectorState, sub_apply, inner_sub_right]
      _ ≤ ‖Ω‖ * ‖(b - x) Ω‖ := norm_inner_le_norm _ _
      _ = ‖(x - b) Ω‖ := by rw [hΩ, one_mul, sub_apply, norm_sub_rev, ← sub_apply]
  apply le_of_lt
  calc
    _ = ‖(productVectorState Ω (c * x) - productVectorState Ω (c * b)) +
        productVectorState Ω a * (productVectorState Ω b - productVectorState Ω x)‖ :=
      congrArg norm he
    _ ≤ ‖productVectorState Ω (c * x) - productVectorState Ω (c * b)‖ +
        ‖productVectorState Ω a * (productVectorState Ω b - productVectorState Ω x)‖ :=
      norm_add_le _ _
    _ ≤ ‖c‖ * ‖(x - b) Ω‖ + ‖(a : H →L[ℂ] H)‖ * ‖(x - b) Ω‖ := by
      apply add_le_add (productVectorState_mul_error Ω hΩ c x b)
      rw [norm_mul]
      exact mul_le_mul (norm_productVectorState_le Ω hΩ a) hv (norm_nonneg _) (norm_nonneg _)
    _ = 2 * ‖(a : H →L[ℂ] H)‖ * ‖(x - b) Ω‖ := by
      dsimp [c]
      rw [norm_unitaryConj]
      ring
    _ ≤ (2 * ‖(a : H →L[ℂ] H)‖ + 1) * ‖(x - b) Ω‖ := by
      nlinarith [norm_nonneg ((x - b) Ω)]
    _ < (2 * ‖(a : H →L[ℂ] H)‖ + 1) * δ :=
      mul_lt_mul_of_pos_left herr (by positivity)
    _ = ε := mul_div_cancel₀ _ (by positivity)

include L in
/-- The relative commutant of the full vector-state centralizer is scalar.
The argument uses only finite-site independence, dense local vectors, and
separation by the product vector. -/
theorem scalar_of_commutes (hΩ : ‖Ω‖ = 1)
    (hsep : Function.Injective (algebraVectorMap D Ω))
    (x : H →L[ℂ] H) (hx : x ∈ D)
    (hcomm : ∀ u : unitary (H →L[ℂ] H), (u : H →L[ℂ] H) ∈ D →
      ProductStateCentralizes D Ω u → (u : H →L[ℂ] H) * x = x * u) :
    x = productVectorState Ω x • (1 : H →L[ℂ] H) := by
  have hv : x Ω = productVectorState Ω x • Ω := by
    apply DenseRange.eq_of_inner_right ℂ L.dense
    rintro ⟨k, a⟩
    have hf := L.local_factorization hΩ x hx hcomm k (star a)
    calc
      inner ℂ ((a : H →L[ℂ] H) Ω) (x Ω) =
          productVectorState Ω ((star (a : H →L[ℂ] H)) * x) := by
        rw [← ContinuousLinearMap.adjoint_inner_right]
        rfl
      _ = productVectorState Ω (star (a : H →L[ℂ] H)) * productVectorState Ω x := hf
      _ = inner ℂ ((a : H →L[ℂ] H) Ω) (productVectorState Ω x • Ω) := by
        rw [inner_smul_right]
        change inner ℂ Ω ((a : H →L[ℂ] H).adjoint Ω) * productVectorState Ω x = _
        rw [ContinuousLinearMap.adjoint_inner_right]
        ring
  have he : (⟨x, hx⟩ : Algebra D) =
      ⟨productVectorState Ω x • (1 : H →L[ℂ] H),
        D.toStarSubalgebra.smul_mem D.one_mem _⟩ := by
    apply hsep
    simpa only [algebraVectorMap, LinearMap.coe_mk, AddHom.coe_mk, smul_apply,
      one_apply_eq_self] using hv
  exact congrArg Subtype.val he

include L in
/-- Set-theoretic form of the relative-commutant assertion, usable before
bundling the state centralizer as a von Neumann subalgebra. -/
theorem relative_commutant_scalar (hΩ : ‖Ω‖ = 1)
    (hsep : Function.Injective (algebraVectorMap D Ω))
    (x : H →L[ℂ] H) (hx : x ∈ D)
    (hcomm : x ∈ Set.centralizer
      {u : H →L[ℂ] H | u ∈ D ∧ ProductStateCentralizes D Ω u}) :
    ∃ z : ℂ, x = z • (1 : H →L[ℂ] H) := by
  refine ⟨productVectorState Ω x, L.scalar_of_commutes hΩ hsep x hx ?_⟩
  intro u hu hc
  exact hcomm u ⟨hu, hc⟩

end LocalProductSwaps

end

end KadisonKastler

end OAI
