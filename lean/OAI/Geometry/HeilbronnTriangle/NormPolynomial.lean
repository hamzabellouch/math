import OAI.Geometry.HeilbronnTriangle.NormFoundation

namespace OAI


noncomputable section

namespace Problem355.NormPolynomial

open scoped BigOperators

variable {F K V : Type*} [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K]

def galoisProduct (P : MvPolynomial V K) : MvPolynomial V K :=
  ∏ σ : K ≃ₐ[F] K, MvPolynomial.map σ.toRingHom P

omit [FiniteDimensional F K] in

theorem eval_conjugate (P : MvPolynomial V K) (x : V → F) (σ : K ≃ₐ[F] K) :
    MvPolynomial.eval (algebraMap F K ∘ x) (MvPolynomial.map σ.toRingHom P) =
      σ (MvPolynomial.eval (algebraMap F K ∘ x) P) := by
  simpa [Function.comp_def] using
    (MvPolynomial.map_eval σ.toRingHom (algebraMap F K ∘ x) P).symm

theorem eval_galoisProduct [IsGalois F K] (P : MvPolynomial V K) (x : V → F) :
    MvPolynomial.eval (algebraMap F K ∘ x) (galoisProduct (F := F) P) =
      algebraMap F K (Algebra.norm F (MvPolynomial.eval (algebraMap F K ∘ x) P)) := by
  rw [galoisProduct, map_prod, Algebra.norm_eq_prod_automorphisms]
  exact Finset.prod_congr rfl (fun σ _ => eval_conjugate P x σ)

theorem map_galoisProduct (P : MvPolynomial V K) (τ : K ≃ₐ[F] K) :
    MvPolynomial.map τ.toRingHom (galoisProduct (F := F) P) =
      galoisProduct (F := F) P := by
  classical
  rw [galoisProduct, map_prod]
  change (∏ σ : K ≃ₐ[F] K, MvPolynomial.map τ.toRingHom
    (MvPolynomial.map σ.toRingHom P)) = _
  simp_rw [MvPolynomial.map_map]
  exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ (fun _ => rfl)

theorem coeff_galoisProduct_mem_range [IsGalois F K]
    (P : MvPolynomial V K) (m : V →₀ ℕ) :
    (galoisProduct (F := F) P).coeff m ∈ Set.range (algebraMap F K) := by
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  intro τ
  have h := congrArg (fun polynomial : MvPolynomial V K => polynomial.coeff m) (map_galoisProduct P τ)
  simpa [MvPolynomial.coeff_map] using h

theorem exists_map_of_coeff_mem_range {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (P : MvPolynomial V S)
    (h : ∀ m, P.coeff m ∈ Set.range f) :
    ∃ Q : MvPolynomial V R, MvPolynomial.map f Q = P := by
  classical
  choose c hc using h
  refine ⟨∑ m ∈ P.support, MvPolynomial.monomial m (c m), ?_⟩
  simp only [map_sum, MvPolynomial.map_monomial, hc]
  exact MvPolynomial.support_sum_monomial_coeff P

theorem exists_normPolynomial [IsGalois F K] (P : MvPolynomial V K) :
    ∃ Q : MvPolynomial V F,
      MvPolynomial.map (algebraMap F K) Q = galoisProduct (F := F) P :=
  exists_map_of_coeff_mem_range _ _ (coeff_galoisProduct_mem_range P)

def normPolynomial [IsGalois F K] (P : MvPolynomial V K) : MvPolynomial V F :=
  Classical.choose (exists_normPolynomial P)

@[simp] theorem map_normPolynomial [IsGalois F K] (P : MvPolynomial V K) :
    MvPolynomial.map (algebraMap F K) (normPolynomial (F := F) P) =
      galoisProduct (F := F) P :=
  Classical.choose_spec (exists_normPolynomial P)

theorem eval_normPolynomial [IsGalois F K] (P : MvPolynomial V K) (x : V → F) :
    MvPolynomial.eval x (normPolynomial (F := F) P) =
      Algebra.norm F (MvPolynomial.eval (algebraMap F K ∘ x) P) := by
  apply (algebraMap F K).injective
  rw [MvPolynomial.eval₂_comp, ← MvPolynomial.eval_map, map_normPolynomial,
    eval_galoisProduct]

theorem rename_galoisProduct_of_odd [IsGalois F K]
    (hodd : Odd (Module.finrank F K)) (P : MvPolynomial V K) (f : V → V)
    (hP : MvPolynomial.rename f P = -P) :
    MvPolynomial.rename f (galoisProduct (F := F) P) =
      -galoisProduct (F := F) P := by
  classical
  rw [galoisProduct, map_prod]
  simp_rw [← MvPolynomial.map_rename, hP, map_neg]
  rw [Finset.prod_neg]
  have hcard : Fintype.card (K ≃ₐ[F] K) = Module.finrank F K := by
    simpa only [Nat.card_eq_fintype_card] using IsGalois.card_aut_eq_finrank F K
  simp only [Finset.card_univ, hcard, hodd.neg_one_pow, neg_one_mul]

theorem rename_normPolynomial_of_odd [IsGalois F K]
    (hodd : Odd (Module.finrank F K)) (P : MvPolynomial V K) (f : V → V)
    (hP : MvPolynomial.rename f P = -P) :
    MvPolynomial.rename f (normPolynomial (F := F) P) =
      -normPolynomial (F := F) P := by
  apply MvPolynomial.map_injective (algebraMap F K) (algebraMap F K).injective
  rw [MvPolynomial.map_rename, map_normPolynomial, map_neg, map_normPolynomial]
  exact rename_galoisProduct_of_odd hodd P f hP

end Problem355.NormPolynomial

end

end OAI
