import OAI.RepresentationTheory.RestrictedTilting.AdicJets

namespace OAI

namespace FiberFunctorProof
open scoped TensorProduct Pointwise
universe u
variable {k : Type u} [Field k]
variable {T N : Type u} [AddCommGroup T] [Module k T]
  [AddCommGroup N] [Module k N]
  [Module (MvPolynomial (Fin 2) k) N] [IsScalarTower k (MvPolynomial (Fin 2) k) N]

 
noncomputable def polynomialJetExtend (j : ℕ)
    (s : T →ₗ[k] N ⧸ ((MvPolynomial.idealOfVars (Fin 2) k)^j •
      (⊤ : Submodule (MvPolynomial (Fin 2) k) N))) :
    (((MvPolynomial (Fin 2) k) ⊗[k] T) ⧸ ((MvPolynomial.idealOfVars (Fin 2) k)^j •
      (⊤ : Submodule (MvPolynomial (Fin 2) k) ((MvPolynomial (Fin 2) k) ⊗[k] T)))) →ₗ[MvPolynomial (Fin 2) k]
      (N ⧸ ((MvPolynomial.idealOfVars (Fin 2) k)^j •
      (⊤ : Submodule (MvPolynomial (Fin 2) k) N))) :=
  ((MvPolynomial.idealOfVars (Fin 2) k)^j • (⊤ : Submodule (MvPolynomial (Fin 2) k) _)).liftQ
    (polynomialExtend s) (by
      intro z hz
      change polynomialExtend s z = 0
      refine Submodule.smul_induction_on hz (fun a ha z _ => ?_) (fun z w hz hw => ?_)
      ·
        rw [map_smul]
        obtain ⟨v,hv⟩ := ((MvPolynomial.idealOfVars (Fin 2) k)^j •
          (⊤ : Submodule (MvPolynomial (Fin 2) k) N)).mkQ_surjective (polynomialExtend s z)
        rw [← hv, ← map_smul]
        exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_smul ha (by trivial))
      · rw [map_add, hz, hw, add_zero])

@[simp] lemma polynomialJetExtend_mk (j : ℕ)
    (s : T →ₗ[k] N ⧸ ((MvPolynomial.idealOfVars (Fin 2) k)^j •
      (⊤ : Submodule (MvPolynomial (Fin 2) k) N)))
    (z : (MvPolynomial (Fin 2) k) ⊗[k] T) :
    polynomialJetExtend j s (Submodule.Quotient.mk z) = polynomialExtend s z := rfl

@[simp] lemma polynomialJetExtend_mk_tmul (j : ℕ)
    (s : T →ₗ[k] N ⧸ ((MvPolynomial.idealOfVars (Fin 2) k)^j •
      (⊤ : Submodule (MvPolynomial (Fin 2) k) N)))
    (P : MvPolynomial (Fin 2) k) (t : T) :
    polynomialJetExtend j s (Submodule.Quotient.mk (P ⊗ₜ[k] t)) = P • s t := rfl

lemma polynomialJetExtend_transition (m n : ℕ) (h : m ≤ n)
    (s : T →ₗ[k] N ⧸ ((MvPolynomial.idealOfVars (Fin 2) k)^n •
      (⊤ : Submodule (MvPolynomial (Fin 2) k) N)))
    (t : T →ₗ[k] N ⧸ ((MvPolynomial.idealOfVars (Fin 2) k)^m •
      (⊤ : Submodule (MvPolynomial (Fin 2) k) N)))
    (ht : ∀ x, AdicCompletion.transitionMap (MvPolynomial.idealOfVars (Fin 2) k) N h (s x) = t x)
    (z : ((MvPolynomial (Fin 2) k) ⊗[k] T) ⧸ ((MvPolynomial.idealOfVars (Fin 2) k)^n •
      (⊤ : Submodule (MvPolynomial (Fin 2) k) ((MvPolynomial (Fin 2) k) ⊗[k] T)))) :
    AdicCompletion.transitionMap (MvPolynomial.idealOfVars (Fin 2) k) N h (polynomialJetExtend n s z) =
      polynomialJetExtend m t (AdicCompletion.transitionMap (MvPolynomial.idealOfVars (Fin 2) k) _ h z) := by
  obtain ⟨w,rfl⟩ := ((MvPolynomial.idealOfVars (Fin 2) k)^n •
    (⊤ : Submodule (MvPolynomial (Fin 2) k) ((MvPolynomial (Fin 2) k) ⊗[k] T))).mkQ_surjective z
  change AdicCompletion.transitionMap _ N h (polynomialExtend s w) = polynomialExtend t w
  induction w using TensorProduct.inductionOn with
  | tmul P x => rw [polynomialExtend_tmul, polynomialExtend_tmul, map_smul, ht]
  | add z w hz hw => simp [hz, hw]

noncomputable def coefficientAdicEquiv (j : ℕ) :
    (N ⧸ jetRelation (M := N) (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) (MvPolynomial.X 1) j) ≃ₗ[MvPolynomial (Fin 2) k]
      (N ⧸ ((MvPolynomial.idealOfVars (Fin 2) k)^j • (⊤ : Submodule (MvPolynomial (Fin 2) k) N))) :=
  Submodule.quotEquivOfEq _ _ (by rw [planeIdeal_eq, jetRelation_eq_pow_smul])

omit [Module k N] [IsScalarTower k (MvPolynomial (Fin 2) k) N] in
@[simp] lemma coefficientAdicEquiv_mk (j : ℕ) (n : N) :
    coefficientAdicEquiv (k := k) j (Submodule.Quotient.mk n) = Submodule.Quotient.mk n := rfl

 

theorem polynomialJetExtend_bijective (j : ℕ) (q : N →ₗ[k] T)
    (s : T →ₗ[k] N ⧸ ((MvPolynomial.idealOfVars (Fin 2) k)^j •
      (⊤ : Submodule (MvPolynomial (Fin 2) k) N)))
    (r : (N ⧸ ((MvPolynomial.idealOfVars (Fin 2) k)^j •
      (⊤ : Submodule (MvPolynomial (Fin 2) k) N))) →ₗ[k] T)
    (hq : ∀ n, q n = 0 ↔ n ∈ pairRelation (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) (MvPolynomial.X 1))
    (hr : ∀ n, r (Submodule.Quotient.mk n) = q n)
    (hs : r ∘ₗ s = LinearMap.id)
    (hx : Function.Injective (fun n : N => (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • n))
    (hy : ∀ v n : N, (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) • v =
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • n →
      ∃ w, v = (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • w) :
    Function.Bijective (polynomialJetExtend j s) := by
  let Q := (MvPolynomial.idealOfVars (Fin 2) k)^j • (⊤ : Submodule (MvPolynomial (Fin 2) k) N)
  obtain ⟨l,hl⟩ := (Q.mkQ.restrictScalars k).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr Q.mkQ_surjective)
  let L : T →ₗ[k] N := l ∘ₗ s
  have hL : ∀ t, Q.mkQ (L t) = s t := by
    intro t
    exact congrArg (fun f : (N ⧸ Q) →ₗ[k] (N ⧸ Q) => f (s t)) hl
  have hqL : q ∘ₗ L = LinearMap.id := by
    ext t
    change q (L t) = t
    rw [← hr]
    change r (Q.mkQ (L t)) = t
    rw [hL]
    exact congrArg (fun f : T →ₗ[k] T => f t) hs
  have he (z : (MvPolynomial (Fin 2) k) ⊗[k] T) :
      polynomialExtend s z = Q.mkQ (polynomialExtend L z) := by
    induction z using TensorProduct.inductionOn with
    | tmul P t => simp only [polynomialExtend_tmul, map_smul, hL]
    | add z w hz hw => simp [hz, hw]
  let a := coefficientAdicEquiv (k := k) (N := (MvPolynomial (Fin 2) k) ⊗[k] T) j
  let b := coefficientAdicEquiv (k := k) (N := N) j
  let f := jetMap (polynomialExtend L) (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) (MvPolynomial.X 1) j
  have hbij : Function.Bijective f := polynomialExtend_jet_bijective q L hq hqL hx hy j
  have hc (z) : polynomialJetExtend j s (a z) = b (f z) := by
    obtain ⟨w,rfl⟩ := (jetRelation (M := (MvPolynomial (Fin 2) k) ⊗[k] T)
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) (MvPolynomial.X 1) j).mkQ_surjective z
    exact he w
  constructor
  · intro x y h
    obtain ⟨x,rfl⟩ := a.surjective x
    obtain ⟨y,rfl⟩ := a.surjective y
    rw [hc,hc] at h
    exact congrArg a (hbij.1 (b.injective h))
  · intro z
    obtain ⟨w,hw⟩ := hbij.2 (b.symm z)
    refine ⟨a w, ?_⟩
    rw [hc, hw, b.apply_symm_apply]
end FiberFunctorProof

end OAI
