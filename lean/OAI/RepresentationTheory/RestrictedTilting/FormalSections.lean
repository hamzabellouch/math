import OAI.RepresentationTheory.RestrictedTilting.FiniteJetMaps
import OAI.RepresentationTheory.RestrictedTilting.CompletionTriviality

namespace OAI

namespace FiberFunctorProof
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct Pointwise
universe u
variable (k : Type u) [Field k]
variable {M : Type u} [AddCommGroup M] [Module k M]
  [Module (MvPolynomial (Fin 2) k) M] [IsScalarTower k (MvPolynomial (Fin 2) k) M]
  [Module.Finite k (M ⧸ planeJetRelation (M := M) k 1)]
variable (σ : Representation k (SL2 k) M) (hσ : PlaneCompatible k σ)
local notation "A" => MvPolynomial (Fin 2) k
local notation "I" => MvPolynomial.idealOfVars (Fin 2) k
local notation "T" => planeJetFD k σ hσ 1

noncomputable def adicPlaneSections
    (s : (j : ℕ) → T ⟶ planeJetFD k σ hσ (j+1)) :
    (j : ℕ) → T →ₗ[k] M ⧸ (I^j • (⊤ : Submodule A M))
  | 0 => 0
  | j+1 => (planeJetAdicEquiv k (j+1)).toLinearMap ∘ₗ fdrepLinear k (s j)

lemma adicPlaneSections_succ
    (s : (j : ℕ) → T ⟶ planeJetFD k σ hσ (j+1))
    (hs : ∀ j, s (j+1) ≫ planeJetTransitionHom k σ hσ (j+1) = s j)
    (j : ℕ) (t : T) :
    AdicCompletion.transitionMap I M (Nat.le_succ j) (adicPlaneSections k σ hσ s (j+1) t) =
      adicPlaneSections k σ hσ s j t := by
  cases j with
  | zero =>
    have : Subsingleton (M ⧸ (I^0 • (⊤ : Submodule A M))) := by
      rw [pow_zero, Submodule.one_smul]
      infer_instance
    exact Subsingleton.elim _ _
  | succ j =>
    change AdicCompletion.transitionMap I M (Nat.le_succ (j+1))
      (planeJetAdicEquiv k (j+2) (fdrepLinear k (s (j+1)) t)) =
        planeJetAdicEquiv k (j+1) (fdrepLinear k (s j) t)
    trans planeJetAdicEquiv k (j+1)
      (planeJetTransition k (j+1) (fdrepLinear k (s (j+1)) t))
    · exact planeJetAdicEquiv_transition k (j+1) _
    apply congrArg
    exact congrArg (fun f : T ⟶ planeJetFD k σ hσ (j+1) => fdrepLinear k f t) (hs j)

lemma adicPlaneSections_transition
    (s : (j : ℕ) → T ⟶ planeJetFD k σ hσ (j+1))
    (hs : ∀ j, s (j+1) ≫ planeJetTransitionHom k σ hσ (j+1) = s j)
    (m n : ℕ) (h : m ≤ n) (t : T) :
    AdicCompletion.transitionMap I M h (adicPlaneSections k σ hσ s n t) =
      adicPlaneSections k σ hσ s m t := by
  exact (Submodule.eq_factor_of_eq_factor_succ
    (fun _ _ h => Submodule.pow_smul_top_le I M h)
    (fun j => adicPlaneSections k σ hσ s j t)
    (fun j => (adicPlaneSections_succ k σ hσ s hs j t).symm) h).symm

lemma adicPlaneSections_origin
    (s : (j : ℕ) → T ⟶ planeJetFD k σ hσ (j+1)) (hs0 : s 0 = 𝟙 _) (t : T) :
    adicPlaneSections k σ hσ s 1 t = planeJetAdicEquiv k 1 t := by
  change planeJetAdicEquiv k 1 (fdrepLinear k (s 0) t) = _
  rw [hs0]
  rfl

lemma adicPlaneSections_bijective
    (s : (j : ℕ) → T ⟶ planeJetFD k σ hσ (j+1)) (hs0 : s 0 = 𝟙 _)
    (hs : ∀ j, s (j+1) ≫ planeJetTransitionHom k σ hσ (j+1) = s j)
    (hx : Function.Injective (fun m : M => (MvPolynomial.X 0 : A) • m))
    (hy : ∀ v n : M, (MvPolynomial.X 1 : A) • v = (MvPolynomial.X 0 : A) • n →
      ∃ w : M, v = (MvPolynomial.X 0 : A) • w) (j : ℕ) :
    Function.Bijective (polynomialJetExtend j (adicPlaneSections k σ hσ s j)) := by
  cases j with
  | zero =>
    have : Subsingleton (M ⧸ (I^0 • (⊤ : Submodule A M))) := by
      rw [pow_zero, Submodule.one_smul]; infer_instance
    have : Subsingleton ((A ⊗[k] T) ⧸ (I^0 • (⊤ : Submodule A (A ⊗[k] T)))) := by
      rw [pow_zero, Submodule.one_smul]; infer_instance
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun z => ⟨0, Subsingleton.elim _ _⟩⟩
  | succ j =>
    let q : M →ₗ[k] T := (planeJetRelation k 1).mkQ
    let r : (M ⧸ (I^(j+1) • (⊤ : Submodule A M))) →ₗ[k] T :=
      (planeJetAdicEquiv k 1).symm.toLinearMap ∘ₗ
        (AdicCompletion.transitionMap I M (Nat.succ_le_succ (Nat.zero_le j))).restrictScalars k
    apply polynomialJetExtend_bijective (j+1) q _ r
    · intro n
      change (Submodule.Quotient.mk n : M ⧸ planeJetRelation k 1) = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero]
      simp only [planeJetRelation, Submodule.restrictScalars_mem, jetRelation_one]
    · intro n; rfl
    · ext t
      change (planeJetAdicEquiv k 1).symm
        (AdicCompletion.transitionMap I M (Nat.succ_le_succ (Nat.zero_le j)) (adicPlaneSections k σ hσ s (j+1) t)) = t
      rw [adicPlaneSections_transition k σ hσ s hs, adicPlaneSections_origin k σ hσ s hs0]
      exact (planeJetAdicEquiv k 1).symm_apply_apply t
    · exact hx
    · exact hy

 
noncomputable def formalPlaneSection
    (s : (j : ℕ) → T ⟶ planeJetFD k σ hσ (j+1))
    (hs : ∀ j, s (j+1) ≫ planeJetTransitionHom k σ hσ (j+1) = s j) :
    T →ₗ[k] AdicCompletion I M where
  toFun t := ⟨fun j => adicPlaneSections k σ hσ s j t,
    fun {_ _} h => adicPlaneSections_transition k σ hσ s hs _ _ h t⟩
  map_add' a b := by ext j; exact map_add _ _ _
  map_smul' c a := by ext j; exact map_smul _ _ _

 

lemma formalPlaneSection_equivariant
    (s : (j : ℕ) → T ⟶ planeJetFD k σ hσ (j+1))
    (hs : ∀ j, s (j+1) ≫ planeJetTransitionHom k σ hσ (j+1) = s j)
    (g : SL2 k) (j : ℕ) (t : T) :
    (formalPlaneSection k σ hσ s hs ((planeJetFD k σ hσ 1).ρ g t)).val (j+1) =
      planeJetAdicEquiv k (j+1)
        ((planeJetFD k σ hσ (j+1)).ρ g (fdrepLinear k (s j) t)) := by
  change planeJetAdicEquiv k (j+1) (fdrepLinear k (s j) ((planeJetFD k σ hσ 1).ρ g t)) = _
  exact congrArg (planeJetAdicEquiv k (j+1)) (fdrepLinear_comm k (s j) g t)

 

noncomputable def formalPlaneTrivialization
    (s : (j : ℕ) → T ⟶ planeJetFD k σ hσ (j+1)) (hs0 : s 0 = 𝟙 _)
    (hs : ∀ j, s (j+1) ≫ planeJetTransitionHom k σ hσ (j+1) = s j)
    (hx : Function.Injective (fun m : M => (MvPolynomial.X 0 : A) • m))
    (hy : ∀ v n : M, (MvPolynomial.X 1 : A) • v = (MvPolynomial.X 0 : A) • n →
      ∃ w : M, v = (MvPolynomial.X 0 : A) • w) :
    (AdicCompletion I A) ⊗[k] T ≃ₗ[AdicCompletion I A] AdicCompletion I M :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange k A
    (AdicCompletion I A) (AdicCompletion I A) T).symm ≪≫ₗ
  AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I (A ⊗[k] T) ≪≫ₗ
  LinearEquiv.ofBijective
    (completionOfJetMaps I (fun j => polynomialJetExtend j (adicPlaneSections k σ hσ s j))
      (fun m n h z => polynomialJetExtend_transition m n h _ _
        (adicPlaneSections_transition k σ hσ s hs m n h) z))
    (completionOfJetMaps_bijective I _ _ (adicPlaneSections_bijective k σ hσ s hs0 hs hx hy))

lemma formalPlaneTrivialization_one_tmul
    (s : (j : ℕ) → T ⟶ planeJetFD k σ hσ (j+1)) (hs0 : s 0 = 𝟙 _)
    (hs : ∀ j, s (j+1) ≫ planeJetTransitionHom k σ hσ (j+1) = s j)
    (hx : Function.Injective (fun m : M => (MvPolynomial.X 0 : A) • m))
    (hy : ∀ v n : M, (MvPolynomial.X 1 : A) • v = (MvPolynomial.X 0 : A) • n →
      ∃ w : M, v = (MvPolynomial.X 0 : A) • w) (t : T) :
    formalPlaneTrivialization k σ hσ s hs0 hs hx hy (1 ⊗ₜ[k] t) =
      formalPlaneSection k σ hσ s hs t := by
  simp only [formalPlaneTrivialization, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_apply,
    AdicCompletion.ofTensorProduct_tmul, one_smul]
  apply AdicCompletion.ext
  intro j
  change polynomialJetExtend j (adicPlaneSections k σ hσ s j)
    (Submodule.Quotient.mk ((1 : A) ⊗ₜ[k] t)) = adicPlaneSections k σ hσ s j t
  rw [polynomialJetExtend_mk_tmul, one_smul]

 

theorem exists_formalPlaneTrivialization [Infinite k]
    (hr : IsRational k σ)
    (hx : Function.Injective (fun m : M => (MvPolynomial.X 0 : A) • m))
    (hy : ∀ v n : M, (MvPolynomial.X 1 : A) • v = (MvPolynomial.X 0 : A) • n →
      ∃ w : M, v = (MvPolynomial.X 0 : A) • w)
    (hT : IsTilting k T) :
    Nonempty ((AdicCompletion I A) ⊗[k] T ≃ₗ[AdicCompletion I A] AdicCompletion I M) := by
  obtain ⟨s,hs0,hs⟩ := compatible_planeJet_sections k σ hσ hr hx hy hT
  exact ⟨formalPlaneTrivialization k σ hσ s hs0 hs hx hy⟩
end FiberFunctorProof

end OAI
