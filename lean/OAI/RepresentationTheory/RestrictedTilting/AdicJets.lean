import OAI.RepresentationTheory.RestrictedTilting.PolynomialJets

namespace OAI

namespace FiberFunctorProof
open scoped Pointwise
section
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

lemma jetRelation_succ (x y : R) (j : ℕ) :
    jetRelation (M := M) x y (j+1) = x • jetRelation x y j ⊔ y • jetRelation x y j := by
  apply le_antisymm
  · rintro m ⟨v,rfl⟩
    rw [binarySum_succ]
    apply Submodule.add_mem
    · apply (show y • jetRelation x y j ≤ x • jetRelation x y j ⊔ y • jetRelation x y j from le_sup_right)
      rw [pow_succ', mul_smul]
      apply Submodule.smul_mem_pointwise_smul
      exact ⟨Pi.single 0 (v 0), binarySum_single_zero x y j (v 0)⟩
    · apply (show x • jetRelation x y j ≤ x • jetRelation x y j ⊔ y • jetRelation x y j from le_sup_left)
      apply Submodule.smul_mem_pointwise_smul
      exact ⟨_,rfl⟩
  · apply sup_le
    · intro m hm
      obtain ⟨w,⟨v,rfl⟩,rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists m x _).mp hm
      exact ⟨Fin.cons 0 v, binarySum_prepend_zero x y j v⟩
    · intro m hm
      obtain ⟨w,⟨v,rfl⟩,rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists m y _).mp hm
      exact ⟨Fin.snoc v 0, binarySum_append_zero x y j v⟩

 

theorem jetRelation_eq_pow_smul (x y : R) (j : ℕ) :
    jetRelation (M := M) x y j = (Ideal.span {x,y})^j • (⊤ : Submodule R M) := by
  induction j with
  | zero => simp [jetRelation_zero]
  | succ j ih =>
    rw [jetRelation_succ, pow_succ', Submodule.mul_smul, ← ih,
      Ideal.span_insert, Submodule.sup_smul,
      Submodule.ideal_span_singleton_smul, Submodule.ideal_span_singleton_smul]

end

section
universe u
variable (k : Type u) [Field k]
variable {M : Type u} [AddCommGroup M] [Module k M]
  [Module (MvPolynomial (Fin 2) k) M] [IsScalarTower k (MvPolynomial (Fin 2) k) M]

lemma planeIdeal_eq : MvPolynomial.idealOfVars (Fin 2) k =
    Ideal.span {MvPolynomial.X 0, MvPolynomial.X 1} := by
  unfold MvPolynomial.idealOfVars
  congr 1
  ext P
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp
  · rintro (rfl|rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩

lemma planeJetRelation_eq_pow_smul (j : ℕ) :
    planeJetRelation (M := M) k j =
      (((MvPolynomial.idealOfVars (Fin 2) k)^j • (⊤ : Submodule (MvPolynomial (Fin 2) k) M)).restrictScalars k) := by
  rw [planeJetRelation, planeIdeal_eq, jetRelation_eq_pow_smul]

noncomputable def planeJetAdicEquiv (j : ℕ) :
    (M ⧸ planeJetRelation (M := M) k j) ≃ₗ[k]
      (M ⧸ ((MvPolynomial.idealOfVars (Fin 2) k)^j • (⊤ : Submodule (MvPolynomial (Fin 2) k) M))) :=
  (Submodule.quotEquivOfEq _ _ (planeJetRelation_eq_pow_smul k j)).trans
    (Submodule.Quotient.restrictScalarsEquiv k _)

lemma planeJetAdicEquiv_mk (j : ℕ) (m : M) :
    planeJetAdicEquiv k j ((planeJetRelation k j).mkQ m) =
      (((MvPolynomial.idealOfVars (Fin 2) k)^j • (⊤ : Submodule (MvPolynomial (Fin 2) k) M))).mkQ m := by
  rfl

lemma planeJetAdicEquiv_transition (j : ℕ) (z : M ⧸ planeJetRelation (M := M) k (j+1)) :
    AdicCompletion.transitionMap (MvPolynomial.idealOfVars (Fin 2) k) M (Nat.le_succ j)
      (planeJetAdicEquiv k (j+1) z) = planeJetAdicEquiv k j (planeJetTransition k j z) := by
  obtain ⟨m,rfl⟩ := (planeJetRelation (M := M) k (j+1)).mkQ_surjective z
  rfl

end
end FiberFunctorProof

end OAI
