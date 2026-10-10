import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientSections

namespace OAI

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PiExponentSiegel.W08

section

open MvPolynomial

variable {k σ τ : Type*} [Field k]

noncomputable def coordinateEval : MvPolynomial (Option σ) k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval (fun o => Option.elim o 0 MvPolynomial.X)

noncomputable def coordinateInclude : MvPolynomial σ k →ₐ[k] MvPolynomial (Option σ) k :=
  MvPolynomial.rename Option.some

@[simp] theorem coordinateEval_X_none :
    coordinateEval (k := k) (σ := σ) (X none) = 0 := by simp [coordinateEval]

@[simp] theorem coordinateEval_X_some (i : σ) :
    coordinateEval (k := k) (X (some i)) = X i := by simp [coordinateEval]

@[simp] theorem coordinateEval_include (p : MvPolynomial σ k) :
    coordinateEval (coordinateInclude p) = p := by
  have h : (coordinateEval (k := k) (σ := σ)).comp coordinateInclude = AlgHom.id k _ := by
    ext i
    simp [coordinateInclude]
  exact AlgHom.congr_fun h p

theorem coordinateEval_surjective :
    Function.Surjective (coordinateEval (k := k) (σ := σ)) :=
  fun p => ⟨coordinateInclude p, coordinateEval_include p⟩

theorem coordinateEval_homogeneous {p : MvPolynomial (Option σ) k} {n : ℕ}
    (hp : p.IsHomogeneous n) : (coordinateEval p).IsHomogeneous n := by
  simpa only [coordinateEval, one_mul] using hp.aeval
    (fun o => Option.elim o 0 (MvPolynomial.X : σ → MvPolynomial σ k))
    (show ∀ o : Option σ, (Option.elim o 0 (MvPolynomial.X : σ → MvPolynomial σ k)).IsHomogeneous 1
      from fun o => by cases o with
        | none => exact (homogeneousSubmodule σ k 1).zero_mem
        | some i => exact isHomogeneous_X k i)

theorem coordinateInclude_homogeneous {p : MvPolynomial σ k} {n : ℕ}
    (hp : p.IsHomogeneous n) : (coordinateInclude p).IsHomogeneous n :=
  hp.rename_isHomogeneous

noncomputable def coordinateImageIdeal (J : Ideal (MvPolynomial (Option σ) k)) :
    Ideal (MvPolynomial σ k) := J.map coordinateEval.toRingHom

theorem homogeneous_ideal_map_of_degree_preserving
    (f : MvPolynomial σ k →ₐ[k] MvPolynomial τ k)
    (hf : ∀ n (p : MvPolynomial σ k), p.IsHomogeneous n → (f p).IsHomogeneous n)
    (J : Ideal (MvPolynomial σ k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    (J.map f.toRingHom).IsHomogeneous (MvPolynomial.homogeneousSubmodule τ k) := by
  obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists (MvPolynomial.homogeneousSubmodule σ k) J).mp hJ
  rw [hS, Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro q ⟨p, ⟨z, hz, rfl⟩, rfl⟩
  obtain ⟨n, hn⟩ := z.property
  exact ⟨n, hf n z hn⟩

theorem coordinateImageIdeal_homogeneous (J : Ideal (MvPolynomial (Option σ) k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Option σ) k)) :
    (coordinateImageIdeal J).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) :=
  homogeneous_ideal_map_of_degree_preserving coordinateEval
    (fun _ _ hp => coordinateEval_homogeneous hp) J hJ

theorem coordinateInclude_eval_mod (J : Ideal (MvPolynomial (Option σ) k))
    (hX : X none ∈ J) (p : MvPolynomial (Option σ) k) :
    Ideal.Quotient.mk J (coordinateInclude (coordinateEval p)) = Ideal.Quotient.mk J p := by
  have h : ((Ideal.Quotient.mkₐ k J).comp coordinateInclude).comp coordinateEval =
      Ideal.Quotient.mkₐ k J := by
    ext i
    cases i with
    | none => simpa [coordinateInclude] using (Ideal.Quotient.eq_zero_iff_mem.mpr hX).symm
    | some i => simp [coordinateInclude]
  exact AlgHom.congr_fun h p

noncomputable def coordinateQuotientMap (J : Ideal (MvPolynomial (Option σ) k)) :
    (MvPolynomial (Option σ) k ⧸ J) →ₐ[k]
      (MvPolynomial σ k ⧸ coordinateImageIdeal J) :=
  Ideal.quotientMapₐ (coordinateImageIdeal J) coordinateEval Ideal.le_comap_map

theorem coordinateInclude_image_mem (J : Ideal (MvPolynomial (Option σ) k))
    (hX : X none ∈ J) {p : MvPolynomial σ k} (hp : p ∈ coordinateImageIdeal J) :
    coordinateInclude p ∈ J := by
  obtain ⟨q, hq, rfl⟩ :=
    (Ideal.mem_map_iff_of_surjective coordinateEval.toRingHom coordinateEval_surjective).mp hp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change Ideal.Quotient.mk J (coordinateInclude (coordinateEval q)) = 0
  rw [coordinateInclude_eval_mod J hX]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hq

noncomputable def coordinateQuotientInverse (J : Ideal (MvPolynomial (Option σ) k))
    (hX : X none ∈ J) :
    (MvPolynomial σ k ⧸ coordinateImageIdeal J) →ₐ[k]
      (MvPolynomial (Option σ) k ⧸ J) :=
  Ideal.quotientMapₐ J coordinateInclude (fun _ hp => coordinateInclude_image_mem J hX hp)

noncomputable def coordinateQuotientEquiv (J : Ideal (MvPolynomial (Option σ) k))
    (hX : X none ∈ J) :
    (MvPolynomial (Option σ) k ⧸ J) ≃ₐ[k]
      (MvPolynomial σ k ⧸ coordinateImageIdeal J) :=
  { coordinateQuotientMap J with
    invFun := coordinateQuotientInverse J hX
    left_inv := by
      intro x
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact coordinateInclude_eval_mod J hX p
    right_inv := by
      intro x
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.mk _ (coordinateEval (coordinateInclude p)) = _
      rw [coordinateEval_include] }

@[simp] theorem coordinateQuotientEquiv_mk (J : Ideal (MvPolynomial (Option σ) k))
    (hX : X none ∈ J) (p : MvPolynomial (Option σ) k) :
    coordinateQuotientEquiv J hX (Ideal.Quotient.mk J p) =
      Ideal.Quotient.mk (coordinateImageIdeal J) (coordinateEval p) := rfl

theorem coordinateQuotientEquiv_section_map (J : Ideal (MvPolynomial (Option σ) k))
    (hX : X none ∈ J) (n : ℕ) :
    (PiExponentJets.W64.quotientSection J n).map
      (coordinateQuotientEquiv J hX).toLinearEquiv.toLinearMap =
      PiExponentJets.W64.quotientSection (coordinateImageIdeal J) n := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hy
    exact Submodule.mem_map.mpr ⟨coordinateEval p, coordinateEval_homogeneous hp, rfl⟩
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
    apply Submodule.mem_map.mpr
    refine ⟨Ideal.Quotient.mk J (coordinateInclude p), ?_, ?_⟩
    · exact Submodule.mem_map.mpr ⟨coordinateInclude p, coordinateInclude_homogeneous hp, rfl⟩
    · change Ideal.Quotient.mk _ (coordinateEval (coordinateInclude p)) = _
      rw [coordinateEval_include]
      rfl

noncomputable def coordinateQuotientSectionEquiv (J : Ideal (MvPolynomial (Option σ) k))
    (hX : X none ∈ J) (n : ℕ) :
    PiExponentJets.W64.quotientSection J n ≃ₗ[k]
      PiExponentJets.W64.quotientSection (coordinateImageIdeal J) n :=
  (coordinateQuotientEquiv J hX).toLinearEquiv.ofSubmodules _ _
    (coordinateQuotientEquiv_section_map J hX n)

theorem coordinateQuotientSection_finrank (J : Ideal (MvPolynomial (Option σ) k))
    (hX : X none ∈ J) (n : ℕ) :
    Module.finrank k (PiExponentJets.W64.quotientSection J n) =
      Module.finrank k (PiExponentJets.W64.quotientSection (coordinateImageIdeal J) n) :=
  (coordinateQuotientSectionEquiv J hX n).finrank_eq

end

variable {k σ τ : Type*} [Field k]

noncomputable def renameQuotientEquiv (e : σ ≃ τ) (J : Ideal (MvPolynomial σ k)) :
    (MvPolynomial σ k ⧸ J) ≃ₐ[k]
      (MvPolynomial τ k ⧸ J.map (MvPolynomial.rename e).toRingHom) :=
  Ideal.quotientEquivAlg J _ (MvPolynomial.renameEquiv k e) rfl

theorem renameQuotientEquiv_section_map (e : σ ≃ τ)
    (J : Ideal (MvPolynomial σ k)) (n : ℕ) :
    (PiExponentJets.W64.quotientSection J n).map
      (renameQuotientEquiv e J).toLinearEquiv.toLinearMap =
      PiExponentJets.W64.quotientSection (J.map (MvPolynomial.rename e).toRingHom) n := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hy
    exact Submodule.mem_map.mpr ⟨MvPolynomial.rename e p, hp.rename_isHomogeneous, rfl⟩
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
    apply Submodule.mem_map.mpr
    refine ⟨Ideal.Quotient.mk J (MvPolynomial.rename e.symm p), ?_, ?_⟩
    · exact Submodule.mem_map.mpr ⟨MvPolynomial.rename e.symm p, hp.rename_isHomogeneous, rfl⟩
    · change Ideal.Quotient.mk _ (MvPolynomial.rename e (MvPolynomial.rename e.symm p)) = _
      exact congrArg (Ideal.Quotient.mk _) ((MvPolynomial.renameEquiv k e).apply_symm_apply p)

noncomputable def renameQuotientSectionEquiv (e : σ ≃ τ)
    (J : Ideal (MvPolynomial σ k)) (n : ℕ) :
    PiExponentJets.W64.quotientSection J n ≃ₗ[k]
      PiExponentJets.W64.quotientSection (J.map (MvPolynomial.rename e).toRingHom) n :=
  (renameQuotientEquiv e J).toLinearEquiv.ofSubmodules _ _
    (renameQuotientEquiv_section_map e J n)

theorem renameQuotientSection_finrank (e : σ ≃ τ)
    (J : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Module.finrank k (PiExponentJets.W64.quotientSection J n) =
      Module.finrank k
        (PiExponentJets.W64.quotientSection (J.map (MvPolynomial.rename e).toRingHom) n) :=
  (renameQuotientSectionEquiv e J n).finrank_eq

theorem renameImageIdeal_homogeneous (e : σ ≃ τ) (J : Ideal (MvPolynomial σ k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    (J.map (MvPolynomial.rename e).toRingHom).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule τ k) :=
  homogeneous_ideal_map_of_degree_preserving (MvPolynomial.rename e)
    (fun _ _ hp => hp.rename_isHomogeneous) J hJ

end PiExponentSiegel.W08

end OAI
