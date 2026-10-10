import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Regular.Defs
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import OAI.NumberTheory.SiegelZeros.Hilbert.HomogeneousSections

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.W64

variable {k σ : Type*} [Field k] [Finite σ]

noncomputable def quotientSection (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Submodule k (MvPolynomial σ k ⧸ I) :=
  (MvPolynomial.homogeneousSubmodule σ k n).map (Ideal.Quotient.mkₐ k I).toLinearMap

noncomputable instance quotientSection_finite (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Module.Finite k (quotientSection I n) := by
  unfold quotientSection
  infer_instance

noncomputable def quotientSectionMultiply (I : Ideal (MvPolynomial σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) (n : ℕ) :
    quotientSection I n →ₗ[k] quotientSection I (n + d) where
  toFun x := ⟨x.1 * Ideal.Quotient.mk I f, by
    obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
    apply Submodule.mem_map.mpr
    refine ⟨p * f, hp.mul hf, ?_⟩
    change Ideal.Quotient.mk I (p * f) = x.1 * Ideal.Quotient.mk I f
    rw [map_mul]
    exact congrArg (fun y => y * Ideal.Quotient.mk I f) hpx⟩
  map_add' x y := by apply Subtype.ext; exact add_mul _ _ _
  map_smul' c x := by apply Subtype.ext; exact smul_mul_assoc _ _ _

omit [Finite σ] in
theorem quotientSectionMultiply_injective (I : Ideal (MvPolynomial σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hreg : IsRightRegular (Ideal.Quotient.mk I f)) (n : ℕ) :
    Function.Injective (quotientSectionMultiply I f hf n) := by
  intro x y h
  apply Subtype.ext
  exact hreg (congrArg Subtype.val h)

theorem quotientSectionCokernel_finrank_add (I : Ideal (MvPolynomial σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hreg : IsRightRegular (Ideal.Quotient.mk I f)) (n : ℕ) :
    Module.finrank k
        (quotientSection I (n + d) ⧸
          LinearMap.range (quotientSectionMultiply I f hf n)) +
      Module.finrank k (quotientSection I n) =
      Module.finrank k (quotientSection I (n + d)) := by
  have hi := quotientSectionMultiply_injective I f hf hreg n
  simpa only [LinearMap.finrank_range_of_inj hi] using
    (LinearMap.range (quotientSectionMultiply I f hf n)).finrank_quotient_add_finrank

end WeightedTorusJets.W64

end

end SiegelZeros

section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace SiegelZeros.W08

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

section Sections

variable [Finite σ]

omit [Finite σ] in
theorem coordinateQuotientEquiv_section_map (J : Ideal (MvPolynomial (Option σ) k))
    (hX : X none ∈ J) (n : ℕ) :
    (WeightedTorusJets.W64.quotientSection J n).map
      (coordinateQuotientEquiv J hX).toLinearEquiv.toLinearMap =
      WeightedTorusJets.W64.quotientSection (coordinateImageIdeal J) n := by
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
    WeightedTorusJets.W64.quotientSection J n ≃ₗ[k]
      WeightedTorusJets.W64.quotientSection (coordinateImageIdeal J) n :=
  (coordinateQuotientEquiv J hX).toLinearEquiv.ofSubmodules _ _
    (coordinateQuotientEquiv_section_map J hX n)

omit [Finite σ] in
theorem coordinateQuotientSection_finrank (J : Ideal (MvPolynomial (Option σ) k))
    (hX : X none ∈ J) (n : ℕ) :
    Module.finrank k (WeightedTorusJets.W64.quotientSection J n) =
      Module.finrank k (WeightedTorusJets.W64.quotientSection (coordinateImageIdeal J) n) :=
  (coordinateQuotientSectionEquiv J hX n).finrank_eq

end Sections

end SiegelZeros.W08

namespace SiegelZeros.W08

variable {k σ τ : Type*} [Field k] [Finite σ] [Finite τ]

noncomputable def renameQuotientEquiv (e : σ ≃ τ) (J : Ideal (MvPolynomial σ k)) :
    (MvPolynomial σ k ⧸ J) ≃ₐ[k]
      (MvPolynomial τ k ⧸ J.map (MvPolynomial.rename e).toRingHom) :=
  Ideal.quotientEquivAlg J _ (MvPolynomial.renameEquiv k e) rfl

omit [Finite σ] [Finite τ] in
theorem renameQuotientEquiv_section_map (e : σ ≃ τ)
    (J : Ideal (MvPolynomial σ k)) (n : ℕ) :
    (WeightedTorusJets.W64.quotientSection J n).map
      (renameQuotientEquiv e J).toLinearEquiv.toLinearMap =
      WeightedTorusJets.W64.quotientSection (J.map (MvPolynomial.rename e).toRingHom) n := by
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
    WeightedTorusJets.W64.quotientSection J n ≃ₗ[k]
      WeightedTorusJets.W64.quotientSection (J.map (MvPolynomial.rename e).toRingHom) n :=
  (renameQuotientEquiv e J).toLinearEquiv.ofSubmodules _ _
    (renameQuotientEquiv_section_map e J n)

omit [Finite σ] [Finite τ] in
theorem renameQuotientSection_finrank (e : σ ≃ τ)
    (J : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Module.finrank k (WeightedTorusJets.W64.quotientSection J n) =
      Module.finrank k
        (WeightedTorusJets.W64.quotientSection (J.map (MvPolynomial.rename e).toRingHom) n) :=
  (renameQuotientSectionEquiv e J n).finrank_eq

omit [Finite σ] [Finite τ] in
theorem renameImageIdeal_homogeneous (e : σ ≃ τ) (J : Ideal (MvPolynomial σ k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    (J.map (MvPolynomial.rename e).toRingHom).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule τ k) :=
  homogeneous_ideal_map_of_degree_preserving (MvPolynomial.rename e)
    (fun _ _ hp => hp.rename_isHomogeneous) J hJ

end SiegelZeros.W08

end

end OAI
