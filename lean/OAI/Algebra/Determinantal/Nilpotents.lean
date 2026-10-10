/-
Portions of this file have been adapted from an external source.
The source copyright header and license information are preserved below.
-/

import OAI.Algebra.Determinantal.CoordinateFields

namespace OAI

namespace PermanentBorder.NilpotentOrbits
open scoped DirectSum
open Submodule Module Polynomial Ideal Submodule.IsPrincipal Submodule.Quotient

section Decomposition
variable {R M : Type*} [CommRing R] [IsPrincipalIdealRing R] [IsDomain R]
  [AddCommGroup M] [Module R M]

/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin

The following decomposition theorem is adapted from Mathlib.Algebra.Module.PID.
Source: https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Algebra/Module/PID.lean

This code has been modified.
-/

theorem decomposition_of_generators {p : R} (hp : Irreducible p)
    (hM : Module.IsTorsion' M (Submonoid.powers p))
    (d : ℕ) (s : Fin d → M) (hs : Submodule.span R (Set.range s) = ⊤) :
    ∃ k : Fin d → ℕ, Nonempty (M ≃ₗ[R] ⨁ i : Fin d, R ⧸ R ∙ p ^ k i) := by
  classical
  induction d generalizing M with
  | zero =>
    use finZeroElim
    rw [Set.range_eq_empty, Submodule.span_empty] at hs
    have : Unique M :=
      ⟨⟨0⟩, fun x => by dsimp; rw [← Submodule.mem_bot R, hs]; exact Submodule.mem_top⟩
    exact ⟨0⟩
  | succ d IH =>
    have : ∀ x : M, Decidable (x = 0) := fun _ => by classical infer_instance
    obtain ⟨j, hj⟩ := exists_isTorsionBy hM d.succ d.succ_ne_zero s hs
    let s' : Fin d → M ⧸ R ∙ s j := Submodule.Quotient.mk ∘ s ∘ j.succAbove

    have := IH ?_ s' ?_
    · obtain ⟨k, ⟨f⟩⟩ := this
      clear IH
      have : ∀ i : Fin d,
          ∃ x : M, p ^ k i • x = 0 ∧ f (Submodule.Quotient.mk x) = DirectSum.lof R _ _ i 1 := by
        intro i
        let fi := f.symm.toLinearMap.comp (DirectSum.lof _ _ _ i)
        obtain ⟨x, h0, h1⟩ := exists_smul_eq_zero_and_mk_eq hp hM hj fi; refine ⟨x, h0, ?_⟩; rw [h1]
        simp only [fi, LinearMap.coe_comp, f.symm.coe_toLinearMap, f.apply_symm_apply,
          Function.comp_apply]
      refine ⟨?_, ⟨?_⟩⟩
      · exact fun a => (fun i => (Option.rec (pOrder hM (s j)) k i : ℕ)) (finSuccEquiv d a)
      · refine
          (lequivProdOfRightSplitExact
            (g := f.toLinearMap.comp <| mkQ _)
            (f := (DirectSum.toModule _ _ _ fun i => (liftQSpanSingleton (p ^ k i)
                (LinearMap.toSpanSingleton _ _ _)
                (show (LinearMap.toSpanSingleton R M (this i).choose) (p ^ k i) = 0 from
                  (this i).choose_spec.left) : R ⧸ _ →ₗ[R] _)))
              (R ∙ s j).injective_subtype ?_ ?_).symm ≪≫ₗ
          (((quotTorsionOfEquivSpanSingleton R M (s j)).symm ≪≫ₗ
            (quotEquivOfEq (torsionOf R M (s j)) _
              (Ideal.torsionOf_eq_span_pow_pOrder hp hM (s j)))).prodCongr (.refl _ _)) ≪≫ₗ
          (@DirectSum.lequivProdDirectSum R _ _
            (fun i => R ⧸ R ∙ p ^ @Option.rec _ (fun _ => ℕ) (pOrder hM <| s j) k i) _ _).symm ≪≫ₗ
          (DirectSum.lequivCongrLeft R (finSuccEquiv d).symm)
        · rw [range_subtype, LinearEquiv.ker_comp, ker_mkQ]
        · rw [LinearMap.comp_assoc]
          ext i : 3
          simp only [LinearMap.coe_comp, Function.comp_apply, mkQ_apply]
          rw [LinearEquiv.coe_toLinearMap, LinearMap.id_apply, DirectSum.toModule_lof,
            liftQSpanSingleton_apply, LinearMap.toSpanSingleton_apply_one, Ideal.Quotient.mk_eq_mk,
            map_one (Ideal.Quotient.mk _), (this i).choose_spec.right]
    · exact (mk_surjective _).forall.mpr fun x =>
        ⟨(@hM x).choose, by rw [← Quotient.mk_smul, (@hM x).choose_spec, Quotient.mk_zero]⟩
    · have hs' := congr_arg (Submodule.map <| mkQ <| R ∙ s j) hs
      rw [Submodule.map_span, Submodule.map_top, range_mkQ] at hs'
      simp only [s']; rw [← Function.comp_assoc, Set.range_comp (_ ∘ s), Fin.range_succAbove]
      rw [← Set.range_comp, ← Set.insert_image_compl_eq_range _ j, Function.comp_apply,
        mkQ_apply, (Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self _),
        Submodule.span_insert_zero] at hs'
      exact hs'

end Decomposition

section Nilpotent
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

abbrev Block (e : ℕ) := K[X] ⧸ Ideal.span {(X : K[X]) ^ e}

theorem torsion_of_nilpotent (f : Module.End K V) (hf : IsNilpotent f) :
    Module.IsTorsion' (Module.AEval' f) (Submonoid.powers (X : K[X])) := by
  obtain ⟨e, he⟩ := hf
  intro x
  refine ⟨⟨X ^ e, ⟨e, rfl⟩⟩, ?_⟩
  change (X ^ e : K[X]) • x = 0
  obtain ⟨v, rfl⟩ := (Module.AEval'.of f).surjective x
  rw [Module.AEval'.X_pow_smul_of, he, zero_smul, map_zero]

theorem nilpotent_decomposition {n : ℕ} (b : Module.Basis (Fin n) K V)
    (f : Module.End K V) (hf : IsNilpotent f) :
    ∃ e : Fin n → ℕ,
      Nonempty (Module.AEval' f ≃ₗ[K[X]] ⨁ i : Fin n, Block (K := K) (e i)) := by
  let b' := b.map (Module.AEval'.of f)
  exact decomposition_of_generators Polynomial.irreducible_X
    (torsion_of_nilpotent f hf) n b'
    (Submodule.span_eq_top_of_span_eq_top K K[X] _ b'.span_eq)

theorem nilpotent_pow_dim {n : ℕ} (b : Module.Basis (Fin n) K V)
    (f : Module.End K V) (hf : IsNilpotent f) : f ^ n = 0 := by
  let := Module.Finite.of_basis b
  have hd : Module.finrank K V = n := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  simpa only [hf.charpoly_eq_X_pow_finrank, hd, map_pow, aeval_X] using
    f.aeval_self_charpoly

theorem exponents_le_dim {n : ℕ} (b : Module.Basis (Fin n) K V)
    (f : Module.End K V) (hf : IsNilpotent f) (e : Fin n → ℕ)
    (E : Module.AEval' f ≃ₗ[K[X]] ⨁ i : Fin n, Block (K := K) (e i)) :
    ∀ i, e i ≤ n := by
  classical
  have hpow := nilpotent_pow_dim b f hf
  have hsmul (x : Module.AEval' f) : (X ^ n : K[X]) • x = 0 := by
    obtain ⟨v, rfl⟩ := (Module.AEval'.of f).surjective x
    rw [Module.AEval'.X_pow_smul_of, hpow, zero_smul, map_zero]
  have hsum (y : ⨁ i : Fin n, Block (K := K) (e i)) : (X ^ n : K[X]) • y = 0 := by
    obtain ⟨x, rfl⟩ := E.surjective y
    rw [← E.map_smul, hsmul, map_zero]
  intro i
  have hi := congrArg (DirectSum.component K[X] (Fin n) (fun i => Block (K := K) (e i)) i)
    (hsum (DirectSum.lof K[X] (Fin n) (fun i => Block (K := K) (e i)) i 1))
  simp only [map_smul, DirectSum.component.of, dite_true, map_zero] at hi
  have hmem : (X ^ n : K[X]) ∈ Ideal.span {(X : K[X]) ^ e i} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change (Ideal.Quotient.mk (Ideal.span {(X : K[X]) ^ e i})) ((X ^ n : K[X]) * 1) = 0 at hi
    simpa only [mul_one] using hi
  have hdvd : (X : K[X]) ^ e i ∣ X ^ n := Ideal.mem_span_singleton.mp hmem
  simpa only [natDegree_X_pow] using
    Polynomial.natDegree_le_of_dvd hdvd (pow_ne_zero n Polynomial.X_ne_zero)

theorem bounded_nilpotent_decomposition {n : ℕ} (b : Module.Basis (Fin n) K V)
    (f : Module.End K V) (hf : IsNilpotent f) :
    ∃ e : Fin n → Fin (n + 1),
      Nonempty (Module.AEval' f ≃ₗ[K[X]] ⨁ i : Fin n, Block (K := K) (e i).val) := by
  obtain ⟨e, ⟨E⟩⟩ := nilpotent_decomposition b f hf
  let e' : Fin n → Fin (n + 1) := fun i => ⟨e i, Nat.lt_succ_of_le (exponents_le_dim b f hf e E i)⟩
  exact ⟨e', ⟨E⟩⟩

theorem intertwiner_of_module_equiv (f g : Module.End K V)
    (E : Module.AEval' f ≃ₗ[K[X]] Module.AEval' g) :
    ∃ L : V ≃ₗ[K] V, ∀ v, L (f v) = g (L v) := by
  refine ⟨(Module.AEval'.of f).trans ((E.restrictScalars K).trans (Module.AEval'.of g).symm), ?_⟩
  intro v
  change (Module.AEval'.of g).symm (E (Module.AEval'.of f (f v))) =
    g ((Module.AEval'.of g).symm (E (Module.AEval'.of f v)))
  rw [← Module.AEval'.X_smul_of, E.map_smul, Module.AEval'.of_symm_X_smul]

theorem finite_nilpotent_similarity_types {n : ℕ} (b : Module.Basis (Fin n) K V) :
    ∃ S : Set (Module.End K V), S.Finite ∧
      (∀ g ∈ S, IsNilpotent g) ∧
      ∀ f : Module.End K V, IsNilpotent f →
        ∃ g ∈ S, ∃ L : V ≃ₗ[K] V, ∀ v, L (f v) = g (L v) := by
  classical
  let Realized (e : Fin n → Fin (n + 1)) : Prop :=
    ∃ f : Module.End K V, IsNilpotent f ∧
      Nonempty (Module.AEval' f ≃ₗ[K[X]] ⨁ i : Fin n, Block (K := K) (e i).val)
  let T := {e : Fin n → Fin (n + 1) // Realized e}
  let repr : T → Module.End K V := fun t => t.property.choose
  have hr (t : T) : IsNilpotent (repr t) ∧
      Nonempty (Module.AEval' (repr t) ≃ₗ[K[X]] ⨁ i : Fin n, Block (K := K) (t.val i).val) :=
    t.property.choose_spec
  refine ⟨Set.range repr, Set.finite_range repr, ?_, ?_⟩
  · rintro g ⟨t, rfl⟩
    exact (hr t).1
  · intro f hf
    obtain ⟨e, ⟨E⟩⟩ := bounded_nilpotent_decomposition b f hf
    let t : T := ⟨e, f, hf, ⟨E⟩⟩
    obtain ⟨F⟩ := (hr t).2
    exact ⟨repr t, ⟨t, rfl⟩, intertwiner_of_module_equiv f (repr t) (E.trans F.symm)⟩

theorem unit_conjugacy_of_intertwiner (f g : Module.End K V)
    (L : V ≃ₗ[K] V) (hL : ∀ v, L (f v) = g (L v)) :
    ∃ U : (Module.End K V)ˣ, g = (U : Module.End K V) * f * (↑U⁻¹ : Module.End K V) := by
  let U := (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm L
  have hu : (U : Module.End K V) = L.toLinearMap := rfl
  have h : (U : Module.End K V) * f = g * (U : Module.End K V) := by
    ext v
    exact hL v
  refine ⟨U, ?_⟩
  rw [h, mul_assoc, Units.mul_inv, mul_one]

end Nilpotent

section Matrices
variable {K : Type*} [Field K]

theorem finite_nilpotent_matrix_orbits (n : ℕ) :
    ∃ S : Set (Matrix (Fin n) (Fin n) K), S.Finite ∧
      (∀ B ∈ S, IsNilpotent B) ∧
      ∀ A : Matrix (Fin n) (Fin n) K, IsNilpotent A →
        ∃ B ∈ S, ∃ U : (Matrix (Fin n) (Fin n) K)ˣ,
          B = (U : Matrix (Fin n) (Fin n) K) * A * (↑U⁻¹ : Matrix (Fin n) (Fin n) K) := by
  classical
  let E : Matrix (Fin n) (Fin n) K ≃ₐ[K] Module.End K (Fin n → K) := Matrix.toLinAlgEquiv'
  obtain ⟨S, hS, hn, hc⟩ := finite_nilpotent_similarity_types (Pi.basisFun K (Fin n))
  refine ⟨E.symm '' S, hS.image E.symm, ?_, ?_⟩
  · rintro B ⟨g, hg, rfl⟩
    exact (hn g hg).map E.symm
  · intro A hA
    obtain ⟨g, hg, L, hL⟩ := hc (E A) (hA.map E)
    obtain ⟨U, hU⟩ := unit_conjugacy_of_intertwiner (E A) g L hL
    let W := Units.map E.symm.toRingHom.toMonoidHom U
    refine ⟨E.symm g, ⟨g, hg, rfl⟩, W, ?_⟩
    change E.symm g = E.symm (U : Module.End K (Fin n → K)) * A *
      E.symm (↑U⁻¹ : Module.End K (Fin n → K))
    rw [hU, map_mul, map_mul, E.symm_apply_apply]

end Matrices
end PermanentBorder.NilpotentOrbits

namespace PermanentBorder.NilpotentBlocks
open Polynomial Module
open scoped DirectSum
variable {K : Type*} [Field K]

abbrev Block (e : ℕ) := K[X] ⧸ Ideal.span {(X : K[X]) ^ e}

noncomputable def blockBasis (e : ℕ) : Basis (Fin e) K (Block (K := K) e) :=
  (AdjoinRoot.powerBasis' (monic_X_pow e)).basis.reindex (finCongr (natDegree_X_pow e))

@[simp] theorem blockBasis_apply (e : ℕ) (i : Fin e) :
    blockBasis (K := K) e i = Ideal.Quotient.mk _ ((X : K[X]) ^ i.val) := by
  change ((AdjoinRoot.powerBasis' (monic_X_pow e)).basis.reindex
    (finCongr (natDegree_X_pow e))) i = AdjoinRoot.mk _ (X ^ i.val)
  rw [Basis.reindex_apply, PowerBasis.basis_eq_pow]
  simp only [AdjoinRoot.powerBasis'_gen]
  exact (map_pow (AdjoinRoot.mk _) X i.val).symm

theorem X_smul_blockBasis (e : ℕ) (i : Fin e) :
    (X : K[X]) • blockBasis (K := K) e i =
      if h : i.val + 1 < e then blockBasis e ⟨i.val + 1, h⟩ else 0 := by
  rw [blockBasis_apply]
  change Ideal.Quotient.mk _ ((X : K[X]) * X ^ i.val) = _
  rw [← pow_succ']
  split_ifs with h
  · exact (blockBasis_apply e ⟨i.val + 1, h⟩).symm
  · have he : i.val + 1 = e := by omega
    rw [he]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (Set.mem_singleton _)

noncomputable def sumBasis {n : ℕ} (e : Fin n → ℕ) :
    Basis (Σ i : Fin n, Fin (e i)) K (⨁ i : Fin n, Block (K := K) (e i)) :=
  DFinsupp.basis (fun i => blockBasis (e i))

@[simp] theorem sumBasis_apply {n : ℕ} (e : Fin n → ℕ)
    (i : Fin n) (j : Fin (e i)) :
    sumBasis (K := K) e ⟨i,j⟩ =
      DirectSum.lof K (Fin n) (fun i => Block (K := K) (e i)) i (blockBasis (e i) j) := by
  classical
  simp [sumBasis, DFinsupp.basis, Basis.coe_ofRepr]
  rfl

noncomputable def action {n : ℕ} (e : Fin n → ℕ) :
    Module.End K (⨁ i : Fin n, Block (K := K) (e i)) where
  toFun x := (X : K[X]) • x
  map_add' := smul_add _
  map_smul' := by intro a x; exact smul_comm _ _ _

@[simp] theorem action_sumBasis {n : ℕ} (e : Fin n → ℕ)
    (i : Fin n) (j : Fin (e i)) :
    action (K := K) e (sumBasis e ⟨i,j⟩) =
      if h : j.val + 1 < e i then sumBasis e ⟨i,⟨j.val + 1,h⟩⟩ else 0 := by
  classical
  rw [sumBasis_apply]
  change (X : K[X]) • DirectSum.lof K (Fin n) (fun i => Block (K := K) (e i)) i (blockBasis (e i) j) = _
  have hmap := (DirectSum.lof K[X] (Fin n) (fun i => Block (K := K) (e i)) i).map_smul
    (X : K[X]) (blockBasis (e i) j)
  change DirectSum.lof K (Fin n) (fun i => Block (K := K) (e i)) i ((X : K[X]) • blockBasis (e i) j) =
    (X : K[X]) • DirectSum.lof K (Fin n) (fun i => Block (K := K) (e i)) i
      (blockBasis (e i) j) at hmap
  rw [← hmap, X_smul_blockBasis]
  split_ifs with h
  · exact (sumBasis_apply e i ⟨j.val + 1,h⟩).symm
  · exact map_zero _

def shiftMatrix {n : ℕ} (e : Fin n → ℕ) :
    Matrix (Σ i : Fin n, Fin (e i)) (Σ i : Fin n, Fin (e i)) K :=
  fun a b => if a.1 = b.1 ∧ a.2.val = b.2.val + 1 then 1 else 0

@[simp] theorem shiftMatrix_map {L : Type*} [Field L] (φ : K →+* L)
    {n : ℕ} (e : Fin n → ℕ) :
    (shiftMatrix (K := K) e).map φ = shiftMatrix (K := L) e := by
  ext a b
  simp [shiftMatrix]

theorem toMatrix_action {n : ℕ} (e : Fin n → ℕ) :
    LinearMap.toMatrix (sumBasis (K := K) e) (sumBasis e) (action e) = shiftMatrix e := by
  classical
  ext ⟨a,i⟩ ⟨b,j⟩
  simp only [LinearMap.toMatrix_apply, action_sumBasis]
  split_ifs with h
  · simp only [Basis.repr_self, Finsupp.single_apply]
    by_cases hab : a = b
    · subst b
      simp [shiftMatrix, Fin.ext_iff, eq_comm]
    · have hba : b ≠ a := Ne.symm hab
      simp [shiftMatrix, hab, hba]
  · simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    simp only [shiftMatrix]
    split_ifs with hab
    · obtain ⟨rfl, hij⟩ := hab
      omega
    · rfl

end PermanentBorder.NilpotentBlocks

namespace PermanentBorder.NilpotentBlocks
open Polynomial Module
open scoped DirectSum
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem toMatrix_of_intertwiner {W ι : Type*} [AddCommGroup W] [Module K W]
    [Fintype ι] [DecidableEq ι] (b : Basis ι K W) (f : Module.End K V)
    (g : Module.End K W) (L : V ≃ₗ[K] W) (hL : ∀ v, L (f v) = g (L v)) :
    LinearMap.toMatrix (b.map L.symm) (b.map L.symm) f = LinearMap.toMatrix b b g := by
  rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right]
  congr 1
  apply LinearMap.ext
  intro x
  change L (f (L.symm x)) = g x
  rw [hL, L.apply_symm_apply]

theorem shift_basis_of_equiv {n : ℕ} (e : Fin n → ℕ) (f : Module.End K V)
    (L : V ≃ₗ[K] ⨁ i : Fin n, Block (K := K) (e i))
    (hL : ∀ v, L (f v) = action e (L v)) :
    ∃ b : Basis (Σ i : Fin n, Fin (e i)) K V,
      LinearMap.toMatrix b b f = shiftMatrix e := by
  classical
  refine ⟨(sumBasis e).map L.symm, ?_⟩
  have ht := toMatrix_of_intertwiner (K := K) (V := V)
    (W := ⨁ i : Fin n, Block (K := K) (e i)) (ι := Σ i : Fin n, Fin (e i))
    (sumBasis (K := K) e) f (action (K := K) e) L hL
  exact ht.trans (toMatrix_action (K := K) e)

theorem exists_shift_basis {n : ℕ} (b₀ : Basis (Fin n) K V)
    (f : Module.End K V) (hf : IsNilpotent f) :
    ∃ e : Fin n → ℕ, (∑ i, e i) = n ∧
      ∃ b : Basis (Σ i : Fin n, Fin (e i)) K V,
        LinearMap.toMatrix b b f = shiftMatrix e := by
  classical
  obtain ⟨e, ⟨E⟩⟩ := NilpotentOrbits.nilpotent_decomposition b₀ f hf
  let L : V ≃ₗ[K] ⨁ i : Fin n, Block (K := K) (e i) :=
    (Module.AEval'.of f).trans (E.restrictScalars K)
  have hL (v : V) : L (f v) = action e (L v) := by
    change E (Module.AEval'.of f (f v)) = (X : K[X]) • E (Module.AEval'.of f v)
    rw [← Module.AEval'.X_smul_of, E.map_smul]
  obtain ⟨b, hb⟩ := shift_basis_of_equiv e f L hL
  refine ⟨e, ?_, b, hb⟩
  have hc := (Module.finrank_eq_card_basis b).symm.trans
    (Module.finrank_eq_card_basis b₀)
  simpa only [Fintype.card_sigma, Fintype.card_fin] using hc

end PermanentBorder.NilpotentBlocks

namespace PermanentBorder.NilpotentBlocks
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def indexEquiv {n : ℕ} (e : Fin n → ℕ) (he : (∑ i, e i) = n) :
    (Σ i : Fin n, Fin (e i)) ≃ Fin n :=
  Fintype.equivFinOfCardEq (by simpa only [Fintype.card_sigma, Fintype.card_fin] using he)

noncomputable def shapeMatrix {n : ℕ} (e : Fin n → ℕ) (he : (∑ i, e i) = n) :
    Matrix (Fin n) (Fin n) K :=
  (shiftMatrix (K := K) e).reindex (indexEquiv e he) (indexEquiv e he)

@[simp] theorem shapeMatrix_map {L : Type*} [Field L] (φ : K →+* L)
    {n : ℕ} (e : Fin n → ℕ) (he : (∑ i, e i) = n) :
    (shapeMatrix (K := K) e he).map φ = shapeMatrix (K := L) e he := by
  ext i j
  simp [shapeMatrix, Matrix.reindex_apply, shiftMatrix]

theorem exists_shape_basis {n : ℕ} (b₀ : Basis (Fin n) K V)
    (f : Module.End K V) (hf : IsNilpotent f) :
    ∃ e : Fin n → ℕ, ∃ he : (∑ i, e i) = n,
      ∃ b : Basis (Fin n) K V, LinearMap.toMatrix b b f = shapeMatrix e he := by
  classical
  obtain ⟨e, he, b, hb⟩ := exists_shift_basis b₀ f hf
  refine ⟨e, he, b.reindex (indexEquiv e he), ?_⟩
  ext i j
  simpa only [LinearMap.toMatrix_apply, Basis.reindex_apply, Basis.repr_reindex_apply,
    shapeMatrix, Matrix.reindex_apply, Matrix.submatrix_apply] using
      congrArg (fun M => M ((indexEquiv e he).symm i) ((indexEquiv e he).symm j)) hb

theorem matrix_conjugacy_of_basis {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (b : Basis (Fin n) K (Fin n → K)) :
    ∃ U : (Matrix (Fin n) (Fin n) K)ˣ,
      LinearMap.toMatrix b b (Matrix.toLinAlgEquiv' A) =
        (U : Matrix (Fin n) (Fin n) K) * A * (↑U⁻¹ : Matrix (Fin n) (Fin n) K) := by
  classical
  let E : Matrix (Fin n) (Fin n) K ≃ₐ[K] Module.End K (Fin n → K) := Matrix.toLinAlgEquiv'
  let B := LinearMap.toMatrix b b (E A)
  have hL (v : Fin n → K) : b.equivFun (E A v) = E B (b.equivFun v) := by
    change b.repr (E A v) = B.mulVec (b.repr v)
    exact (LinearMap.toMatrix_mulVec_repr b b (E A) v).symm
  obtain ⟨U, hU⟩ := NilpotentOrbits.unit_conjugacy_of_intertwiner (E A) (E B) b.equivFun hL
  let W := Units.map E.symm.toRingHom.toMonoidHom U
  refine ⟨W, ?_⟩
  change B = E.symm (U : Module.End K (Fin n → K)) * A *
    E.symm (↑U⁻¹ : Module.End K (Fin n → K))
  have h := congrArg E.symm hU
  simpa only [map_mul, E.symm_apply_apply] using h

theorem canonical_nilpotent_form (K : Type*) [Field K] {L : Type*} [Field L]
    (φ : K →+* L) {n : ℕ} (A : Matrix (Fin n) (Fin n) L) (hA : IsNilpotent A) :
    ∃ e : Fin n → ℕ, ∃ he : (∑ i, e i) = n,
      ∃ U : (Matrix (Fin n) (Fin n) L)ˣ,
        (shapeMatrix (K := K) e he).map φ =
          (U : Matrix (Fin n) (Fin n) L) * A * (↑U⁻¹ : Matrix (Fin n) (Fin n) L) := by
  obtain ⟨e, he, b, hb⟩ := exists_shape_basis (Pi.basisFun L (Fin n))
    (Matrix.toLinAlgEquiv' A) (hA.map Matrix.toLinAlgEquiv')
  obtain ⟨U, hU⟩ := matrix_conjugacy_of_basis A b
  exact ⟨e, he, U, by rw [shapeMatrix_map, ← hb]; exact hU⟩

end PermanentBorder.NilpotentBlocks

end OAI
