import Mathlib
import OAI.Probability.BinarySweep.TensorBounds.SignedBlock
import OAI.Probability.BinarySweep.Representations.IsotypicDensity
import OAI.Probability.BinarySweep.TensorBounds.PiTensorMatrices
import OAI.Probability.BinarySweep.YoungTheory.KoszulBlocks

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Signed
open Matrix Density

variable {I A : Type*} [Fintype I] [LinearOrder I]
  [Fintype A] [DecidableEq A] {n : I → ℕ} {N : ℕ}

omit [Fintype I] in
@[simp] lemma blockPerm_inv (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : ∀i, Equiv.Perm (Fin (n i))) : (blockPerm e g)⁻¹=blockPerm e (fun i => (g i)⁻¹) := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨i,a⟩,rfl⟩ := (toLex.trans e.toEquiv).surjective x
  apply (blockPerm e g).injective
  change blockPerm e g ((blockPerm e g).symm (e (toLex ⟨i,a⟩))) = _
  rw [Equiv.apply_symm_apply]
  simp

lemma signC_blocks (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : ∀i, Equiv.Perm (Fin (n i))) (β : Fin N → Bool) :
    signC β (blockPerm e g) = ∏i, signC (fun a => β (e (toLex ⟨i,a⟩))) (g i) := by
  simp only [signC,koszulSign_blocks,Units.coe_prod,Int.cast_prod]

def blockWords (e : (Σₗ i, Fin (n i)) ≃o Fin N) :
    (Fin N → A) ≃ (∀i, Fin (n i) → A) :=
  ((toLex.trans e.toEquiv).symm.arrowCongr (Equiv.refl A)).trans (Equiv.piCurry (fun _ _ => A))

omit [Fintype I] [Fintype A] [DecidableEq A] in
@[simp] lemma blockWords_apply (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (x : Fin N → A) (i : I) (a : Fin (n i)) : blockWords e x i a=x (e (toLex ⟨i,a⟩)) := rfl

omit [Fintype I] [Fintype A] [DecidableEq A] in
lemma blockWords_comp (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : ∀i, Equiv.Perm (Fin (n i))) (x : Fin N → A) :
    blockWords e (x ∘ blockPerm e g) = fun i => (blockWords e x i) ∘ g i := by
  funext i a
  simp

theorem actionMatrix_blocks (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : ∀i, Equiv.Perm (Fin (n i))) (p : A → Bool) :
    LinearMap.toMatrix' (act p (blockPerm e g)) =
      (piTensorMatrices (fun i => LinearMap.toMatrix' (act p (g i)))).submatrix
        (blockWords e) (blockWords e) := by
  ext x y
  change LinearMap.toMatrix' (act p (blockPerm e g)) x y =
    ∏i, LinearMap.toMatrix' (act p (g i)) (blockWords e x i) (blockWords e y i)
  simp only [actionMatrix_apply]
  have he : x ∘ blockPerm e g=y ↔ ∀i, (blockWords e x i) ∘ g i=blockWords e y i := by
    rw [← (blockWords e).injective.eq_iff,blockWords_comp]
    exact funext_iff
  by_cases h : x ∘ blockPerm e g=y
  · rw [ite_eq_left h,blockPerm_inv,signC_blocks]
    apply Finset.prod_congr rfl
    intro i _
    rw [ite_eq_left (he.mp h i)]
    rfl
  · rw [ite_eq_right h]
    have hh := h
    rw [he] at hh
    push Not at hh
    obtain ⟨i,hi⟩ := hh
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

end BinaryCoordinateSweeps.Signed

end

open scoped BigOperators Classical ComplexOrder MonoidAlgebra
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density Irrep Representation

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def vacuumDensity : Matrix A A ℂ := Matrix.diagonal (fun a => if a=Classical.choice (inferInstance : Nonempty A) then 1 else 0)

omit [Fintype A] in
lemma vacuumDensity_psd : (vacuumDensity (A:=A)).PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro a
  split <;> norm_num

lemma vacuumDensity_trace : (vacuumDensity (A:=A)).trace=1 := by
  simp [vacuumDensity,Matrix.trace,Matrix.diag]

omit [Fintype A] in
lemma vacuumDensity_even (p : A → Bool) (a b : A) (h : p a ≠ p b) :
    vacuumDensity a b=0 := by
  have hh : a≠b := fun he => h (congrArg p he)
  simp [vacuumDensity,hh]

abbrev LocalDensityIndex (p : A → Bool) (n : ℕ) :=
  WordType (MatchedPair p) n × (MatchedPair p → ZMod (n+1))

def localDensity (p : A → Bool) (n : ℕ) (u : LocalDensityIndex p n) : Matrix A A ℂ :=
  if n=0 then vacuumDensity else reducedPhaseDensity n (matchedEmbedding p) u.1 u.2

lemma localDensity_psd (p : A → Bool) (n : ℕ) (u : LocalDensityIndex p n) :
    (localDensity p n u).PosSemidef := by
  unfold localDensity
  split
  · exact vacuumDensity_psd
  · exact reducedPhaseDensity_psd _ _ _ _

lemma localDensity_trace (p : A → Bool) (n : ℕ) (u : LocalDensityIndex p n) :
    (localDensity p n u).trace=1 := by
  unfold localDensity
  split
  · exact vacuumDensity_trace
  · exact reducedPhaseDensity_trace n (by omega) _ (matchedEmbedding_injective p) _ _

lemma localDensity_even (p : A → Bool) (n : ℕ) (u : LocalDensityIndex p n)
    (a b : A) (h : p a ≠ p b) : localDensity p n u a b=0 := by
  unfold localDensity
  split
  · exact vacuumDensity_even p a b h
  · exact reducedPhaseDensity_even n p p (matchedEmbedding p) (fun k => k.property) _ _ a b h

omit [Nonempty A] in
lemma localDensityIndex_card (p : A → Bool) (n : ℕ) :
    Fintype.card (LocalDensityIndex p n) ≤ (n+1)^(2*(Fintype.card A)^2) := by
  have hc : Fintype.card (MatchedPair p) ≤ (Fintype.card A)^2 := by
    simpa only [Fintype.card_prod,pow_two] using Fintype.card_le_of_injective
      (matchedEmbedding p) (matchedEmbedding_injective p)
  calc
    _ = Fintype.card (WordType (MatchedPair p) n) * (n+1)^Fintype.card (MatchedPair p) := by
      rw [Fintype.card_prod,Fintype.card_fun,ZMod.card]
    _ ≤ (n+1)^Fintype.card (MatchedPair p) * (n+1)^Fintype.card (MatchedPair p) :=
      Nat.mul_le_mul_right _ (by simpa only [Fintype.card_coe] using card_types_le (A:=MatchedPair p) n)
    _ = (n+1)^(2*Fintype.card (MatchedPair p)) := by rw [two_mul,pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left 2 hc)

lemma localDensityIndex_nonempty (p : A → Bool) (n : ℕ) : Nonempty (LocalDensityIndex p n) := by
  let a : A := Classical.choice inferInstance
  exact ⟨wordType n (fun _ => ⟨(a,a),rfl⟩),fun _ => 0⟩

lemma projection_complement_psd {I : Type*} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℂ) (hP : P.IsHermitian) (hPP : P*P=P) : (1-P).PosSemidef := by
  have he : (1-P).conjTranspose*(1-P)=1-P := by
    simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,hP.eq,mul_sub,sub_mul,
      one_mul,mul_one,hPP]
    abel
  rw [← he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem local_type_density_domination (p : A → Bool) (n : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [ρ.IsIrreducible] :
    (((Module.finrank ℂ V : ℂ)*(n+1 : ℂ)^(2*(Fintype.card A)^2)) •
      (∑u : LocalDensityIndex p n, matrixTensorPower n (localDensity p n u)) -
      isotypicProjection p ρ).PosSemidef := by
  by_cases hn : n=0
  · subst n
    have : Nonempty (LocalDensityIndex p 0) := localDensityIndex_nonempty p 0
    have hc : Fintype.card (LocalDensityIndex p 0)=1 := le_antisymm
      (by simp) (Fintype.card_pos_iff.mpr inferInstance)
    have he (u : LocalDensityIndex p 0) : matrixTensorPower 0 (localDensity p 0 u)=1 := by
      ext x y
      simp [matrixTensorPower,Matrix.one_apply,Subsingleton.elim x y]
    simp only [he,Finset.sum_const,Finset.card_univ,hc,one_nsmul,Nat.cast_zero,zero_add,one_pow,mul_one]
    have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial ℂ[Equiv.Perm (Fin 0)] ρ.asModule
    have hd : (1:ℂ) ≤ (Module.finrank ℂ V : ℂ) := by
      have hh : 0 < Module.finrank ℂ V := by
        rw [← ρ.asModuleEquiv.finrank_eq]
        exact Module.finrank_pos
      exact_mod_cast hh
    have h := (Matrix.PosSemidef.one : (1 : Matrix (Fin 0 → A) (Fin 0 → A) ℂ).PosSemidef).smul
      (sub_nonneg.mpr hd)
    have hp := projection_complement_psd (isotypicProjection p ρ)
      (isotypicProjection_psd p ρ).isHermitian (projectionMatrix_idempotent _)
    convert h.add hp using 1
    simp only [sub_smul,one_smul]
    abel
  · simpa only [localDensity,ite_eq_right hn,Fintype.sum_prod_type] using
      isotypic_density_domination n (by omega) p ρ

end BinaryCoordinateSweeps.Signed

end

end OAI
