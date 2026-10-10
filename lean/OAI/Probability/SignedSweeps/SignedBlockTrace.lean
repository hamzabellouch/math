import OAI.Probability.SignedSweeps.GroupedDensity
import OAI.Probability.SignedSweeps.BlockPermutations

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
local instance (priority := 2000) signedBlockTraceWordDecidableEq {C : Type*} (p : ℕ) : DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) signedBlockTraceSumDecidableEq {C D : Type*} : DecidableEq (C ⊕ D) := Classical.decEq _
variable {J C : Type*} [Fintype J] [Fintype C] {p : ℕ} {k : J → ℕ}

omit [Fintype J] [Fintype C] in
@[simp] lemma groupWordEquiv_permutation (e : (Σ j, Fin (k j)) ≃ Fin p)
    (w : Fin p → C) (g : ∀ j, SymmetricGroup (k j)) (j : J) :
    groupWordEquiv e (w ∘ blockPermutation e g) j = (groupWordEquiv e w j) ∘ g j := by
  funext i
  simp only [groupWordEquiv, Equiv.coe_fn_mk, Function.comp_apply, blockPermutation_apply]

omit [Fintype J] [Fintype C] in
lemma group_parity_eq (e : (Σ j, Fin (k j)) ≃ Fin p)
    (w z : Fin p → C ⊕ C)
    (h : ∀ j, wordEvenSites (groupWordEquiv e w j) = wordEvenSites (groupWordEquiv e z j)) :
    wordEvenSites w = wordEvenSites z := by
  ext i
  obtain ⟨⟨j,a⟩,rfl⟩ := e.surjective i
  have hh := Finset.ext_iff.mp (h j) a
  simpa only [mem_wordEvenSites, groupWordEquiv, Equiv.coe_fn_mk] using hh

def blockOddEquiv (e : (Σ j, Fin (k j)) ≃ Fin p) (w : Fin p → C ⊕ C) :
    (Σ j, {i : Fin (k j) // i ∉ wordEvenSites (groupWordEquiv e w j)}) ≃
      {i : Fin p // i ∉ wordEvenSites w} where
  toFun x := ⟨e ⟨x.1,x.2.1⟩, by
    simpa only [mem_wordEvenSites, groupWordEquiv, Equiv.coe_fn_mk] using x.2.2⟩
  invFun i := ⟨(e.symm i).1, ⟨(e.symm i).2, by
    simpa only [mem_wordEvenSites, groupWordEquiv, Equiv.coe_fn_mk,
      Sigma.eta, Equiv.apply_symm_apply] using i.2⟩⟩
  left_inv x := by
    have hinj : Function.Injective (fun x : Σ j,
        {i : Fin (k j) // i ∉ wordEvenSites (groupWordEquiv e w j)} =>
        (⟨x.1,x.2.1⟩ : Σ j, Fin (k j))) := by
      rintro ⟨j,i,hi⟩ ⟨a,b,hb⟩ hh
      obtain ⟨rfl,hh⟩ := Sigma.mk.inj_iff.mp hh
      have hh := eq_of_heq hh
      change i = b at hh
      subst b
      rfl
    apply hinj
    exact e.symm_apply_apply ⟨x.1,x.2.1⟩
  right_inv i := by apply Subtype.ext; exact e.apply_symm_apply i

omit [Fintype C] in
theorem wordPhase_block_fixedParity (e : (Σ j, Fin (k j)) ≃ Fin p)
    (w : Fin p → C ⊕ C) (g : ∀ j, SymmetricGroup (k j))
    (h : ∀ j, wordEvenSites ((groupWordEquiv e w j) ∘ g j) = wordEvenSites (groupWordEquiv e w j)) :
    wordPhase (blockPermutation e g) w = ∏ j, wordPhase (g j) (groupWordEquiv e w j) := by
  have hp : wordEvenSites (w ∘ blockPermutation e g) = wordEvenSites w :=
    group_parity_eq e _ _ (by intro j; rw [groupWordEquiv_permutation, h j])
  have hm (j) (i : Fin (k j)) :
      i ∈ wordEvenSites (groupWordEquiv e w j) ↔ g j i ∈ wordEvenSites (groupWordEquiv e w j) := by
    rw [← wordEvenSites_comp_mem, h j]
  have hM (i : Fin p) : i ∈ wordEvenSites w ↔ blockPermutation e g i ∈ wordEvenSites w := by
    rw [← wordEvenSites_comp_mem, hp]
  let a (j) := oddPositionSetEquiv (g j) (wordEvenSites (groupWordEquiv e w j))
    (wordEvenSites (groupWordEquiv e w j)) (hm j)
  let A := oddPositionSetEquiv (blockPermutation e g) (wordEvenSites w) (wordEvenSites w) hM
  have he : A = (blockOddEquiv e w).permCongr (sigmaPermutation a) := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    change blockPermutation e g i =
      e ⟨(e.symm i).1, g (e.symm i).1 (e.symm i).2⟩
    conv_lhs => rw [← e.apply_symm_apply (i : Fin p)]
    exact blockPermutation_apply e g _ _
  have hw : wordPhase (blockPermutation e g) w = complexEquivSign A :=
    oddPositionSetEquiv_sign_congr _ rfl hp _ _
  have hl (j) : wordPhase (g j) (groupWordEquiv e w j) = complexEquivSign (a j) :=
    oddPositionSetEquiv_sign_congr _ rfl (h j) _ _
  rw [hw]
  simp only [hl, complexEquivSign, equivSign_perm, he, Equiv.Perm.sign_permCongr,
]
  have hf := sign_sigmaPermutation a
  have hc := congrArg (fun z : ℤˣ => ((z : ℤ) : ℂ)) hf
  simp only [Units.coe_prod, Int.cast_prod] at hc
  convert hc using 1
  congr 3
  congr 1
  exact Subsingleton.elim _ _

lemma signedWord_left_matrix (g : SymmetricGroup p)
    (A : WordSpace p (C ⊕ C) →ₗ[ℂ] WordSpace p (C ⊕ C))
    (w z : Fin p → C ⊕ C) :
    wordMatrixEquiv p (C ⊕ C) (signedWordRepresentation p C g * A) w z =
      wordPhase g w * wordMatrixEquiv p (C ⊕ C) A (w ∘ g) z := by
  simp only [wordMatrixEquiv, LinearMap.toMatrixOrthonormal_apply_apply,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left, map_one, one_mul,
    Module.End.mul_apply, signedWordRepresentation_apply]

lemma signedWord_trace (g : SymmetricGroup p)
    (A : WordSpace p (C ⊕ C) →ₗ[ℂ] WordSpace p (C ⊕ C)) :
    LinearMap.trace ℂ (WordSpace p (C ⊕ C)) (A * signedWordRepresentation p C g) =
      ∑ w, wordPhase g w * wordMatrixEquiv p (C ⊕ C) A (w ∘ g) w := by
  rw [LinearMap.trace_mul_comm, ← wordMatrix_trace]
  simp only [Matrix.trace, Matrix.diag, signedWord_left_matrix]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
local instance (priority := 2000) groupedPairProjectionWordDecidableEq {C : Type*} (p : ℕ) : DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) groupedPairProjectionSumDecidableEq {C D : Type*} : DecidableEq (C ⊕ D) := Classical.decEq _
variable {J C : Type*} [Fintype J] [Fintype C] {p : ℕ} {k : J → ℕ}
variable {u v : J → ℕ}

lemma groupedPairTypeProjection_matrix (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (a : ∀ j, Partition (u j)) (b : ∀ j, Partition (v j))
    (w z : Fin p → C ⊕ C) :
    wordMatrixEquiv p (C ⊕ C) (groupedPairTypeProjection e h a b) w z =
      ∏ j, wordMatrixEquiv (k j) (C ⊕ C) (pairTypeProjection (h j) (a j) (b j) C)
        (groupWordEquiv e w j) (groupWordEquiv e z j) := by
  change wordMatrixEquiv p (C ⊕ C) ((wordMatrixEquiv p (C ⊕ C)).symm _) w z = _
  rw [StarAlgEquiv.apply_symm_apply]
  rfl

lemma groupedPairTypeProjection_local_parity_off (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (a : ∀ j, Partition (u j)) (b : ∀ j, Partition (v j))
    (w z : Fin p → C ⊕ C) (j : J)
    (hwz : wordEvenSites (groupWordEquiv e w j) ≠ wordEvenSites (groupWordEquiv e z j)) :
    wordMatrixEquiv p (C ⊕ C) (groupedPairTypeProjection e h a b) w z = 0 := by
  rw [groupedPairTypeProjection_matrix]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (pairTypeProjection_parity_off (h j) (a j) (b j) _ _ hwz)

lemma groupedPairTypeProjection_parity_off (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (a : ∀ j, Partition (u j)) (b : ∀ j, Partition (v j))
    (w z : Fin p → C ⊕ C) (hwz : wordEvenSites w ≠ wordEvenSites z) :
    wordMatrixEquiv p (C ⊕ C) (groupedPairTypeProjection e h a b) w z = 0 := by
  have hh : ∃ j, wordEvenSites (groupWordEquiv e w j) ≠ wordEvenSites (groupWordEquiv e z j) := by
    by_contra hh
    push Not at hh
    exact hwz (group_parity_eq e w z hh)
  obtain ⟨j,hj⟩ := hh
  exact groupedPairTypeProjection_local_parity_off e h a b w z j hj

theorem grouped_signed_type_trace (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (a : ∀ j, Partition (u j)) (b : ∀ j, Partition (v j))
    (g : ∀ j, SymmetricGroup (k j)) :
    LinearMap.trace ℂ (WordSpace p (C ⊕ C))
      (groupedPairTypeProjection e h a b * signedWordRepresentation p C (blockPermutation e g)) =
      ∏ j, LinearMap.trace ℂ (WordSpace (k j) (C ⊕ C))
        (pairTypeProjection (h j) (a j) (b j) C * signedWordRepresentation (k j) C (g j)) := by
  simp only [signedWord_trace, groupedPairTypeProjection_matrix, groupWordEquiv_permutation]
  calc
    _ = ∑ w : Fin p → C ⊕ C, ∏ j, wordPhase (g j) (groupWordEquiv e w j) *
        wordMatrixEquiv (k j) (C ⊕ C) (pairTypeProjection (h j) (a j) (b j) C)
          ((groupWordEquiv e w j) ∘ g j) (groupWordEquiv e w j) := by
      apply Finset.sum_congr rfl
      intro w _
      by_cases hp : ∀ j, wordEvenSites ((groupWordEquiv e w j) ∘ g j) = wordEvenSites (groupWordEquiv e w j)
      · rw [wordPhase_block_fixedParity e w g hp, Finset.prod_mul_distrib]
      · push Not at hp
        obtain ⟨j,hj⟩ := hp
        have hz := pairTypeProjection_parity_off (h j) (a j) (b j)
          ((groupWordEquiv e w j) ∘ g j) (groupWordEquiv e w j) hj
        have hl : (∏ j, wordMatrixEquiv (k j) (C ⊕ C)
            (pairTypeProjection (h j) (a j) (b j) C)
              ((groupWordEquiv e w j) ∘ g j) (groupWordEquiv e w j)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ j) hz
        rw [Finset.prod_mul_distrib, hl, mul_zero, mul_zero]
    _ = _ := by
      rw [Fintype.prod_sum]
      exact (groupWordEquiv (C := C ⊕ C) e).sum_comp
        (fun w => ∏ j, wordPhase (g j) (w j) *
          wordMatrixEquiv (k j) (C ⊕ C) (pairTypeProjection (h j) (a j) (b j) C)
            (w j ∘ g j) (w j))

lemma groupedPairTypeProjection_phase_commute (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (a : ∀ j, Partition (u j)) (b : ∀ j, Partition (v j))
    (g : SymmetricGroup p) :
    groupedPairTypeProjection (C:=C) e h a b * wordPhaseDiagonal g =
      wordPhaseDiagonal g * groupedPairTypeProjection e h a b := by
  apply (wordMatrixEquiv p (C ⊕ C)).injective
  change wordMatrixEquiv p (C ⊕ C) (_ * _) = wordMatrixEquiv p (C ⊕ C) (_ * _)
  rw [map_mul, map_mul, wordPhaseDiagonal_matrix]
  ext w z
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hp : wordEvenSites w = wordEvenSites z
  · rw [wordPhase_eq_of_parity g w z hp, mul_comm]
  · rw [groupedPairTypeProjection_parity_off e h a b w z hp, zero_mul, mul_zero]

lemma groupedPairTypeProjection_permutation_commute (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (a : ∀ j, Partition (u j)) (b : ∀ j, Partition (v j))
    (g : ∀ j, SymmetricGroup (k j)) :
    groupedPairTypeProjection e h a b * wordRepresentation p (C ⊕ C) (blockPermutation e g) =
      wordRepresentation p (C ⊕ C) (blockPermutation e g) * groupedPairTypeProjection e h a b := by
  apply (wordMatrixEquiv p (C ⊕ C)).injective
  change wordMatrixEquiv p (C ⊕ C) (_ * _) = wordMatrixEquiv p (C ⊕ C) (_ * _)
  rw [map_mul, map_mul, wordRepresentation_matrix]
  simp only [wordPositionMatrix, Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv,
    PEquiv.toMatrix_toPEquiv_mul]
  ext w z
  change wordMatrixEquiv p (C ⊕ C) (groupedPairTypeProjection e h a b) w (z ∘ (blockPermutation e g).symm) =
    wordMatrixEquiv p (C ⊕ C) (groupedPairTypeProjection e h a b) (w ∘ blockPermutation e g) z
  have hg : (blockPermutation e g).symm = blockPermutation e g⁻¹ := (map_inv _ _).symm
  rw [hg, groupedPairTypeProjection_matrix, groupedPairTypeProjection_matrix]
  simp only [groupWordEquiv_permutation]
  apply Finset.prod_congr rfl
  intro j _
  have ht := (mem_wordCommutant_iff _).mp (pairTypeProjection_mem_commutant (C:=C) (h j) (a j) (b j))
    (g j) (groupWordEquiv e w j) ((groupWordEquiv e z j) ∘ (g j).symm)
  simpa only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id, Pi.inv_apply, Equiv.Perm.inv_def] using ht.symm

theorem groupedPairTypeProjection_signed_commute (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (a : ∀ j, Partition (u j)) (b : ∀ j, Partition (v j))
    (g : ∀ j, SymmetricGroup (k j)) :
    groupedPairTypeProjection (C:=C) e h a b * signedWordRepresentation p C (blockPermutation e g) =
      signedWordRepresentation p C (blockPermutation e g) * groupedPairTypeProjection e h a b := by
  rw [signedWordRepresentation_eq, ← mul_assoc,
    groupedPairTypeProjection_phase_commute e h a b, mul_assoc,
    groupedPairTypeProjection_permutation_commute e h a b, ← mul_assoc]

end SignedSweeps
end

end OAI
