import Mathlib

namespace OAI

namespace PiExponent.NatToIntGrading
noncomputable section
open DirectSum
variable {M σM : Type*} [AddCommGroup M] [SetLike σM M] [AddSubgroupClass σM M]
  (𝓜 : ℕ → σM) [DirectSum.Decomposition 𝓜]

def piece : ℤ → AddSubgroup M
  | .ofNat n => AddSubgroup.ofClass (𝓜 n)
  | .negSucc _ => ⊥

def component (m : M) : ∀ d, piece 𝓜 d
  | .ofNat n => ⟨DirectSum.decompose 𝓜 m n, (DirectSum.decompose 𝓜 m n).property⟩
  | .negSucc _ => 0

def support (m : M) : Finset ℤ := by
  classical
  exact (DirectSum.decompose 𝓜 m).support.image (fun n : ℕ => (n : ℤ))

theorem component_eq_zero_of_not_mem (m : M) (d : ℤ) (hd : d ∉ support 𝓜 m) :
    component 𝓜 m d = 0 := by
  classical
  cases d with
  | ofNat n =>
      apply Subtype.ext
      have hn : n ∉ (DirectSum.decompose 𝓜 m).support := by
        intro hn
        exact hd (Finset.mem_image.mpr ⟨n, hn, rfl⟩)
      change (DirectSum.decompose 𝓜 m n : M) = 0
      rw [DFinsupp.notMem_support_iff.mp hn]
      rfl
  | negSucc n => rfl

def decompositionMap : M →+ ⨁ d, piece 𝓜 d where
  toFun m := DFinsupp.mk' (component 𝓜 m) (Trunc.mk
    ⟨(support 𝓜 m).val, fun d => by
      classical
      by_cases hd : d ∈ support 𝓜 m
      · exact Or.inl hd
      · exact Or.inr (component_eq_zero_of_not_mem 𝓜 m d hd)⟩)
  map_zero' := by
    apply DFinsupp.ext
    intro d
    apply Subtype.ext
    cases d with
    | ofNat n =>
        change (DirectSum.decompose 𝓜 (0 : M) n : M) = 0
        rw [DirectSum.decompose_zero]
        rfl
    | negSucc n => rfl
  map_add' m n := by
    apply DFinsupp.ext
    intro d
    apply Subtype.ext
    cases d with
    | ofNat k =>
        change (DirectSum.decompose 𝓜 (m + n) k : M) =
          (DirectSum.decompose 𝓜 m k : M) + (DirectSum.decompose 𝓜 n k : M)
        rw [DirectSum.decompose_add]
        rfl
    | negSucc k => exact (zero_add (0 : M)).symm

@[simp] theorem decompositionMap_nat (m : M) (n : ℕ) :
    (decompositionMap 𝓜 m (n : ℤ) : M) = (DirectSum.decompose 𝓜 m n : M) := rfl

theorem decompositionMap_injective : Function.Injective (decompositionMap 𝓜) := by
  intro m n h
  apply (DirectSum.decompose 𝓜).injective
  ext k
  exact congrArg (fun z : ⨁ d, piece 𝓜 d => (z (k : ℤ) : M)) h

theorem decompositionMap_homogeneous (d : ℤ) (m : piece 𝓜 d) :
    decompositionMap 𝓜 m.val = DirectSum.of (fun d => piece 𝓜 d) d m := by
  classical
  cases d with
  | negSucc n =>
      have hm : m = 0 := Subtype.ext m.property
      subst m
      simp
  | ofNat n =>
      apply DFinsupp.ext
      intro e
      apply Subtype.ext
      cases e with
      | negSucc k =>
          rw [DirectSum.of_eq_of_ne _ _ _ (show Int.negSucc k ≠ Int.ofNat n from by intro h; cases h)]
          rfl
      | ofNat k =>
          by_cases hnk : n = k
          · subst k
            rw [DirectSum.of_eq_same]
            exact DirectSum.decompose_of_mem_same 𝓜 m.property
          · rw [DirectSum.of_eq_of_ne _ _ _ (show Int.ofNat k ≠ Int.ofNat n from
              fun h => hnk (Int.ofNat.inj h).symm)]
            exact DirectSum.decompose_of_mem_ne 𝓜 m.property hnk

instance decomposition : DirectSum.Decomposition (piece 𝓜) := by
  have hr : (decompositionMap 𝓜).comp (DirectSum.coeAddMonoidHom (piece 𝓜)) = AddMonoidHom.id _ := by
    apply DirectSum.addHom_ext
    intro d m
    simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of,
      AddMonoidHom.id_apply, decompositionMap_homogeneous]
  apply DirectSum.Decomposition.ofAddHom (piece 𝓜) (decompositionMap 𝓜) ?_ hr
  apply AddMonoidHom.ext
  intro m
  apply decompositionMap_injective 𝓜
  exact DFunLike.congr_fun hr (decompositionMap 𝓜 m)

@[simp] theorem decompose_nat (m : M) (n : ℕ) :
    (DirectSum.decompose (piece 𝓜) m (n : ℤ) : M) = (DirectSum.decompose 𝓜 m n : M) := rfl

@[simp] theorem decompose_negSucc (m : M) (n : ℕ) :
    (DirectSum.decompose (piece 𝓜) m (.negSucc n) : M) = 0 := rfl

section Scalars
variable {R σR : Type*} [Ring R] [Module R M] [SetLike σR R] [AddSubgroupClass σR R]
  (𝒜 : ℕ → σR) [SetLike.GradedSMul 𝒜 𝓜]

instance gradedSMul : SetLike.GradedSMul (piece 𝒜) (piece 𝓜) where
  smul_mem := by
    intro i j a m ha hm
    cases i with
    | negSucc n =>
        have ha' : a = 0 := ha
        rw [ha', zero_smul]
        exact zero_mem _
    | ofNat n =>
        cases j with
        | negSucc k =>
            have hm' : m = 0 := hm
            rw [hm', smul_zero]
            exact zero_mem _
        | ofNat k =>
            change a • m ∈ 𝓜 (n + k)
            exact SetLike.GradedSMul.smul_mem (show a ∈ 𝒜 n from ha) (show m ∈ 𝓜 k from hm)
end Scalars

section Ring
variable {R σR : Type*} [Ring R] [SetLike σR R] [AddSubgroupClass σR R]
  (𝒜 : ℕ → σR) [SetLike.GradedMonoid 𝒜]

instance gradedMonoid : SetLike.GradedMonoid (piece 𝒜) where
  one_mem := by
    change (1 : R) ∈ 𝒜 0
    exact SetLike.GradedOne.one_mem
  mul_mem := by
    intro i j a b ha hb
    cases i with
    | negSucc n =>
        have ha' : a = 0 := ha
        rw [ha', zero_mul]
        exact zero_mem _
    | ofNat n =>
        cases j with
        | negSucc k =>
            have hb' : b = 0 := hb
            rw [hb', mul_zero]
            exact zero_mem _
        | ofNat k =>
            change a * b ∈ 𝒜 (n + k)
            exact SetLike.mul_mem_graded (show a ∈ 𝒜 n from ha) (show b ∈ 𝒜 k from hb)
end Ring

end
end PiExponent.NatToIntGrading

end OAI
