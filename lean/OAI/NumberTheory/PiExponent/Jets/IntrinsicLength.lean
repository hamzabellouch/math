import Mathlib

namespace OAI

namespace PiExponentJets.W24

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

theorem augmentation_surjective (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k) : Function.Surjective ε :=
  fun k => ⟨algebraMap K A k, hε k⟩

variable [IsLocalRing A]

theorem simple_annihilator_eq_augmentation_kernel (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k)
    {M : Type*} [AddCommGroup M] [Module A M] [IsSimpleModule A M] :
    Module.annihilator A M = RingHom.ker ε := by
  have hker : (RingHom.ker ε).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective ε (augmentation_surjective ε hε)
  exact (IsLocalRing.eq_maximalIdeal (IsSimpleModule.annihilator_isMaximal (R := A)
    (M := M))).trans (IsLocalRing.eq_maximalIdeal hker).symm

theorem simple_smul_eq_augmentation_smul (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k)
    {M : Type*} [AddCommGroup M] [Module A M] [Module K M]
    [IsScalarTower K A M] [IsSimpleModule A M] (a : A) (x : M) :
    a • x = ε a • x := by
  have ha : a - algebraMap K A (ε a) ∈ Module.annihilator A M := by
    rw [simple_annihilator_eq_augmentation_kernel ε hε]
    rw [RingHom.mem_ker, map_sub, hε, sub_self]
  have hx := Module.mem_annihilator.mp ha x
  exact sub_eq_zero.mp (by simpa only [sub_smul, algebraMap_smul] using hx)

theorem simple_over_coefficient_field (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k)
    {M : Type*} [AddCommGroup M] [Module A M] [Module K M]
    [IsScalarTower K A M] [IsSimpleModule A M] : IsSimpleModule K M := by
  apply isSimpleModule_iff_toSpanSingleton_surjective.mpr
  refine ⟨IsSimpleModule.nontrivial A M, ?_⟩
  intro x hx y
  obtain ⟨a, ha⟩ := IsSimpleModule.toSpanSingleton_surjective A hx y
  refine ⟨ε a, ?_⟩
  change ε a • x = y
  rw [← simple_smul_eq_augmentation_smul ε hε a x]
  exact ha

theorem length_eq_coefficient_length (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k)
    {M : Type*} [AddCommGroup M] [Module A M] (hM : IsFiniteLength A M) :
    ∀ [Module K M] [IsScalarTower K A M], Module.length A M = Module.length K M := by
  induction hM with
  | of_subsingleton =>
    intro _ _
    simp only [Module.length_eq_zero]
  | @of_simple_quotient M _ _ N hsimple hN ih =>
    intro _ _
    have : IsSimpleModule K (M ⧸ N) := simple_over_coefficient_field ε hε
    have hexact : Function.Exact N.subtype N.mkQ := by
      rw [LinearMap.exact_iff, Submodule.range_subtype, Submodule.ker_mkQ]
    have hA := Module.length_eq_add_of_exact N.subtype N.mkQ
      (Submodule.subtype_injective N) (Submodule.mkQ_surjective N) hexact
    have hK := Module.length_eq_add_of_exact (N.subtype.restrictScalars K)
      (N.mkQ.restrictScalars K) (Submodule.subtype_injective N)
      (Submodule.mkQ_surjective N) hexact
    calc
      Module.length A M = Module.length A N + Module.length A (M ⧸ N) := hA
      _ = Module.length K N + Module.length K (M ⧸ N) := by
        rw [ih, Module.length_eq_one A (M ⧸ N), Module.length_eq_one K (M ⧸ N)]
      _ = Module.length K M := hK.symm

theorem module_length_eq_finrank_of_augmentation (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k)
    {M : Type*} [AddCommGroup M] [Module A M] [Module K M]
    [IsScalarTower K A M] [Module.Finite K M] :
    Module.length A M = Module.finrank K M := by
  have : IsNoetherian A M := isNoetherian_of_tower K inferInstance
  have : IsArtinian A M := isArtinian_of_tower K inferInstance
  have hM : IsFiniteLength A M := isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨inferInstance, inferInstance⟩
  rw [length_eq_coefficient_length ε hε hM, Module.length_eq_finrank]

theorem ring_length_eq_finrank_of_augmentation [Module.Finite K A] (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k) :
    Module.length A A = Module.finrank K A :=
  module_length_eq_finrank_of_augmentation ε hε

end PiExponentJets.W24

end OAI
