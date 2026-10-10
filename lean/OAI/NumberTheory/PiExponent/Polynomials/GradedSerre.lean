import Mathlib
import OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher
import OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading

namespace OAI

namespace PiExponent.GradedSerre

noncomputable section
open scoped BigOperators

variable {R M ι σ : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [DecidableEq ι] [SetLike σ M] [AddSubmonoidClass σ M]
  (𝓜 : ι → σ) [DirectSum.Decomposition 𝓜]

theorem span_homogeneous_eq (K : Submodule R M) (hK : K.IsHomogeneous 𝓜) :
    Submodule.span R {x : M | x ∈ K ∧ ∃ d, x ∈ 𝓜 d} = K := by
  classical
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun x hx => hx.1)
  · intro x hx
    rw [← DirectSum.sum_support_decompose 𝓜 x]
    apply Submodule.sum_mem
    intro d hd
    exact Submodule.subset_span ⟨hK d hx, d, (DirectSum.decompose 𝓜 x d).property⟩

theorem exists_finite_homogeneous_generators (K : Submodule R M)
    (hK : K.IsHomogeneous 𝓜) (hfg : K.FG) :
    ∃ (s : Finset M) (degree : s → ι),
      (∀ j : s, j.val ∈ K ∧ j.val ∈ 𝓜 (degree j)) ∧
      Submodule.span R (s : Set M) = K := by
  classical
  have hspan := span_homogeneous_eq 𝓜 K hK
  have hfg' : (Submodule.span R {x : M | x ∈ K ∧ ∃ d, x ∈ 𝓜 d}).FG := by
    rwa [hspan]
  obtain ⟨s, hs, hspan'⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset _).mp hfg'
  have hdegree : ∀ j : s, ∃ d, j.val ∈ K ∧ j.val ∈ 𝓜 d := by
    intro j
    obtain ⟨hj, d, hd⟩ := hs j.property
    exact ⟨d, hj, hd⟩
  choose degree hdegree using hdegree
  exact ⟨s, degree, hdegree, hspan'.symm.trans hspan⟩

theorem exists_homogeneous_free_cover [Module.Finite R M] :
    ∃ (s : Finset M) (degree : s → ι),
      (∀ j : s, j.val ∈ 𝓜 (degree j)) ∧
      Function.Surjective (Fintype.linearCombination R (fun j : s => j.val)) := by
  classical
  have htop : (⊤ : Submodule R M).IsHomogeneous 𝓜 := fun _ _ _ => trivial
  obtain ⟨s, d, hs, hspan⟩ := exists_finite_homogeneous_generators 𝓜 ⊤ htop
    Module.Finite.fg_top
  refine ⟨s, d, fun j => (hs j).2, ?_⟩
  rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
  have hr : Set.range (fun j : s => j.val) = (s : Set M) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact j.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [hr]
  exact hspan

theorem kernel_homogeneous
    {N τ : Type*} [AddCommMonoid N] [Module R N]
    [SetLike τ N] [AddSubmonoidClass τ N]
    (𝓝 : ι → τ) [DirectSum.Decomposition 𝓝]
    (f : M →ₗ[R] N)
    (hf : ∀ d x, f (DirectSum.decompose 𝓜 x d : M) =
      (DirectSum.decompose 𝓝 (f x) d : N)) :
    f.ker.IsHomogeneous 𝓜 := by
  intro d x hx
  change f (DirectSum.decompose 𝓜 x d : M) = 0
  rw [hf, LinearMap.mem_ker.mp hx, DirectSum.decompose_zero]
  rfl

theorem exists_finite_homogeneous_relations [IsNoetherianRing R] [Module.Finite R M]
    {N τ : Type*} [AddCommMonoid N] [Module R N]
    [SetLike τ N] [AddSubmonoidClass τ N]
    (𝓝 : ι → τ) [DirectSum.Decomposition 𝓝]
    (f : M →ₗ[R] N)
    (hf : ∀ d x, f (DirectSum.decompose 𝓜 x d : M) =
      (DirectSum.decompose 𝓝 (f x) d : N)) :
    ∃ (s : Finset M) (degree : s → ι),
      (∀ j : s, f j.val = 0 ∧ j.val ∈ 𝓜 (degree j)) ∧
      Submodule.span R (s : Set M) = f.ker := by
  obtain ⟨s, d, hs, hspan⟩ := exists_finite_homogeneous_generators 𝓜 f.ker
    (kernel_homogeneous 𝓜 𝓝 f hf) (IsNoetherian.noetherian f.ker)
  exact ⟨s, d, fun j => ⟨LinearMap.mem_ker.mp (hs j).1, (hs j).2⟩, hspan⟩

section IntegerGrading
variable {A P σA σP : Type*} [Ring A] [AddCommGroup P] [Module A P]
  [SetLike σA A] [AddSubgroupClass σA A]
  [SetLike σP P] [AddSubgroupClass σP P]
  (𝒜 : ℤ → σA) (𝓟 : ℤ → σP)
  [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition 𝓟]
  [SetLike.GradedSMul 𝒜 𝓟]

theorem decompose_smul_homogeneous {m : P} {w : ℤ} (hm : m ∈ 𝓟 w)
    (a : A) (d : ℤ) :
    (DirectSum.decompose 𝓟 (a • m) d : P) =
      (DirectSum.decompose 𝒜 a (d - w) : A) • m := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous a =>
      rename_i k
      have ham : (a : A) • m ∈ 𝓟 (k + w) :=
        SetLike.GradedSMul.smul_mem a.property hm
      by_cases h : k + w = d
      · have hk : k = d - w := by omega
        rw [← h, DirectSum.decompose_of_mem_same 𝓟 ham]
        rw [show k + w - w = k by omega, DirectSum.decompose_of_mem_same 𝒜 a.property]
      · rw [DirectSum.decompose_of_mem_ne 𝓟 ham h,
          DirectSum.decompose_of_mem_ne 𝒜 a.property (by omega), zero_smul]
  | add a b ha hb =>
      simp only [add_smul, DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add]
      rw [ha, hb]

theorem free_cover_degree_compatible {J : Type*} [Fintype J]
    (w : J → ℤ) (v : J → P) (hv : ∀ j, v j ∈ 𝓟 (w j))
    (d : ℤ) (a : J → A) :
    Fintype.linearCombination A v
        (DirectSum.decompose (ShiftedFreeGrading.piece 𝒜 w) a d : J → A) =
      (DirectSum.decompose 𝓟 (Fintype.linearCombination A v a) d : P) := by
  classical
  simp only [Fintype.linearCombination_apply, DirectSum.decompose_sum,
    DirectSum.sum_apply, AddSubmonoidClass.coe_finsetSum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [ShiftedFreeGrading.decompose_apply]
  exact (decompose_smul_homogeneous 𝒜 𝓟 (hv j) (a j) d).symm

theorem exists_graded_free_map (K : Submodule A P) (hK : K.IsHomogeneous 𝓟)
    (hfg : K.FG) :
    ∃ (n : ℕ) (w : Fin n → ℤ) (f : (Fin n → A) →ₗ[A] P),
      LinearMap.range f = K ∧
      ∀ d x, f (DirectSum.decompose (ShiftedFreeGrading.piece 𝒜 w) x d : Fin n → A) =
        (DirectSum.decompose 𝓟 (f x) d : P) := by
  classical
  obtain ⟨s, degree, hs, hspan⟩ := exists_finite_homogeneous_generators 𝓟 K hK hfg
  let e : s ≃ Fin s.card := s.equivFin
  let v : Fin s.card → P := fun j => (e.symm j).val
  let w : Fin s.card → ℤ := fun j => degree (e.symm j)
  refine ⟨s.card, w, Fintype.linearCombination A v, ?_, ?_⟩
  · rw [Fintype.range_linearCombination]
    have hv : Set.range v = (s : Set P) := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        exact (e.symm j).property
      · intro hx
        refine ⟨e ⟨x, hx⟩, ?_⟩
        simp only [v, Equiv.symm_apply_apply]
    rw [hv]
    exact hspan
  · exact free_cover_degree_compatible 𝒜 𝓟 w v (fun j => (hs (e.symm j)).2)

instance shiftedFreeGradedSMul [SetLike.GradedMonoid 𝒜] {J : Type*} [Fintype J]
    (w : J → ℤ) : SetLike.GradedSMul 𝒜 (ShiftedFreeGrading.piece 𝒜 w) where
  smul_mem := by
    intro i d a f ha hf j
    change a * f j ∈ 𝒜 (i + d - w j)
    have h : a * f j ∈ 𝒜 (i + (d - w j)) :=
      SetLike.GradedMul.mul_mem ha (hf j)
    convert h using 1
    congr 1
    omega

theorem exists_graded_free_presentation [SetLike.GradedMonoid 𝒜]
    [IsNoetherianRing A] [Module.Finite A P] :
    ∃ (n₀ n₁ : ℕ) (w₀ : Fin n₀ → ℤ) (w₁ : Fin n₁ → ℤ)
      (f₀ : (Fin n₀ → A) →ₗ[A] P)
      (f₁ : (Fin n₁ → A) →ₗ[A] (Fin n₀ → A)),
      Function.Surjective f₀ ∧ LinearMap.range f₁ = f₀.ker ∧
      (∀ d x, f₀ (DirectSum.decompose (ShiftedFreeGrading.piece 𝒜 w₀) x d : Fin n₀ → A) =
        (DirectSum.decompose 𝓟 (f₀ x) d : P)) ∧
      (∀ d x, f₁ (DirectSum.decompose (ShiftedFreeGrading.piece 𝒜 w₁) x d : Fin n₁ → A) =
        (DirectSum.decompose (ShiftedFreeGrading.piece 𝒜 w₀) (f₁ x) d : Fin n₀ → A)) := by
  classical
  have htop : (⊤ : Submodule A P).IsHomogeneous 𝓟 := fun _ _ _ => trivial
  obtain ⟨n₀, w₀, f₀, hf₀, hg₀⟩ := exists_graded_free_map 𝒜 𝓟 ⊤ htop Module.Finite.fg_top
  have hker := kernel_homogeneous (ShiftedFreeGrading.piece 𝒜 w₀) 𝓟 f₀ hg₀
  obtain ⟨n₁, w₁, f₁, hf₁, hg₁⟩ := exists_graded_free_map 𝒜
    (ShiftedFreeGrading.piece 𝒜 w₀) f₀.ker hker (IsNoetherian.noetherian f₀.ker)
  exact ⟨n₀, n₁, w₀, w₁, f₀, f₁, LinearMap.range_eq_top.mp hf₀, hf₁, hg₀, hg₁⟩

end IntegerGrading

section FreeTwistCech
open ProjectiveMonomialCech ProjectiveMonomialCechHigher
variable {J C B : Type*} [Fintype J] [Fintype C] [AddCommGroup B]

theorem eventually_free_twist_cech_exact (w : J → ℤ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ q : ℕ,
      ∀ c : (j : J) → Cochain C (Laurent C B ((n : ℤ) - w j)) (q + 1),
      (∀ j, Regular (c j)) → (∀ j, differential (c j) = 0) →
      ∃ b : (j : J) → Cochain C (Laurent C B ((n : ℤ) - w j)) q,
        (∀ j, Regular (b j)) ∧ (∀ j, differential (b j) = c j) := by
  classical
  let N : ℕ := ∑ j, (w j).toNat
  have hN (j : J) : w j ≤ (N : ℤ) := by
    calc
      w j ≤ ((w j).toNat : ℤ) := by omega
      _ ≤ (N : ℤ) := by
        exact_mod_cast (Finset.single_le_sum (fun i _ => Nat.zero_le ((w i).toNat))
          (Finset.mem_univ j))
  refine ⟨N, ?_⟩
  intro n hn q c hc hz
  have hnonneg (j : J) : 0 ≤ (n : ℤ) - w j := by
    have hj := hN j
    have hn' : (N : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    omega
  choose b hb hdb using fun j =>
    nonnegative_twist_cech_exact_all_positive (hnonneg j) (c j) (hc j) (hz j)
  exact ⟨b, hb, hdb⟩

theorem compatible_vertices_are_polynomial [Nonempty C] {d : ℤ} (hd : 0 ≤ d)
    (c : C → Laurent C B d) (hc : ∀ j, RegularOn {j} (c j))
    (heq : ∀ i j, c i = c j) :
    ∃ f : Laurent C B d, RegularOn ∅ f ∧ ∀ j, c j = f := by
  classical
  let p : C := Classical.choice inferInstance
  refine ⟨c p, ?_, fun j => heq j p⟩
  intro a ha k hk
  obtain ⟨j, hj⟩ := exists_nonnegative_coordinate hd a
  have hcoeff : c j a ≠ 0 := by rw [heq j p]; exact ha
  have hkj := hc j a hcoeff k hk
  have hkj' : k = j := hkj
  exact False.elim ((not_lt_of_ge hj) (hkj' ▸ hk))

end FreeTwistCech

end
end PiExponent.GradedSerre

end OAI
