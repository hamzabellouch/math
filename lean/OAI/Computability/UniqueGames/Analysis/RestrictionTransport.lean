import OAI.Computability.UniqueGames.Analysis.Identities
import OAI.Computability.UniqueGames.Analysis.MatrixRestrictions
import OAI.Computability.UniqueGames.Analysis.RestrictionLemmas

namespace OAI

namespace UniqueGamesTheorem

/-!
# Exact transport of nested affine restrictions

The nested quotient-domain/range inclusion has exactly the effective
annihilator and target obtained by comap and map. Its parameterization is
linearly equivalent to the direct effective restriction, independently of
any Fourier frequency. Thus normalized second moments and the outer average
of their squares agree while retaining the full affine translate.
-/

noncomputable section

namespace Appendix.RestrictionTransport

open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixRestrictions

section Nested

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

/-- Compose the two actual quotient-domain and target-subspace embeddings. -/
def nestedEmbedding (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) :
    Parameter C D →ₗ[F2] (E →ₗ[F2] F) :=
  (embedding A B).comp (embedding C D)

theorem nestedEmbedding_injective (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) :
    Function.Injective (nestedEmbedding A B C D) := by
  intro N N' h
  apply embed_injective C D
  apply embed_injective A B
  exact h

/-- Exact effective annihilator and target of a nested restriction. -/
theorem exists_nested_embed_iff (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) (M : E →ₗ[F2] F) :
    (∃ N : Parameter C D, nestedEmbedding A B C D N = M) ↔
      C.comap A.mkQ ≤ M.ker ∧ M.range ≤ D.map B.subtype := by
  constructor
  · rintro ⟨N, rfl⟩
    constructor
    · intro x hx
      change (embed C D N (A.mkQ x) : F) = 0
      have hz : embed C D N (A.mkQ x) = 0 := embed_vanishes C D N hx
      rw [hz]
      rfl
    · rintro y ⟨x, rfl⟩
      apply Submodule.mem_map.mpr
      refine ⟨embed C D N (A.mkQ x), ?_, rfl⟩
      exact embed_range C D N ⟨A.mkQ x, rfl⟩
  · rintro ⟨hker, hrange⟩
    have hA : A ≤ M.ker := by
      intro x hx
      apply hker
      change A.mkQ x ∈ C
      have hz : A.mkQ x = 0 := by simpa using hx
      rw [hz]
      exact C.zero_mem
    have hB : M.range ≤ B := by
      intro y hy
      obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp (hrange hy)
      exact b.property
    obtain ⟨N, hN⟩ := (exists_embed_iff A B M).mpr ⟨hA, hB⟩
    have hC : C ≤ N.ker := by
      intro q hq
      obtain ⟨x, rfl⟩ := A.mkQ_surjective q
      change N (A.mkQ x) = 0
      apply Subtype.ext
      change embed A B N x = 0
      rw [hN]
      exact hker hq
    have hD : N.range ≤ D := by
      rintro b ⟨q, rfl⟩
      obtain ⟨x, rfl⟩ := A.mkQ_surjective q
      have hm : M x ∈ D.map B.subtype := hrange ⟨x, rfl⟩
      have hco : (N (A.mkQ x) : F) = M x := congrArg (fun L : E →ₗ[F2] F => L x) hN
      rw [← hco] at hm
      obtain ⟨b, hb, heq⟩ := Submodule.mem_map.mp hm
      have heq' : b = N (A.mkQ x) := Subtype.ext heq
      exact heq' ▸ hb
    obtain ⟨P, hP⟩ := (exists_embed_iff C D N).mpr ⟨hC, hD⟩
    refine ⟨P, ?_⟩
    change embed A B (embed C D P) = M
    rw [hP, hN]

/-- Nested and effective direct restrictions describe exactly the same perturbations. -/
theorem nested_range_eq (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) :
    (nestedEmbedding A B C D).range =
      (embedding (C.comap A.mkQ) (D.map B.subtype)).range := by
  ext M
  change (∃ N, nestedEmbedding A B C D N = M) ↔
    (∃ N, embed (C.comap A.mkQ) (D.map B.subtype) N = M)
  rw [exists_nested_embed_iff, exists_embed_iff]

end Nested

section SameRange

variable {K : Type*} {G : Type*} {P : Type*} {Q : Type*} [Field K]
  [AddCommGroup G] [Module K G] [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q]

private theorem exists_range_preimage (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (h : f.range ≤ g.range) (x : P) : ∃ y : Q, g y = f x := h ⟨x, rfl⟩

/-- The actual linear change of parameters between two injective presentations. -/
def sameRangeEquiv (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) : P ≃ₗ[K] Q := by
  let fw (x : P) := Classical.choose (exists_range_preimage f g (le_of_eq h) x)
  let bw (y : Q) := Classical.choose (exists_range_preimage g f (le_of_eq h.symm) y)
  have hfw (x : P) : g (fw x) = f x :=
    Classical.choose_spec (exists_range_preimage f g (le_of_eq h) x)
  have hbw (y : Q) : f (bw y) = g y :=
    Classical.choose_spec (exists_range_preimage g f (le_of_eq h.symm) y)
  exact
    { toFun := fw
      invFun := bw
      left_inv := by
        intro x
        apply hf
        rw [hbw, hfw]
      right_inv := by
        intro y
        apply hg
        rw [hfw, hbw]
      map_add' := by
        intro x y
        apply hg
        simp only [map_add, hfw]
      map_smul' := by
        intro c x
        change fw (c • x) = c • fw x
        apply hg
        simp only [map_smul, hfw] }

theorem sameRangeEquiv_commutes (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) (x : P) :
    g (sameRangeEquiv f g hf hg h x) = f x := by
  exact Classical.choose_spec (exists_range_preimage f g (le_of_eq h) x)

variable [Fintype P] [Fintype Q]

/-- Injective parameter changes preserve normalized uniform expectations. -/
theorem expect_eq_of_same_range (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) (observable : G → ℝ) :
    (𝔼 x, observable (f x)) = 𝔼 y, observable (g y) := by
  exact Fintype.expect_equiv (sameRangeEquiv f g hf hg h).toEquiv _ _
    (fun x => congrArg observable (sameRangeEquiv_commutes f g hf hg h x).symm)

/-- Preserve second moments at the same full ambient translate. -/
theorem restriction_secondMoment_eq_of_same_range
    (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) (observable : G → ℝ) (T : G) :
    (𝔼 x, observable (T + f x) ^ 2) = 𝔼 y, observable (T + g y) ^ 2 :=
  expect_eq_of_same_range f g hf hg h (fun z => observable (T + z) ^ 2)

/-- Preserve the outer mean of squared restriction energies, with the square outside. -/
theorem restriction_energySquare_average_eq_of_same_range [Fintype G]
    (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) (observable : G → ℝ) :
    (𝔼 T, (𝔼 x, observable (T + f x) ^ 2) ^ 2) =
      𝔼 T, (𝔼 y, observable (T + g y) ^ 2) ^ 2 := by
  apply Finset.expect_congr rfl
  intro T _
  rw [restriction_secondMoment_eq_of_same_range f g hf hg h observable T]

end SameRange

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F] [Finite E] [Finite F]

local instance (A : Submodule F2 E) : Finite (E ⧸ A) :=
  Finite.of_surjective A.mkQ A.mkQ_surjective
/-- The genuine nested affine restriction has the effective direct second moment. -/
theorem nested_restriction_secondMoment_eq
    (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B)
    (h : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F) :
    (𝔼 N : Parameter C D, h (T + nestedEmbedding A B C D N) ^ 2) =
      𝔼 M : Parameter (C.comap A.mkQ) (D.map B.subtype),
        h (T + embed (C.comap A.mkQ) (D.map B.subtype) M) ^ 2 := by
  have transported := restriction_secondMoment_eq_of_same_range
    (K := F2) (G := E →ₗ[F2] F) (P := Parameter C D)
    (Q := Parameter (C.comap A.mkQ) (D.map B.subtype))
    (nestedEmbedding A B C D) (embedding (C.comap A.mkQ) (D.map B.subtype))
    (nestedEmbedding_injective A B C D)
    (embed_injective (C.comap A.mkQ) (D.map B.subtype))
    (nested_range_eq A B C D) h T
  exact transported

/-- Squared normalized energies also agree before averaging over the full translate. -/
theorem nested_restriction_energySquare_average_eq [Fintype (E →ₗ[F2] F)]
    (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B)
    (h : (E →ₗ[F2] F) → ℝ) :
    (𝔼 T, (𝔼 N, h (T + nestedEmbedding A B C D N) ^ 2) ^ 2) =
      𝔼 T, (𝔼 M, h (T + embed (C.comap A.mkQ) (D.map B.subtype) M) ^ 2) ^ 2 := by
  apply Finset.expect_congr rfl
  intro T _
  rw [nested_restriction_secondMoment_eq A B C D h T]

end Appendix.RestrictionTransport

namespace Appendix.LinearIdentities

variable {K : Type*} {W : Type*} {V : Type*} [Field K]
  [AddCommGroup W] [AddCommGroup V] [Module K W] [Module K V]

/-- A subspace disjoint from the image has exactly the original kernel as preimage. -/
theorem a5_preimage_eq_ker (X : W →ₗ[K] V) (A₀ : Submodule K V)
    (hd : Disjoint A₀ (LinearMap.range X)) : A₀.comap X = LinearMap.ker X := by
  ext w
  constructor
  · intro hw
    exact Submodule.disjoint_def.mp hd (X w) hw ⟨w, rfl⟩
  · intro hw
    change X w ∈ A₀
    rw [show X w = 0 from hw]
    exact A₀.zero_mem

/-- Restricting to a subspace that covers the domain modulo the kernel preserves the image. -/
theorem a5_range_domRestrict_eq_of_cover (X : W →ₗ[K] V) (B₀ : Submodule K W)
    (hc : B₀ ⊔ LinearMap.ker X = ⊤) :
    LinearMap.range (X.domRestrict B₀) = LinearMap.range X := by
  apply le_antisymm (LinearMap.range_domRestrict_le_range X B₀)
  rintro v ⟨w, hw⟩
  have ht : w ∈ B₀ ⊔ LinearMap.ker X := by rw [hc]; trivial
  rcases Submodule.mem_sup.mp ht with ⟨b, hb, k, hk, hbk⟩
  refine ⟨⟨b, hb⟩, ?_⟩
  change X b = v
  rw [← hw, ← hbk, map_add, show X k = 0 from hk, add_zero]

/-- The A.5 compressed image pulls back to its exact effective annihilator. -/
theorem a5_effective_annihilator (X : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B₀ : Submodule K W)
    (hA : A₀ ⊔ LinearMap.range X = A)
    (hc : B₀ ⊔ LinearMap.ker X = ⊤) :
    (LinearMap.range (compress X A₀ B₀)).comap A₀.mkQ = A := by
  rw [compress, LinearMap.range_comp, a5_range_domRestrict_eq_of_cover X B₀ hc,
    Submodule.comap_map_mkQ, hA]

/-- The A.5 compressed kernel maps to its exact effective codomain. -/
theorem a5_effective_codomain (X : W →ₗ[K] V)
    (A₀ : Submodule K V) (B B₀ : Submodule K W)
    (hd : Disjoint A₀ (LinearMap.range X))
    (hB : B₀ ⊓ LinearMap.ker X = B) :
    (LinearMap.ker (compress X A₀ B₀)).map B₀.subtype = B := by
  rw [compress, LinearMap.ker_comp, Submodule.ker_mkQ]
  change ((A₀.comap X).comap B₀.subtype).map B₀.subtype = B
  rw [a5_preimage_eq_ker X A₀ hd, Submodule.map_comap_subtype, hB]

end Appendix.LinearIdentities

end

end UniqueGamesTheorem

end OAI
