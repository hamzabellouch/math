import Mathlib

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

noncomputable section
open scoped TensorProduct
namespace ReverseLogKodaira.CanonicalAdjunction

abbrev BaseDifferentials (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] := B ⊗[A] KaehlerDifferential R A

section DeterminantLine
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {n : ℕ}

lemma alternating_basis_formula (b : Module.Basis (Fin n) R M)
    (f : M [⋀^Fin n]→ₗ[R] N) (v : Fin n → M) :
    f v = b.det v • f b := by
  have h : f = b.det.smulRight (f b) := by
    apply b.ext_alternating
    intro i hi
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective i (Finite.injective_iff_bijective.mp hi)
    change f (b ∘ σ) = (b.det.smulRight (f b)) (b ∘ σ)
    simp [AlternatingMap.map_perm, Module.Basis.det_self]
  exact DFunLike.congr_fun h v

 
def determinantCoordinate (b : Module.Basis (Fin n) R M) : ⋀[R]^n M ≃ₗ[R] R where
  toLinearMap := exteriorPower.alternatingMapLinearEquiv b.det
  invFun c := c • exteriorPower.ιMulti R n b
  left_inv := by
    intro x
    have h : ((LinearMap.id : ⋀[R]^n M →ₗ[R] ⋀[R]^n M)) =
        (LinearMap.toSpanSingleton R (⋀[R]^n M) (exteriorPower.ιMulti R n b)).comp
          (exteriorPower.alternatingMapLinearEquiv b.det) := by
      apply LinearMap.ext_on (exteriorPower.ιMulti_span R n M)
      rintro _ ⟨v, rfl⟩
      simpa using alternating_basis_formula b (exteriorPower.ιMulti R n) v
    exact (LinearMap.congr_fun h x).symm
  right_inv := by
    intro c
    simp [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, Module.Basis.det_self]

@[simp] lemma determinantCoordinate_wedge (b : Module.Basis (Fin n) R M) (v : Fin n → M) :
    determinantCoordinate b (exteriorPower.ιMulti R n v) = b.det v := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti b.det v

end DeterminantLine

section SplitSequence
variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]
variable (f : M →ₗ[R] N) (q : N →ₗ[R] P) (s : P →ₗ[R] N)
  (hf : Function.Injective f) (he : Function.Exact f q) (hs : q ∘ₗ s = LinearMap.id)

include hf he hs
lemma split_coprod_bijective : Function.Bijective (f.coprod s) := by
  have hqs (y : P) : q (s y) = y := LinearMap.congr_fun hs y
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    rintro ⟨x, y⟩ hxy
    change f x + s y = 0 at hxy
    have hy : y = 0 := by
      have h := congrArg q hxy
      simpa [he.apply_apply_eq_zero, hqs] using h
    have hx : x = 0 := by
      apply hf
      simpa [hy] using hxy
    simp [hx, hy]
  · intro z
    have hz : q (z - s (q z)) = 0 := by simp [hqs]
    obtain ⟨x, hx⟩ := (he (z - s (q z))).mp hz
    refine ⟨(x, q z), ?_⟩
    simp [hx]

 
def splitEquiv : (M × P) ≃ₗ[R] N :=
  LinearEquiv.ofBijective (f.coprod s) (split_coprod_bijective f q s hf he hs)

@[simp] lemma splitEquiv_apply (x : M × P) :
    splitEquiv f q s hf he hs x = f x.1 + s x.2 := rfl

lemma splitEquiv_symm_snd (z : N) :
    ((splitEquiv f q s hf he hs).symm z).2 = q z := by
  have hqs (y : P) : q (s y) = y := LinearMap.congr_fun hs y
  have h := congrArg q ((splitEquiv f q s hf he hs).apply_symm_apply z)
  simpa only [splitEquiv_apply, map_add, he.apply_apply_eq_zero, hqs, zero_add] using h

lemma splitEquiv_symm_f (x : M) :
    (splitEquiv f q s hf he hs).symm (f x) = (x, 0) := by
  apply (splitEquiv f q s hf he hs).injective
  simp

variable {n r : ℕ} (b : Module.Basis (Fin n) R M) (c : Module.Basis (Fin r) R P)

 
def adaptedBasis : Module.Basis (Fin n ⊕ Fin r) R N :=
  (b.prod c).map (splitEquiv f q s hf he hs)

lemma adaptedBasis_det (v : Fin n → M) (z : Fin r → N) :
    (adaptedBasis f q s hf he hs b c).det (Sum.elim (f ∘ v) z) =
      b.det v * c.det (q ∘ z) := by
  rw [adaptedBasis, Module.Basis.det_map, Module.Basis.det_apply,
    Module.Basis.det_apply, Module.Basis.det_apply]
  have hmatrix : (b.prod c).toMatrix
      ((splitEquiv f q s hf he hs).symm ∘ Sum.elim (f ∘ v) z) =
      Matrix.fromBlocks (b.toMatrix v)
        (b.toMatrix fun j => ((splitEquiv f q s hf he hs).symm (z j)).1)
        0 (c.toMatrix (q ∘ z)) := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simp [Module.Basis.toMatrix_apply, splitEquiv_symm_f]
      | inr j => simp [Module.Basis.toMatrix_apply]
    | inr i =>
      cases j with
      | inl j => simp [Module.Basis.toMatrix_apply, splitEquiv_symm_f]
      | inr j => simp [Module.Basis.toMatrix_apply, splitEquiv_symm_snd]
  rw [hmatrix, Matrix.det_fromBlocks_zero₂₁]

 
def splitDeterminantEquiv :
    (⋀[R]^n M) ⊗[R] (⋀[R]^r P) ≃ₗ[R] ⋀[R]^(n + r) N :=
  ((TensorProduct.congr (determinantCoordinate b) (determinantCoordinate c)).trans
    (TensorProduct.lid R R)).trans
      (determinantCoordinate
        ((adaptedBasis f q s hf he hs b c).reindex finSumFinEquiv)).symm

lemma splitDeterminantEquiv_wedge (v : Fin n → M) (z : Fin r → N) :
    splitDeterminantEquiv f q s hf he hs b c
      (exteriorPower.ιMulti R n v ⊗ₜ[R] exteriorPower.ιMulti R r (q ∘ z)) =
      exteriorPower.ιMulti R (n + r) (Fin.append (f ∘ v) z) := by
  apply (determinantCoordinate
    ((adaptedBasis f q s hf he hs b c).reindex finSumFinEquiv)).injective
  have happend : Fin.append (f ∘ v) z ∘ finSumFinEquiv = Sum.elim (f ∘ v) z := by
    funext i
    cases i <;> simp
  simp only [splitDeterminantEquiv, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, determinantCoordinate_wedge, TensorProduct.lid_tmul,
    smul_eq_mul, LinearEquiv.apply_symm_apply, Module.Basis.det_reindex, happend]
  exact (adaptedBasis_det f q s hf he hs b c v z).symm

end SplitSequence

 

theorem exact_canonical_adjunction
    {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (f : M →ₗ[R] N) (q : N →ₗ[R] P)
    (hf : Function.Injective f) (he : Function.Exact f q) (hq : Function.Surjective q)
    {n r : ℕ} (b : Module.Basis (Fin n) R M) (c : Module.Basis (Fin r) R P) :
    ∃ e : (⋀[R]^n M) ⊗[R] (⋀[R]^r P) ≃ₗ[R] ⋀[R]^(n + r) N,
      ∀ (v : Fin n → M) (z : Fin r → N),
        e (exteriorPower.ιMulti R n v ⊗ₜ[R] exteriorPower.ιMulti R r (q ∘ z)) =
          exteriorPower.ιMulti R (n + r) (Fin.append (f ∘ v) z) := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q LinearMap.id hq
  exact ⟨splitDeterminantEquiv f q s hf he hs b c,
    splitDeterminantEquiv_wedge f q s hf he hs b c⟩

 

theorem smooth_canonical_adjunction
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B] [Nontrivial B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (n r : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n R A]
    [Algebra.IsStandardSmoothOfRelativeDimension r A B] :
    ∃ e : (⋀[B]^n (BaseDifferentials R A B)) ⊗[B]
        (⋀[B]^r (KaehlerDifferential A B)) ≃ₗ[B]
        ⋀[B]^(n + r) (KaehlerDifferential R B),
      ∀ (v : Fin n → BaseDifferentials R A B) (z : Fin r → KaehlerDifferential R B),
        e (exteriorPower.ιMulti B n v ⊗ₜ[B]
          exteriorPower.ιMulti B r (KaehlerDifferential.map R A B B ∘ z)) =
        exteriorPower.ιMulti B (n + r)
          (Fin.append (KaehlerDifferential.mapBaseChange R A B ∘ v) z) := by
  let : Nontrivial A := (algebraMap A B).domain_nontrivial
  let : Algebra.IsStandardSmooth R A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let : Algebra.IsStandardSmooth A B :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth r
  have hn : Module.finrank A (KaehlerDifferential R A) = n :=
    Module.finrank_eq_of_rank_eq
      (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n)
  have hr : Module.finrank B (KaehlerDifferential A B) = r :=
    Module.finrank_eq_of_rank_eq
      (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential r)
  let b : Module.Basis (Fin n) B (BaseDifferentials R A B) :=
    (((Module.finBasis A (KaehlerDifferential R A)).reindex (finCongr hn)).baseChange B)
  let c : Module.Basis (Fin r) B (KaehlerDifferential A B) :=
    (Module.finBasis B (KaehlerDifferential A B)).reindex (finCongr hr)
  apply exact_canonical_adjunction (KaehlerDifferential.mapBaseChange R A B)
    (KaehlerDifferential.map R A B B) _
    (KaehlerDifferential.exact_mapBaseChange_map R A B)
    (KaehlerDifferential.map_surjective R A B) b c
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨y, hy⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R A B x).mp hx
  have hy0 : y = 0 := Subsingleton.elim _ _
  rw [hy0, map_zero] at hy
  exact hy.symm

end ReverseLogKodaira.CanonicalAdjunction

end
end

end OAI
