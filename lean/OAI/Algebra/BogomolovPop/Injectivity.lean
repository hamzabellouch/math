import Mathlib
import OAI.Algebra.BogomolovPop.Kummer

namespace OAI

/-! Perfect-closure descent and injectivity of the canonical orbit map. -/

noncomputable section
open scoped Topology

noncomputable section
namespace BogomolovPop

lemma purely_inseparable_pow_mem_mono
    (F E : Type*) [Field F] [Field E] [Algebra F E] (q : ℕ)
    {x : E} {n m : ℕ} (h : x ^ q ^ n ∈ (algebraMap F E).range) (hnm : n ≤ m) :
    x ^ q ^ m ∈ (algebraMap F E).range := by
  obtain ⟨y, hy⟩ := h
  refine ⟨y ^ (q ^ (m - n)), ?_⟩
  rw [map_pow, hy, ← pow_mul, ← pow_add, Nat.add_sub_of_le hnm]

theorem uniform_frobenius_clearing
    (k F E : Type*) [Field k] [Field F] [Field E]
    [Algebra k F] [Algebra F E] [Algebra k E] [IsScalarTower k F E]
    [Algebra.EssFiniteType k F] [IsPurelyInseparable F E]
    (q : ℕ) [ExpChar F q] (σ : F →+* E)
    (hc : ∀ c : k, ∃ d : k, σ (algebraMap k F c) = algebraMap k E d) :
    ∃ n : ℕ, ∃ φ : F →+* F, ∀ x : F,
      algebraMap F E (φ x) = (σ x) ^ (q ^ n) := by
  classical
  let : ExpChar E q := expChar_of_injective_algebraMap (algebraMap F E).injective q
  obtain ⟨s, hs⟩ := IntermediateField.fg_top k F
  choose e he using fun x : F => IsPurelyInseparable.pow_mem F q (σ x)
  let n := s.sup e
  let ψ : F →+* E := (iterateFrobenius E q n).comp σ
  let S : IntermediateField k F := ((algebraMap F E).fieldRange.comap ψ).toIntermediateField
    (by
      intro c
      obtain ⟨d, hd⟩ := hc c
      change ψ (algebraMap k F c) ∈ (algebraMap F E).fieldRange
      refine ⟨(algebraMap k F d) ^ (q ^ n), ?_⟩
      simp only [ψ, RingHom.comp_apply, iterateFrobenius_def, hd, map_pow,
        ← IsScalarTower.algebraMap_apply k F E])
  have hS : S = ⊤ := by
    apply top_le_iff.mp
    rw [← hs, IntermediateField.adjoin_le_iff]
    intro x hx
    change σ x ^ (q ^ n) ∈ (algebraMap F E).fieldRange
    exact purely_inseparable_pow_mem_mono F E q (he x) (Finset.le_sup hx)
  have hψ : ∀ x : F, ψ x ∈ (algebraMap F E).fieldRange := by
    intro x
    change x ∈ S
    simp [hS]
  let φ : F →+* F := ((algebraMap F E).rangeRestrictFieldEquiv.symm.toRingHom).comp
    (ψ.codRestrict _ hψ)
  refine ⟨n, φ, ?_⟩
  intro x
  exact congrArg (fun z : (algebraMap F E).fieldRange => (z : E))
    ((algebraMap F E).rangeRestrictFieldEquiv.apply_symm_apply ⟨ψ x, hψ x⟩)

end BogomolovPop

namespace BogomolovPop
lemma purely_inseparable_ringHom_ext
    {F E T : Type*} [Field F] [Field E] [Field T]
    [Algebra F E] [IsPurelyInseparable F E]
    (q : ℕ) [ExpChar F q] [ExpChar T q]
    (f g : E →+* T) (h : ∀ x : F, f (algebraMap F E x) = g (algebraMap F E x)) : f = g := by
  ext x
  obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem F q x
  apply (iterateFrobenius T q n).injective
  simp only [iterateFrobenius_def, ← map_pow, ← hy, h]

def frobeniusPerfectIsom
    {k K l L : Type*} [Field k] [Field K] [Field l] [Field L]
    [Algebra k K] [Algebra l L] [IsAlgClosed l]
    (q : ℕ) [ExpChar L q] (n : ℕ) (α : PerfectIsom k K l L) :
    PerfectIsom k K l L := by
  letI : ExpChar (PerfectFieldClosure L) q :=
    expChar_of_injective_algebraMap (algebraMap L (PerfectFieldClosure L)).injective q
  refine ⟨α.1.trans (iterateFrobeniusEquiv (PerfectFieldClosure L) q n), ?_⟩
  change ((iterateFrobeniusEquiv (PerfectFieldClosure L) q n) ∘ α.1) '' _ = _
  rw [Set.image_comp, α.2]
  ext x
  constructor
  · rintro ⟨y, ⟨c, rfl⟩, rfl⟩
    exact ⟨c ^ (q ^ n), by simp [iterateFrobeniusEquiv_apply, iterateFrobenius_def]⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c (expChar_pow_pos L q n)
    refine ⟨algebraMap l (PerfectFieldClosure L) d, ⟨d, rfl⟩, ?_⟩
    simp only [iterateFrobeniusEquiv_apply, iterateFrobenius_def, ← map_pow, hd]

@[simp] lemma frobeniusPerfectIsom_apply
    {k K l L : Type*} [Field k] [Field K] [Field l] [Field L]
    [Algebra k K] [Algebra l L] [IsAlgClosed l]
    (q : ℕ) [ExpChar L q] (n : ℕ) (α : PerfectIsom k K l L) (x : PerfectFieldClosure K) :
    (frobeniusPerfectIsom q n α).1 x = (α.1 x) ^ (q ^ n) := rfl

lemma frobeniusPerfectIsom_eqvGen
    {k K l L : Type*} [Field k] [Field K] [Field l] [Field L]
    [Algebra k K] [Algebra l L] [IsAlgClosed l]
    (q : ℕ) [ExpChar L q] (n : ℕ) (α : PerfectIsom k K l L) :
    Relation.EqvGen FrobeniusStep α (frobeniusPerfectIsom q n α) := by
  induction n with
  | zero =>
    have he : frobeniusPerfectIsom q 0 α = α := by
      apply Subtype.ext; apply RingEquiv.ext; intro x
      simp
    rw [he]
    exact Relation.EqvGen.refl _
  | succ n ih =>
    apply Relation.EqvGen.trans _ _ _ ih
    rcases expChar_is_prime_or_one L q with hp | rfl
    · apply Relation.EqvGen.rel
      refine ⟨q, hp, ?_, ?_⟩
      · have : CharP L q := by
          cases (inferInstance : ExpChar L q) with
          | zero => exact False.elim (hp.ne_one rfl)
          | prime hp => infer_instance
        exact CharP.cast_eq_zero L q
      · intro x
        simp only [frobeniusPerfectIsom_apply, pow_succ, pow_mul]
    · have he : frobeniusPerfectIsom 1 (n + 1) α = frobeniusPerfectIsom 1 n α := by
        apply Subtype.ext; apply RingEquiv.ext; intro x
        simp
      rw [he]
      exact Relation.EqvGen.refl _

theorem frobenius_orbit_of_iterates
    {k K l L : Type*} [Field k] [Field K] [Field l] [Field L]
    [Algebra k K] [Algebra l L] [IsAlgClosed l]
    (q : ℕ) [ExpChar L q] (α β : PerfectIsom k K l L)
    (n m : ℕ) (h : ∀ x, (α.1 x) ^ (q ^ n) = (β.1 x) ^ (q ^ m)) :
    Relation.EqvGen FrobeniusStep α β := by
  have he : frobeniusPerfectIsom q n α = frobeniusPerfectIsom q m β := by
    apply Subtype.ext; apply RingEquiv.ext; intro x
    exact h x
  exact Relation.EqvGen.trans _ _ _ (frobeniusPerfectIsom_eqvGen q n α)
    (he ▸ Relation.EqvGen.symm _ _ (frobeniusPerfectIsom_eqvGen q m β))
end BogomolovPop
namespace BogomolovPop
open scoped Topology
theorem perfect_scalar_iterates (ell : ℕ) [Fact ell.Prime]
    (k F : Type*) [Field k] [Field F] [Algebra k F] [IsAlgClosed k]
    [Algebra.EssFiniteType k F] (hchar : (ell : F) ≠ 0)
    (q : ℕ) [ExpChar F q] (δ : PerfectIsom k F k F)
    (β : AlgebraicClosure F ≃+* AlgebraicClosure F)
    (hβ : ∀ x : PerfectFieldClosure F, β x = (δ.1 x : AlgebraicClosure F))
    (u : (PadicInt ell)ˣ)
    (hg : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
      ∃ τ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
        (∀ x, β (τ x) = σ (β x)) ∧
        Filter.Tendsto (fun n : ℕ => absoluteToPiA ell F σ ^ (u : PadicInt ell).appr n)
          Filter.atTop (nhds (absoluteToPiA ell F τ)))
    (hx : ∃ x : F, Transcendental k x) :
    ∃ n m : ℕ, ∀ x : PerfectFieldClosure F, (δ.1 x) ^ (q ^ n) = x ^ (q ^ m) := by
  let P : Type _ := PerfectFieldClosure F
  let A := AlgebraicClosure F
  let : ExpChar P q := expChar_of_injective_algebraMap (algebraMap F P).injective q
  let : ExpChar A q := expChar_of_injective_algebraMap (algebraMap F A).injective q
  let σ : F →+* P := δ.1.toRingHom.comp (algebraMap F P)
  have hc : ∀ c : k, ∃ d : k, σ (algebraMap k F c) = algebraMap k P d := by
    intro c
    have hm : δ.1 (algebraMap k P c) ∈ Set.range (algebraMap k P) := by
      have hs : δ.1 '' Set.range (algebraMap k P) ⊆ Set.range (algebraMap k P) := le_of_eq δ.2
      exact hs ⟨algebraMap k P c, ⟨c, rfl⟩, rfl⟩
    obtain ⟨d, hd⟩ := hm
    refine ⟨d, ?_⟩
    change δ.1 (algebraMap F P (algebraMap k F c)) = _
    rw [← IsScalarTower.algebraMap_apply k F P]
    exact hd.symm
  obtain ⟨n, φ, hφ⟩ := uniform_frobenius_clearing k F P q σ hc
  let γ : A ≃+* A := β.trans (iterateFrobeniusEquiv A q n)
  have hγ : ∀ x : F, γ (algebraMap F A x) = algebraMap F A (φ x) := by
    intro x
    change (β (algebraMap F A x)) ^ (q ^ n) = _
    change (β ((algebraMap F P x : P) : A)) ^ (q ^ n) = _
    rw [hβ]
    have hh := congrArg (algebraMap P A) (hφ x)
    rw [map_pow] at hh
    exact hh.symm
  have hγg : ∀ ρ : A ≃ₐ[F] A, ∃ τ : A ≃ₐ[F] A,
      (∀ x, γ (τ x) = ρ (γ x)) ∧
      Filter.Tendsto (fun n : ℕ => absoluteToPiA ell F ρ ^ (u : PadicInt ell).appr n)
        Filter.atTop (nhds (absoluteToPiA ell F τ)) := by
    intro ρ
    obtain ⟨τ, hτ, hlim⟩ := hg ρ
    refine ⟨τ, ?_, hlim⟩
    intro x
    change (β (τ x)) ^ (q ^ n) = ρ ((β x) ^ (q ^ n))
    rw [hτ, map_pow]
  obtain ⟨a, ha⟩ := conjugation_kummer_scalar ell k F hchar φ γ hγ u hγg
  have he : ∃ m : ℕ, ∀ x : F, φ x = x ^ (q ^ m) := by
    rcases kummer_endomorphism_frobenius ell k F φ a hx ha with hid | ⟨p, r, hp, hpF, hr⟩
    · exact ⟨0, fun x => by simp [hid]⟩
    · have : CharP F p := (CharP.charP_iff_prime_eq_zero hp).mpr hpF
      have hpq : p = q := ExpChar.eq (R := F) (ExpChar.prime hp) inferInstance
      exact ⟨r, hpq ▸ hr⟩
  obtain ⟨m, hm⟩ := he
  refine ⟨n, m, ?_⟩
  have heq : (iterateFrobenius P q n).comp δ.1.toRingHom = iterateFrobenius P q m := by
    apply purely_inseparable_ringHom_ext (F := F) q
    intro x
    change (σ x) ^ (q ^ n) = (algebraMap F P x) ^ (q ^ m)
    rw [← hφ x, hm, map_pow]
  intro x
  exact DFunLike.congr_fun heq x
end BogomolovPop

namespace BogomolovPop
open scoped Topology

theorem pullback_scalar_frobenius (ell : ℕ) [Fact ell.Prime]
    {k K l L : Type*} [Field k] [Field K] [Field l] [Field L]
    [Algebra k K] [Algebra l L] [IsAlgClosed k] [IsAlgClosed l]
    [Algebra.EssFiniteType k K]
    (hchar : (ell : K) ≠ 0) (hx : ∃ x : K, Transcendental k x)
    (α β : PerfectIsom k K l L) (φ χ : IsomC ell K L)
    (hφ : PullbackGraph α φ) (hχ : PullbackGraph β χ)
    (hu : ScalarStep φ χ) : Relation.EqvGen FrobeniusStep α β := by
  obtain ⟨a, ha, hfa⟩ := hφ
  obtain ⟨b, hb, hfb⟩ := hχ
  obtain ⟨u, hu⟩ := hu
  let δ : PerfectIsom k K k K := ⟨β.1.trans α.1.symm, by
    calc (α.1.symm ∘ β.1) '' Set.range (algebraMap k (PerfectFieldClosure K)) =
        α.1.symm '' (β.1 '' Set.range (algebraMap k (PerfectFieldClosure K))) := Set.image_comp _ _ _
      _ = α.1.symm '' Set.range (algebraMap l (PerfectFieldClosure L)) := congrArg _ β.2
      _ = α.1.symm '' (α.1 '' Set.range (algebraMap k (PerfectFieldClosure K))) := congrArg _ α.2.symm
      _ = Set.range (algebraMap k (PerfectFieldClosure K)) := by
        simp only [Set.image_image, RingEquiv.symm_apply_apply]
        exact Set.image_id _⟩
  let γ : AlgebraicClosure K ≃+* AlgebraicClosure K := b.trans a.symm
  have hγ : ∀ x : PerfectFieldClosure K, γ x = (δ.1 x : AlgebraicClosure K) := by
    intro x
    change a.symm (b x) = _
    rw [hb, perfectExtension_symm α.1 a ha]
    rfl
  have hγg : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      ∃ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
        (∀ x, γ (τ x) = σ (γ x)) ∧
        Filter.Tendsto (fun n : ℕ => absoluteToPiA ell K σ ^ (u : PadicInt ell).appr n)
          Filter.atTop (nhds (absoluteToPiA ell K τ)) := by
    intro σ
    obtain ⟨ρ, hρ⟩ := (absoluteConjugateEquiv α.1 a ha).surjective σ
    change absoluteConjugate α.1 a ha ρ = σ at hρ
    obtain ⟨τ, hτ, hχτ⟩ := hfb ρ
    change AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K at τ
    change (∀ x, b (τ x) = ρ (b x)) at hτ
    obtain ⟨ν, hν, hφν⟩ := hfa ρ
    have hνσ : ν = σ := by
      rw [← hρ]
      apply AlgEquiv.ext
      intro x
      apply a.injective
      exact (hν x).trans (a.apply_symm_apply _).symm
    refine ⟨τ, ?_, ?_⟩
    · intro x
      change a.symm (b (τ x)) = σ (a.symm (b x))
      rw [hτ, ← hρ, absoluteConjugate_apply, a.apply_symm_apply]
    · have ht := hu (absoluteToPiA ell L ρ)
      rw [hφν, hνσ, hχτ] at ht
      exact ht
  obtain ⟨q, hq⟩ := ExpChar.exists K
  let := hq
  let : ExpChar (AlgebraicClosure K) q :=
    expChar_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective q
  let : ExpChar (AlgebraicClosure L) q := expChar_of_injective_ringHom (f := a.toRingHom) a.injective q
  let : ExpChar L q := (algebraMap L (AlgebraicClosure L)).expChar
    (algebraMap L (AlgebraicClosure L)).injective q
  obtain ⟨n, m, hm⟩ := perfect_scalar_iterates ell k K hchar q δ γ hγ u hγg hx
  apply frobenius_orbit_of_iterates q α β m n
  intro x
  have he := congrArg α.1 (hm x)
  simpa only [map_pow, δ, RingEquiv.trans_apply, RingEquiv.apply_symm_apply] using he.symm

theorem main_canonical_injective (ell : ℕ) [Fact ell.Prime]
    (k K l L : Type*) [Field k] [Field K] [Field l] [Field L]
    [IsAlgClosed k] [IsAlgClosed l] [Algebra k K] [Algebra l L]
    [Algebra.EssFiniteType k K] [Algebra.EssFiniteType l L]
    (hk : (ell : k) ≠ 0) (_hl : (ell : l) ≠ 0)
    (hK : 2 ≤ Algebra.trdeg k K) (_hL : 2 ≤ Algebra.trdeg l L) :
    Function.Injective (canonicalPhi ell (k := k) (K := K) (l := l) (L := L)) := by
  have hchar : (ell : K) ≠ 0 := by
    simpa only [map_natCast] using (map_ne_zero (algebraMap k K)).mpr hk
  have ht : Algebra.Transcendental k K := trdeg_ne_zero_iff.mp (by
    intro he
    rw [he] at hK
    norm_num at hK)
  let := ht
  have hx : ∃ x : K, Transcendental k x := Algebra.Transcendental.transcendental
  intro a b hab
  induction a using Quotient.inductionOn with | h α =>
    induction b using Quotient.inductionOn with | h β =>
      apply Quotient.sound
      change Quotient.mk _ (canonicalPullback ell α) = Quotient.mk _ (canonicalPullback ell β) at hab
      have hs := (scalarEqvGen_iff (canonicalPullback ell α) (canonicalPullback ell β)).mp
        (Quotient.exact hab)
      exact pullback_scalar_frobenius ell hchar hx α β _ _
        (canonicalPullback_spec ell α) (canonicalPullback_spec ell β) hs
end BogomolovPop

namespace BogomolovPop

/-- Injectivity of the canonical Galois graph on its prescribed orbit sets. -/
theorem main_graph_injective (ell : ℕ) [Fact ell.Prime]
    (k K l L : Type*) [Field k] [Field K] [Field l] [Field L]
    [IsAlgClosed k] [IsAlgClosed l] [Algebra k K] [Algebra l L]
    [Algebra.EssFiniteType k K] [Algebra.EssFiniteType l L]
    (hk : (ell : k) ≠ 0) (hl : (ell : l) ≠ 0)
    (hK : 2 ≤ Algebra.trdeg k K) (hL : 2 ≤ Algebra.trdeg l L) :
    ∀ (a a' : IsomF k K l L) (b : IsomCUnits ell K L),
      PhiGraph a b → PhiGraph a' b → a = a'  := by
  intro a a' b ha ha'
  apply main_canonical_injective ell k K l L hk hl hK hL
  exact (phiGraph_eq_canonicalPhi ell ha).symm.trans (phiGraph_eq_canonicalPhi ell ha')

end BogomolovPop

end
end

end OAI
