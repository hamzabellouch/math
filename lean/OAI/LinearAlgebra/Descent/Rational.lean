import Mathlib

namespace OAI

/-!
# Rational descent of automorphism-invariant subspaces

Over an algebraically closed field of characteristic zero, a coefficient-invariant subspace
of finitely supported vectors is obtained by scalar extension from its rational intersection.
The coordinate index set is arbitrary, and the intersection is given both as a pullback and
as a literal subspace of the ambient space.

`CoefficientStable` is a hypothesis on an arbitrary subspace, not a definition of the Arthur
filtration. The trace-defined Arthur filtration, its geometric setup and characteristic
hypotheses, and coefficient independence for that filtration are not formalized here.
-/

noncomputable section
open scoped TensorProduct Classical

namespace ArthurLinearDescent

theorem exists_extension_ringAut (F E : Type*) [Field F] [Field E] [Algebra F E]
    [IsAlgClosed E] (σ : F ≃+* F) :
    ∃ τ : E ≃+* E, ∀ a : F, τ (algebraMap F E a) = algebraMap F E (σ a) := by
  classical
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F E
  let v : s → E := Subtype.val
  let A := Algebra.adjoin F (Set.range v)
  let e : MvPolynomial s F ≃ₐ[F] A := hs.1.aevalEquiv
  let α : A ≃+* A := e.symm.toRingEquiv.trans
    ((MvPolynomial.mapEquiv s σ).trans e.toRingEquiv)
  let : IsAlgClosure A E := IsAlgClosed.isAlgClosure_of_transcendence_basis v hs
  let τ : E ≃+* E := IsAlgClosure.equivOfEquiv E E α
  refine ⟨τ, fun a => ?_⟩
  have hea : algebraMap A E (e (MvPolynomial.C a)) = algebraMap F E a := by
    change MvPolynomial.aeval v (MvPolynomial.C a) = algebraMap F E a
    simp
  calc
    τ (algebraMap F E a) = τ (algebraMap A E (e (MvPolynomial.C a))) := by rw [hea]
    _ = algebraMap A E (α (e (MvPolynomial.C a))) :=
      IsAlgClosure.equivOfEquiv_algebraMap E E α _
    _ = algebraMap F E (σ a) := by
      have heα (p : MvPolynomial s F) : α (e p) = e (MvPolynomial.mapEquiv s σ p) := by
        simp [α]
      rw [heα]
      change algebraMap A E (e (MvPolynomial.mapEquiv s σ (MvPolynomial.C a))) = _
      rw [MvPolynomial.mapEquiv_apply, MvPolynomial.map_C]
      change MvPolynomial.aeval v (MvPolynomial.C (σ a)) = _
      simp

def translateVariables (ι : Type*) (F : Type*) [CommRing F] :
    MvPolynomial ι F ≃ₐ[F] MvPolynomial ι F :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval fun i : ι => MvPolynomial.X i + 1)
    (MvPolynomial.aeval fun i : ι => MvPolynomial.X i - 1)
    (by ext i; simp) (by ext i; simp)

@[simp] theorem translateVariables_X (ι : Type*) (F : Type*) [CommRing F] (i : ι) :
    translateVariables ι F (MvPolynomial.X i) = MvPolynomial.X i + 1 := by
  simp [translateVariables]

theorem exists_move_transcendental (E : Type*) [Field E] [CharZero E] [IsAlgClosed E]
    {x : E} (hx : Transcendental ℚ x) :
    ∃ τ : E ≃ₐ[ℚ] E, τ x ≠ x := by
  classical
  have hi : AlgebraicIndepOn ℚ id ({x} : Set E) :=
    (algebraicIndependent_singleton_iff (⟨x, rfl⟩ : ({x} : Set E))).mpr hx
  obtain ⟨s, hxs, hs⟩ := exists_isTranscendenceBasis_superset hi
  let v : s → E := Subtype.val
  let j : s := ⟨x, hxs rfl⟩
  let A := Algebra.adjoin ℚ (Set.range v)
  let e : MvPolynomial s ℚ ≃ₐ[ℚ] A := hs.1.aevalEquiv
  let α : A ≃+* A := e.symm.toRingEquiv.trans
    ((translateVariables s ℚ).toRingEquiv.trans e.toRingEquiv)
  let : IsAlgClosure A E := IsAlgClosed.isAlgClosure_of_transcendence_basis v hs
  let τ : E ≃+* E := IsAlgClosure.equivOfEquiv E E α
  have hej : algebraMap A E (e (MvPolynomial.X j)) = x := by
    change MvPolynomial.aeval v (MvPolynomial.X j) = x
    simp [v, j]
  have hτ : τ x = x + 1 := by
    calc
      τ x = τ (algebraMap A E (e (MvPolynomial.X j))) := by rw [hej]
      _ = algebraMap A E (α (e (MvPolynomial.X j))) :=
        IsAlgClosure.equivOfEquiv_algebraMap E E α _
      _ = x + 1 := by
        have heα (p : MvPolynomial s ℚ) : α (e p) = e (translateVariables s ℚ p) := by
          simp [α]
        rw [heα]
        change algebraMap A E (e (translateVariables s ℚ (MvPolynomial.X j))) = _
        rw [translateVariables_X, map_add, map_one, map_add, map_one, hej]
  refine ⟨τ.toRatAlgEquiv, ?_⟩
  change τ x ≠ x
  rw [hτ]
  simp

theorem fixedField_rat (E : Type*) [Field E] [CharZero E] [IsAlgClosed E]
    (x : E) (hx : ∀ σ : E ≃ₐ[ℚ] E, σ x = x) :
    ∃ q : ℚ, algebraMap ℚ E q = x := by
  classical
  by_cases halg : IsAlgebraic ℚ x
  · let F := algebraicClosure ℚ E
    let : IsAlgClosure ℚ F := algebraicClosure.isAlgClosure ℚ E
    let y : F := ⟨x, mem_algebraicClosure_iff.mpr halg⟩
    have hy : ∀ σ : F ≃ₐ[ℚ] F, σ y = y := by
      intro σ
      obtain ⟨τ, hτ⟩ := exists_extension_ringAut F E σ.toRingEquiv
      apply (algebraMap F E).injective
      exact (hτ y).symm.trans (hx τ.toRatAlgEquiv)
    obtain ⟨q, hq⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed y).mpr hy
    refine ⟨q, ?_⟩
    have heq := congrArg (algebraMap F E) hq
    rw [← IsScalarTower.algebraMap_apply ℚ F E] at heq
    exact heq
  · obtain ⟨σ, hσ⟩ := exists_move_transcendental E halg
    exact False.elim (hσ (hx σ))

variable {k K I : Type*} [Field k] [Field K] [Algebra k K]

def coefficientInclusion : (I →₀ k) →ₗ[k] (I →₀ K) :=
  Finsupp.mapRange.linearMap (Algebra.linearMap k K)

@[simp] theorem coefficientInclusion_apply (f : I →₀ k) (i : I) :
    coefficientInclusion (K := K) f i = algebraMap k K (f i) := rfl

def coefficientIntersection (W : Submodule K (I →₀ K)) : Submodule k (I →₀ k) :=
  (W.restrictScalars k).comap coefficientInclusion

@[simp] theorem mem_coefficientIntersection (W : Submodule K (I →₀ K)) (f : I →₀ k) :
    f ∈ coefficientIntersection (k := k) W ↔ coefficientInclusion f ∈ W := Iff.rfl

theorem coefficientInclusion_injective :
    Function.Injective (coefficientInclusion (k := k) (K := K) (I := I)) := by
  intro f g h
  ext i
  apply (algebraMap k K).injective
  exact congrArg (fun v : I →₀ K => v i) h

def ambientIntersection (W : Submodule K (I →₀ K)) : Submodule k (I →₀ K) :=
  LinearMap.range (coefficientInclusion (k := k)) ⊓ W.restrictScalars k

def intersectionToAmbient (W : Submodule K (I →₀ K)) :
    coefficientIntersection (k := k) W →ₗ[k] ambientIntersection (k := k) W :=
  (coefficientInclusion.comp (coefficientIntersection W).subtype).codRestrict
    (ambientIntersection W) (fun q => ⟨⟨q.val, rfl⟩, q.property⟩)

@[simp] theorem intersectionToAmbient_apply (W : Submodule K (I →₀ K))
    (q : coefficientIntersection (k := k) W) :
    (intersectionToAmbient W q : I →₀ K) = coefficientInclusion q.val := rfl

def intersectionEquiv (W : Submodule K (I →₀ K)) :
    coefficientIntersection (k := k) W ≃ₗ[k] ambientIntersection (k := k) W :=
  LinearEquiv.ofBijective (intersectionToAmbient W) (by
    constructor
    · intro x y h
      apply Subtype.ext
      apply coefficientInclusion_injective (K := K)
      exact congrArg Subtype.val h
    · rintro ⟨v, ⟨⟨q, hq⟩, hv⟩⟩
      have hqW : q ∈ coefficientIntersection (k := k) W := by
        rw [mem_coefficientIntersection, hq]
        exact hv
      exact ⟨⟨q, hqW⟩, Subtype.ext hq⟩)

@[simp] theorem intersectionEquiv_apply (W : Submodule K (I →₀ K))
    (q : coefficientIntersection (k := k) W) :
    (intersectionEquiv W q : I →₀ K) = coefficientInclusion q.val := rfl

def coefficientAction (σ : K ≃ₐ[k] K) :
    (I →₀ K) ≃ₗ[k] (I →₀ K) :=
  Finsupp.mapRange.linearEquiv σ.toLinearEquiv

@[simp] theorem coefficientAction_apply (σ : K ≃ₐ[k] K) (f : I →₀ K) (i : I) :
    coefficientAction σ f i = σ (f i) := rfl

def CoefficientStable (W : Submodule K (I →₀ K)) : Prop :=
  ∀ (σ : K ≃ₐ[k] K) (f : I →₀ K), f ∈ W → coefficientAction σ f ∈ W

private theorem elimination_support {f g : I →₀ K} {i : I} (hgi : g i ≠ 0)
    (hgf : g.support ⊆ f.support) :
    (f - (f i / g i) • g).support ⊆ f.support.erase i := by
  classical
  intro j hj
  rw [Finset.mem_erase]
  have hj' : (f - (f i / g i) • g) j ≠ 0 := Finsupp.mem_support_iff.mp hj
  constructor
  · intro hji
    subst j
    simp [div_mul_cancel₀ _ hgi] at hj'
  · by_contra hjf
    have hg : j ∉ g.support := fun h => hjf (hgf h)
    exact hj' (by simp [Finsupp.notMem_support_iff.mp hjf,
      Finsupp.notMem_support_iff.mp hg])

private theorem minimal_support_fixed (W : Submodule K (I →₀ K))
    (hW : CoefficientStable (k := k) W) {g : I →₀ K} (hgW : g ∈ W)
    (hmin : ∀ f : I →₀ K, f ∈ W → f ≠ 0 → f.support ⊆ g.support →
      g.support.card ≤ f.support.card)
    {i : I} (hgi : g i ≠ 0) (σ : K ≃ₐ[k] K) :
    coefficientAction σ ((g i)⁻¹ • g) = (g i)⁻¹ • g := by
  classical
  let v : I →₀ K := (g i)⁻¹ • g
  have hvi : v i = 1 := by simp [v, hgi]
  have hvW : v ∈ W := W.smul_mem _ hgW
  let d : I →₀ K := coefficientAction σ v - v
  have hdW : d ∈ W := W.sub_mem (hW σ v hvW) hvW
  have hd : d.support ⊆ g.support.erase i := by
    intro j hj
    rw [Finset.mem_erase]
    have hj' : d j ≠ 0 := Finsupp.mem_support_iff.mp hj
    constructor
    · intro hji
      subst j
      simp [d, hvi] at hj'
    · by_contra hjg
      have hvj : v j = 0 := by simp [v, Finsupp.notMem_support_iff.mp hjg]
      exact hj' (by simp [d, hvj])
  have hdz : d = 0 := by
    by_contra hdne
    have hle := hmin d hdW hdne (hd.trans (Finset.erase_subset _ _))
    have hlt : (g.support.erase i).card < g.support.card :=
      Finset.card_erase_lt_of_mem (Finsupp.mem_support_iff.mpr hgi)
    exact (Nat.not_lt_of_ge hle) ((Finset.card_le_card hd).trans_lt hlt)
  exact sub_eq_zero.mp hdz

theorem span_fixedVectors (W : Submodule K (I →₀ K))
    (hW : CoefficientStable (k := k) W) :
    Submodule.span K {f : I →₀ K | f ∈ W ∧
      ∀ σ : K ≃ₐ[k] K, coefficientAction σ f = f} = W := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro f hf
    exact hf.1
  · intro f hf
    suffices aux : ∀ (n : ℕ) (f : I →₀ K), f.support.card = n → f ∈ W →
        f ∈ Submodule.span K {g : I →₀ K | g ∈ W ∧
          ∀ σ : K ≃ₐ[k] K, coefficientAction σ g = g} from
      aux f.support.card f rfl hf
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f hcard hf
      by_cases hfz : f = 0
      · subst f
        exact Submodule.zero_mem _
      have hex : ∃ m : ℕ, ∃ g : I →₀ K,
          g ∈ W ∧ g ≠ 0 ∧ g.support ⊆ f.support ∧ g.support.card = m :=
        ⟨f.support.card, f, hf, hfz, Finset.Subset.refl _, rfl⟩
      obtain ⟨g, hgW, hgne, hgf, hgcard⟩ := Nat.find_spec hex
      have hmin : ∀ v : I →₀ K, v ∈ W → v ≠ 0 → v.support ⊆ g.support →
          g.support.card ≤ v.support.card := by
        intro v hvW hvz hvg
        rw [hgcard]
        exact Nat.find_min' hex ⟨v, hvW, hvz, hvg.trans hgf, rfl⟩
      obtain ⟨i, hgi⟩ := Finsupp.support_nonempty_iff.mpr hgne
      have hgi' : g i ≠ 0 := Finsupp.mem_support_iff.mp hgi
      have hnorm : (g i)⁻¹ • g ∈ Submodule.span K {g : I →₀ K | g ∈ W ∧
          ∀ σ : K ≃ₐ[k] K, coefficientAction σ g = g} :=
        Submodule.subset_span ⟨W.smul_mem _ hgW, fun σ =>
          minimal_support_fixed W hW hgW hmin hgi' σ⟩
      have hgspan : g ∈ Submodule.span K {g : I →₀ K | g ∈ W ∧
          ∀ σ : K ≃ₐ[k] K, coefficientAction σ g = g} := by
        simpa [smul_smul, hgi'] using
          (Submodule.smul_mem _ (g i) hnorm)
      have hdf := elimination_support hgi' hgf
      have hlt : (f - (f i / g i) • g).support.card < n := by
        rw [← hcard]
        exact (Finset.card_le_card hdf).trans_lt
          (Finset.card_erase_lt_of_mem (hgf hgi))
      have hsub := ih _ hlt _ rfl (W.sub_mem hf (W.smul_mem _ hgW))
      convert Submodule.add_mem _ hsub (Submodule.smul_mem _ (f i / g i) hgspan) using 1
      exact (sub_add_cancel _ _).symm

theorem exists_preimage_coefficientInclusion {f : I →₀ K}
    (hf : ∀ i, ∃ a : k, algebraMap k K a = f i) :
    ∃ q : I →₀ k, coefficientInclusion q = f := by
  classical
  choose q hq using hf
  have hqfin : ∀ i, q i ≠ 0 → i ∈ f.support := by
    intro i hi
    apply Finsupp.mem_support_iff.mpr
    rw [← hq]
    simpa using (algebraMap k K).injective.ne hi
  refine ⟨Finsupp.onFinset f.support q hqfin, ?_⟩
  ext i
  exact hq i

def intersectionInclusion (W : Submodule K (I →₀ K)) :
    coefficientIntersection (k := k) W →ₗ[k] W :=
  ((coefficientInclusion (k := k) (K := K) (I := I)).comp
    (coefficientIntersection W).subtype).codRestrict (W.restrictScalars k)
      (fun f => f.property)

def naturalMap (W : Submodule K (I →₀ K)) :
    K ⊗[k] coefficientIntersection (k := k) W →ₗ[K] W :=
  (intersectionInclusion W).liftBaseChange K

@[simp] theorem naturalMap_tmul (W : Submodule K (I →₀ K)) (a : K)
    (q : coefficientIntersection (k := k) W) :
    (naturalMap W (a ⊗ₜ[k] q) : I →₀ K) = a • coefficientInclusion q.val := rfl

def ambientIntersectionInclusion (W : Submodule K (I →₀ K)) :
    ambientIntersection (k := k) W →ₗ[k] W :=
  (ambientIntersection W).subtype.codRestrict (W.restrictScalars k)
    (fun x => x.property.2)

def ambientNaturalMap (W : Submodule K (I →₀ K)) :
    K ⊗[k] ambientIntersection (k := k) W →ₗ[K] W :=
  (ambientIntersectionInclusion W).liftBaseChange K

@[simp] theorem ambientNaturalMap_tmul (W : Submodule K (I →₀ K)) (a : K)
    (q : ambientIntersection (k := k) W) :
    (ambientNaturalMap W (a ⊗ₜ[k] q) : I →₀ K) = a • q.val := rfl

theorem naturalMap_eq_ambientNaturalMap (W : Submodule K (I →₀ K))
    (z : K ⊗[k] coefficientIntersection (k := k) W) :
    ambientNaturalMap W ((intersectionEquiv W).baseChange k K _ _ z) =
      naturalMap W z := by
  induction z using TensorProduct.inductionOn with
  | tmul a q => rfl
  | add x y hx hy => simp [hx, hy]

theorem subtype_naturalMap (W : Submodule K (I →₀ K))
    (z : K ⊗[k] coefficientIntersection (k := k) W) :
    (naturalMap W z : I →₀ K) =
      TensorProduct.finsuppScalarRight k K K I
        ((coefficientIntersection (k := k) W).subtype.lTensor K z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a q =>
    ext i
    simp [Algebra.smul_def, mul_comm]
  | add x y hx hy => simp [hx, hy]

theorem naturalMap_injective (W : Submodule K (I →₀ K)) :
    Function.Injective (naturalMap (k := k) W) := by
  intro x y hxy
  apply Module.Flat.lTensor_preserves_injective_linearMap
    (M := K) (coefficientIntersection (k := k) W).subtype
    (coefficientIntersection W).injective_subtype
  apply (TensorProduct.finsuppScalarRight k K K I).injective
  rw [← subtype_naturalMap, ← subtype_naturalMap, hxy]

theorem naturalMap_bijective_of_fixedField
    (hfixed : ∀ a : K, (∀ σ : K ≃ₐ[k] K, σ a = a) →
      ∃ b : k, algebraMap k K b = a)
    (W : Submodule K (I →₀ K)) (hW : CoefficientStable (k := k) W) :
    Function.Bijective (naturalMap (k := k) W) := by
  refine ⟨naturalMap_injective W, ?_⟩
  have hspan : W ≤ LinearMap.range (W.subtype.comp (naturalMap (k := k) W)) := by
    nth_rw 1 [← span_fixedVectors W hW]
    apply Submodule.span_le.mpr
    rintro f ⟨hfW, hf⟩
    have hcoeff : ∀ i, ∃ a : k, algebraMap k K a = f i := by
      intro i
      apply hfixed
      intro σ
      exact congrArg (fun g : I →₀ K => g i) (hf σ)
    obtain ⟨q, hq⟩ := exists_preimage_coefficientInclusion hcoeff
    have hqW : q ∈ coefficientIntersection (k := k) W := by
      rw [mem_coefficientIntersection, hq]
      exact hfW
    refine ⟨1 ⊗ₜ[k] (⟨q, hqW⟩ : coefficientIntersection (k := k) W), ?_⟩
    simpa only [LinearMap.comp_apply, Submodule.subtype_apply,
      naturalMap_tmul, one_smul] using hq
  intro f
  obtain ⟨z, hz⟩ := hspan f.property
  exact ⟨z, Subtype.ext hz⟩

def naturalEquiv_of_fixedField
    (hfixed : ∀ a : K, (∀ σ : K ≃ₐ[k] K, σ a = a) →
      ∃ b : k, algebraMap k K b = a)
    (W : Submodule K (I →₀ K)) (hW : CoefficientStable (k := k) W) :
    K ⊗[k] coefficientIntersection (k := k) W ≃ₗ[K] W :=
  LinearEquiv.ofBijective (naturalMap W)
    (naturalMap_bijective_of_fixedField hfixed W hW)

theorem rational_descent (E : Type*) [Field E] [CharZero E] [IsAlgClosed E]
    (W : Submodule E (I →₀ E)) (hW : CoefficientStable (k := ℚ) W) :
    Function.Bijective (naturalMap (k := ℚ) W) :=
  naturalMap_bijective_of_fixedField (fixedField_rat E) W hW

def rationalDescentEquiv (E : Type*) [Field E] [CharZero E] [IsAlgClosed E]
    (W : Submodule E (I →₀ E)) (hW : CoefficientStable (k := ℚ) W) :
    E ⊗[ℚ] coefficientIntersection (k := ℚ) W ≃ₗ[E] W :=
  LinearEquiv.ofBijective (naturalMap W) (rational_descent E W hW)

@[simp] theorem rationalDescentEquiv_apply
    (E : Type*) [Field E] [CharZero E] [IsAlgClosed E]
    (W : Submodule E (I →₀ E)) (hW : CoefficientStable (k := ℚ) W)
    (z : E ⊗[ℚ] coefficientIntersection (k := ℚ) W) :
    rationalDescentEquiv E W hW z = naturalMap (k := ℚ) W z := rfl

@[simp] theorem rationalDescentEquiv_tmul
    (E : Type*) [Field E] [CharZero E] [IsAlgClosed E]
    (W : Submodule E (I →₀ E)) (hW : CoefficientStable (k := ℚ) W)
    (a : E) (q : coefficientIntersection (k := ℚ) W) :
    (rationalDescentEquiv E W hW (a ⊗ₜ[ℚ] q) : I →₀ E) =
      a • coefficientInclusion q.val := rfl

def ambientRationalDescentEquiv
    (E : Type*) [Field E] [CharZero E] [IsAlgClosed E]
    (W : Submodule E (I →₀ E)) (hW : CoefficientStable (k := ℚ) W) :
    E ⊗[ℚ] ambientIntersection (k := ℚ) W ≃ₗ[E] W :=
  ((intersectionEquiv W).baseChange ℚ E _ _).symm.trans (rationalDescentEquiv E W hW)

@[simp] theorem ambientRationalDescentEquiv_apply
    (E : Type*) [Field E] [CharZero E] [IsAlgClosed E]
    (W : Submodule E (I →₀ E)) (hW : CoefficientStable (k := ℚ) W)
    (z : E ⊗[ℚ] ambientIntersection (k := ℚ) W) :
    ambientRationalDescentEquiv E W hW z = ambientNaturalMap (k := ℚ) W z := by
  change naturalMap W (((intersectionEquiv W).baseChange ℚ E _ _).symm z) = _
  rw [← naturalMap_eq_ambientNaturalMap]
  simp

theorem ambient_rational_descent
    (E : Type*) [Field E] [CharZero E] [IsAlgClosed E]
    (W : Submodule E (I →₀ E)) (hW : CoefficientStable (k := ℚ) W) :
    Function.Bijective (ambientNaturalMap (k := ℚ) W) := by
  have heq : (ambientRationalDescentEquiv E W hW :
        E ⊗[ℚ] ambientIntersection (k := ℚ) W → W) = ambientNaturalMap W := by
    funext z
    exact ambientRationalDescentEquiv_apply E W hW z
  rw [← heq]
  exact (ambientRationalDescentEquiv E W hW).bijective

end ArthurLinearDescent

end

end OAI
