import Mathlib

namespace OAI

noncomputable section

namespace Foulkes.SemisimpleBridge
open Module
open scoped Classical

section Algebra
variable {K R A B C : Type*} [Field K] [Ring R] [Algebra K R]
  [AddCommGroup A] [Module K A] [Module R A] [IsScalarTower K R A]
  [AddCommGroup B] [Module K B] [Module R B] [IsScalarTower K R B]
  [AddCommGroup C] [Module K C] [Module R C] [IsScalarTower K R C]

def homCongrRight (e : B ≃ₗ[R] C) : (A →ₗ[R] B) ≃ₗ[K] (A →ₗ[R] C) where
  toFun f := e.toLinearMap.comp f
  invFun f := e.symm.toLinearMap.comp f
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' f g := by ext x; simp
  map_smul' k f := by
    ext x
    exact e.toLinearMap.map_smul_of_tower k (f x)

lemma finite_hom [FiniteDimensional K A] [FiniteDimensional K B] :
    FiniteDimensional K (A →ₗ[R] B) :=
  Module.Finite.of_injective (LinearMap.restrictScalarsₗ K R A B K)
    (LinearMap.restrictScalars_injective K)

lemma simple_hom_finrank [IsAlgClosed K] [FiniteDimensional K A]
    [FiniteDimensional K B] [IsSimpleModule R A] [IsSimpleModule R B] :
    finrank K (A →ₗ[R] B) = if Nonempty (A ≃ₗ[R] B) then 1 else 0 := by
  classical
  by_cases h : Nonempty (A ≃ₗ[R] B)
  · rw [ite_eq_left h]
    have he := homCongrRight (K := K) (A := A) h.some.symm
    rw [he.finrank_eq]
    have hb := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := R) (V := A) K
    have hh := (LinearEquiv.ofBijective (Algebra.linearMap K (Module.End R A)) hb).finrank_eq
    simpa using hh.symm
  · rw [ite_eq_right h]
    have hz (f : A →ₗ[R] B) : f = 0 := by
      rcases LinearMap.bijective_or_eq_zero f with hbij | hzero
      · exact (h ⟨LinearEquiv.ofBijective f hbij⟩).elim
      · exact hzero
    let : Subsingleton (A →ₗ[R] B) := ⟨fun f g => (hz f).trans (hz g).symm⟩
    exact finrank_zero_of_subsingleton

end Algebra
end Foulkes.SemisimpleBridge

namespace Foulkes.SemisimpleBridge
open scoped Classical
open Module Finset

def fibreEmbedding {ι κ C : Type*} [Fintype ι] [Fintype κ]
    (f : ι → C) (g : κ → C)
    (hc : ∀ c, Fintype.card {i // f i = c} ≤ Fintype.card {j // g j = c}) : ι ↪ κ := by
  let e (c : C) : {i // f i = c} ↪ {j // g j = c} :=
    (Fintype.equivFin _).toEmbedding.trans
      ((Fin.castLEEmb (hc c)).trans (Fintype.equivFin _).symm.toEmbedding)
  exact (Equiv.sigmaFiberEquiv f).symm.toEmbedding.trans
    ((Function.Embedding.sigmaMap (Function.Embedding.refl C) e).trans
      (Equiv.sigmaFiberEquiv g).toEmbedding)

lemma fibreEmbedding_label {ι κ C : Type*} [Fintype ι] [Fintype κ]
    (f : ι → C) (g : κ → C)
    (hc : ∀ c, Fintype.card {i // f i = c} ≤ Fintype.card {j // g j = c}) (i : ι) :
    g (fibreEmbedding f g hc i) = f i := by
  exact (show {j // g j = f i} from
    ((Fintype.equivFin {i' // f i' = f i}).toEmbedding.trans
      ((Fin.castLEEmb (hc (f i))).trans
        (Fintype.equivFin {j // g j = f i}).symm.toEmbedding)) ⟨i,rfl⟩).property

section PiHom
variable {K R A : Type*} [Field K] [Ring R] [Algebra K R]
  [IsAlgClosed K] [AddCommGroup A] [Module K A] [Module R A]
  [IsScalarTower K R A] [FiniteDimensional K A] [IsSimpleModule R A]
  {ι : Type*} [Fintype ι] (P : ι → Type*) [∀ i, AddCommGroup (P i)]
  [∀ i, Module K (P i)] [∀ i, Module R (P i)] [∀ i, IsScalarTower K R (P i)]
  [∀ i, FiniteDimensional K (P i)] [∀ i, IsSimpleModule R (P i)]

lemma hom_pi_finrank :
    finrank K (A →ₗ[R] Π i, P i) = Fintype.card {i // Nonempty (A ≃ₗ[R] P i)} := by
  let (i : ι) : FiniteDimensional K (A →ₗ[R] P i) := finite_hom
  rw [← (LinearEquiv.linearMapPi (R := R) (M₂ := A) (φ := P) K).finrank_eq]
  rw [Module.finrank_pi_fintype]
  simp only [simple_hom_finrank]
  simp [Fintype.card_subtype]

end PiHom

section PiEmbedding
variable {R : Type*} [Ring R] {ι κ : Type*} [Fintype ι] [Fintype κ]
  (A : ι → Type*) (B : κ → Type*) [∀ i, AddCommGroup (A i)]
  [∀ j, AddCommGroup (B j)] [∀ i, Module R (A i)] [∀ j, Module R (B j)]

def piMapOfMatching (f : ι ↪ κ) (e : ∀ i, A i ≃ₗ[R] B (f i)) :
    (Π i, A i) →ₗ[R] (Π j, B j) :=
  ∑ i, (LinearMap.single _ _ (f i)).comp
    ((e i).toLinearMap.comp (LinearMap.proj i))

omit [Fintype κ] in
lemma piMapOfMatching_apply (f : ι ↪ κ) (e : ∀ i, A i ≃ₗ[R] B (f i))
    (x : Π i, A i) (i : ι) : piMapOfMatching A B f e x (f i) = e i (x i) := by
  classical
  simp only [piMapOfMatching, LinearMap.sum_apply, Finset.sum_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearMap.proj_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have hf : f j ≠ f i := fun hh => hji (f.injective hh)
    simp [LinearMap.single_apply, Pi.single_eq_of_ne (Ne.symm hf)]
  · simp

omit [Fintype κ] in
lemma piMapOfMatching_injective (f : ι ↪ κ) (e : ∀ i, A i ≃ₗ[R] B (f i)) :
    Function.Injective (piMapOfMatching A B f e) := by
  intro x y h
  funext i
  apply (e i).injective
  simpa only [piMapOfMatching_apply] using congrFun h (f i)

end PiEmbedding
end Foulkes.SemisimpleBridge

namespace Foulkes.SemisimpleBridge
universe v
open scoped Classical

private def classSet {X : Type*} (s : Setoid X) (x : X) : Set X := {y | s.r x y}

private lemma classSet_eq_iff {X : Type*} (s : Setoid X) (x y : X) :
    classSet s x = classSet s y ↔ s.r x y := by
  constructor
  · intro h
    have hy : y ∈ classSet s y := s.refl y
    rw [← h] at hy
    exact hy
  · intro h
    ext z
    exact ⟨fun hz => s.trans (s.symm h) hz, fun hz => s.trans h hz⟩

theorem matching_of_equivalence_counts {ι κ X : Type*} [Fintype ι] [Fintype κ]
    (s : Setoid X) (a : ι → X) (b : κ → X)
    (hc : ∀ i, Fintype.card {i' // s.r (a i) (a i')} ≤
      Fintype.card {j // s.r (a i) (b j)}) :
    ∃ f : ι ↪ κ, ∀ i, s.r (a i) (b (f i)) := by
  classical
  let fa := classSet s ∘ a
  let fb := classSet s ∘ b
  have hcard : ∀ c, Fintype.card {i // fa i = c} ≤ Fintype.card {j // fb j = c} := by
    intro c
    by_cases hc' : ∃ i, fa i = c
    · obtain ⟨i,rfl⟩ := hc'
      have equivA : {i' // fa i' = fa i} ≃ {i' // s.r (a i) (a i')} :=
        Equiv.subtypeEquivRight fun i' =>
          (classSet_eq_iff s (a i') (a i)).trans ⟨fun h => s.symm h, fun h => s.symm h⟩
      have equivB : {j // fb j = fa i} ≃ {j // s.r (a i) (b j)} :=
        Equiv.subtypeEquivRight fun j =>
          (classSet_eq_iff s (b j) (a i)).trans ⟨fun h => s.symm h, fun h => s.symm h⟩
      rw [Fintype.card_congr equivA, Fintype.card_congr equivB]
      exact hc i
    · have : IsEmpty {i // fa i = c} := ⟨fun i => hc' ⟨i.val,i.property⟩⟩
      simp
  refine ⟨fibreEmbedding fa fb hcard, fun i => ?_⟩
  exact s.symm ((classSet_eq_iff s _ _).mp (fibreEmbedding_label fa fb hcard i))

private def moduleIsoSetoid (R : Type*) [Ring R] : Setoid (ModuleCat R) where
  r M N := Nonempty (M ≃ₗ[R] N)
  iseqv := ⟨fun M => ⟨LinearEquiv.refl R M⟩,
    fun h => ⟨h.some.symm⟩, fun h h' => ⟨h.some.trans h'.some⟩⟩

theorem pi_embedding_of_iso_counts {R : Type*} [Ring R]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → Type v) (B : κ → Type v) [∀ i, AddCommGroup (A i)]
    [∀ j, AddCommGroup (B j)] [∀ i, Module R (A i)] [∀ j, Module R (B j)]
    (hc : ∀ i, Fintype.card {i' // Nonempty (A i ≃ₗ[R] A i')} ≤
      Fintype.card {j // Nonempty (A i ≃ₗ[R] B j)}) :
    ∃ f : (Π i, A i) →ₗ[R] (Π j, B j), Function.Injective f := by
  obtain ⟨f,hf⟩ := matching_of_equivalence_counts (moduleIsoSetoid R)
    (fun i => ModuleCat.of R (A i)) (fun j => ModuleCat.of R (B j)) hc
  let e (i : ι) : A i ≃ₗ[R] B (f i) := (hf i).some
  exact ⟨piMapOfMatching A B f e, piMapOfMatching_injective A B f e⟩

end Foulkes.SemisimpleBridge

namespace Foulkes.SemisimpleBridge
universe u
open Module

theorem embedding_of_simple_hom_le {K R : Type*} [Field K] [IsAlgClosed K]
    [Ring R] [Algebra K R] (A B : Type u)
    [AddCommGroup A] [Module K A] [Module R A] [IsScalarTower K R A]
    [AddCommGroup B] [Module K B] [Module R B] [IsScalarTower K R B]
    [FiniteDimensional K A] [FiniteDimensional K B]
    [IsSemisimpleModule R A] [IsSemisimpleModule R B]
    (h : ∀ (T : Type u) [AddCommGroup T] [Module K T] [Module R T]
      [IsScalarTower K R T] [FiniteDimensional K T] [IsSimpleModule R T],
      finrank K (T →ₗ[R] A) ≤ finrank K (T →ₗ[R] B)) :
    ∃ f : A →ₗ[R] B, Function.Injective f := by
  classical
  let : Module.Finite R A := Module.Finite.of_restrictScalars_finite K R A
  let : Module.Finite R B := Module.Finite.of_restrictScalars_finite K R B
  obtain ⟨n,S,eA,hS⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp R A
  obtain ⟨m,T,eB,hT⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp R B
  let (i : Fin n) : IsSimpleModule R (S i) := hS i
  let (j : Fin m) : IsSimpleModule R (T j) := hT j
  let (i : Fin n) : FiniteDimensional K (S i) :=
    Module.Finite.of_injective ((S i).subtype.restrictScalars K) (S i).subtype_injective
  let (j : Fin m) : FiniteDimensional K (T j) :=
    Module.Finite.of_injective ((T j).subtype.restrictScalars K) (T j).subtype_injective
  let eA' : A ≃ₗ[R] Π i, S i := eA.trans DFinsupp.linearEquivFunOnFintype
  let eB' : B ≃ₗ[R] Π j, T j := eB.trans DFinsupp.linearEquivFunOnFintype
  have hc (i : Fin n) : Fintype.card {i' // Nonempty (S i ≃ₗ[R] S i')} ≤
      Fintype.card {j // Nonempty (S i ≃ₗ[R] T j)} := by
    rw [← hom_pi_finrank (K := K) (R := R) (A := S i) (fun i' => S i'),
      ← hom_pi_finrank (K := K) (R := R) (A := S i) (fun j => T j)]
    rw [← (homCongrRight (K := K) (A := S i) eA').finrank_eq,
      ← (homCongrRight (K := K) (A := S i) eB').finrank_eq]
    exact h (S i)
  obtain ⟨f,hf⟩ := pi_embedding_of_iso_counts (R := R) (fun i => S i) (fun j => T j) hc
  refine ⟨eB'.symm.toLinearMap.comp (f.comp eA'.toLinearMap), ?_⟩
  exact eB'.symm.injective.comp (hf.comp eA'.injective)

end Foulkes.SemisimpleBridge

end

end OAI
