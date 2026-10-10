import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Finiteness.Prod
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.ConeQuotientAugmentation

namespace OAI

namespace SiegelZeros

section

namespace SiegelZerosAwei.W30
open CategoryTheory

universe u
variable {R : Type u} [CommRing R]

lemma coneBottom_comp {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup Z] [Module R X] [Module R Y] [Module R Z]
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (r : R) (hgf : g.comp f = 0) :
    (coneBottom g r).comp (coneDifferential f g r) = 0 := by
  apply LinearMap.ext
  intro xy
  have hz : g (f xy.1) = 0 := LinearMap.congr_fun hgf xy.1
  change g (f xy.1 + r • xy.2) + r • (-g xy.2) = 0
  simp [map_add, map_smul, hz]

def scalarConeObject (C : ChainComplex (ModuleCat.{u} R) ℕ) : ℕ → ModuleCat.{u} R
  | 0 => C.X 0
  | n + 1 => ModuleCat.of R (C.X (n + 1) × C.X n)

def scalarConeMap (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) :
    ∀ n, scalarConeObject C (n + 1) ⟶ scalarConeObject C n
  | 0 => ModuleCat.ofHom (coneBottom (C.d 1 0).hom r)
  | n + 1 => ModuleCat.ofHom
      (coneDifferential (C.d (n + 2) (n + 1)).hom (C.d (n + 1) n).hom r)

lemma chain_linear_comp_zero (C : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (C.d (n + 1) n).hom.comp (C.d (n + 2) (n + 1)).hom = 0 := by
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero] using
    congrArg (fun f => f.hom) (C.d_comp_d (n + 2) (n + 1) n)

theorem scalarConeMap_comp (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) (n : ℕ) :
    scalarConeMap C r (n + 1) ≫ scalarConeMap C r n = 0 := by
  cases n with
  | zero =>
    apply ModuleCat.hom_ext
    exact coneBottom_comp _ _ r (chain_linear_comp_zero C 0)
  | succ n =>
    apply ModuleCat.hom_ext
    exact coneDifferential_comp _ _ _ r
      (chain_linear_comp_zero C (n + 1)) (chain_linear_comp_zero C n)

def scalarConeComplex (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (scalarConeObject C) (scalarConeMap C r) (scalarConeMap_comp C r)

theorem scalarCone_interior_exact (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R)
    (n : ℕ)
    (hnext : LinearMap.range (C.d (n + 3) (n + 2)).hom =
      LinearMap.ker (C.d (n + 2) (n + 1)).hom)
    (hprev : LinearMap.range (C.d (n + 2) (n + 1)).hom =
      LinearMap.ker (C.d (n + 1) n).hom) :
    LinearMap.range (scalarConeMap C r (n + 2)).hom =
      LinearMap.ker (scalarConeMap C r (n + 1)).hom :=
  coneDifferential_exact _ _ _ r hnext hprev

end SiegelZerosAwei.W30

end

section

namespace SiegelZerosAwei.W30
open Module

variable {R X Y Z W : Type*} [CommRing R]
variable [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [AddCommGroup W]
variable [Module R X] [Module R Y] [Module R Z] [Module R W]

def dualConeDifferential (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (r : R) :
    (Dual R Y × Dual R Z) →ₗ[R] (Dual R X × Dual R Y) :=
  (f.dualMap.comp (LinearMap.fst R _ _)).prod
    (r • LinearMap.fst R _ _ - g.dualMap.comp (LinearMap.snd R _ _))

@[simp] theorem dualConeDifferential_apply (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (r : R) (α : Dual R Y) (β : Dual R Z) :
    dualConeDifferential f g r (α, β) = (α.comp f, r • α - β.comp g) := rfl

theorem coneDifferential_dual_precomposition (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (r : R) (α : Dual R Y) (β : Dual R Z) :
    (α.coprod β).comp (coneDifferential f g r) =
      (α.comp f).coprod (r • α - β.comp g) := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  change α (f x + r • y) + β (-g y) = α (f x) + (r • α - β.comp g) y
  change α (f x + r • y) + β (-g y) =
    α (f x) + (r • α y - β (g y))
  simp only [map_add, map_smul, map_neg, sub_eq_add_neg]
  abel

theorem coneDifferential_dual_equiv (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (r : R) :
    (dualProdDualEquivDual R X Y).toLinearMap.comp (dualConeDifferential f g r) =
      (coneDifferential f g r).dualMap.comp (dualProdDualEquivDual R Y Z).toLinearMap := by
  apply LinearMap.ext
  rintro ⟨α, β⟩
  exact (coneDifferential_dual_precomposition f g r α β).symm

theorem dualConeDifferential_exact (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (h : Z →ₗ[R] W) (r : R)
    (hhg : LinearMap.range h.dualMap = LinearMap.ker g.dualMap)
    (hgf : LinearMap.range g.dualMap = LinearMap.ker f.dualMap) :
    LinearMap.range (dualConeDifferential g h r) =
      LinearMap.ker (dualConeDifferential f g r) := by
  ext ab
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨⟨α, β⟩, rfl⟩
    have hfg : f.dualMap (g.dualMap α) = 0 :=
      LinearMap.congr_fun (comp_zero_of_range_eq_ker g.dualMap f.dualMap hgf) α
    have hgh : g.dualMap (h.dualMap β) = 0 :=
      LinearMap.congr_fun (comp_zero_of_range_eq_ker h.dualMap g.dualMap hhg) β
    apply Prod.ext
    · exact hfg
    · change r • g.dualMap α - g.dualMap (r • α - h.dualMap β) = 0
      simp only [map_sub, map_smul, hgh, sub_zero, sub_self]
  · intro hab
    have ha : f.dualMap ab.1 = 0 := congrArg Prod.fst hab
    have hb : r • ab.1 - g.dualMap ab.2 = 0 := congrArg Prod.snd hab
    have hamem : ab.1 ∈ LinearMap.range g.dualMap := by
      rw [hgf]
      exact ha
    obtain ⟨t, ht⟩ := LinearMap.mem_range.mp hamem
    have hcycle : g.dualMap (r • t - ab.2) = 0 := by
      simpa only [map_sub, map_smul, ht] using hb
    have hbmem : r • t - ab.2 ∈ LinearMap.range h.dualMap := by
      rw [hhg]
      exact hcycle
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hbmem
    refine ⟨(t, a), ?_⟩
    apply Prod.ext
    · exact ht
    · change r • t - h.dualMap a = ab.2
      rw [ha]
      abel

end SiegelZerosAwei.W30

end

section

namespace SiegelZerosAwei.W30

universe u
variable {R : Type u} [CommRing R]

def emptyKoszulObject : ℕ → ModuleCat.{u} R
  | 0 => ModuleCat.of R R
  | _ + 1 => ModuleCat.of R (Fin 0 → R)

def emptyKoszulComplex : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of emptyKoszulObject (fun _ => 0) (fun _ => by simp)

def iterateScalarCones (C : ChainComplex (ModuleCat.{u} R) ℕ) :
    List R → ChainComplex (ModuleCat.{u} R) ℕ
  | [] => C
  | r :: rs => iterateScalarCones (scalarConeComplex C r) rs

def regularSequenceComplex (rs : List R) : ChainComplex (ModuleCat.{u} R) ℕ :=
  iterateScalarCones emptyKoszulComplex rs

lemma scalarCone_free (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R)
    (hfree : ∀ n, Module.Free R (C.X n)) (n : ℕ) :
    Module.Free R ((scalarConeComplex C r).X n) := by
  cases n with
  | zero => exact hfree 0
  | succ n =>
    let := hfree (n + 1)
    let := hfree n
    change Module.Free R (C.X (n + 1) × C.X n)
    infer_instance

lemma scalarCone_finite (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R)
    (hfinite : ∀ n, Module.Finite R (C.X n)) (n : ℕ) :
    Module.Finite R ((scalarConeComplex C r).X n) := by
  cases n with
  | zero => exact hfinite 0
  | succ n =>
    let := hfinite (n + 1)
    let := hfinite n
    change Module.Finite R (C.X (n + 1) × C.X n)
    infer_instance

lemma iterateScalarCones_free (rs : List R) (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (hfree : ∀ n, Module.Free R (C.X n)) (n : ℕ) :
    Module.Free R ((iterateScalarCones C rs).X n) := by
  induction rs generalizing C with
  | nil => exact hfree n
  | cons r rs ih => exact ih (scalarConeComplex C r) (scalarCone_free C r hfree)

lemma iterateScalarCones_finite (rs : List R) (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (hfinite : ∀ n, Module.Finite R (C.X n)) (n : ℕ) :
    Module.Finite R ((iterateScalarCones C rs).X n) := by
  induction rs generalizing C with
  | nil => exact hfinite n
  | cons r rs ih => exact ih (scalarConeComplex C r) (scalarCone_finite C r hfinite)

theorem regularSequenceComplex_free (rs : List R) (n : ℕ) :
    Module.Free R ((regularSequenceComplex rs).X n) := by
  apply iterateScalarCones_free
  intro k
  cases k with
  | zero =>
    change Module.Free R R
    exact Module.Free.self R
  | succ k =>
    change Module.Free R (Fin 0 → R)
    infer_instance

theorem regularSequenceComplex_finite (rs : List R) (n : ℕ) :
    Module.Finite R ((regularSequenceComplex rs).X n) := by
  apply iterateScalarCones_finite
  intro k
  cases k with
  | zero =>
    change Module.Finite R R
    exact Module.Finite.self R
  | succ k =>
    change Module.Finite R (Fin 0 → R)
    infer_instance

end SiegelZerosAwei.W30

end

section

namespace SiegelZerosAwei.W30
open Module

variable {R X Y Z W Q : Type*} [CommRing R]
variable [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [AddCommGroup W]
variable [AddCommGroup Q]
variable [Module R X] [Module R Y] [Module R Z] [Module R W] [Module R Q]

theorem dualCone_endpoint_exact (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (h : Z →ₗ[R] W) (r : R) (π : Dual R Y →ₗ[R] Q)
    (hfg : f.dualMap.comp g.dualMap = 0)
    (hgh : g.dualMap.comp h.dualMap = 0)
    (hhg : LinearMap.range h.dualMap = LinearMap.ker g.dualMap)
    (hgπ : LinearMap.range g.dualMap = LinearMap.ker π)
    (hr : IsSMulRegular Q r) :
    LinearMap.range (dualConeDifferential g h r) =
      LinearMap.ker (dualConeDifferential f g r) := by
  ext ab
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨⟨α, β⟩, rfl⟩
    apply Prod.ext
    · exact LinearMap.congr_fun hfg α
    · change r • g.dualMap α - g.dualMap (r • α - h.dualMap β) = 0
      have hz : g.dualMap (h.dualMap β) = 0 := LinearMap.congr_fun hgh β
      simp only [map_sub, map_smul, hz, sub_zero, sub_self]
  · intro hab
    have hb : r • ab.1 - g.dualMap ab.2 = 0 := congrArg Prod.snd hab
    have hπg : π (g.dualMap ab.2) = 0 :=
      LinearMap.congr_fun (comp_zero_of_range_eq_ker g.dualMap π hgπ) ab.2
    have hrπ : r • π ab.1 = 0 := by
      have h := congrArg π hb
      simpa only [map_sub, map_smul, hπg, sub_zero, map_zero] using h
    have hπa : π ab.1 = 0 := hr (by simpa only [smul_zero] using hrπ)
    have hamem : ab.1 ∈ LinearMap.range g.dualMap := by
      rw [hgπ]
      exact hπa
    obtain ⟨t, ht⟩ := LinearMap.mem_range.mp hamem
    have hcycle : g.dualMap (r • t - ab.2) = 0 := by
      simpa only [map_sub, map_smul, ht] using hb
    have hbmem : r • t - ab.2 ∈ LinearMap.range h.dualMap := by
      rw [hhg]
      exact hcycle
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hbmem
    refine ⟨(t, a), ?_⟩
    apply Prod.ext
    · exact ht
    · change r • t - h.dualMap a = ab.2
      rw [ha]
      abel

end SiegelZerosAwei.W30

end

section

namespace SiegelZerosAwei.W30
open Module

variable {R A B C A' B' C' : Type*} [CommRing R]
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
variable [Module R A] [Module R B] [Module R C]
variable [Module R A'] [Module R B'] [Module R C']

theorem exact_of_equivalences (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (f' : A' →ₗ[R] B') (g' : B' →ₗ[R] C')
    (eA : A' ≃ₗ[R] A) (eB : B' ≃ₗ[R] B) (eC : C' ≃ₗ[R] C)
    (hf : eB.toLinearMap.comp f' = f.comp eA.toLinearMap)
    (hg : eC.toLinearMap.comp g' = g.comp eB.toLinearMap)
    (hex : LinearMap.range f' = LinearMap.ker g') :
    LinearMap.range f = LinearMap.ker g := by
  have hf_apply (a : A') : eB (f' a) = f (eA a) := LinearMap.congr_fun hf a
  have hg_apply (b : B') : eC (g' b) = g (eB b) := LinearMap.congr_fun hg b
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨a', rfl⟩ := eA.surjective a
    change g (f (eA a')) = 0
    rw [← hf_apply a', ← hg_apply (f' a')]
    have hz : g' (f' a') = 0 := by
      have hm : f' a' ∈ LinearMap.range f' := ⟨a', rfl⟩
      rw [hex] at hm
      exact hm
    rw [hz, map_zero]
  · intro hb
    obtain ⟨b', rfl⟩ := eB.surjective b
    have hz : g' b' = 0 := by
      apply eC.injective
      rw [map_zero, hg_apply b']
      exact hb
    have hm : b' ∈ LinearMap.range f' := by
      rw [hex]
      exact hz
    obtain ⟨a', ha'⟩ := hm
    refine ⟨eA a', ?_⟩
    rw [← hf_apply a', ha']

universe u
variable {S : Type u} [CommRing S]

theorem scalarCone_dual_interior_exact
    (P : ChainComplex (ModuleCat.{u} S) ℕ) (r : S) (n : ℕ)
    (hlo : LinearMap.range (P.d (n + 1) n).hom.dualMap =
      LinearMap.ker (P.d (n + 2) (n + 1)).hom.dualMap)
    (hhi : LinearMap.range (P.d (n + 2) (n + 1)).hom.dualMap =
      LinearMap.ker (P.d (n + 3) (n + 2)).hom.dualMap) :
    LinearMap.range ((scalarConeComplex P r).d (n + 2) (n + 1)).hom.dualMap =
      LinearMap.ker ((scalarConeComplex P r).d (n + 3) (n + 2)).hom.dualMap := by
  apply exact_of_equivalences
    (((scalarConeComplex P r).d (n + 2) (n + 1)).hom.dualMap)
    (((scalarConeComplex P r).d (n + 3) (n + 2)).hom.dualMap)
    (dualConeDifferential (P.d (n + 2) (n + 1)).hom (P.d (n + 1) n).hom r)
    (dualConeDifferential (P.d (n + 3) (n + 2)).hom (P.d (n + 2) (n + 1)).hom r)
    (dualProdDualEquivDual S (P.X (n + 1)) (P.X n))
    (dualProdDualEquivDual S (P.X (n + 2)) (P.X (n + 1)))
    (dualProdDualEquivDual S (P.X (n + 3)) (P.X (n + 2)))
  · have hd : (scalarConeComplex P r).d (n + 2) (n + 1) = scalarConeMap P r (n + 1) := by
      exact ChainComplex.of_d _ _ (n + 1)
    rw [hd]
    exact coneDifferential_dual_equiv (P.d (n + 2) (n + 1)).hom (P.d (n + 1) n).hom r
  · have hd : (scalarConeComplex P r).d (n + 3) (n + 2) = scalarConeMap P r (n + 2) := by
      exact ChainComplex.of_d _ _ (n + 2)
    rw [hd]
    exact coneDifferential_dual_equiv (P.d (n + 3) (n + 2)).hom (P.d (n + 2) (n + 1)).hom r
  · exact dualConeDifferential_exact _ _ _ r hlo hhi

end SiegelZerosAwei.W30

end

section

namespace SiegelZerosAwei.W30
open Module

variable {R X Y Z : Type*} [CommRing R]
variable [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
variable [Module R X] [Module R Y] [Module R Z]

def dualConeBottom (g : Y →ₗ[R] Z) (r : R) :
    Dual R Z →ₗ[R] (Dual R Y × Dual R Z) :=
  g.dualMap.prod (r • LinearMap.id)

@[simp] theorem dualConeBottom_apply (g : Y →ₗ[R] Z) (r : R) (α : Dual R Z) :
    dualConeBottom g r α = (α.comp g, r • α) := rfl

theorem coneBottom_dual_equiv (g : Y →ₗ[R] Z) (r : R) :
    (dualProdDualEquivDual R Y Z).toLinearMap.comp (dualConeBottom g r) =
      (coneBottom g r).dualMap := by
  apply LinearMap.ext
  intro α
  apply LinearMap.ext
  rintro ⟨y, z⟩
  change α (g y) + r • α z = α (g y + r • z)
  rw [map_add, map_smul]

theorem dualConeBottom_exact (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (r : R)
    (hex : LinearMap.range g.dualMap = LinearMap.ker f.dualMap)
    (hinj : Function.Injective g.dualMap) :
    LinearMap.range (dualConeBottom g r) = LinearMap.ker (dualConeDifferential f g r) := by
  ext ab
  constructor
  · rintro ⟨α, rfl⟩
    apply Prod.ext
    · exact LinearMap.congr_fun (comp_zero_of_range_eq_ker g.dualMap f.dualMap hex) α
    · change r • g.dualMap α - g.dualMap (r • α) = 0
      rw [map_smul, sub_self]
  · intro hab
    have ha : f.dualMap ab.1 = 0 := congrArg Prod.fst hab
    have hb : r • ab.1 - g.dualMap ab.2 = 0 := congrArg Prod.snd hab
    have hm : ab.1 ∈ LinearMap.range g.dualMap := by
      rw [hex]
      exact ha
    obtain ⟨t, ht⟩ := hm
    refine ⟨t, ?_⟩
    apply Prod.ext
    · exact ht
    · change r • t = ab.2
      apply hinj
      rw [map_smul, ht]
      exact sub_eq_zero.mp hb

theorem dualConeBottom_injective (g : Y →ₗ[R] Z) (r : R)
    (hinj : Function.Injective g.dualMap) : Function.Injective (dualConeBottom g r) := by
  intro α β h
  exact hinj (congrArg Prod.fst h)

theorem dualConeBottom_injective_of_regular (g : Y →ₗ[R] Z) (r : R)
    (hr : IsSMulRegular (Dual R Z) r) : Function.Injective (dualConeBottom g r) := by
  intro α β h
  exact hr (congrArg Prod.snd h)

theorem dualConeBottom_endpoint_exact {Q : Type*} [AddCommGroup Q] [Module R Q]
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (r : R) (π : Dual R Y →ₗ[R] Q)
    (hfg : f.dualMap.comp g.dualMap = 0)
    (hgπ : LinearMap.range g.dualMap = LinearMap.ker π)
    (hinj : Function.Injective g.dualMap) (hr : IsSMulRegular Q r) :
    LinearMap.range (dualConeBottom g r) = LinearMap.ker (dualConeDifferential f g r) := by
  ext ab
  constructor
  · rintro ⟨α, rfl⟩
    apply Prod.ext
    · exact LinearMap.congr_fun hfg α
    · change r • g.dualMap α - g.dualMap (r • α) = 0
      rw [map_smul, sub_self]
  · intro hab
    have hb : r • ab.1 - g.dualMap ab.2 = 0 := congrArg Prod.snd hab
    have hπg : π (g.dualMap ab.2) = 0 :=
      LinearMap.congr_fun (comp_zero_of_range_eq_ker g.dualMap π hgπ) ab.2
    have hrπ : r • π ab.1 = 0 := by
      have h := congrArg π hb
      simpa only [map_sub, map_smul, hπg, sub_zero, map_zero] using h
    have hπa : π ab.1 = 0 := hr (by simpa only [smul_zero] using hrπ)
    have hm : ab.1 ∈ LinearMap.range g.dualMap := by
      rw [hgπ]
      exact hπa
    obtain ⟨t, ht⟩ := hm
    refine ⟨t, ?_⟩
    apply Prod.ext
    · exact ht
    · change r • t = ab.2
      apply hinj
      rw [map_smul, ht]
      exact sub_eq_zero.mp hb

universe u
variable {S : Type u} [CommRing S]

theorem scalarCone_dual_one_exact (P : ChainComplex (ModuleCat.{u} S) ℕ) (r : S)
    (hex : LinearMap.range (P.d 1 0).hom.dualMap =
      LinearMap.ker (P.d 2 1).hom.dualMap)
    (hinj : Function.Injective (P.d 1 0).hom.dualMap) :
    LinearMap.range ((scalarConeComplex P r).d 1 0).hom.dualMap =
      LinearMap.ker ((scalarConeComplex P r).d 2 1).hom.dualMap := by
  apply exact_of_equivalences
    (((scalarConeComplex P r).d 1 0).hom.dualMap)
    (((scalarConeComplex P r).d 2 1).hom.dualMap)
    (dualConeBottom (P.d 1 0).hom r)
    (dualConeDifferential (P.d 2 1).hom (P.d 1 0).hom r)
    (LinearEquiv.refl S (Dual S (P.X 0)))
    (dualProdDualEquivDual S (P.X 1) (P.X 0))
    (dualProdDualEquivDual S (P.X 2) (P.X 1))
  · have hd : (scalarConeComplex P r).d 1 0 = scalarConeMap P r 0 := by
      exact ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) 0
    rw [hd]
    exact coneBottom_dual_equiv (P.d 1 0).hom r
  · have hd : (scalarConeComplex P r).d 2 1 = scalarConeMap P r 1 := by
      exact ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) 1
    rw [hd]
    exact coneDifferential_dual_equiv (P.d 2 1).hom (P.d 1 0).hom r
  · exact dualConeBottom_exact _ _ r hex hinj

end SiegelZerosAwei.W30

end

section

namespace SiegelZerosAwei.W30
open Module
universe u
variable {R : Type u} [CommRing R]

theorem chain_dual_comp_zero (P : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (P.d (n + 2) (n + 1)).hom.dualMap.comp (P.d (n + 1) n).hom.dualMap = 0 := by
  apply LinearMap.ext
  intro α
  apply LinearMap.ext
  intro x
  change α ((P.d (n + 1) n).hom ((P.d (n + 2) (n + 1)).hom x)) = 0
  have hz : (P.d (n + 1) n).hom ((P.d (n + 2) (n + 1)).hom x) = 0 :=
    LinearMap.congr_fun (chain_linear_comp_zero P n) x
  rw [hz, map_zero]

theorem scalarCone_dual_endpoint_exact
    {Q : Type u} [AddCommGroup Q] [Module R Q]
    (P : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) (n : ℕ)
    (π : Dual R (P.X (n + 2)) →ₗ[R] Q)
    (hlo : LinearMap.range (P.d (n + 1) n).hom.dualMap =
      LinearMap.ker (P.d (n + 2) (n + 1)).hom.dualMap)
    (hπ : LinearMap.range (P.d (n + 2) (n + 1)).hom.dualMap = LinearMap.ker π)
    (hr : IsSMulRegular Q r) :
    LinearMap.range ((scalarConeComplex P r).d (n + 2) (n + 1)).hom.dualMap =
      LinearMap.ker ((scalarConeComplex P r).d (n + 3) (n + 2)).hom.dualMap := by
  apply exact_of_equivalences
    (((scalarConeComplex P r).d (n + 2) (n + 1)).hom.dualMap)
    (((scalarConeComplex P r).d (n + 3) (n + 2)).hom.dualMap)
    (dualConeDifferential (P.d (n + 2) (n + 1)).hom (P.d (n + 1) n).hom r)
    (dualConeDifferential (P.d (n + 3) (n + 2)).hom (P.d (n + 2) (n + 1)).hom r)
    (dualProdDualEquivDual R (P.X (n + 1)) (P.X n))
    (dualProdDualEquivDual R (P.X (n + 2)) (P.X (n + 1)))
    (dualProdDualEquivDual R (P.X (n + 3)) (P.X (n + 2)))
  · have hd : (scalarConeComplex P r).d (n + 2) (n + 1) = scalarConeMap P r (n + 1) :=
      ChainComplex.of_d _ _ (n + 1)
    rw [hd]
    exact coneDifferential_dual_equiv (P.d (n + 2) (n + 1)).hom (P.d (n + 1) n).hom r
  · have hd : (scalarConeComplex P r).d (n + 3) (n + 2) = scalarConeMap P r (n + 2) :=
      ChainComplex.of_d _ _ (n + 2)
    rw [hd]
    exact coneDifferential_dual_equiv (P.d (n + 3) (n + 2)).hom (P.d (n + 2) (n + 1)).hom r
  · exact dualCone_endpoint_exact _ _ _ r π
      (chain_dual_comp_zero P (n + 1)) (chain_dual_comp_zero P n) hlo hπ hr

theorem scalarCone_dual_one_endpoint_exact
    {Q : Type u} [AddCommGroup Q] [Module R Q]
    (P : ChainComplex (ModuleCat.{u} R) ℕ) (r : R)
    (π : Dual R (P.X 1) →ₗ[R] Q)
    (hπ : LinearMap.range (P.d 1 0).hom.dualMap = LinearMap.ker π)
    (hinj : Function.Injective (P.d 1 0).hom.dualMap)
    (hr : IsSMulRegular Q r) :
    LinearMap.range ((scalarConeComplex P r).d 1 0).hom.dualMap =
      LinearMap.ker ((scalarConeComplex P r).d 2 1).hom.dualMap := by
  apply exact_of_equivalences
    (((scalarConeComplex P r).d 1 0).hom.dualMap)
    (((scalarConeComplex P r).d 2 1).hom.dualMap)
    (dualConeBottom (P.d 1 0).hom r)
    (dualConeDifferential (P.d 2 1).hom (P.d 1 0).hom r)
    (LinearEquiv.refl R (Dual R (P.X 0)))
    (dualProdDualEquivDual R (P.X 1) (P.X 0))
    (dualProdDualEquivDual R (P.X 2) (P.X 1))
  · have hd : (scalarConeComplex P r).d 1 0 = scalarConeMap P r 0 := by
      exact ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) 0
    rw [hd]
    exact coneBottom_dual_equiv (P.d 1 0).hom r
  · have hd : (scalarConeComplex P r).d 2 1 = scalarConeMap P r 1 := by
      exact ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) 1
    rw [hd]
    exact coneDifferential_dual_equiv (P.d 2 1).hom (P.d 1 0).hom r
  · exact dualConeBottom_endpoint_exact _ _ r π (chain_dual_comp_zero P 0) hπ hinj hr

theorem scalarCone_dual_low_exact
    {Q : Type u} [AddCommGroup Q] [Module R Q]
    (P : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) (n : ℕ)
    (π : Dual R (P.X (n + 1)) →ₗ[R] Q)
    (hinj : Function.Injective (P.d 1 0).hom.dualMap)
    (hlow : ∀ k, k < n → LinearMap.range (P.d (k + 1) k).hom.dualMap =
      LinearMap.ker (P.d (k + 2) (k + 1)).hom.dualMap)
    (hπ : LinearMap.range (P.d (n + 1) n).hom.dualMap = LinearMap.ker π)
    (hr : IsSMulRegular Q r) :
    ∀ k, k < n + 1 →
      LinearMap.range ((scalarConeComplex P r).d (k + 1) k).hom.dualMap =
        LinearMap.ker ((scalarConeComplex P r).d (k + 2) (k + 1)).hom.dualMap := by
  intro k hk
  by_cases hkn : k < n
  · cases k with
    | zero => exact scalarCone_dual_one_exact P r (hlow 0 hkn) hinj
    | succ k =>
      exact scalarCone_dual_interior_exact P r k (hlow k (by omega))
        (hlow (k + 1) hkn)
  · have hkn : k = n := by omega
    subst k
    cases n with
    | zero => exact scalarCone_dual_one_endpoint_exact P r π hπ hinj hr
    | succ n =>
      exact scalarCone_dual_endpoint_exact P r n π (hlow n (by omega)) hπ hr

end SiegelZerosAwei.W30

end

end SiegelZeros

end OAI
