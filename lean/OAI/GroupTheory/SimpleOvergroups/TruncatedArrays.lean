import Mathlib
import OAI.GroupTheory.FiniteType.SequentialLimit
import OAI.GroupTheory.SimpleOvergroups.EnlargementCore
import OAI.GroupTheory.SimpleOvergroups.TruncatedAction

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding
noncomputable section
open scoped Classical

namespace KeyBall
variable {X K : Type*} (C : KeyBall X K) (D : Type*) [AddCommMonoid D]

def arrayBall (b : ℕ) (p : X →₀ D) : Prop := ∀ x ∈ p.support, x ∈ C.ball b

def arrayCollect : (X →₀ D) →+ (K →₀ D) := Finsupp.mapDomain.addMonoidHom C.key

@[simp] theorem arrayCollect_single (x : X) (d : D) :
    C.arrayCollect D (Finsupp.single x d) = Finsupp.single (C.key x) d :=
  Finsupp.mapDomain_single

@[simp] theorem arrayBall_zero (b : ℕ) : C.arrayBall D b 0 := by simp [arrayBall]

theorem arrayBall_single {b : ℕ} {x : X} (hx : x ∈ C.ball b) (d : D) :
    C.arrayBall D b (Finsupp.single x d) := by
  intro y hy
  simpa only [((Finsupp.mem_support_single y x d).mp hy).1] using hx

theorem arrayBall_add {b : ℕ} {p q : X →₀ D}
    (hp : C.arrayBall D b p) (hq : C.arrayBall D b q) : C.arrayBall D b (p+q) := by
  intro x hx
  rcases Finset.mem_union.mp (Finsupp.support_add hx) with hx | hx
  · exact hp x hx
  · exact hq x hx

theorem arrayBall_mono {b c : ℕ} (hbc : b ≤ c) {p : X →₀ D}
    (hp : C.arrayBall D b p) : C.arrayBall D c p := fun x hx => C.mono hbc (hp x hx)

theorem array_induction {b : ℕ} {P : (X →₀ D) → Prop}
    (hz : P 0) (hs : ∀ x ∈ C.ball b, ∀ d : D, P (Finsupp.single x d))
    (ha : ∀ p q, P p → P q → P (p+q)) {p : X →₀ D} (hp : C.arrayBall D b p) : P p := by
  revert hp
  induction p using Finsupp.induction with
  | zero => exact fun _ => hz
  | single_add x d p hx hd ih =>
    intro hp
    have hb : x ∈ C.ball b := hp x (by rw [Finsupp.support_single_add hx hd]; simp)
    have hq : C.arrayBall D b p := by
      intro y hy
      exact hp y (by rw [Finsupp.support_single_add hx hd]; simp [hy])
    exact ha _ _ (hs x hb d) (ih hq)

def arrays : KeyBall (X →₀ D) (K →₀ D) where
  ball := C.arrayBall D
  mono := fun _ _ hbc _ hp => C.arrayBall_mono D hbc hp
  key := C.arrayCollect D

variable (m : ℕ) [Nonempty X]

def arrayCanonical : (X →₀ D) →+ (X →₀ D) :=
  Finsupp.mapDomain.addMonoidHom (C.canonical m)

@[simp] theorem arrayCanonical_single (x : X) (d : D) :
    C.arrayCanonical D m (Finsupp.single x d) = Finsupp.single (C.canonical m x) d :=
  Finsupp.mapDomain_single

theorem arrayCanonical_mem {b : ℕ} {p : X →₀ D}
    (hp : C.arrayBall D b p) (hb : b ≤ m) : C.arrayBall D b (C.arrayCanonical D m p) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hy)
  exact C.canonical_mem m (hp x hx) hb

theorem arrayCanonical_congr {p q : X →₀ D}
    (he : C.arrayCollect D p = C.arrayCollect D q) :
    C.arrayCanonical D m p = C.arrayCanonical D m q := by
  change Finsupp.mapDomain (C.representative m ∘ C.key) p =
    Finsupp.mapDomain (C.representative m ∘ C.key) q
  rw [Finsupp.mapDomain_comp, Finsupp.mapDomain_comp]
  exact congrArg (Finsupp.mapDomain (C.representative m)) he

theorem arrayCollect_canonical {b : ℕ} {p : X →₀ D}
    (hp : C.arrayBall D b p) (hb : b ≤ m) :
    C.arrayCollect D (C.arrayCanonical D m p) = C.arrayCollect D p := by
  change Finsupp.mapDomain C.key (Finsupp.mapDomain (C.canonical m) p) =
    Finsupp.mapDomain C.key p
  rw [← Finsupp.mapDomain_comp]
  exact Finsupp.mapDomain_congr (fun x hx => C.key_canonical m (hp x hx) hb)

end KeyBall

namespace KeyBall
variable {V K : Type*} [Monoid V] (C : KeyBall V K) (D : Type*) [Semiring D]

def algebraBall (b : ℕ) (p : MonoidAlgebra D V) : Prop := C.arrayBall D b p.coeff

def algebraCollect : MonoidAlgebra D V →+ (K →₀ D) :=
  (C.arrayCollect D).comp MonoidAlgebra.coeffAddEquiv.toAddMonoidHom

@[simp] theorem algebraCollect_single {V K : Type*} [Monoid V]
    (C : KeyBall V K) (D : Type*) [Semiring D] (v : V) (d : D) :
    C.algebraCollect D (MonoidAlgebra.single v d) = Finsupp.single (C.key v) d := by
  change C.arrayCollect D (Finsupp.single v d) = _
  exact C.arrayCollect_single D v d

@[simp] theorem algebraBall_zero (b : ℕ) : C.algebraBall D b 0 := C.arrayBall_zero D b

theorem algebraBall_single {V K : Type*} [Monoid V]
    (C : KeyBall V K) (D : Type*) [Semiring D] {b : ℕ} {v : V}
    (hv : v ∈ C.ball b) (d : D) :
    C.algebraBall D b (MonoidAlgebra.single v d) := C.arrayBall_single D hv d

theorem algebraBall_add {b : ℕ} {p q : MonoidAlgebra D V}
    (hp : C.algebraBall D b p) (hq : C.algebraBall D b q) : C.algebraBall D b (p+q) :=
  C.arrayBall_add D hp hq

theorem algebra_induction {b : ℕ} {P : MonoidAlgebra D V → Prop}
    (hz : P 0) (hs : ∀ v ∈ C.ball b, ∀ d : D, P (MonoidAlgebra.single v d))
    (ha : ∀ p q, P p → P q → P (p+q)) {p : MonoidAlgebra D V} (hp : C.algebraBall D b p) :
    P p := by
  have hh := C.array_induction D (P := fun a => P (MonoidAlgebra.ofCoeff a))
    hz (by intro v hv d; exact hs v hv d)
    (by intro p q hp hq; exact ha _ _ hp hq) hp
  simpa only [MonoidAlgebra.ofCoeff_coeff] using hh

variable (m : ℕ)

def algebraCanonical : MonoidAlgebra D V →+ MonoidAlgebra D V :=
  MonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom.comp
    ((C.arrayCanonical D m).comp MonoidAlgebra.coeffAddEquiv.toAddMonoidHom)

@[simp] theorem algebraCanonical_single (v : V) (d : D) :
    C.algebraCanonical D m (MonoidAlgebra.single v d) =
      MonoidAlgebra.single (C.canonical m v) d := by
  change MonoidAlgebra.ofCoeff (C.arrayCanonical D m (Finsupp.single v d)) = _
  rw [C.arrayCanonical_single D m, MonoidAlgebra.ofCoeff_single]

theorem algebraCanonical_congr {p q : MonoidAlgebra D V}
    (he : C.algebraCollect D p = C.algebraCollect D q) :
    C.algebraCanonical D m p = C.algebraCanonical D m q :=
  congrArg MonoidAlgebra.ofCoeff (C.arrayCanonical_congr D m he)

end KeyBall

namespace ActionCalculus
variable {V X K L : Type*} [Group V] [MulAction V X] {m : ℕ}
  (C : ActionCalculus V X K L m) (D : Type*) [Ring D]

theorem algebra_mul_mem {p q : MonoidAlgebra D V} {b c : ℕ}
    (hp : C.group.algebraBall D b p) (hq : C.group.algebraBall D c q) :
    C.group.algebraBall D (b+c) (p*q) := by
  apply C.group.algebra_induction D (P := fun p => C.group.algebraBall D (b+c) (p*q))
    ?_ ?_ ?_ hp
  · simp
  · intro u hu a
    apply C.group.algebra_induction D
      (P := fun q => C.group.algebraBall D (b+c) (MonoidAlgebra.single u a*q)) ?_ ?_ ?_ hq
    · simp
    · intro v hv d
      rw [MonoidAlgebra.single_mul_single]
      exact C.group.algebraBall_single D (C.mul_mem hu hv) _
    · intro x y hx hy
      rw [mul_add]
      exact C.group.algebraBall_add D hx hy
  · intro x y hx hy
    rw [add_mul]
    exact C.group.algebraBall_add D hx hy

theorem algebraCollect_product {p q : MonoidAlgebra D V} {b c : ℕ}
    (hp : C.group.algebraBall D b p) (hq : C.group.algebraBall D c q) (hbc : b+c ≤ m) :
    C.group.algebraCollect D (C.group.algebraCanonical D m p * C.group.algebraCanonical D m q) =
      C.group.algebraCollect D (p*q) := by
  apply C.group.algebra_induction D
    (P := fun p => C.group.algebraCollect D
      (C.group.algebraCanonical D m p * C.group.algebraCanonical D m q) =
      C.group.algebraCollect D (p*q)) ?_ ?_ ?_ hp
  · simp
  · intro u hu a
    apply C.group.algebra_induction D
      (P := fun q => C.group.algebraCollect D
        (C.group.algebraCanonical D m (MonoidAlgebra.single u a) * C.group.algebraCanonical D m q) =
        C.group.algebraCollect D (MonoidAlgebra.single u a*q)) ?_ ?_ ?_ hq
    · simp
    · intro v hv d
      simp only [KeyBall.algebraCanonical_single, MonoidAlgebra.single_mul_single,
        KeyBall.algebraCollect_single]
      have hk := C.mul_congr (C.group.canonical_mem m hu (by omega))
        (C.group.canonical_mem m hv (by omega)) hu hv hbc hbc
        (C.group.key_canonical m hu (by omega)) (C.group.key_canonical m hv (by omega))
      rw [hk]
    · intro x y hx hy
      simp only [map_add, mul_add, hx, hy]
  · intro x y hx hy
    simp only [map_add, add_mul, hx, hy]

theorem algebraCollect_mul_congr {p q p' q' : MonoidAlgebra D V} {b c b' c' : ℕ}
    (hp : C.group.algebraBall D b p) (hq : C.group.algebraBall D c q)
    (hp' : C.group.algebraBall D b' p') (hq' : C.group.algebraBall D c' q')
    (hbc : b+c ≤ m) (hbc' : b'+c' ≤ m)
    (hep : C.group.algebraCollect D p = C.group.algebraCollect D p')
    (heq : C.group.algebraCollect D q = C.group.algebraCollect D q') :
    C.group.algebraCollect D (p*q) = C.group.algebraCollect D (p'*q') := by
  rw [← C.algebraCollect_product D hp hq hbc, ← C.algebraCollect_product D hp' hq' hbc',
    C.group.algebraCanonical_congr D m hep, C.group.algebraCanonical_congr D m heq]

theorem array_action_mem {p : MonoidAlgebra D V} {x : X →₀ D} {b c : ℕ}
    (hp : C.group.algebraBall D b p) (hx : C.point.arrayBall D c x) :
    C.point.arrayBall D (b+c) (SourceEnlargement.ringAction p x) := by
  apply C.group.algebra_induction D
    (P := fun p => C.point.arrayBall D (b+c) (SourceEnlargement.ringAction p x)) ?_ ?_ ?_ hp
  · simp
  · intro v hv a
    apply C.point.array_induction D
      (P := fun x => C.point.arrayBall D (b+c)
        (SourceEnlargement.ringAction (MonoidAlgebra.single v a) x)) ?_ ?_ ?_ hx
    · simp
    · intro z hz d
      rw [SourceEnlargement.ringAction_single]
      exact C.point.arrayBall_single D (C.smul_mem hv hz) _
    · intro x y hx hy
      rw [map_add]
      exact C.point.arrayBall_add D hx hy
  · intro p q hp hq
    rw [map_add]
    exact C.point.arrayBall_add D hp hq

variable [Nonempty X]

theorem arrayCollect_action {p : MonoidAlgebra D V} {x : X →₀ D} {b c : ℕ}
    (hp : C.group.algebraBall D b p) (hx : C.point.arrayBall D c x) (hbc : b+c ≤ m) :
    C.point.arrayCollect D (SourceEnlargement.ringAction (C.group.algebraCanonical D m p)
      (C.point.arrayCanonical D m x)) =
      C.point.arrayCollect D (SourceEnlargement.ringAction p x) := by
  apply C.group.algebra_induction D
    (P := fun p => C.point.arrayCollect D (SourceEnlargement.ringAction (C.group.algebraCanonical D m p)
      (C.point.arrayCanonical D m x)) = C.point.arrayCollect D (SourceEnlargement.ringAction p x))
    ?_ ?_ ?_ hp
  · simp
  · intro v hv a
    apply C.point.array_induction D
      (P := fun x => C.point.arrayCollect D
        (SourceEnlargement.ringAction (C.group.algebraCanonical D m (MonoidAlgebra.single v a))
          (C.point.arrayCanonical D m x)) =
        C.point.arrayCollect D (SourceEnlargement.ringAction (MonoidAlgebra.single v a) x))
      ?_ ?_ ?_ hx
    · simp
    · intro z hz d
      simp only [KeyBall.algebraCanonical_single, KeyBall.arrayCanonical_single,
        SourceEnlargement.ringAction_single, KeyBall.arrayCollect_single]
      have hk := C.smul_congr (C.group.canonical_mem m hv (by omega))
        (C.point.canonical_mem m hz (by omega)) hv hz hbc hbc
        (C.group.key_canonical m hv (by omega)) (C.point.key_canonical m hz (by omega))
      rw [hk]
    · intro x y hx hy
      simp only [map_add, hx, hy]
  · intro p q hp hq
    simp only [map_add]
    change C.point.arrayCollect D
      (SourceEnlargement.ringAction (C.group.algebraCanonical D m p) (C.point.arrayCanonical D m x) +
        SourceEnlargement.ringAction (C.group.algebraCanonical D m q) (C.point.arrayCanonical D m x)) =
      C.point.arrayCollect D (SourceEnlargement.ringAction p x + SourceEnlargement.ringAction q x)
    simp only [map_add, hp, hq]

theorem arrayCollect_action_congr {p p' : MonoidAlgebra D V} {x x' : X →₀ D} {b c b' c' : ℕ}
    (hp : C.group.algebraBall D b p) (hx : C.point.arrayBall D c x)
    (hp' : C.group.algebraBall D b' p') (hx' : C.point.arrayBall D c' x')
    (hbc : b+c ≤ m) (hbc' : b'+c' ≤ m)
    (hep : C.group.algebraCollect D p = C.group.algebraCollect D p')
    (hex : C.point.arrayCollect D x = C.point.arrayCollect D x') :
    C.point.arrayCollect D (SourceEnlargement.ringAction p x) =
      C.point.arrayCollect D (SourceEnlargement.ringAction p' x') := by
  rw [← C.arrayCollect_action D hp hx hbc, ← C.arrayCollect_action D hp' hx' hbc',
    C.group.algebraCanonical_congr D m hep, C.point.arrayCanonical_congr D m hex]

def enlargement :
    ActionCalculus (MonoidAlgebra D V)ˣ (X →₀ D) ((K →₀ D) × (K →₀ D)) (L →₀ D) m where
  group :=
    { ball := fun b v => C.group.algebraBall D b v.val ∧ C.group.algebraBall D b v.inv
      mono := by
        intro b c hbc v hv
        exact ⟨C.group.arrayBall_mono D hbc hv.1, C.group.arrayBall_mono D hbc hv.2⟩
      key := fun v => (C.group.algebraCollect D v.val, C.group.algebraCollect D v.inv) }
  point := C.point.arrays D
  one_mem b := by
    have h : C.group.algebraBall D b 1 := by
      rw [MonoidAlgebra.one_def]
      exact C.group.algebraBall_single D (C.one_mem b) 1
    exact ⟨h,h⟩
  inv_mem := fun h => ⟨h.2,h.1⟩
  mul_mem := by
    intro b c u v hu hv
    refine ⟨C.algebra_mul_mem D hu.1 hv.1, ?_⟩
    change C.group.algebraBall D (b+c) (v.inv*u.inv)
    simpa only [Nat.add_comm] using C.algebra_mul_mem D hv.2 hu.2
  smul_mem := fun hu hx => C.array_action_mem D hu.1 hx
  inv_congr := fun he => Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
  mul_congr := by
    intro b c b' c' u v u' v' hu hv hu' hv' hb hb' heu hev
    apply Prod.ext
    · exact C.algebraCollect_mul_congr D hu.1 hv.1 hu'.1 hv'.1 hb hb'
        (congrArg Prod.fst heu) (congrArg Prod.fst hev)
    · exact C.algebraCollect_mul_congr D hv.2 hu.2 hv'.2 hu'.2 (by omega) (by omega)
        (congrArg Prod.snd hev) (congrArg Prod.snd heu)
  smul_congr := by
    intro b c b' c' u x u' x' hu hx hu' hx' hb hb' heu hex
    exact C.arrayCollect_action_congr D hu.1 hx hu'.1 hx' hb hb' (congrArg Prod.fst heu) hex

theorem unitMap_mem (E : D) (hE : E*E = E) {v : V} {b : ℕ} (hv : v ∈ C.group.ball b) :
    SourceEnlargement.unitMap E hE v ∈ (C.enlargement D).group.ball b := by
  constructor
  · exact C.group.algebraBall_add D (C.group.algebraBall_single D (C.one_mem b) _)
      (C.group.algebraBall_single D hv _)
  · exact C.group.algebraBall_add D (C.group.algebraBall_single D (C.one_mem b) _)
      (C.group.algebraBall_single D (C.inv_mem hv) _)

theorem basis_mem {x : X} {b : ℕ} (hx : x ∈ C.point.ball b) :
    Finsupp.single x (1 : D) ∈ (C.enlargement D).point.ball b :=
  C.point.arrayBall_single D hx 1

end ActionCalculus
end
end SimpleFInftyOvergroups.BoundedEncoding

end OAI
