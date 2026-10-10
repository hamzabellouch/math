import Mathlib

namespace OAI

noncomputable section
namespace DeligneDrinfeld

theorem freeLie_induction {R α : Type*} [CommRing R]
    {P : FreeLieAlgebra R α → Prop} (h0 : P 0)
    (hg : ∀ a, P (FreeLieAlgebra.of R a))
    (ha : ∀ a b, P a → P b → P (a+b))
    (hs : ∀ (r : R) a, P a → P (r • a))
    (hl : ∀ a b, P a → P b → P ⁅a,b⁆) (q : FreeLieAlgebra R α) : P q := by
  let K : LieSubalgebra R (FreeLieAlgebra R α) :=
    { carrier := {a | P a}
      zero_mem' := h0
      add_mem' := fun ha' hb' => ha _ _ ha' hb'
      smul_mem' := fun r a h => hs r a h
      lie_mem' := fun ha' hb' => hl _ _ ha' hb' }
  let f : FreeLieAlgebra R α →ₗ⁅R⁆ K :=
    FreeLieAlgebra.lift R (fun a => ⟨FreeLieAlgebra.of R a, hg a⟩)
  have hf : K.incl.comp f = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro a
    simp [f]
  have h := (f q).property
  change P ((K.incl.comp f) q) at h
  simpa only [hf, LieHom.id_apply] using h

abbrev L := FreeLieAlgebra ℚ Bool
def x : L := FreeLieAlgebra.of ℚ false
def y : L := FreeLieAlgebra.of ℚ true

def eval {M : Type*} [LieRing M] [LieAlgebra ℚ M] (a b : M) : L →ₗ⁅ℚ⁆ M :=
  FreeLieAlgebra.lift ℚ (fun i => if i then b else a)

abbrev Edge := {p : Fin 4 × Fin 4 // p.1 < p.2}
abbrev BraidFree := FreeLieAlgebra ℚ Edge

def chord (i j : Fin 4) : BraidFree :=
  if h : i < j then FreeLieAlgebra.of ℚ ⟨(i, j), h⟩
  else if h : j < i then FreeLieAlgebra.of ℚ ⟨(j, i), h⟩ else 0

def braidRelations : Set BraidFree :=
  {z | (∃ i j k l : Fin 4,
    i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
      z = ⁅chord i j, chord k l⁆) ∨
    (∃ i j k : Fin 4, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      z = ⁅chord i j, chord i k + chord j k⁆)}

def braidIdeal : LieIdeal ℚ BraidFree :=
  LieSubmodule.lieSpan ℚ BraidFree braidRelations

abbrev T4 := BraidFree ⧸ braidIdeal
def t (i j : Fin 4) : T4 := LieSubmodule.Quotient.mk (chord i j)

def IsSolution (p : L) : Prop :=
  p + eval y x p = 0 ∧
  p + eval y (-x-y) p + eval (-x-y) x p = 0 ∧
  eval (t 0 1) (t 1 2 + t 1 3) p + eval (t 0 2 + t 1 2) (t 2 3) p =
    eval (t 1 2) (t 2 3) p + eval (t 0 1 + t 0 2) (t 1 3 + t 2 3) p +
      eval (t 0 1) (t 1 2) p

def W : Submodule ℚ L where
  carrier := {p | IsSolution p}
  zero_mem' := by simp [IsSolution]
  add_mem' := by
    intro p q hp hq
    rcases hp with ⟨hp1, hp2, hp3⟩
    rcases hq with ⟨hq1, hq2, hq3⟩
    refine ⟨?_, ?_, ?_⟩
    · simp only [map_add]
      calc
        _ = (p + eval y x p) + (q + eval y x q) := by abel
        _ = 0 := by rw [hp1, hq1, add_zero]
    · simp only [map_add]
      calc
        _ = (p + eval y (-x-y) p + eval (-x-y) x p) +
            (q + eval y (-x-y) q + eval (-x-y) x q) := by abel
        _ = 0 := by rw [hp2, hq2, add_zero]
    · simp only [map_add]
      calc
        _ = (eval (t 0 1) (t 1 2 + t 1 3) p + eval (t 0 2 + t 1 2) (t 2 3) p) +
            (eval (t 0 1) (t 1 2 + t 1 3) q + eval (t 0 2 + t 1 2) (t 2 3) q) := by abel
        _ = _ := by rw [hp3, hq3]; abel
  smul_mem' := by
    intro a p hp
    rcases hp with ⟨hp1, hp2, hp3⟩
    change IsSolution (a • p)
    simp only [IsSolution, map_smul]
    constructor
    · simpa only [smul_add, smul_zero] using congrArg (a • ·) hp1
    constructor
    · simpa only [smul_add, smul_zero] using congrArg (a • ·) hp2
    · simpa only [smul_add] using congrArg (a • ·) hp3

structure Tangent where
  base : L
  velocity : L

def Tangent.equiv : Tangent ≃ L × L where
  toFun z := (z.base, z.velocity)
  invFun z := ⟨z.1, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup Tangent := Tangent.equiv.addCommGroup
instance : Module ℚ Tangent := Tangent.equiv.addEquiv.module ℚ
instance : Bracket Tangent Tangent :=
  ⟨fun a b => ⟨⁅a.base, b.base⁆,
    ⁅a.velocity, b.base⁆ + ⁅a.base, b.velocity⁆⟩⟩

@[ext] theorem Tangent.ext {a b : Tangent} (h : a.base = b.base)
    (k : a.velocity = b.velocity) : a = b := by cases a; cases b; simp_all

@[simp] theorem Tangent.base_zero : (0 : Tangent).base = 0 := rfl
@[simp] theorem Tangent.velocity_zero : (0 : Tangent).velocity = 0 := rfl
@[simp] theorem Tangent.base_add (a b : Tangent) : (a+b).base = a.base+b.base := rfl
@[simp] theorem Tangent.velocity_add (a b : Tangent) :
    (a+b).velocity = a.velocity+b.velocity := rfl
@[simp] theorem Tangent.base_smul (q : ℚ) (a : Tangent) : (q • a).base = q • a.base := rfl
@[simp] theorem Tangent.velocity_smul (q : ℚ) (a : Tangent) :
    (q • a).velocity = q • a.velocity := rfl
@[simp] theorem Tangent.base_lie (a b : Tangent) : ⁅a,b⁆.base = ⁅a.base,b.base⁆ := rfl
@[simp] theorem Tangent.velocity_lie (a b : Tangent) :
    ⁅a,b⁆.velocity = ⁅a.velocity,b.base⁆ + ⁅a.base,b.velocity⁆ := rfl

instance : LieRing Tangent where
  add_lie a b c := by
    apply Tangent.equiv.injective
    apply Prod.ext
    · exact add_lie a.base b.base c.base
    · change ⁅a.velocity + b.velocity, c.base⁆ + ⁅a.base + b.base, c.velocity⁆ =
        (⁅a.velocity, c.base⁆ + ⁅a.base, c.velocity⁆) +
          (⁅b.velocity, c.base⁆ + ⁅b.base, c.velocity⁆)
      simp only [add_lie]
      abel
  lie_add a b c := by
    apply Tangent.equiv.injective
    apply Prod.ext
    · exact lie_add a.base b.base c.base
    · change ⁅a.velocity, b.base + c.base⁆ + ⁅a.base, b.velocity + c.velocity⁆ =
        (⁅a.velocity, b.base⁆ + ⁅a.base, b.velocity⁆) +
          (⁅a.velocity, c.base⁆ + ⁅a.base, c.velocity⁆)
      simp only [lie_add]
      abel
  lie_self a := by
    apply Tangent.equiv.injective
    apply Prod.ext
    · exact lie_self a.base
    · change ⁅a.velocity, a.base⁆ + ⁅a.base, a.velocity⁆ = 0
      rw [← lie_skew a.velocity a.base]
      exact neg_add_cancel _
  leibniz_lie a b c := by
    apply Tangent.equiv.injective
    apply Prod.ext
    · exact leibniz_lie a.base b.base c.base
    · change ⁅a.velocity, ⁅b.base, c.base⁆⁆ +
          ⁅a.base, ⁅b.velocity, c.base⁆ + ⁅b.base, c.velocity⁆⁆ =
        (⁅⁅a.velocity, b.base⁆ + ⁅a.base, b.velocity⁆, c.base⁆ +
          ⁅⁅a.base, b.base⁆, c.velocity⁆) +
        (⁅b.velocity, ⁅a.base, c.base⁆⁆ +
          ⁅b.base, ⁅a.velocity, c.base⁆ + ⁅a.base, c.velocity⁆⁆)
      simp only [lie_add, add_lie, lie_lie]
      abel

instance : LieAlgebra ℚ Tangent where
  lie_smul scalar left right := by
    apply Tangent.equiv.injective
    apply Prod.ext
    · exact lie_smul scalar left.base right.base
    · change ⁅left.velocity, scalar • right.base⁆ + ⁅left.base, scalar • right.velocity⁆ =
        scalar • (⁅left.velocity, right.base⁆ + ⁅left.base, right.velocity⁆)
      simp only [lie_smul, smul_add]

def tangentLift (p : L) : L →ₗ⁅ℚ⁆ Tangent :=
  FreeLieAlgebra.lift ℚ (fun i => if i then ⟨y, ⁅y,p⁆⟩ else ⟨x, 0⟩)

def D (p q : L) : L := (tangentLift p q).velocity

def ihara (p q : L) : L := D p q - D q p + ⁅p,q⁆

@[simp] theorem eval_x {M : Type*} [LieRing M] [LieAlgebra ℚ M] (a b : M) :
    eval a b x = a := by simp [eval, x]
@[simp] theorem eval_y {M : Type*} [LieRing M] [LieAlgebra ℚ M] (a b : M) :
    eval a b y = b := by simp [eval, y]

def Tangent.baseHom : Tangent →ₗ⁅ℚ⁆ L where
  toFun := Tangent.base
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

@[simp] theorem tangentLift_base (p q : L) : (tangentLift p q).base = q := by
  have h : Tangent.baseHom.comp (tangentLift p) = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro i
    cases i <;> simp [tangentLift, Tangent.baseHom, x, y] <;> rfl
  exact LieHom.congr_fun h q

@[simp] theorem D_x (p : L) : D p x = 0 := by simp [D, tangentLift, x]
@[simp] theorem D_y (p : L) : D p y = ⁅y,p⁆ := by simp [D, tangentLift, y]
@[simp] theorem D_zero (p : L) : D p 0 = 0 := by simp [D]
@[simp] theorem D_add (p q r : L) : D p (q+r) = D p q + D p r := by simp [D]
@[simp] theorem D_smul (p q : L) (a : ℚ) : D p (a • q) = a • D p q := by simp [D]
theorem D_lie (p q r : L) : D p ⁅q,r⁆ = ⁅D p q,r⁆ + ⁅q,D p r⁆ := by
  simp [D, LieHom.map_lie]

def derivation (p : L) : LieDerivation ℚ L L where
  toFun := D p
  map_add' := D_add p
  map_smul' a q := D_smul p q a
  leibniz' a b := by
    change D p ⁅a,b⁆ = ⁅a,D p b⁆ - ⁅b,D p a⁆
    rw [D_lie, sub_eq_add_neg, lie_skew, add_comm]

@[simp] theorem derivation_apply (p q : L) : derivation p q = D p q := rfl

theorem derivation_ext {d₁ d₂ : LieDerivation ℚ L L}
    (hx : d₁ x = d₂ x) (hy : d₁ y = d₂ y) : d₁ = d₂ := by
  ext q
  induction q using freeLie_induction with
  | h0 => simp
  | hg i => cases i; exact hx; exact hy
  | ha a b ha hb => simp [ha, hb]
  | hs r a ha => simp [ha]
  | hl a b ha hb => simp [ha, hb]

@[simp] theorem D_zero_left (q : L) : D 0 q = 0 := by
  have h : derivation 0 = 0 := by
    apply derivation_ext <;> simp
  exact LieDerivation.congr_fun h q

@[simp] theorem D_add_left (p q r : L) : D (p+q) r = D p r + D q r := by
  have h : derivation (p+q) = derivation p + derivation q := by
    apply derivation_ext <;> simp [lie_add]
  exact LieDerivation.congr_fun h r

@[simp] theorem D_smul_left (p q : L) (a : ℚ) : D (a • p) q = a • D p q := by
  have h : derivation (a • p) = a • derivation p := by
    apply derivation_ext <;> simp
  exact LieDerivation.congr_fun h q

inductive WeightedWord {α : Type*} (wt : α → ℕ) : ℕ → FreeLieAlgebra ℚ α → Prop
  | generator (a : α) : WeightedWord wt (wt a) (FreeLieAlgebra.of ℚ a)
  | bracket {n m a b} : WeightedWord wt n a → WeightedWord wt m b →
      WeightedWord wt (n+m) ⁅a,b⁆

def weightPiece {α : Type*} (wt : α → ℕ) (n : ℕ) : Submodule ℚ (FreeLieAlgebra ℚ α) :=
  Submodule.span ℚ {p | WeightedWord wt n p}

abbrev OddFree := FreeLieAlgebra ℚ ℕ
def oddWeight (k : ℕ) : ℕ := 2*k+3
abbrev Fn (n : ℕ) := weightPiece oddWeight n
abbrev Ln (n : ℕ) := weightPiece (fun _ : Bool => 1) n
abbrev Wn (n : ℕ) : Submodule ℚ L := W ⊓ Ln n

def Graded (e : OddFree ≃ₗ[ℚ] W) : Prop :=
  ∀ n a, (e a : L) ∈ Ln n ↔ a ∈ Fn n

abbrev OddCompletion := (n : ℕ) → Fn n
abbrev WCompletion := (n : ℕ) → Wn n

instance : TopologicalSpace L := ⊥
instance : TopologicalSpace OddFree := ⊥

def completed (e : OddFree ≃ₗ[ℚ] W) (h : Graded e) : OddCompletion → WCompletion :=
  fun a n => ⟨e (a n), (e (a n)).property, (h n (a n)).2 (a n).property⟩

def completedInv (e : OddFree ≃ₗ[ℚ] W) (h : Graded e) : WCompletion → OddCompletion :=
  fun a n => ⟨e.symm ⟨a n, (a n).property.1⟩,
    (h n (e.symm ⟨a n, (a n).property.1⟩)).1 (by
      rw [LinearEquiv.apply_symm_apply]
      exact (a n).property.2)⟩

def MainStatement : Prop :=
  ∃ (e : OddFree ≃ₗ[ℚ] W) (h : Graded e),
    (∀ a b, (e ⁅a,b⁆ : L) = ihara (e a) (e b)) ∧
    Function.LeftInverse (completedInv e h) (completed e h) ∧
    Function.RightInverse (completedInv e h) (completed e h) ∧
    Continuous (completed e h) ∧ Continuous (completedInv e h) ∧
    (∀ (a b : OddCompletion) n,
      (e (∑ i ∈ Finset.range (n+1), ⁅(a i : OddFree), (b (n-i) : OddFree)⁆) : L) =
      ∑ i ∈ Finset.range (n+1),
        ihara (completed e h a i) (completed e h b (n-i)))

namespace AssociativeModel

variable {α : Type*}
abbrev FL (α : Type*) := FreeLieAlgebra ℚ α
abbrev A (α : Type*) := MonoidAlgebra ℚ (FreeMonoid α)
attribute [local instance] LieRing.ofAssociativeRing

def atom (a : α) : A α := MonoidAlgebra.single (FreeMonoid.of a) 1

def embed : FL α →ₗ⁅ℚ⁆ A α := FreeLieAlgebra.lift ℚ atom

@[simp] theorem embed_of (a : α) : embed (FreeLieAlgebra.of ℚ a) = atom a := by
  simp [embed]

def dynkinWord : List α → FL α
  | [] => 0
  | [a] => FreeLieAlgebra.of ℚ a
  | a :: b :: w => ⁅FreeLieAlgebra.of ℚ a, dynkinWord (b :: w)⁆

theorem dynkinWord_cons (a : α) (w : List α) (hw : w ≠ []) :
    dynkinWord (a::w) = ⁅FreeLieAlgebra.of ℚ a, dynkinWord w⁆ := by
  cases w with
  | nil => contradiction
  | cons b w => rfl

def wordLinear {M : Type*} [AddCommGroup M] [Module ℚ M]
    (f : FreeMonoid α → M) : A α →ₗ[ℚ] M :=
  (Finsupp.linearCombination ℚ f).comp (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

@[simp] theorem wordLinear_single {M : Type*} [AddCommGroup M] [Module ℚ M]
    (f : FreeMonoid α → M) (w : FreeMonoid α) (c : ℚ) :
    wordLinear f (MonoidAlgebra.single w c) = c • f w := by
  change Finsupp.linearCombination ℚ f (Finsupp.single w c) = _; simp

def dynkin : A α →ₗ[ℚ] FL α := wordLinear (fun w => dynkinWord w.toList)

def wordAct : FreeMonoid α →* Module.End ℚ (FL α) :=
  FreeMonoid.lift (fun a => LieAlgebra.ad ℚ (FL α) (FreeLieAlgebra.of ℚ a))

def act : A α →ₐ[ℚ] Module.End ℚ (FL α) :=
  MonoidAlgebra.lift ℚ (Module.End ℚ (FL α)) (FreeMonoid α) wordAct

@[simp] theorem act_single (w : FreeMonoid α) (c : ℚ) :
    act (MonoidAlgebra.single w c) = c • wordAct w := by simp [act]

@[simp] theorem wordAct_of_apply (a : α) (q : FL α) :
    wordAct (FreeMonoid.of a) q = ⁅FreeLieAlgebra.of ℚ a,q⁆ := by
  simp [wordAct, LieAlgebra.ad_apply]

@[simp] theorem act_embed (p q : FL α) : act (embed p) q = ⁅p,q⁆ := by
  have h : act.toLieHom.comp embed = LieAlgebra.ad ℚ (FL α) := by
    apply FreeLieAlgebra.hom_ext
    intro a
    simp [atom, wordAct]
  exact LinearMap.congr_fun (LieHom.congr_fun h p) q

theorem dynkinWord_append (u v : List α) (hv : v ≠ []) :
    dynkinWord (u++v) = wordAct (FreeMonoid.ofList u) (dynkinWord v) := by
  induction u with
  | nil => simp
  | cons a u ih =>
    rw [List.cons_append, dynkinWord_cons _ _ (List.append_ne_nil_of_right_ne_nil u hv),
      ih, FreeMonoid.ofList_cons, map_mul, Module.End.mul_apply, wordAct_of_apply]

def homogeneous (n : ℕ) : Submodule ℚ (A α) :=
  Submodule.span ℚ {p | ∃ w : FreeMonoid α,
    w.toList.length = n ∧ p = MonoidAlgebra.single w 1}

theorem single_mem_homogeneous (w : FreeMonoid α) (n : ℕ)
    (hn : w.toList.length = n) : MonoidAlgebra.single w 1 ∈ homogeneous (α := α) n :=
  Submodule.subset_span ⟨w, hn, rfl⟩

theorem mul_homogeneous {n m : ℕ} {a b : A α}
    (ha : a ∈ homogeneous n) (hb : b ∈ homogeneous m) : a*b ∈ homogeneous (n+m) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    rcases ha with ⟨v,hv,rfl⟩
    induction hb using Submodule.span_induction with
    | mem b hb =>
      rcases hb with ⟨w,hw,rfl⟩
      simpa only [MonoidAlgebra.single_mul_single, one_mul] using
        single_mem_homogeneous (v*w) (n+m) (by simp [hv,hw])
    | zero => simp
    | add b c _ _ hb hc => simpa only [mul_add] using (homogeneous (n+m)).add_mem hb hc
    | smul r b _ hb => simpa only [mul_smul_comm] using (homogeneous (n+m)).smul_mem r hb
  | zero => simp
  | add a c _ _ ha hc => simpa only [add_mul] using (homogeneous (n+m)).add_mem ha hc
  | smul r a _ ha => simpa only [smul_mul_assoc] using (homogeneous (n+m)).smul_mem r ha

theorem dynkin_mul {n : ℕ} (hn : n > 0) (a : A α) {b : A α}
    (hb : b ∈ homogeneous n) : dynkin (a*b) = act a (dynkin b) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a c ha hc => simp [add_mul, ha, hc]
  | single v r =>
    induction hb using Submodule.span_induction with
    | mem b hb =>
      rcases hb with ⟨w,hw,rfl⟩
      have hw' : w.toList ≠ [] := by intro h; simp [h] at hw; omega
      simp [dynkin, dynkinWord_append _ _ hw']
    | zero => simp
    | add b c _ _ hb hc => simp [mul_add, hb, hc]
    | smul r b _ hb => simp [hb]

theorem dynkin_embed_word {n : ℕ} {p : FL α}
    (hp : WeightedWord (fun _ : α => 1) n p) :
    0 < n ∧ embed p ∈ homogeneous n ∧ dynkin (embed p) = (n : ℚ) • p := by
  induction hp with
  | generator a =>
    refine ⟨by omega, ?_, ?_⟩
    · simpa [atom] using single_mem_homogeneous (FreeMonoid.of a) 1 rfl
    · simp [dynkin, atom, dynkinWord]
  | @bracket n m p q hp hq ihp ihq =>
    rcases ihp with ⟨hn,hn',hpn⟩
    rcases ihq with ⟨hm,hm',hqm⟩
    refine ⟨by omega, ?_, ?_⟩
    · rw [LieHom.map_lie]
      change embed p * embed q - embed q * embed p ∈ homogeneous (n+m)
      exact (homogeneous (n+m)).sub_mem (mul_homogeneous hn' hm')
        (by simpa [Nat.add_comm] using mul_homogeneous hm' hn')
    · rw [LieHom.map_lie]
      change dynkin (embed p * embed q - embed q * embed p) = _
      rw [map_sub, dynkin_mul hm _ hm', dynkin_mul hn _ hn', hqm, hpn]
      simp only [map_smul, act_embed]
      rw [← lie_skew q p]
      simp only [smul_neg, sub_neg_eq_add, Nat.cast_add, add_smul]
      exact add_comm _ _

def normalizedDynkin : A α →ₗ[ℚ] FL α :=
  wordLinear (fun w => (w.toList.length : ℚ)⁻¹ • dynkinWord w.toList)

theorem normalizedDynkin_homogeneous {n : ℕ} {a : A α}
    (ha : a ∈ homogeneous n) : normalizedDynkin a = (n : ℚ)⁻¹ • dynkin a := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    rcases ha with ⟨w,hw,rfl⟩
    simp [normalizedDynkin, dynkin, hw]
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb, smul_add]
  | smul r a _ ha =>
    rw [map_smul, map_smul, ha, smul_comm]

theorem normalizedDynkin_embed_word {n : ℕ} {p : FL α}
    (hp : WeightedWord (fun _ : α => 1) n p) : normalizedDynkin (embed p) = p := by
  obtain ⟨hn,hn',hp'⟩ := dynkin_embed_word hp
  rw [normalizedDynkin_homogeneous hn', hp', smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast (Nat.ne_of_gt hn)

theorem mem_word_span (wt : α → ℕ) (p : FL α) :
    p ∈ Submodule.span ℚ {q | ∃ n, WeightedWord wt n q} := by
  let S : Submodule ℚ (FL α) := Submodule.span ℚ {q | ∃ n, WeightedWord wt n q}
  change p ∈ S
  induction p using freeLie_induction with
  | h0 => exact S.zero_mem
  | hg a => exact Submodule.subset_span ⟨wt a, WeightedWord.generator a⟩
  | ha a b ha hb => exact S.add_mem ha hb
  | hs r a ha => exact S.smul_mem r ha
  | hl a b ha hb =>
    induction ha using Submodule.span_induction with
    | mem a ha =>
      rcases ha with ⟨n, hn⟩
      induction hb using Submodule.span_induction with
      | mem b hb =>
        rcases hb with ⟨m, hm⟩
        exact Submodule.subset_span ⟨n+m, WeightedWord.bracket hn hm⟩
      | zero => simp
      | add b c _ _ hb hc => simpa only [lie_add] using S.add_mem hb hc
      | smul r b _ hb => simpa only [lie_smul] using S.smul_mem r hb
    | zero => simp
    | add a c _ _ ha hc => simpa only [add_lie] using S.add_mem ha hc
    | smul r a _ ha => simpa only [smul_lie] using S.smul_mem r ha

theorem normalizedDynkin_embed (p : FL α) : normalizedDynkin (embed p) = p := by
  have hp := mem_word_span (fun _ : α => 1) p
  induction hp using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨n,hn⟩ := ha
    exact normalizedDynkin_embed_word hn
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul r a _ ha => simp [ha]

theorem embed_injective : Function.Injective (embed (α := α)) :=
  Function.LeftInverse.injective normalizedDynkin_embed

end AssociativeModel

namespace FreeDerivations

variable {R : Type*} [CommRing R]
variable {M : Type*} [LieRing M] [LieAlgebra R M]

structure Jet (R M : Type*) [CommRing R] [LieRing M] [LieAlgebra R M] where
  base : M
  velocity : M

def Jet.equiv : Jet R M ≃ M × M where
  toFun z := (z.base, z.velocity)
  invFun z := ⟨z.1, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (Jet R M) := Jet.equiv.addCommGroup
instance : Module R (Jet R M) := Jet.equiv.addEquiv.module R
instance : Bracket (Jet R M) (Jet R M) :=
  ⟨fun a b => ⟨⁅a.base, b.base⁆,
    ⁅a.velocity, b.base⁆ + ⁅a.base, b.velocity⁆⟩⟩

@[ext] theorem Jet.ext {a b : Jet R M} (h : a.base = b.base)
    (k : a.velocity = b.velocity) : a = b := by cases a; cases b; simp_all

@[simp] theorem Jet.base_zero : (0 : Jet R M).base = 0 := rfl
@[simp] theorem Jet.velocity_zero : (0 : Jet R M).velocity = 0 := rfl
@[simp] theorem Jet.base_add (a b : Jet R M) : (a+b).base = a.base+b.base := rfl
@[simp] theorem Jet.velocity_add (a b : Jet R M) :
    (a+b).velocity = a.velocity+b.velocity := rfl
@[simp] theorem Jet.base_smul (q : R) (a : Jet R M) : (q • a).base = q • a.base := rfl
@[simp] theorem Jet.velocity_smul (q : R) (a : Jet R M) :
    (q • a).velocity = q • a.velocity := rfl
@[simp] theorem Jet.base_lie (a b : Jet R M) : ⁅a,b⁆.base = ⁅a.base,b.base⁆ := rfl
@[simp] theorem Jet.velocity_lie (a b : Jet R M) :
    ⁅a,b⁆.velocity = ⁅a.velocity,b.base⁆ + ⁅a.base,b.velocity⁆ := rfl

instance : LieRing (Jet R M) where
  add_lie a b c := by (ext <;> simp [add_lie]); abel
  lie_add a b c := by (ext <;> simp [lie_add]); abel
  lie_self a := by
    ext
    · simp
    · change ⁅a.velocity, a.base⁆ + ⁅a.base, a.velocity⁆ = 0
      rw [← lie_skew a.velocity a.base]
      exact neg_add_cancel _
  leibniz_lie a b c := by (ext <;> simp [lie_add, add_lie, lie_lie]); abel
instance : LieAlgebra R (Jet R M) where
  lie_smul q a b := by ext <;> simp [lie_smul, smul_add]

def Jet.baseHom : Jet R M →ₗ⁅R⁆ M where
  toFun := Jet.base
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' {_ _} := rfl

variable {α : Type*}
local notation "F" => FreeLieAlgebra R α

def jetLift (f : α → F) : F →ₗ⁅R⁆ Jet R F :=
  FreeLieAlgebra.lift R (fun a => ⟨FreeLieAlgebra.of R a, f a⟩)

@[simp] theorem jetLift_base (f : α → F) (p : F) :
    (jetLift f p).base = p := by
  have h : Jet.baseHom.comp (jetLift f) = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro a
    simp [jetLift, Jet.baseHom]
    rfl
  exact LieHom.congr_fun h p

def extend (f : α → F) : LieDerivation R F F where
  toFun q := (jetLift f q).velocity
  map_add' a b := by
    change (jetLift f (a+b)).velocity = _
    rw [map_add]
    rfl
  map_smul' r a := by
    change (jetLift f (r • a)).velocity = _
    rw [map_smul]
    rfl
  leibniz' a b := by
    change (jetLift f ⁅a,b⁆).velocity = ⁅a,(jetLift f b).velocity⁆ - ⁅b,(jetLift f a).velocity⁆
    rw [LieHom.map_lie, Jet.velocity_lie, jetLift_base, jetLift_base]
    rw [sub_eq_add_neg, lie_skew, add_comm]

@[simp] theorem extend_of (f : α → F) (a : α) :
    extend f (FreeLieAlgebra.of R a) = f a := by
  change (jetLift f (FreeLieAlgebra.of R a)).velocity = _
  simp [jetLift]

@[ext] theorem ext {d₁ d₂ : LieDerivation R F F}
    (h : ∀ a, d₁ (FreeLieAlgebra.of R a) = d₂ (FreeLieAlgebra.of R a)) : d₁ = d₂ := by
  ext q
  induction q using freeLie_induction with
  | h0 => simp
  | hg a => exact h a
  | ha a b ha hb => simp [ha, hb]
  | hs r a ha => simp [ha]
  | hl a b ha hb => simp [ha, hb]

theorem extend_unique (f : α → F) (d : LieDerivation R F F)
    (h : ∀ a, d (FreeLieAlgebra.of R a) = f a) : d = extend f := by
  apply ext
  intro a
  simpa using h a

variable [DecidableEq α]
def pair (i j : α) : LieDerivation R F F :=
  extend (fun k => if k = i then ⁅FreeLieAlgebra.of R i, FreeLieAlgebra.of R j⁆
    else if k = j then ⁅FreeLieAlgebra.of R j, FreeLieAlgebra.of R i⁆ else 0)

@[simp] theorem pair_of_left (i j : α) :
    pair (R := R) i j (FreeLieAlgebra.of R i) = ⁅FreeLieAlgebra.of R i,FreeLieAlgebra.of R j⁆ := by
  simp [pair]

@[simp] theorem pair_of_right (i j : α) :
    pair (R := R) i j (FreeLieAlgebra.of R j) = ⁅FreeLieAlgebra.of R j,FreeLieAlgebra.of R i⁆ := by
  by_cases h : j = i
  · subst j; simp
  · simp [pair, h]

@[simp] theorem pair_of_other (i j k : α) (hi : k ≠ i) (hj : k ≠ j) :
    pair (R := R) i j (FreeLieAlgebra.of R k) = 0 := by
  simp [pair, hi, hj]

theorem pair_comm (i j : α) : pair (R := R) i j = pair j i := by
  apply ext
  intro a
  by_cases hi : a=i
  · subst a; simp
  by_cases hj : a=j
  · subst a; simp
  simp [hi,hj]

theorem pair_self (i : α) : pair (R := R) i i = 0 := by
  apply ext
  intro a
  by_cases hi : a=i
  · subst a; simp
  simp [hi]

theorem pair_disjoint (i j k l : α)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    ⁅pair (R := R) i j,pair (R := R) k l⁆ = 0 := by
  apply ext
  intro a
  by_cases hai : a=i
  · subst a; simp [hik,hil,hjk,hjl]
  by_cases haj : a=j
  · subst a; simp [hik,hil,hjk,hjl]
  by_cases hak : a=k
  · subst a; simp [hik.symm,hjk.symm,hil.symm,hjl.symm]
  by_cases hal : a=l
  · subst a; simp [hik.symm,hjk.symm,hil.symm,hjl.symm]
  simp [hai,haj,hak,hal]

theorem pair_three (i j k : α) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅pair (R := R) i j, pair (R := R) i k + pair (R := R) j k⁆ = 0 := by
  apply ext
  intro a
  by_cases hai : a=i
  · subst a
    simp [hik,hij,hjk,hij.symm,hik.symm,hjk.symm]
    grind [lie_skew, lie_lie]
  by_cases haj : a=j
  · subst a
    simp [hik,hij,hjk,hij.symm,hik.symm,hjk.symm]
    grind [lie_skew, lie_lie]
  by_cases hak : a=k
  · subst a
    simp [hik.symm,hjk.symm]
    grind [lie_skew, lie_lie]
  simp [hai,haj,hak]

end FreeDerivations

namespace BraidRepresentation
open FreeDerivations LieAlgebra
variable {R α : Type*} [CommRing R] [DecidableEq α]
local notation "F" => FreeLieAlgebra R α
local notation "Der" => LieDerivation R F F
local notation "SD" => SemiDirectSum F Der (LieHom.id : Der →ₗ⁅R⁆ Der)

def fiber (i : α) : SD := SemiDirectSum.inl LieHom.id (FreeLieAlgebra.of R i)
def base (i j : α) : SD := SemiDirectSum.inr LieHom.id (pair i j)

def chord : Option α → Option α → SD
  | none, none => 0
  | none, some j => fiber j
  | some i, none => fiber i
  | some i, some j => base i j

@[simp] theorem chord_none_none : chord (R := R) (α := α) none none = 0 := rfl
@[simp] theorem chord_none_some (j : α) : chord (R := R) none (some j) = fiber j := rfl
@[simp] theorem chord_some_none (i : α) : chord (R := R) (some i) none = fiber i := rfl
@[simp] theorem chord_some_some (i j : α) : chord (R := R) (some i) (some j) = base i j := rfl

theorem chord_comm (i j : Option α) : chord (R := R) i j = chord j i := by
  cases i <;> cases j <;> simp [base, pair_comm]

@[simp] theorem chord_self (i : Option α) : chord (R := R) i i = 0 := by
  cases i <;> simp [base, pair_self]

theorem base_fiber (i j k : α) :
    ⁅base (R := R) i j, fiber k⁆ = SemiDirectSum.inl LieHom.id
      (pair (R := R) i j (FreeLieAlgebra.of R k)) := by
  simp [base, fiber]

theorem fiber_base (i j k : α) :
    ⁅fiber (R := R) k, base i j⁆ = - SemiDirectSum.inl LieHom.id
      (pair (R := R) i j (FreeLieAlgebra.of R k)) := by
  rw [← lie_skew, base_fiber]

theorem chord_disjoint (i j k l : Option α)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    ⁅chord (R := R) i j, chord (R := R) k l⁆ = 0 := by
  cases i <;> cases j <;> cases k <;> cases l <;>
    simp_all [base, fiber, pair_disjoint]
  all_goals apply pair_of_other <;> intro h <;> subst_vars <;> contradiction

theorem chord_three (i j k : Option α)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅chord (R := R) i j, chord (R := R) i k + chord (R := R) j k⁆ = 0 := by
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j =>
      cases k with
      | none => exact (hik rfl).elim
      | some k =>
        rw [chord_none_some, chord_none_some, chord_some_some, lie_add, fiber_base]
        simp [fiber]
        grind [lie_skew]
  | some i =>
    cases j with
    | none =>
      cases k with
      | none => exact (hjk rfl).elim
      | some k =>
        rw [chord_some_none, chord_some_some, chord_none_some, lie_add, fiber_base]
        simp [fiber]
        grind [lie_skew]
    | some j =>
      cases k with
      | none =>
        rw [chord_some_some, chord_some_none, chord_some_none, lie_add,
          base_fiber, base_fiber]
        simp only [pair_of_left, pair_of_right, ← map_add]
        grind [lie_skew]
      | some k =>
        simp only [chord_some_some, base, ← map_add, ← LieHom.map_lie]
        rw [pair_three _ _ _ (fun h => hij (congrArg some h))
          (fun h => hik (congrArg some h)) (fun h => hjk (congrArg some h)), map_zero]

end BraidRepresentation

namespace BraidModel
open LieAlgebra
abbrev Fiber := FreeLieAlgebra ℚ (Fin 3)
abbrev Der := LieDerivation ℚ Fiber Fiber
abbrev Model := SemiDirectSum Fiber Der (LieHom.id : Der →ₗ⁅ℚ⁆ Der)
def chord (i j : Fin 4) : Model :=
  BraidRepresentation.chord (finSuccEquiv' (1 : Fin 4) i) (finSuccEquiv' (1 : Fin 4) j)

theorem chord_comm (i j : Fin 4) : chord i j = chord j i :=
  BraidRepresentation.chord_comm _ _

@[simp] theorem chord_self (i : Fin 4) : chord i i = 0 :=
  BraidRepresentation.chord_self _

def preMap : BraidFree →ₗ⁅ℚ⁆ Model := FreeLieAlgebra.lift ℚ (fun e => chord e.val.1 e.val.2)

@[simp] theorem preMap_chord (i j : Fin 4) : preMap (DeligneDrinfeld.chord i j) = chord i j := by
  unfold DeligneDrinfeld.chord
  split_ifs with hij hji
  · simp [preMap]
  · simp [preMap, chord_comm j i]
  · have h : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
    subst j
    simp

theorem ideal_le_ker : braidIdeal ≤ preMap.ker := by
  rw [braidIdeal, LieSubmodule.lieSpan_le]
  intro z hz
  change preMap z = 0
  rcases hz with ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,rfl⟩ | ⟨i,j,k,hij,hik,hjk,rfl⟩
  · rw [LieHom.map_lie, preMap_chord, preMap_chord]
    exact BraidRepresentation.chord_disjoint _ _ _ _
      ((finSuccEquiv' (1 : Fin 4)).injective.ne hik) ((finSuccEquiv' (1 : Fin 4)).injective.ne hil)
      ((finSuccEquiv' (1 : Fin 4)).injective.ne hjk) ((finSuccEquiv' (1 : Fin 4)).injective.ne hjl)
  · rw [LieHom.map_lie, map_add, preMap_chord, preMap_chord, preMap_chord]
    exact BraidRepresentation.chord_three _ _ _
      ((finSuccEquiv' (1 : Fin 4)).injective.ne hij) ((finSuccEquiv' (1 : Fin 4)).injective.ne hik)
      ((finSuccEquiv' (1 : Fin 4)).injective.ne hjk)

def map : T4 →ₗ⁅ℚ⁆ Model :=
  { braidIdeal.toSubmodule.liftQ preMap.toLinearMap ideal_le_ker with
    map_lie' := by
      intro a b
      induction a using Submodule.Quotient.induction_on with | _ a =>
        induction b using Submodule.Quotient.induction_on with | _ b =>
          exact preMap.map_lie a b }

@[simp] theorem map_t (i j : Fin 4) : map (t i j) = chord i j := preMap_chord i j

end BraidModel

namespace AssociativeModel
attribute [local instance] LieRing.ofAssociativeRing
variable {α : Type*}

theorem coeff_rotate {P : A α} {b : α} (h : atom b * P = P * atom b) (w : List α) :
    P.coeff (FreeMonoid.ofList (b :: w)) = P.coeff (FreeMonoid.ofList (w ++ [b])) := by
  calc
    P.coeff (FreeMonoid.ofList (b :: w)) =
        (P * atom b).coeff ((FreeMonoid.of b * FreeMonoid.ofList w) * FreeMonoid.of b) := by
      simp [atom, FreeMonoid.ofList_cons]
    _ = (atom b * P).coeff (FreeMonoid.of b * (FreeMonoid.ofList w * FreeMonoid.of b)) := by
      rw [h, mul_assoc]
    _ = P.coeff (FreeMonoid.ofList (w ++ [b])) := by
      simp [atom, FreeMonoid.ofList_append]

theorem coeff_starts_ne {P : A α} {b a : α} (h : atom b * P = P * atom b)
    (hab : a ≠ b) (v : List α) : P.coeff (FreeMonoid.ofList (a :: v)) = 0 := by
  have hz : (atom b * P).coeff (FreeMonoid.ofList (a::v) * FreeMonoid.of b) = 0 := by
    apply MonoidAlgebra.coeff_single_mul_of_forall_mul_ne
    intro d hd
    have hh := congrArg (fun w : FreeMonoid α => w.toList.head?) hd
    exact hab (by simpa using hh.symm)
  rw [h] at hz
  simpa [atom] using hz

theorem coeff_contains_ne {P : A α} {b a : α} (h : atom b * P = P * atom b)
    (hab : a ≠ b) (u v : List α) : P.coeff (FreeMonoid.ofList (u ++ a :: v)) = 0 := by
  induction u generalizing v with
  | nil => exact coeff_starts_ne h hab v
  | cons c u ih =>
    by_cases hc : c = b
    · subst c
      rw [List.cons_append, coeff_rotate h]
      simpa [List.append_assoc] using ih (v ++ [b])
    · exact coeff_starts_ne h hc (u ++ a :: v)

theorem coeff_eq_zero_of_letter_ne {P : A α} {b a : α}
    (h : atom b * P = P * atom b) {w : List α} (ha : a ∈ w) (hab : a ≠ b) :
    P.coeff (FreeMonoid.ofList w) = 0 := by
  obtain ⟨u,v,rfl⟩ := List.append_of_mem ha
  exact coeff_contains_ne h hab u v

theorem dynkinWord_all_eq (b : α) (w : List α) (hw : ∀ a ∈ w, a = b) :
    dynkinWord w ∈ Submodule.span ℚ {FreeLieAlgebra.of ℚ b} := by
  induction w with
  | nil => simp [dynkinWord]
  | cons a w ih =>
    have ha : a = b := hw a (by simp)
    subst a
    cases w with
    | nil => exact Submodule.subset_span (by simp [dynkinWord])
    | cons c w =>
      rw [dynkinWord]
      have hmem := ih (fun a ha => hw a (by simp [ha]))
      obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hmem
      rw [← hr, lie_smul, lie_self, smul_zero]
      exact Submodule.zero_mem _

theorem centralizer_generator {p : FL α} (b : α) (h : ⁅FreeLieAlgebra.of ℚ b,p⁆ = 0) :
    p ∈ Submodule.span ℚ {FreeLieAlgebra.of ℚ b} := by
  classical
  have hc : atom b * embed p = embed p * atom b := by
    have ht := congrArg embed h
    rw [LieHom.map_lie, embed_of, map_zero] at ht
    exact sub_eq_zero.mp ht
  rw [← normalizedDynkin_embed p, ← MonoidAlgebra.sum_coeff_single (embed p)]
  unfold Finsupp.sum
  rw [map_sum]
  apply Submodule.sum_mem
  intro w hw
  rw [normalizedDynkin, wordLinear_single]
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  apply dynkinWord_all_eq
  intro a ha
  by_contra hab
  have hz := coeff_eq_zero_of_letter_ne hc ha hab
  have hn := Finsupp.mem_support_iff.mp hw
  exact hn (by simpa using hz)

end AssociativeModel

theorem map_eval {M N : Type*} [LieRing M] [LieAlgebra ℚ M]
    [LieRing N] [LieAlgebra ℚ N] (f : M →ₗ⁅ℚ⁆ N) (a b : M) (p : L) :
    f (eval a b p) = eval (f a) (f b) p := by
  have h : f.comp (eval a b) = eval (f a) (f b) := by
    apply FreeLieAlgebra.hom_ext
    intro i
    cases i <;> simp [eval]
  exact LieHom.congr_fun h p

theorem eval_self : eval x y = LieHom.id := by
  apply FreeLieAlgebra.hom_ext
  intro i
  cases i <;> simp [eval, x, y]

theorem eval_commutes {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    (a b z : M) (ha : ⁅z,a⁆ = 0) (hb : ⁅z,b⁆ = 0) (p : L) :
    ⁅z,eval a b p⁆ = 0 := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [eval, ha, hb]
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [hp]
  | hl p q hp hq => simp [LieHom.map_lie, leibniz_lie, hp, hq]

@[simp] theorem chord_comm (i j : Fin 4) : chord i j = chord j i := by
  unfold chord
  split_ifs <;> first | rfl | omega

@[simp] theorem t_comm (i j : Fin 4) : t i j = t j i := by
  unfold t
  rw [chord_comm]

theorem t_disjoint (i j k l : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ⁅t i j,t k l⁆ = 0 := by
  rw [t, t, ← LieSubmodule.Quotient.mk_bracket, LieSubmodule.Quotient.mk_eq_zero']
  exact LieSubmodule.subset_lieSpan (Or.inl ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,rfl⟩)

theorem t_three (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅t i j,t i k + t j k⁆ = 0 := by
  change LieSubmodule.Quotient.mk (⁅chord i j, chord i k + chord j k⁆) = (0 : T4)
  rw [LieSubmodule.Quotient.mk_eq_zero']
  exact LieSubmodule.subset_lieSpan (Or.inr ⟨i,j,k,hij,hik,hjk,rfl⟩)

namespace BraidModel

def inclusion : Fiber →ₗ⁅ℚ⁆ T4 := FreeLieAlgebra.lift ℚ
  (fun i => t 1 ((finSuccEquiv' (1 : Fin 4)).symm (some i)))

theorem map_inclusion : map.comp inclusion = LieAlgebra.SemiDirectSum.inl LieHom.id := by
  apply FreeLieAlgebra.hom_ext
  intro i
  simp [inclusion, chord, BraidRepresentation.fiber]

theorem inclusion_injective : Function.Injective inclusion := by
  intro a b hab
  have h := congrArg map hab
  have hm (c : Fiber) : map (inclusion c) = LieAlgebra.SemiDirectSum.inl LieHom.id c :=
    LieHom.congr_fun map_inclusion c
  rw [hm,hm] at h
  exact LieAlgebra.SemiDirectSum.inl_injective _ h

end BraidModel

theorem commute_symm {M : Type*} [LieRing M] {a b : M} (h : ⁅a,b⁆ = 0) : ⁅b,a⁆ = 0 := by
  rw [← lie_skew, h, neg_zero]

theorem evals_commute {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    (a b c d : M) (hac : ⁅a,c⁆ = 0) (had : ⁅a,d⁆ = 0)
    (hbc : ⁅b,c⁆ = 0) (hbd : ⁅b,d⁆ = 0) (p q : L) :
    ⁅eval a b p,eval c d q⁆ = 0 := by
  apply eval_commutes
  · exact commute_symm (eval_commutes a b c (commute_symm hac) (commute_symm hbc) p)
  · exact commute_symm (eval_commutes a b d (commute_symm had) (commute_symm hbd) p)

theorem eval_add_of_commuting {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    (a b c d : M) (hac : ⁅a,c⁆ = 0) (had : ⁅a,d⁆ = 0)
    (hbc : ⁅b,c⁆ = 0) (hbd : ⁅b,d⁆ = 0) (p : L) :
    eval (a+c) (b+d) p = eval a b p + eval c d p := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [eval]
  | ha p q hp hq => simp [hp,hq]; abel
  | hs r p hp => simp [hp,smul_add]
  | hl p q hp hq =>
    simp only [LieHom.map_lie, hp, hq, add_lie, lie_add]
    rw [evals_commute a b c d hac had hbc hbd p q,
      commute_symm (evals_commute a b c d hac had hbc hbd q p)]
    simp

theorem eval_vanish_of_commuting {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    (a b : M) (hab : ⁅a,b⁆ = 0) {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1 < n) :
    eval a b p = 0 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    cases hp with
    | generator i => omega
    | @bracket n m p q hp hq =>
      rw [LieHom.map_lie]
      exact evals_commute a b a b (lie_self a) hab (commute_symm hab) (lie_self b) p q
  | zero => simp
  | add p q _ _ hp hq => simp [hp,hq]
  | smul r p _ hp => simp [hp]

theorem eval_central_shift {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    (a b c : M) (hac : ⁅a,c⁆ = 0) (hbc : ⁅b,c⁆ = 0)
    {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1 < n) :
    eval a (b+c) p = eval a b p := by
  have h := eval_add_of_commuting a b 0 c (lie_zero a) hac (lie_zero b) hbc p
  simpa [eval_vanish_of_commuting 0 c (zero_lie c) hp hn] using h

namespace T4Universal
variable {M : Type*} [LieRing M] [LieAlgebra ℚ M]

def pre (f : Fin 4 → Fin 4 → M) : BraidFree →ₗ⁅ℚ⁆ M :=
  FreeLieAlgebra.lift ℚ (fun e => f e.val.1 e.val.2)

theorem pre_chord (f : Fin 4 → Fin 4 → M)
    (hs : ∀ i j, f i j = f j i) (hz : ∀ i, f i i = 0) (i j : Fin 4) :
    pre f (chord i j) = f i j := by
  unfold chord
  split_ifs with hij hji
  · simp [pre]
  · simp [pre, hs j i]
  · have h : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
    subst j
    simp [hz]

def lift (f : Fin 4 → Fin 4 → M)
    (hs : ∀ i j, f i j = f j i) (hz : ∀ i, f i i = 0)
    (hd : ∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      ⁅f i j,f k l⁆ = 0)
    (ht : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ⁅f i j,f i k+f j k⁆ = 0) : T4 →ₗ⁅ℚ⁆ M := by
  have hker : braidIdeal ≤ (pre f).ker := by
    rw [braidIdeal, LieSubmodule.lieSpan_le]
    intro z hz'
    change pre f z = 0
    rcases hz' with ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,rfl⟩ | ⟨i,j,k,hij,hik,hjk,rfl⟩
    · simpa only [LieHom.map_lie, pre_chord f hs hz] using hd i j k l hij hik hil hjk hjl hkl
    · simpa only [LieHom.map_lie, map_add, pre_chord f hs hz] using ht i j k hij hik hjk
  exact { braidIdeal.toSubmodule.liftQ (pre f).toLinearMap hker with
    map_lie' := by
      intro a b
      induction a using Submodule.Quotient.induction_on with | _ a =>
        induction b using Submodule.Quotient.induction_on with | _ b =>
          exact (pre f).map_lie a b }

@[simp] theorem lift_t (f : Fin 4 → Fin 4 → M) (hs hz hd ht) (i j : Fin 4) :
    lift f hs hz hd ht (t i j) = f i j := pre_chord f hs hz i j

end T4Universal

@[simp] theorem t_self (i : Fin 4) : t i i = 0 := by simp [t, chord]

def t4Rename (e : Equiv.Perm (Fin 4)) : T4 →ₗ⁅ℚ⁆ T4 :=
  T4Universal.lift (fun i j => t (e i) (e j))
    (fun _ _ => t_comm _ _) (fun _ => t_self _)
    (fun _ _ _ _ hij hik hil hjk hjl hkl => t_disjoint _ _ _ _
      (e.injective.ne hij) (e.injective.ne hik) (e.injective.ne hil)
      (e.injective.ne hjk) (e.injective.ne hjl) (e.injective.ne hkl))
    (fun _ _ _ hij hik hjk => t_three _ _ _
      (e.injective.ne hij) (e.injective.ne hik) (e.injective.ne hjk))

@[simp] theorem t4Rename_t (e : Equiv.Perm (Fin 4)) (i j : Fin 4) :
    t4Rename e (t i j) = t (e i) (e j) := T4Universal.lift_t _ _ _ _ _ _ _

theorem solution_swap {p : L} (hp : p ∈ W)
    {M : Type*} [LieRing M] [LieAlgebra ℚ M] (a b : M) :
    eval a b p = - eval b a p := by
  have h := congrArg (eval a b) hp.1
  simp only [map_add, map_zero, map_eval, eval_x, eval_y] at h
  exact eq_neg_of_add_eq_zero_left h

theorem solution_three {p : L} (hp : p ∈ W)
    {M : Type*} [LieRing M] [LieAlgebra ℚ M] (a b : M) :
    eval a b p + eval b (-a-b) p + eval (-a-b) a p = 0 := by
  have h := congrArg (eval a b) hp.2.1
  simpa only [map_add, map_zero, map_eval, map_sub, map_neg, eval_x, eval_y] using h

theorem free_action_inner {R α β Z : Type*} [CommRing R]
    [LieRing Z] [LieAlgebra R Z]
    (f : FreeLieAlgebra R α →ₗ⁅R⁆ Z) (g : FreeLieAlgebra R β →ₗ⁅R⁆ Z)
    (h : FreeLieAlgebra R β →ₗ⁅R⁆ LieDerivation R (FreeLieAlgebra R α) (FreeLieAlgebra R α))
    (hg : ∀ b a, f (h (FreeLieAlgebra.of R b) (FreeLieAlgebra.of R a)) =
      ⁅g (FreeLieAlgebra.of R b),f (FreeLieAlgebra.of R a)⁆)
    (q : FreeLieAlgebra R β) (p : FreeLieAlgebra R α) :
    f (h q p) = ⁅g q,f p⁆ := by
  have H : ∀ q : FreeLieAlgebra R β, ∀ p : FreeLieAlgebra R α,
      f (h q p) = ⁅g q,f p⁆ := by
    intro q
    induction q using freeLie_induction with
    | h0 => intro p; simp
    | hg b =>
      intro p
      induction p using freeLie_induction with
      | h0 => simp
      | hg a => exact hg b a
      | ha p r hp hr => simp [hp,hr]
      | hs c p hp => simp [hp]
      | hl p r hp hr =>
        simp [hp,hr,LieHom.map_lie]
        grind [lie_lie,lie_skew]
    | ha q r hq hr => intro p; simp [hq,hr]
    | hs c q hq => intro p; simp [hq]
    | hl q r hq hr => intro p; simp [LieHom.map_lie,hq,hr,lie_lie]
  exact H q p

namespace InnerSemiDirect
open LieAlgebra
variable {R K B Z : Type*} [CommRing R]
  [LieRing K] [LieAlgebra R K] [LieRing B] [LieAlgebra R B]
  [LieRing Z] [LieAlgebra R Z]
variable (action : B →ₗ⁅R⁆ LieDerivation R K K)
  (f : K →ₗ⁅R⁆ Z) (g : B →ₗ⁅R⁆ Z)
  (h : ∀ q p, f (action q p) = ⁅g q,f p⁆)

def lift : SemiDirectSum K B action →ₗ⁅R⁆ Z where
  toFun z := f z.left + g z.right
  map_add' z t := by simp; abel
  map_smul' c z := by simp [smul_add]
  map_lie' {z t} := by
    simp only [SemiDirectSum.lie_eq_mk, map_sub, map_add, LieHom.map_lie, h,
      add_lie, lie_add]
    rw [sub_eq_add_neg, lie_skew]
    abel

@[simp] theorem lift_inl (p : K) : lift action f g h (SemiDirectSum.inl action p) = f p := by
  simp [lift]
@[simp] theorem lift_inr (p : B) : lift action f g h (SemiDirectSum.inr action p) = g p := by
  simp [lift]
end InnerSemiDirect

namespace SpecialFiber
open LieAlgebra FreeDerivations
abbrev F := FreeLieAlgebra ℚ (Fin 3)
def fa : F := FreeLieAlgebra.of ℚ 0
def fb : F := FreeLieAlgebra.of ℚ 1
def fc : F := FreeLieAlgebra.of ℚ 2

def action : L →ₗ⁅ℚ⁆ LieDerivation ℚ F F := eval (pair 0 1) (pair 1 2)
abbrev M := SemiDirectSum F L action

def a : M := SemiDirectSum.inl action fa
def b : M := SemiDirectSum.inl action fb
def c : M := SemiDirectSum.inl action fc
def u : M := SemiDirectSum.inr action x
def v : M := SemiDirectSum.inr action y
def w : M := -a-b-c-u-v

theorem au : ⁅a,u⁆ = -⁅a,b⁆ := by
  simp only [a,u,b, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk, SemiDirectSum.neg_eq_mk]
  ext <;> simp [action,fa,fb]
theorem bu : ⁅b,u⁆ = ⁅a,b⁆ := by
  simp only [a,u,b, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk]
  ext <;> simp [action,fa,fb]
theorem cu : ⁅c,u⁆ = 0 := by
  simp only [c,u, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk]
  ext <;> simp [action,fc]
theorem av : ⁅a,v⁆ = 0 := by
  simp only [a,v, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk]
  ext <;> simp [action,fa]
theorem bv : ⁅b,v⁆ = -⁅b,c⁆ := by
  simp only [b,v,c, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk, SemiDirectSum.neg_eq_mk]
  ext <;> simp [action,fb,fc]
theorem cv : ⁅c,v⁆ = ⁅b,c⁆ := by
  simp only [b,v,c, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk]
  ext <;> simp [action,fb,fc]

def chord (i j : Fin 4) : M :=
  match i.val, j.val with
  | 0,1 | 1,0 => a
  | 0,2 | 2,0 => u
  | 0,3 | 3,0 => w
  | 1,2 | 2,1 => b
  | 1,3 | 3,1 => c
  | 2,3 | 3,2 => v
  | _,_ => 0

private theorem chord_symm (i j : Fin 4) : chord i j = chord j i := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem chord_zero (i : Fin 4) : chord i i = 0 := by fin_cases i <;> rfl

private theorem chord_disjoint (i j k l : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) : ⁅chord i j,chord k l⁆ = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all only [ne_eq, not_true_eq_false]
  all_goals fin_cases k <;> simp_all only [not_true_eq_false]
  all_goals fin_cases l <;> simp_all only [not_true_eq_false]
  all_goals dsimp only [chord]
  all_goals simp only [w, lie_sub, sub_lie, lie_neg, neg_lie,
    bu,cu,av,bv,lie_self]
  all_goals grind [lie_skew, au,bu,cu,av,bv,cv]

private theorem chord_three (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅chord i j,chord i k+chord j k⁆ = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all only [ne_eq, not_true_eq_false]
  all_goals fin_cases k <;> simp_all only [not_true_eq_false]
  all_goals dsimp only [chord]
  all_goals simp only [w, lie_sub, sub_lie, lie_neg, neg_lie, lie_add,
    au,bu,cu,av,bv,cv,lie_self]
  all_goals grind [lie_skew, au,bu,cu,av,bv,cv]

def representation : T4 →ₗ⁅ℚ⁆ M :=
  T4Universal.lift chord chord_symm chord_zero chord_disjoint chord_three

@[simp] theorem representation_t (i j : Fin 4) : representation (t i j) = chord i j :=
  T4Universal.lift_t _ _ _ _ _ _ _

def fiberSpec : F →ₗ⁅ℚ⁆ L := FreeLieAlgebra.lift ℚ
  (fun i => if i = 0 then x else if i = 1 then y else -x-y)
def baseSpec : L →ₗ⁅ℚ⁆ L := eval (-x-y) x

@[simp] theorem fiberSpec_fa : fiberSpec fa = x := by simp [fiberSpec,fa]
@[simp] theorem fiberSpec_fb : fiberSpec fb = y := by simp [fiberSpec,fb]
@[simp] theorem fiberSpec_fc : fiberSpec fc = -x-y := by simp [fiberSpec,fc]
@[simp] theorem baseSpec_x : baseSpec x = -x-y := eval_x _ _
@[simp] theorem baseSpec_y : baseSpec y = x := eval_y _ _

theorem spec_equivariant (q : L) (p : F) :
    fiberSpec (action q p) = ⁅baseSpec q,fiberSpec p⁆ := by
  apply free_action_inner
  intro i j
  cases i <;> fin_cases j <;>
    simp [action, eval, baseSpec, fiberSpec, FreeDerivations.pair,
      x,y,sub_lie,neg_lie,lie_sub,lie_neg]

def specialize : M →ₗ⁅ℚ⁆ L := InnerSemiDirect.lift action fiberSpec baseSpec spec_equivariant

@[simp] theorem specialize_a : specialize a = x := by simp [specialize,a, InnerSemiDirect.lift]
@[simp] theorem specialize_b : specialize b = y := by simp [specialize,b, InnerSemiDirect.lift]
@[simp] theorem specialize_c : specialize c = -x-y := by simp [specialize,c, InnerSemiDirect.lift]
@[simp] theorem specialize_u : specialize u = -x-y := by simp [specialize,u, InnerSemiDirect.lift]
@[simp] theorem specialize_v : specialize v = x := by simp [specialize,v, InnerSemiDirect.lift]

@[simp] theorem eval_right (d e : M) (p : L) :
    (eval d e p).right = eval d.right e.right p :=
  map_eval (SemiDirectSum.projr action) d e p

def Fa (p : L) : F := (eval (u+b) v p - eval u v p).left
def Fb (p : L) : F := (eval (u+a) (v+c) p - eval u v p).left
def Fc (p : L) : F := (eval u (v+b) p - eval u v p).left

 theorem Fa_inl (p : L) : SemiDirectSum.inl action (Fa p) = eval (u+b) v p - eval u v p := by
  ext
  · rfl
  · simp [eval_right, u,b,v]
 theorem Fb_inl (p : L) : SemiDirectSum.inl action (Fb p) = eval (u+a) (v+c) p - eval u v p := by
  ext
  · rfl
  · simp [eval_right, u,a,v,c]
 theorem Fc_inl (p : L) : SemiDirectSum.inl action (Fc p) = eval u (v+b) p - eval u v p := by
  ext
  · rfl
  · simp [eval_right, u,b,v]

theorem eval_comm_a (p : L) : ⁅a,eval (u+b) v p⁆ = 0 := by
  apply eval_commutes
  · rw [lie_add,au]; exact neg_add_cancel _
  · exact av
theorem eval_comm_b (p : L) : ⁅b,eval (u+a) (v+c) p⁆ = 0 := by
  apply eval_commutes
  · rw [lie_add,bu]; grind [lie_skew]
  · rw [lie_add,bv]; exact neg_add_cancel _
theorem eval_comm_c (p : L) : ⁅c,eval u (v+b) p⁆ = 0 := by
  apply eval_commutes
  · exact cu
  · rw [lie_add,cv]; grind [lie_skew]
theorem eval_comm_sum (p : L) : ⁅a+b+c,eval u v p⁆ = 0 := by
  apply eval_commutes
  · rw [add_lie,add_lie,au,bu,cu]; abel
  · rw [add_lie,add_lie,av,bv,cv]; abel

theorem fiber_identity (p : L) :
    ⁅fa+fb+fc,Fb p⁆ = ⁅fa,Fb p-Fa p⁆ + ⁅fc,Fb p-Fc p⁆ := by
  apply SemiDirectSum.inl_injective action
  simp only [LieHom.map_lie, map_add, map_sub, Fa_inl,Fb_inl,Fc_inl]
  change ⁅a+b+c,eval (u+a) (v+c) p - eval u v p⁆ =
    ⁅a,(eval (u+a) (v+c) p - eval u v p) - (eval (u+b) v p - eval u v p)⁆ +
    ⁅c,(eval (u+a) (v+c) p - eval u v p) - (eval u (v+b) p - eval u v p)⁆
  rw [lie_sub,eval_comm_sum]
  simp only [lie_sub,add_lie,eval_comm_a,eval_comm_b,eval_comm_c]
  abel

theorem Fb_specialize {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1<n) :
    fiberSpec (Fb p) = -eval (-x-y) x p := by
  have H := congrArg specialize (Fb_inl p)
  rw [show specialize (SemiDirectSum.inl action (Fb p)) = fiberSpec (Fb p) from
    InnerSemiDirect.lift_inl _ _ _ _ _] at H
  simp only [map_sub,map_eval,map_add,specialize_u,specialize_a,specialize_v,specialize_c] at H
  have ha : -x-y+x = -y := by abel
  have hb : x+(-x-y) = -y := by abel
  rw [ha,hb,eval_vanish_of_commuting (-y) (-y) (lie_self _) hp hn,zero_sub] at H
  exact H

theorem pentagon {p : L} (hp : p ∈ W) :
    eval a (b+c) p + eval (u+b) v p =
    eval b v p + eval (a+u) (c+v) p + eval a b p := by
  have h := congrArg representation hp.2.2
  simpa [map_eval,chord] using h

theorem pentagon_reverse {p : L} (hp : p ∈ W) :
    eval c (b+a) p + eval (v+b) u p =
    eval b u p + eval (c+v) (a+u) p + eval c b p := by
  have h := congrArg (representation.comp (t4Rename (Equiv.swap 0 3))) hp.2.2
  simp only [LieHom.comp_apply,map_add,map_eval,t4Rename_t,representation_t] at h
  exact h

theorem eval_bv_shift {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1<n) :
    eval b v p = eval b (-b-c) p := by
  have H := eval_central_shift b (-b-c) (v+b+c) (p := p) (n := n) ?_ ?_ hp hn
  · have he : -b-c+(v+b+c) = v := by abel
    simpa only [he] using H
  · simp only [lie_add,lie_self,bv]
    abel
  · simp only [sub_lie,neg_lie,lie_add,lie_self,bv,cv]
    grind [lie_skew]

theorem eval_bu_shift {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1<n) :
    eval b u p = eval b (-b-a) p := by
  have H := eval_central_shift b (-b-a) (u+b+a) (p := p) (n := n) ?_ ?_ hp hn
  · have he : -b-a+(u+b+a) = u := by abel
    simpa only [he] using H
  · simp only [lie_add,lie_self,bu]
    grind [lie_skew]
  · simp only [sub_lie,neg_lie,lie_add,lie_self,bu,au]
    grind [lie_skew]

theorem delta_a {n : ℕ} {p : L} (hp : p ∈ W) (hpn : p ∈ Ln n) (hn : 1<n) :
    Fb p-Fa p = eval fa (fb+fc) p - eval fa fb p - eval fb (-fb-fc) p := by
  apply SemiDirectSum.inl_injective action
  simp only [map_sub,map_eval,map_add,map_neg,Fb_inl,Fa_inl]
  change (eval (u+a) (v+c) p - eval u v p) - (eval (u+b) v p - eval u v p) =
    eval a (b+c) p - eval a b p - eval b (-b-c) p
  have H := pentagon hp
  rw [eval_bv_shift hpn hn,add_comm a u,add_comm c v] at H
  grind only

theorem delta_c {n : ℕ} {p : L} (hp : p ∈ W) (hpn : p ∈ Ln n) (hn : 1<n) :
    Fb p-Fc p = -eval fc (fa+fb) p + eval fc fb p + eval fb (-fb-fa) p := by
  apply SemiDirectSum.inl_injective action
  simp only [map_sub,map_eval,map_add,map_neg,Fb_inl,Fc_inl]
  change (eval (u+a) (v+c) p - eval u v p) - (eval u (v+b) p - eval u v p) =
    -eval c (a+b) p + eval c b p + eval b (-b-a) p
  have H := pentagon_reverse hp
  rw [eval_bu_shift hpn hn,solution_swap hp (v+b) u,solution_swap hp (c+v) (a+u),
    add_comm b a,add_comm a u,add_comm c v] at H
  grind only

end SpecialFiber

namespace Differentiation
open FreeDerivations

variable {M N : Type} [LieRing M] [LieAlgebra ℚ M] [LieRing N] [LieAlgebra ℚ N]

@[simp] theorem Jet.base_neg (p : Jet ℚ M) : (-p).base = -p.base := rfl
@[simp] theorem Jet.velocity_neg (p : Jet ℚ M) : (-p).velocity = -p.velocity := rfl
@[simp] theorem Jet.base_sub (p q : Jet ℚ M) : (p-q).base = p.base-q.base := rfl
@[simp] theorem Jet.velocity_sub (p q : Jet ℚ M) : (p-q).velocity = p.velocity-q.velocity := rfl

@[simp] theorem Jet.mk_add (a b da db : M) :
    (Jet.mk a da : Jet ℚ M) + Jet.mk b db = Jet.mk (a+b) (da+db) := rfl
@[simp] theorem Jet.mk_neg (a da : M) :
    -(Jet.mk a da : Jet ℚ M) = Jet.mk (-a) (-da) := rfl
@[simp] theorem Jet.mk_sub (a b da db : M) :
    (Jet.mk a da : Jet ℚ M) - Jet.mk b db = Jet.mk (a-b) (da-db) := rfl

@[simp] theorem eval_base (a b : Jet ℚ M) (p : L) :
    (eval a b p).base = eval a.base b.base p := map_eval Jet.baseHom a b p

def adPower (a : M) : ℕ → M → M
  | 0, t => t
  | n+1, t => ⁅a,adPower a n t⁆

omit [LieAlgebra ℚ M] in
@[simp] theorem adPower_zero (a t : M) : adPower a 0 t = t := rfl
omit [LieAlgebra ℚ M] in
@[simp] theorem adPower_succ (a t : M) (n : ℕ) : adPower a (n+1) t = ⁅a,adPower a n t⁆ := rfl
@[simp] theorem adPower_smul (a t : M) (n : ℕ) (r : ℚ) :
    adPower a n (r • t) = r • adPower a n t := by
  induction n <;> simp_all
omit [LieAlgebra ℚ M] in
@[simp] theorem adPower_zero_right (a : M) (n : ℕ) : adPower a n 0 = 0 := by
  induction n <;> simp_all
omit [LieAlgebra ℚ M] in
@[simp] theorem adPower_self (a : M) {n : ℕ} (hn : 0<n) : adPower a n a = 0 := by
  cases n with
  | zero => omega
  | succ n =>
    induction n with
    | zero => simp
    | succ n ih => simp_all
omit [LieAlgebra ℚ M] in
@[simp] theorem adPower_zero_left (t : M) {n : ℕ} (hn : 0<n) : adPower (0:M) n t = 0 := by
  cases n <;> simp_all

def slope (p : L) (a b da db : M) : M :=
  (eval (Jet.mk a da : Jet ℚ M) (Jet.mk b db) p).velocity

@[simp] theorem slope_x (a b da db : M) : slope x a b da db = da := by simp [slope]
@[simp] theorem slope_y (a b da db : M) : slope y a b da db = db := by simp [slope]
@[simp] theorem slope_zero (a b da db : M) : slope 0 a b da db = 0 := by simp [slope]
@[simp] theorem slope_add (p q : L) (a b da db : M) :
    slope (p+q) a b da db = slope p a b da db + slope q a b da db := by simp [slope]
@[simp] theorem slope_smul (r : ℚ) (p : L) (a b da db : M) :
    slope (r • p) a b da db = r • slope p a b da db := by simp [slope]
@[simp] theorem slope_lie (p q : L) (a b da db : M) :
    slope ⁅p,q⁆ a b da db = ⁅slope p a b da db,eval a b q⁆ +
      ⁅eval a b p,slope q a b da db⁆ := by simp [slope,LieHom.map_lie]

@[simp] theorem slope_zero_direction (p : L) (a b : M) : slope p a b 0 0 = 0 := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [slope,eval]
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [hp]
  | hl p q hp hq => simp [hp,hq]

theorem slope_add_direction (p : L) (a b da db ea eb : M) :
    slope p a b (da+ea) (db+eb) = slope p a b da db + slope p a b ea eb := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [slope,eval]
  | ha p q hp hq => simp [hp,hq]; abel
  | hs r p hp => simp [hp,smul_add]
  | hl p q hp hq => simp [hp,hq,add_lie,lie_add]; abel

theorem slope_smul_direction (p : L) (a b da db : M) (r : ℚ) :
    slope p a b (r • da) (r • db) = r • slope p a b da db := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [slope,eval]
  | ha p q hp hq => simp [hp,hq,smul_add]
  | hs s p hp => simp [hp,smul_comm s r]
  | hl p q hp hq => simp [hp,hq,smul_add]

theorem word_pos {n : ℕ} {p : L} (hp : WeightedWord (fun _:Bool => 1) n p) : 0<n := by
  induction hp with
  | generator => omega
  | bracket hp hq ihp ihq => omega

def DiagonalData (n : ℕ) (p : L) (s k : ℚ) : Prop :=
  (n ≠ 1 → s = 0) ∧ ∀ (M : Type) [LieRing M] [LieAlgebra ℚ M] (a t : M),
    eval (Jet.mk a 0 : Jet ℚ M) (Jet.mk (-a) t) p =
      Jet.mk (s • a) (k • adPower a (n-1) t)

theorem diagonal_bracket {n m : ℕ} {p q : L} {s k t l : ℚ}
    (hn : 0 < n) (hm : 0 < m) (hp : DiagonalData n p s k) (hq : DiagonalData m q t l) :
    ∃ r : ℚ, DiagonalData (n+m) ⁅p,q⁆ 0 r := by
  rcases hp with ⟨hs,hp⟩
  rcases hq with ⟨ht,hq⟩
  by_cases hn1 : n=1 <;> by_cases hm1 : m=1
  · subst n; subst m
    refine ⟨s*l-t*k, fun _ => rfl, ?_⟩
    intro M _ _ a b
    rw [LieHom.map_lie,hp,hq]
    ext
    · simp
    · change ⁅k • b,t • a⁆ + ⁅s • a,l • b⁆ = (s*l-t*k) • ⁅a,b⁆
      rw [smul_lie,lie_smul,←lie_skew b a,smul_neg,smul_lie,lie_smul]
      simp only [sub_smul,mul_smul]
      module
  · subst n
    have ht0 := ht hm1
    subst t
    refine ⟨s*l, fun _ => rfl, ?_⟩
    intro M _ _ a b
    rw [LieHom.map_lie,hp,hq]
    ext
    · simp
    · have he : 1+m-1 = (m-1)+1 := by omega
      simp [he,mul_smul,smul_comm l s]
  · subst m
    have hs0 := hs hn1
    subst s
    refine ⟨-(t*k), fun _ => rfl, ?_⟩
    intro M _ _ a b
    rw [LieHom.map_lie,hp,hq]
    ext
    · simp
    · have he : n+1-1 = (n-1)+1 := by omega
      simp only [Jet.velocity_lie,zero_smul,zero_lie,he,adPower_succ,
        smul_lie,lie_smul,neg_smul,mul_smul]
      rw [←lie_skew (adPower a (n-1) b) a,smul_neg,smul_neg]
      rw [smul_comm]
      simp
  · have hs0 := hs hn1
    have ht0 := ht hm1
    subst s; subst t
    refine ⟨0, fun _ => rfl, ?_⟩
    intro M _ _ a b
    rw [LieHom.map_lie,hp,hq]
    ext <;> simp

theorem diagonal_word {n : ℕ} {p : L} (hp : WeightedWord (fun _:Bool => 1) n p) :
    ∃ s k : ℚ, DiagonalData n p s k := by
  induction hp with
  | generator i =>
    cases i
    · refine ⟨1,0, ?_⟩
      constructor
      · simp
      · intro M _ _ a b; simp [eval]
    · refine ⟨-1,1, ?_⟩
      constructor
      · simp
      · intro M _ _ a b; simp [eval]
  | bracket hp hq ihp ihq =>
    rcases ihp with ⟨s,k,hp'⟩
    rcases ihq with ⟨t,l,hq'⟩
    obtain ⟨r,hr⟩ := diagonal_bracket (word_pos hp) (word_pos hq) hp' hq'
    exact ⟨0,r,hr⟩

theorem diagonal_homogeneous {n : ℕ} {p : L} (hp : p ∈ Ln n) :
    ∃ s k : ℚ, DiagonalData n p s k := by
  induction hp using Submodule.span_induction with
  | mem p hp => exact diagonal_word hp
  | zero =>
    refine ⟨0,0,fun _ => rfl,?_⟩
    intro M _ _ a b
    ext <;> simp
  | add p q _ _ hp hq =>
    rcases hp with ⟨s,k,hs,hp⟩
    rcases hq with ⟨t,l,ht,hq⟩
    refine ⟨s+t,k+l,fun hn => by simp [hs hn,ht hn],?_⟩
    intro M _ _ a b
    rw [map_add,hp,hq]
    ext <;> simp [add_smul]
  | smul r p _ hp =>
    rcases hp with ⟨s,k,hs,hp⟩
    refine ⟨r*s,r*k,fun hn => by simp [hs hn],?_⟩
    intro M _ _ a b
    rw [map_smul,hp]
    ext <;> simp [mul_smul]

 theorem slope_neg_direction (p : L) (a b da db : M) :
    slope p a b (-da) (-db) = -slope p a b da db := by
  simpa using slope_smul_direction p a b da db (-1)

 theorem slope_inner (p : L) (a b t : M) :
    slope p a b ⁅t,a⁆ ⁅t,b⁆ = ⁅t,eval a b p⁆ := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [slope,eval]
  | ha p q hp hq => simp [hp,hq,lie_add]
  | hs r p hp => simp [hp]
  | hl p q hp hq => simp [hp,hq,LieHom.map_lie,lie_lie]

 theorem slope_swap {p : L} (hp : p ∈ W) (a b da db : M) :
    slope p a b da db = -slope p b a db da := by
  exact congrArg Jet.velocity (solution_swap hp (Jet.mk a da : Jet ℚ M) (Jet.mk b db))

 theorem diagonal_slope {n : ℕ} {p : L} {s k : ℚ}
    (hp : DiagonalData n p s k) (a t : M) :
    slope p a (-a) 0 t = k • adPower a (n-1) t :=
  congrArg Jet.velocity (hp.2 M a t)

 theorem diagonal_first {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1<n) (a t : M) :
    slope p a (-a) t 0 = slope p a (-a) 0 t := by
  have H := congrArg Jet.velocity (eval_vanish_of_commuting
    (Jet.mk a t : Jet ℚ M) (-Jet.mk a t) (by rw [lie_neg,lie_self,neg_zero]) hp hn)
  change slope p a (-a) t (-t) = 0 at H
  have hs := slope_add_direction p a (-a) t 0 0 (-t)
  have hneg := slope_neg_direction p a (-a) 0 t
  simp only [neg_zero] at hneg
  simp only [add_zero,zero_add,hneg,H] at hs
  exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg] using hs.symm)

 def G (p : L) : L := ⁅x,eval y x p⁆ + ⁅-x-y,eval y (-x-y) p⁆

 theorem eval_G (p : L) (a b : M) :
    eval a b (G p) = ⁅a,eval b a p⁆ + ⁅-a-b,eval b (-a-b) p⁆ := by
  simp only [G,map_add,LieHom.map_lie,map_eval,eval_x,eval_y,map_sub,map_neg]

 theorem slope_G (p : L) (a b t : M) :
    slope (G p) a b t 0 =
      ⁅t,eval b a p-eval b (-a-b) p⁆ +
      ⁅a,slope p b a 0 t⁆ - ⁅-a-b,slope p b (-a-b) 0 t⁆ := by
  have hh := congrArg Jet.velocity (eval_G p (Jet.mk a t : Jet ℚ M) (Jet.mk b 0))
  change slope (G p) a b t 0 = _ at hh
  simp only [Jet.mk_neg,Jet.mk_sub,sub_zero] at hh
  simp only [Jet.velocity_add,Jet.velocity_lie,eval_base] at hh
  have he : slope p b (-a-b) 0 (-t) = -slope p b (-a-b) 0 t := by
    simpa only [neg_zero] using slope_neg_direction p b (-a-b) 0 t
  change slope (G p) a b t 0 = ⁅t,eval b a p⁆ + ⁅a,slope p b a 0 t⁆ +
    (⁅-t,eval b (-a-b) p⁆ + ⁅-a-b,slope p b (-a-b) 0 (-t)⁆) at hh
  rw [he,neg_lie,lie_neg] at hh
  rw [lie_sub]
  grind only

 def fiberEval (a b c : M) : SpecialFiber.F →ₗ⁅ℚ⁆ M :=
  FreeLieAlgebra.lift ℚ (fun i => if i=0 then a else if i=1 then b else c)
@[simp] theorem fiberEval_fa (a b c : M) : fiberEval a b c SpecialFiber.fa = a := by
  simp [fiberEval,SpecialFiber.fa]
@[simp] theorem fiberEval_fb (a b c : M) : fiberEval a b c SpecialFiber.fb = b := by
  simp [fiberEval,SpecialFiber.fb]
@[simp] theorem fiberEval_fc (a b c : M) : fiberEval a b c SpecialFiber.fc = c := by
  simp [fiberEval,SpecialFiber.fc]

 theorem fiberEval_spec (a b : M) (z : SpecialFiber.F) :
    fiberEval a b (-a-b) z = eval a b (SpecialFiber.fiberSpec z) := by
  have h : fiberEval a b (-a-b) = (eval a b).comp SpecialFiber.fiberSpec := by
    apply FreeLieAlgebra.hom_ext
    intro i
    fin_cases i <;> simp [fiberEval,SpecialFiber.fiberSpec]
  exact LieHom.congr_fun h z

@[simp] theorem fiberEval_base (a b c : Jet ℚ M) (z : SpecialFiber.F) :
    (fiberEval a b c z).base = fiberEval a.base b.base c.base z := by
  have h : Jet.baseHom.comp (fiberEval a b c) = fiberEval a.base b.base c.base := by
    apply FreeLieAlgebra.hom_ext
    intro i
    fin_cases i <;> simp [fiberEval,Jet.baseHom] <;> rfl
  exact LieHom.congr_fun h z

 theorem fiberEval_Fb {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1<n) (a b : M) :
    fiberEval a b (-a-b) (SpecialFiber.Fb p) = - eval (-a-b) a p := by
  rw [fiberEval_spec,SpecialFiber.Fb_specialize hp hn]
  simp [map_eval]

 theorem transverse {n : ℕ} {p : L} {k : ℚ} (hp : p ∈ W) (hpn : p ∈ Ln n)
    (hn : 1<n) (hdiag : DiagonalData n p 0 k) (a b t : M) :
    -⁅t,eval (-a-b) a p⁆ = k • (adPower a n t-adPower (-a-b) n t) +
       ⁅a,slope p b a 0 t⁆ - ⁅-a-b,slope p b (-a-b) 0 t⁆ := by
  have H := congrArg (fiberEval (Jet.mk a 0 : Jet ℚ M) (Jet.mk b 0)
    (Jet.mk (-a-b) t)) (SpecialFiber.fiber_identity p)
  rw [SpecialFiber.delta_a hp hpn hn,SpecialFiber.delta_c hp hpn hn] at H
  simp only [LieHom.map_lie,map_add,map_sub,map_neg,map_eval,
    fiberEval_fa,fiberEval_fb,fiberEval_fc] at H
  have hc : (Jet.mk a 0 : Jet ℚ M) + Jet.mk b 0 + Jet.mk (-a-b) t = Jet.mk 0 t := by
    ext <;> simp
  rw [hc] at H
  simp only [Jet.mk_add,Jet.mk_neg,Jet.mk_sub,zero_add,add_zero,neg_zero,sub_zero,zero_sub] at H
  have Hv := congrArg Jet.velocity H
  simp only [Jet.velocity_lie,Jet.velocity_sub,Jet.velocity_add,Jet.velocity_neg,
    Jet.base_add,Jet.base_sub,Jet.base_neg,eval_base,fiberEval_base] at Hv
  have hdiagNeg : -(-a-b) = a+b := by abel
  have hba : b+(-a-b) = -a := by abel
  have hab : -b-(-a-b) = a := by abel
  have hc0 : eval (-a-b) (a+b) p = 0 := by
    have h := eval_vanish_of_commuting (-a-b) (-(-a-b)) (by simp only [lie_neg,lie_self,neg_zero]) hpn hn
    simpa only [hdiagNeg] using h
  have hdelc : -eval (-a-b) (a+b) p + eval (-a-b) b p + eval b (-b-a) p = 0 := by
    rw [hc0,neg_zero,zero_add,solution_swap hp (-a-b) b]
    have he : -b-a = -a-b := by abel
    rw [he,neg_add_cancel]
  have hdp : slope p (-a-b) (a+b) t 0 = k • adPower (-a-b) (n-1) t := by
    rw [← hdiagNeg,diagonal_first hpn hn,diagonal_slope hdiag]
  have hdm : slope p b a 0 (-t) = -slope p b a 0 t := by
    simpa only [neg_zero] using slope_neg_direction p b a 0 t
  have hswap := slope_swap hp (-a-b) b t 0
  have hnp : n=(n-1)+1 := by omega
  change ⁅t,fiberEval a b (-a-b) (SpecialFiber.Fb p)⁆ + ⁅(0:M),_⁆ =
    (⁅(0:M),_⁆ + ⁅a,slope p a (b+(-a-b)) 0 t - slope p a b 0 0 -
      slope p b (-b-(-a-b)) 0 (-t)⁆) +
    (⁅t,-eval (-a-b) (a+b) p + eval (-a-b) b p + eval b (-b-a) p⁆ +
      ⁅-a-b,-slope p (-a-b) (a+b) t 0 + slope p (-a-b) b t 0 +
        slope p b (-b-a) 0 0⁆) at Hv
  rw [fiberEval_Fb hpn hn,hdelc,hba,hab,slope_zero_direction,slope_zero_direction,
    diagonal_slope hdiag,hdp,hdm,hswap] at Hv
  simp only [zero_lie,lie_zero,add_zero,zero_add,sub_zero,lie_neg,lie_sub,lie_add,lie_smul] at Hv
  rw [show ⁅a,adPower a (n-1) t⁆ = adPower a n t by rw [hnp]; rfl,
    show ⁅-a-b,adPower (-a-b) (n-1) t⁆ = adPower (-a-b) n t by rw [hnp]; rfl] at Hv
  rw [smul_sub]
  grind only

 theorem slope_G_formula {n : ℕ} {p : L} {k : ℚ} (hp : p ∈ W) (hpn : p ∈ Ln n)
    (hn : 1<n) (hdiag : DiagonalData n p 0 k) (a b t : M) :
    slope (G p) a b t 0 = - k • (adPower a n t-adPower (-a-b) n t) := by
  have H := transverse hp hpn hn hdiag a b t
  have h3 := solution_three hp a b
  rw [solution_swap hp a b] at h3
  have he : eval b a p - eval b (-a-b) p = eval (-a-b) a p := by grind only
  rw [slope_G,he,neg_smul]
  grind only

def swapJet : Jet ℚ (Jet ℚ M) →ₗ⁅ℚ⁆ Jet ℚ (Jet ℚ M) where
  toFun z := ⟨⟨z.base.base,z.velocity.base⟩,⟨z.base.velocity,z.velocity.velocity⟩⟩
  map_add' a b := by apply Jet.ext <;> apply Jet.ext <;> rfl
  map_smul' r a := by apply Jet.ext <;> apply Jet.ext <;> rfl
  map_lie' {a b} := by
    apply Jet.ext <;> apply Jet.ext
    all_goals simp only [Jet.base_lie,Jet.velocity_lie,Jet.base_add,Jet.velocity_add]
    all_goals first | rfl | abel

theorem mixed_slope (p : L) (a b u v : M) :
    (slope p (Jet.mk a u : Jet ℚ M) (Jet.mk b 0) (Jet.mk v 0) 0).velocity =
    (slope p (Jet.mk a v : Jet ℚ M) (Jet.mk b 0) (Jet.mk u 0) 0).velocity := by
  have h := map_eval (swapJet : Jet ℚ (Jet ℚ M) →ₗ⁅ℚ⁆ Jet ℚ (Jet ℚ M))
    (Jet.mk (Jet.mk a u) (Jet.mk v 0)) (Jet.mk (Jet.mk b 0) 0) p
  exact congrArg (fun z => z.velocity.velocity) h

@[simp] theorem adPower_base (a t : Jet ℚ M) (n : ℕ) :
    (adPower a n t).base = adPower a.base n t.base := by
  induction n <;> simp_all

theorem adPower_radial (a t : M) (n : ℕ) :
    (adPower (Jet.mk a a : Jet ℚ M) n (Jet.mk t 0)).velocity =
      (n : ℚ) • adPower a n t := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [adPower_succ,Jet.velocity_lie,adPower_base,ih,lie_smul,
      Nat.cast_add,Nat.cast_one,add_smul,one_smul]
    abel

theorem adPower_transverse_self (a t : M) {n : ℕ} (hn : 0<n) :
    (adPower (Jet.mk a t : Jet ℚ M) n (Jet.mk a 0)).velocity = -adPower a n t := by
  cases n with
  | zero => omega
  | succ n =>
    induction n with
    | zero => simp [lie_skew]
    | succ n ih =>
      rw [adPower_succ,Jet.velocity_lie,adPower_base]
      change ⁅t,adPower a (n+1) a⁆ +
        ⁅a,(adPower (Jet.mk a t : Jet ℚ M) (n+1) (Jet.mk a 0)).velocity⁆ = _
      rw [adPower_self a (n := n+1) (by omega),lie_zero,zero_add,ih (by omega),lie_neg]
      rfl

theorem adPower_zero_base (a t : M) {n : ℕ} (hn : 1<n) :
    (adPower (Jet.mk 0 a : Jet ℚ M) n (Jet.mk t 0)).velocity = 0 := by
  cases n with
  | zero => omega
  | succ n =>
    simp only [adPower_succ,Jet.velocity_lie,adPower_base,zero_lie,add_zero]
    rw [adPower_zero_left t (by omega),lie_zero]

 theorem mixed_scalar {n : ℕ} {p : L} {k : ℚ} (hp : p ∈ W) (hpn : p ∈ Ln n)
    (hn : 2<n) (hdiag : DiagonalData n p 0 k) (a t : M) :
    (((n : ℚ)+1)*k) • adPower a n t = 0 := by
  have H1 := congrArg Jet.velocity (slope_G_formula hp hpn (by omega) hdiag
    (Jet.mk a a : Jet ℚ M) (Jet.mk (-a) 0) (Jet.mk t 0))
  have H2 := congrArg Jet.velocity (slope_G_formula hp hpn (by omega) hdiag
    (Jet.mk a t : Jet ℚ M) (Jet.mk (-a) 0) (Jet.mk a 0))
  have hc1 : -(Jet.mk a a : Jet ℚ M) - Jet.mk (-a) 0 = Jet.mk 0 (-a) := by
    ext <;> simp
  have hc2 : -(Jet.mk a t : Jet ℚ M) - Jet.mk (-a) 0 = Jet.mk 0 (-t) := by
    ext <;> simp
  rw [hc1] at H1
  rw [hc2] at H2
  simp only [Jet.velocity_smul,Jet.velocity_sub,adPower_radial,
    adPower_zero_base (-a) t (n := n) (by omega),sub_zero] at H1
  simp only [Jet.velocity_smul,Jet.velocity_sub,
    adPower_transverse_self a t (n := n) (by omega),adPower_zero_base (-t) a (n := n) (by omega),sub_zero] at H2
  have hm := mixed_slope (G p) a (-a) a t
  rw [H1,H2] at hm
  have hz : (-k) • ((n:ℚ) • adPower a n t) - (-k) • (-adPower a n t) = 0 := sub_eq_zero.mpr hm
  calc
    (((n : ℚ)+1)*k) • adPower a n t =
        -((-k) • ((n:ℚ) • adPower a n t) - (-k) • (-adPower a n t)) := by module
    _ = 0 := by rw [hz,neg_zero]

 theorem diagonal_scalar_zero {n : ℕ} {p : L} {k : ℚ} (hp : p ∈ W) (hpn : p ∈ Ln n)
    (hn : 2<n) (hdiag : DiagonalData n p 0 k) : k=0 := by
  let := LieRing.ofAssociativeRing (A := Matrix (Fin 2) (Fin 2) ℚ)
  let a : Matrix (Fin 2) (Fin 2) ℚ := !![1,0;0,0]
  let t : Matrix (Fin 2) (Fin 2) ℚ := !![0,1;0,0]
  have hbr : ⁅a,t⁆ = t := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [a,t,Ring.lie_def,Matrix.mul_apply,Fin.sum_univ_two]
  have had (m : ℕ) : adPower a m t = t := by
    induction m with
    | zero => rfl
    | succ m ih => rw [adPower_succ,ih,hbr]
  have H := mixed_scalar hp hpn hn hdiag a t
  rw [had] at H
  have hc := congrArg (fun z => z 0 1) H
  change (((n : ℚ)+1)*k) * 1 = 0 at hc
  rw [mul_one] at hc
  exact (mul_eq_zero.mp hc).resolve_left (by positivity)

 theorem special_linearization {n : ℕ} {p : L} (hp : p ∈ W) (hpn : p ∈ Ln n)
    (hn : 2<n) (a t : M) : slope p a (-a) 0 t = 0 := by
  obtain ⟨s,k,hd⟩ := diagonal_homogeneous hpn
  have hs := hd.1 (by omega)
  subst s
  have hk := diagonal_scalar_zero hp hpn hn hd
  rw [diagonal_slope hd,hk,zero_smul]

 theorem special_G_zero {n : ℕ} {p : L} (hp : p ∈ W) (hpn : p ∈ Ln n)
    (hn : 2<n) : G p = 0 := by
  obtain ⟨s,k,hd⟩ := diagonal_homogeneous hpn
  have hs := hd.1 (by omega)
  subst s
  have hk := diagonal_scalar_zero hp hpn hn hd
  subst k
  have hder (t : L) : slope (G p) x y t 0 = 0 := by
    rw [slope_G_formula hp hpn (by omega) hd]
    simp
  have hcomm : ⁅y,G p⁆ = 0 := by
    have h := slope_inner (G p) x y y
    rw [lie_self,eval_self,LieHom.id_apply] at h
    rw [← h,hder]
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp
    (AssociativeModel.centralizer_generator true hcomm)
  change r • y = G p at hr
  have he : eval (0 : L) y (G p) = 0 := by
    rw [eval_G]
    simp only [zero_lie,neg_zero,zero_sub,zero_add]
    rw [eval_vanish_of_commuting y (-y) (by simp) hpn (by omega),lie_zero]
  rw [← hr,map_smul,eval_y] at he
  exact hr.symm.trans he

 theorem special_identity {n : ℕ} {p : L} (hp : p ∈ W) (hpn : p ∈ Ln n)
    (hn : 2<n) (a b : M) : ⁅a,eval b a p⁆ + ⁅-a-b,eval b (-a-b) p⁆ = 0 := by
  rw [← eval_G,special_G_zero hp hpn hn,map_zero]

end Differentiation

namespace Elimination
open LieAlgebra
variable {R α : Type*} [CommRing R]
attribute [local instance] LieRing.ofAssociativeRing
abbrev F (R α : Type*) [CommRing R] := FreeLieAlgebra R (ℕ × α)
abbrev G (R α : Type*) [CommRing R] := FreeLieAlgebra R (Option α)
def X : G R α := FreeLieAlgebra.of R none
def Y (a : α) : G R α := FreeLieAlgebra.of R (some a)
def E (n : ℕ) (a : α) : F R α := FreeLieAlgebra.of R (n,a)
def shift : LieDerivation R (F R α) (F R α) :=
  FreeDerivations.extend (fun (i,a) => E (i+1) a)
@[simp] theorem shift_E (n : ℕ) (a : α) : shift (E n a : F R α) = E (n+1) a := by
  simp [shift,E]
def action : R →ₗ⁅R⁆ LieDerivation R (F R α) (F R α) where
  toFun r := r • shift
  map_add' r s := add_smul r s shift
  map_smul' r s := mul_smul r s shift
  map_lie' {r s} := by simp [Ring.lie_def,mul_comm,smul_lie,lie_smul]
abbrev M (R α : Type*) [CommRing R] := SemiDirectSum (F R α) R action

def expand : G R α →ₗ⁅R⁆ M R α :=
  FreeLieAlgebra.lift R (fun a => match a with
    | none => SemiDirectSum.inr action 1
    | some a => SemiDirectSum.inl action (E 0 a))
@[simp] theorem expand_X : expand (X : G R α) = SemiDirectSum.inr action 1 := by
  simp [expand,X]
@[simp] theorem expand_Y (a : α) : expand (Y a : G R α) = SemiDirectSum.inl action (E 0 a) := by
  simp [expand,Y]

def adWord (n : ℕ) (a : α) : G R α :=
  (LieAlgebra.ad R (G R α) X)^[n] (Y a)
@[simp] theorem adWord_zero (a : α) : adWord 0 a = (Y a : G R α) := rfl
@[simp] theorem adWord_succ (n : ℕ) (a : α) :
    (adWord (n+1) a : G R α) = ⁅(X : G R α),adWord n a⁆ := by
  exact Function.iterate_succ_apply' _ n _
def collapseFiber : F R α →ₗ⁅R⁆ G R α := FreeLieAlgebra.lift R (fun (n,a) => adWord n a)
@[simp] theorem collapseFiber_E (n : ℕ) (a : α) :
    collapseFiber (E n a : F R α) = adWord n a := by simp [collapseFiber,E]

theorem collapse_shift (p : F R α) : collapseFiber (shift p) = ⁅(X : G R α),collapseFiber p⁆ := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg a => cases a; simp [shift,collapseFiber,E,adWord_succ]
  | ha p q hp hq => simp [hp,hq,lie_add]
  | hs r p hp => simp [hp]
  | hl p q hp hq =>
    simp only [LieDerivation.apply_lie_eq_add,map_add,LieHom.map_lie,hp,hq]
    simpa only [add_comm] using (leibniz_lie (X : G R α) (collapseFiber p) (collapseFiber q)).symm

def scalarX : R →ₗ⁅R⁆ G R α where
  toFun r := r • X
  map_add' r s := add_smul r s X
  map_smul' r s := mul_smul r s X
  map_lie' {r s} := by simp [Ring.lie_def,mul_comm,smul_lie,lie_smul]

def collapse : M R α →ₗ⁅R⁆ G R α :=
  InnerSemiDirect.lift action collapseFiber scalarX (by
    intro r p
    change collapseFiber (r • shift p) = ⁅r • X,collapseFiber p⁆
    rw [map_smul,collapse_shift,smul_lie])

@[simp] theorem collapse_inl (p : F R α) :
    collapse (SemiDirectSum.inl action p) = collapseFiber p := by simp [collapse,InnerSemiDirect.lift]
@[simp] theorem collapse_inr (r : R) :
    collapse (SemiDirectSum.inr action r : M R α) = r • X := by simp [collapse,InnerSemiDirect.lift,scalarX]

theorem collapse_expand (p : G R α) : collapse (expand p) = p := by
  have h : collapse.comp (expand : G R α →ₗ⁅R⁆ M R α) = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro a
    cases a <;> simp [expand,collapse,InnerSemiDirect.lift,scalarX,collapseFiber,E,X,Y]
  exact LieHom.congr_fun h p

theorem expand_adWord (n : ℕ) (a : α) :
    expand (adWord n a : G R α) = SemiDirectSum.inl action (E n a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [adWord_succ,LieHom.map_lie,expand_X,ih]
    simp only [SemiDirectSum.lie_eq_mk,SemiDirectSum.inl_eq_mk,SemiDirectSum.inr_eq_mk]
    ext <;> simp [action]

theorem expand_collapseFiber (p : F R α) :
    expand (collapseFiber p) = SemiDirectSum.inl action p := by
  have h : (expand : G R α →ₗ⁅R⁆ M R α).comp collapseFiber = SemiDirectSum.inl action := by
    apply FreeLieAlgebra.hom_ext
    intro a
    cases a
    simp [collapseFiber,expand_adWord,E]
  exact LieHom.congr_fun h p

theorem expand_collapse (p : M R α) : expand (collapse p) = p := by
  change expand (collapseFiber p.left + scalarX p.right) = p
  rw [map_add,expand_collapseFiber]
  change _ + expand (p.right • X) = p
  rw [map_smul,expand_X]
  ext <;> simp

def equivalence : G R α ≃ₗ⁅R⁆ M R α :=
  { expand with
    invFun := collapse
    left_inv := collapse_expand
    right_inv := expand_collapse }

theorem collapseFiber_injective : Function.Injective (collapseFiber : F R α → G R α) := by
  intro p q h
  apply_fun expand at h
  rw [expand_collapseFiber,expand_collapseFiber] at h
  exact congrArg SemiDirectSum.left h

end Elimination

namespace AssociativeElimination
open LieAlgebra
variable {R α β : Type*} [CommRing R]
attribute [local instance] LieRing.ofAssociativeRing
abbrev A (R α : Type*) [CommRing R] := MonoidAlgebra R (FreeMonoid α)
def atom (a : α) : A R α := MonoidAlgebra.single (FreeMonoid.of a) 1

def lift {B : Type*} [Ring B] [Algebra R B] (f : α → B) : A R α →ₐ[R] B :=
  MonoidAlgebra.lift R B (FreeMonoid α) (FreeMonoid.lift f)
@[simp] theorem lift_atom {B : Type*} [Ring B] [Algebra R B] (f : α → B) (a : α) :
    lift (R := R) f (atom a) = f a := by simp [lift,atom]

@[ext] theorem hom_ext {B : Type*} [Semiring B] [Algebra R B] {f g : A R α →ₐ[R] B}
    (h : ∀ a, f (atom a) = g (atom a)) : f=g := by
  apply (MonoidAlgebra.lift R B (FreeMonoid α)).symm.injective
  apply FreeMonoid.hom_eq
  intro a
  exact h a

def embed : FreeLieAlgebra R α →ₗ⁅R⁆ A R α := FreeLieAlgebra.lift R atom
@[simp] theorem embed_of (a : α) : embed (FreeLieAlgebra.of R a) = atom a := by simp [embed]

def dualLift (f : α → A R α) : A R α →ₐ[R] DualNumber (A R α) :=
  lift (fun a => TrivSqZeroExt.inl (atom a) + TrivSqZeroExt.inr (f a))
@[simp] theorem dualLift_base (f : α → A R α) (p : A R α) :
    (dualLift f p).fst = p := by
  have h : (TrivSqZeroExt.fstHom R (A R α) (A R α)).comp (dualLift f) = AlgHom.id R (A R α) := by
    apply hom_ext
    intro a
    simp [dualLift]
  exact AlgHom.congr_fun h p

def deriv (f : α → A R α) : A R α →ₗ[R] A R α :=
  ((TrivSqZeroExt.sndHom (A R α) (A R α)).restrictScalars R).comp (dualLift f).toLinearMap
@[simp] theorem deriv_atom (f : α → A R α) (a : α) : deriv f (atom a) = f a := by
  simp [deriv,dualLift]
@[simp] theorem deriv_one (f : α → A R α) : deriv f 1 = 0 := by simp [deriv]
theorem deriv_mul (f : α → A R α) (p q : A R α) :
    deriv f (p*q) = deriv f p*q + p*deriv f q := by
  change (dualLift f (p*q)).snd = _
  rw [map_mul,DualNumber.snd_mul,dualLift_base,dualLift_base]
  exact add_comm _ _
theorem deriv_lie (f : α → A R α) (p q : A R α) :
    deriv f ⁅p,q⁆ = ⁅deriv f p,q⁆ + ⁅p,deriv f q⁆ := by
  simp only [Ring.lie_def,map_sub,deriv_mul]
  abel

def shift : A R (ℕ×α) →ₗ[R] A R (ℕ×α) := deriv (fun (i,a) => atom (i+1,a))
@[simp] theorem shift_atom (i : ℕ) (a : α) : shift (atom (i,a) : A R (ℕ×α)) = atom (i+1,a) := by
  simp [shift]
@[simp] theorem shift_one : shift (1 : A R (ℕ×α)) = 0 := deriv_one _
theorem shift_mul (p q : A R (ℕ×α)) : shift (p*q) = shift p*q + p*shift q := deriv_mul _ _ _

theorem embed_shift (p : Elimination.F R α) : embed (Elimination.shift p) = shift (embed p) := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg a => cases a; simp [Elimination.shift,Elimination.E]
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [hp]
  | hl p q hp hq =>
    simp only [LieDerivation.apply_lie_eq_add,map_add,LieHom.map_lie,hp,hq]
    simpa only [shift,add_comm] using (deriv_lie (fun (i,a) => (atom (i+1,a) : A R (ℕ×α))) (embed p) (embed q)).symm

def leftMul : A R α →ₐ[R] Module.End R (A R α) := Algebra.lsmul R R (A R α)
@[simp] theorem leftMul_apply (p q : A R α) : leftMul p q = p*q := rfl
@[simp] theorem comm_shift_left (p : A R (ℕ×α)) :
    ⁅(shift : Module.End R (A R (ℕ×α))),leftMul p⁆ = leftMul (shift p) := by
  apply LinearMap.ext
  intro q
  change shift (p*q)-p*shift q = shift p*q
  rw [shift_mul,add_sub_cancel_right]

def scalarShift : R →ₗ⁅R⁆ Module.End R (A R (ℕ×α)) where
  toFun r := r • shift
  map_add' r s := add_smul r s shift
  map_smul' r s := mul_smul r s shift
  map_lie' {r s} := by simp [Ring.lie_def,smul_smul,mul_comm]

def representation : Elimination.M R α →ₗ⁅R⁆ Module.End R (A R (ℕ×α)) :=
  InnerSemiDirect.lift Elimination.action (leftMul.toLieHom.comp embed) scalarShift (by
    intro r p
    change leftMul (embed (r • Elimination.shift p)) = ⁅r • (shift : Module.End R (A R (ℕ×α))),leftMul (embed p)⁆
    rw [map_smul,map_smul,embed_shift]
    apply LinearMap.ext
    intro q
    change r • (shift (embed p)*q) = r • shift (embed p*q) - embed p*(r • shift q)
    rw [shift_mul,smul_add,mul_smul_comm,add_sub_cancel_right])

def operator : A R (Option α) →ₐ[R] Module.End R (A R (ℕ×α)) :=
  lift (fun | none => shift | some a => leftMul (atom (0,a)))

@[simp] theorem representation_inl (p : Elimination.F R α) :
    representation (SemiDirectSum.inl Elimination.action p) = leftMul (embed p) := by simp [representation,InnerSemiDirect.lift]
@[simp] theorem representation_inr (r : R) :
    representation (SemiDirectSum.inr Elimination.action r : Elimination.M R α) = r • shift := by
  simp [representation,InnerSemiDirect.lift,scalarShift]

theorem operator_embed (p : Elimination.G R α) :
    operator (embed p) = representation (Elimination.expand p) := by
  have h : operator.toLieHom.comp embed = representation.comp (Elimination.expand : Elimination.G R α →ₗ⁅R⁆ Elimination.M R α) := by
    apply FreeLieAlgebra.hom_ext
    intro a
    cases a <;> simp [operator,Elimination.expand,Elimination.E,representation,InnerSemiDirect.lift,scalarShift]
  exact LieHom.congr_fun h p

def extract : A R (Option α) →ₗ[R] A R (ℕ×α) :=
  (LinearMap.applyₗ 1).comp operator.toLinearMap

theorem extract_embed (p : Elimination.G R α) :
    extract (embed p) = embed (Elimination.expand p).left := by
  change operator (embed p) 1 = _
  rw [operator_embed]
  change (leftMul (embed (Elimination.expand p).left) + (Elimination.expand p).right • (shift : Module.End R (A R (ℕ×α)))) 1 = _
  simp

end AssociativeElimination

namespace IntegralWords
open Classical
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {α β : Type*}
abbrev AQ (α : Type*) := A ℚ α

def word (w : List α) : AQ α := MonoidAlgebra.single (FreeMonoid.ofList w) 1
@[simp] theorem word_nil : word ([] : List α) = 1 := rfl
@[simp] theorem word_singleton (a : α) : word [a] = atom a := rfl
theorem word_append (u v : List α) : word (u++v) = word u * word v := by
  simp [word,MonoidAlgebra.single_mul_single,FreeMonoid.ofList_append]
theorem word_cons (a : α) (w : List α) : word (a::w) = atom a * word w := by
  exact word_append [a] w

def lattice : Submodule ℤ (AQ α) := Submodule.span ℤ (Set.range word)
def lieLattice : LieSubalgebra ℤ (AQ α) := LieSubalgebra.lieSpan ℤ (AQ α) (Set.range atom)
def rationalLie : LieSubalgebra ℚ (AQ α) := LieSubalgebra.lieSpan ℚ (AQ α) (Set.range atom)

theorem word_integral (w : List α) : word w ∈ lattice := Submodule.subset_span ⟨w,rfl⟩
theorem atom_integral (a : α) : (atom a : AQ α) ∈ lattice := word_integral [a]
theorem one_integral : (1 : AQ α) ∈ lattice := word_integral []

theorem integral_mul {p q : AQ α} (hp : p ∈ lattice) (hq : q ∈ lattice) : p*q ∈ lattice := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    rcases hp with ⟨u,rfl⟩
    induction hq using Submodule.span_induction with
    | mem q hq =>
      rcases hq with ⟨v,rfl⟩
      rw [← word_append]
      exact word_integral _
    | zero => simp
    | add p q _ _ hp hq => simpa only [mul_add] using (lattice.add_mem hp hq)
    | smul r p _ hp => simpa only [mul_smul_comm] using lattice.smul_mem r hp
  | zero => simp
  | add p q _ _ hp hq => simpa only [add_mul] using lattice.add_mem hp hq
  | smul r p _ hp => simpa only [smul_mul_assoc] using lattice.smul_mem r hp

theorem integral_lie {p q : AQ α} (hp : p ∈ lattice) (hq : q ∈ lattice) : ⁅p,q⁆ ∈ lattice :=
  lattice.sub_mem (integral_mul hp hq) (integral_mul hq hp)

theorem integral_coeff {p : AQ α} (hp : p ∈ lattice) (w : FreeMonoid α) :
    ∃ z : ℤ, p.coeff w = (z : ℚ) := by
  classical
  induction hp using Submodule.span_induction with
  | mem p hp =>
    rcases hp with ⟨u,rfl⟩
    by_cases h : FreeMonoid.ofList u = w
    · exact ⟨1,by simp [word,h]⟩
    · exact ⟨0,by simp [word,h]⟩
  | zero => exact ⟨0,by simp⟩
  | add p q _ _ hp hq =>
    obtain ⟨a,ha⟩ := hp
    obtain ⟨b,hb⟩ := hq
    exact ⟨a+b,by simp [ha,hb]⟩
  | smul r p _ hp =>
    obtain ⟨a,ha⟩ := hp
    refine ⟨r*a,?_⟩
    calc
      (r • p).coeff w = r • p.coeff w := MonoidAlgebra.coeff_smul_apply _ _ _
      _ = ((r*a : ℤ) : ℚ) := by rw [ha]; simp [zsmul_eq_mul]

theorem integral_of_coeff {p : AQ α} (hp : ∀ w, ∃ z : ℤ, p.coeff w = (z : ℚ)) : p ∈ lattice := by
  classical
  rw [← MonoidAlgebra.sum_coeff_single p]
  apply Submodule.sum_mem
  intro w hw
  obtain ⟨z,hz⟩ := hp w
  rw [hz]
  convert lattice.smul_mem z (word_integral w.toList) using 1
  simp [word]

def words (P : List α → Prop) : Submodule ℚ (AQ α) :=
  Submodule.span ℚ {p | ∃ w, P w ∧ p=word w}

theorem word_mem {P : List α → Prop} {w : List α} (hw : P w) : word w ∈ words P :=
  Submodule.subset_span ⟨w,hw,rfl⟩

theorem mem_words {P : List α → Prop} {p : AQ α} :
    p ∈ words P ↔ ∀ w, p.coeff w ≠ 0 → P w.toList := by
  classical
  constructor
  · intro hp w hw
    induction hp using Submodule.span_induction with
    | mem p hp =>
      rcases hp with ⟨u,hu,rfl⟩
      have h : FreeMonoid.ofList u = w := by
        by_contra h
        exact hw (by simp [word,h])
      simpa [← h] using hu
    | zero => exact (hw (by simp)).elim
    | add p q _ _ hp hq =>
      by_cases h : p.coeff w = 0
      · exact hq (by simpa [h] using hw)
      · exact hp h
    | smul r p _ hp =>
      exact hp (by intro h; apply hw; simp [h])
  · intro hp
    rw [← MonoidAlgebra.sum_coeff_single p]
    apply Submodule.sum_mem
    intro w hw
    have h : P w.toList := hp w (Finsupp.mem_support_iff.mp hw)
    convert (words P).smul_mem (p.coeff w) (word_mem h) using 1
    simp [word]

theorem words_mono {P Q : List α → Prop} (h : ∀ w, P w → Q w) : words P ≤ words Q := by
  apply Submodule.span_le.mpr
  rintro _ ⟨w,hw,rfl⟩
  exact word_mem (h w hw)

theorem mul_words {P Q T : List α → Prop} {p q : AQ α}
    (h : ∀ u v, P u → Q v → T (u++v)) (hp : p ∈ words P) (hq : q ∈ words Q) : p*q ∈ words T := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    rcases hp with ⟨u,hu,rfl⟩
    induction hq using Submodule.span_induction with
    | mem q hq =>
      rcases hq with ⟨v,hv,rfl⟩
      rw [← word_append]
      exact word_mem (h u v hu hv)
    | zero => simp
    | add p q _ _ hp hq => simpa only [mul_add] using (words T).add_mem hp hq
    | smul r p _ hp => simpa only [mul_smul_comm] using (words T).smul_mem r hp
  | zero => simp
  | add p q _ _ hp hq => simpa only [add_mul] using (words T).add_mem hp hq
  | smul r p _ hp => simpa only [smul_mul_assoc] using (words T).smul_mem r hp

theorem lie_has_preimage {p : AQ α} (hp : p ∈ rationalLie) : ∃ q : FreeLieAlgebra ℚ α, embed q = p := by
  have h : rationalLie (α := α) ≤ (embed : FreeLieAlgebra ℚ α →ₗ⁅ℚ⁆ AQ α).range := by
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨a,rfl⟩
    exact ⟨FreeLieAlgebra.of ℚ a,embed_of a⟩
  exact h hp

theorem embed_mem_lie (p : FreeLieAlgebra ℚ α) : embed p ∈ rationalLie := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg a => rw [embed_of]; exact LieSubalgebra.subset_lieSpan ⟨a,rfl⟩
  | ha p q hp hq => simpa using rationalLie.add_mem hp hq
  | hs r p hp => simpa using rationalLie.smul_mem r hp
  | hl p q hp hq => simpa only [LieHom.map_lie] using rationalLie.lie_mem hp hq

theorem shift_integral {p : AQ (ℕ×α)} (hp : p ∈ lattice) : shift p ∈ lattice := by
  have hword : ∀ w : List (ℕ×α), shift (word w) ∈ lattice := by
    intro w
    induction w with
    | nil => simp
    | cons a w ih =>
      rcases a with ⟨i,a⟩
      rw [word_cons,shift_mul,shift_atom]
      exact lattice.add_mem (integral_mul (atom_integral _) (word_integral _))
        (integral_mul (atom_integral _) ih)
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨w,rfl⟩ := hp; exact hword w
  | zero => simp
  | add p q _ _ hp hq => simpa using lattice.add_mem hp hq
  | smul r p _ hp => simpa only [map_zsmul] using lattice.smul_mem r hp

theorem extract_integral {p : AQ (Option α)} (hp : p ∈ lattice) : extract p ∈ lattice := by
  have hword : ∀ w : List (Option α), ∀ q : AQ (ℕ×α), q ∈ lattice → operator (word w) q ∈ lattice := by
    intro w
    induction w with
    | nil => intro q hq; simpa using hq
    | cons a w ih =>
      intro q hq
      rw [word_cons,map_mul,Module.End.mul_apply]
      cases a with
      | none => simpa [operator] using shift_integral (ih q hq)
      | some a => simpa [operator] using integral_mul (atom_integral (0,a)) (ih q hq)
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨w,rfl⟩ := hp; exact hword w 1 one_integral
  | zero => simp
  | add p q _ _ hp hq => simpa using lattice.add_mem hp hq
  | smul r p _ hp => simpa only [map_zsmul] using lattice.smul_mem r hp

theorem extract_lie {p : AQ (Option α)} (hp : p ∈ rationalLie) : extract p ∈ rationalLie := by
  obtain ⟨q,rfl⟩ := lie_has_preimage hp
  rw [extract_embed]
  exact embed_mem_lie _

def countSome : List (Option α) → ℕ
  | [] => 0
  | none::w => countSome w
  | some _::w => countSome w + 1

theorem countSome_le (w : List (Option α)) : countSome w ≤ w.length := by
  induction w with
  | nil => simp [countSome]
  | cons a w ih => cases a <;> simp [countSome] <;> omega

theorem countSome_lt {w : List (Option α)} (hw : none ∈ w) : countSome w < w.length := by
  induction w with
  | nil => simp at hw
  | cons a w ih =>
    cases a with
    | none => simpa [countSome] using Nat.lt_succ_of_le (countSome_le w)
    | some a =>
      have h := ih (by simpa using hw)
      simp [countSome]
      omega

theorem shift_length {p : AQ (ℕ×α)} {n : ℕ} (hp : p ∈ words (fun w => w.length=n)) :
    shift p ∈ words (fun w => w.length=n) := by
  have hword : ∀ w : List (ℕ×α), shift (word w) ∈ words (fun v => v.length=w.length) := by
    intro w
    induction w with
    | nil => simp
    | cons a w ih =>
      rcases a with ⟨i,a⟩
      rw [word_cons,shift_mul,shift_atom]
      apply (words _).add_mem
      · exact mul_words (fun u v hu hv => by simp [List.length_append,hu,hv,Nat.add_comm])
          (word_mem (P := fun v => v.length=1) (w := [(i+1,a)]) rfl) (word_mem (P := fun v => v.length=w.length) (w := w) rfl)
      · exact mul_words (fun u v hu hv => by simp [List.length_append,hu,hv,Nat.add_comm])
          (word_mem (P := fun v => v.length=1) (w := [(i,a)]) rfl) ih
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨w,hw,rfl⟩ := hp; simpa [hw] using hword w
  | zero => simp
  | add p q _ _ hp hq => simpa using (words _).add_mem hp hq
  | smul r p _ hp => simpa using (words _).smul_mem r hp

theorem operator_length (w : List (Option α)) {q : AQ (ℕ×α)} {n : ℕ}
    (hq : q ∈ words (fun v => v.length=n)) :
    operator (word w) q ∈ words (fun v => v.length=n+countSome w) := by
  induction w with
  | nil => simpa [countSome] using hq
  | cons a w ih =>
    rw [word_cons,map_mul,Module.End.mul_apply]
    cases a with
    | none => simpa [operator,countSome] using shift_length ih
    | some a =>
      have h : atom (0,a) * operator (word w) q ∈ words (fun v => v.length=n+countSome w+1) :=
        mul_words (fun u v (hu : u.length=1) (hv : v.length=n+countSome w) => by
          simp [List.length_append,hu,hv,Nat.add_comm])
          (word_mem (P := fun v => v.length=1) (w := [(0,a)]) rfl) ih
      simpa [operator,countSome, Nat.add_assoc] using h

theorem extract_word_length (w : List (Option α)) :
    extract (word w) ∈ words (fun v => v.length=countSome w) := by
  simpa [extract] using operator_length w (word_mem (w := []) rfl)

def rename (f : α → β) : AQ α →ₐ[ℚ] AQ β := lift (fun a => atom (f a))
@[simp] theorem rename_atom (f : α → β) (a : α) : rename f (atom a) = atom (f a) := by
  simp [rename]

theorem rename_word (f : α → β) (w : List α) : rename f (word w) = word (w.map f) := by
  induction w with
  | nil => simp
  | cons a w ih => simp [word_cons,ih]

theorem rename_integral (f : α → β) {p : AQ α} (hp : p ∈ lattice) : rename f p ∈ lattice := by
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨w,rfl⟩ := hp; rw [rename_word]; exact word_integral _
  | zero => simp
  | add p q _ _ hp hq => simpa using lattice.add_mem hp hq
  | smul r p _ hp => simpa only [map_zsmul] using lattice.smul_mem r hp

theorem rename_lie (f : α → β) {p : AQ α} (hp : p ∈ rationalLie) : rename f p ∈ rationalLie := by
  induction hp using LieSubalgebra.lieSpan_induction ℚ with
  | mem p hp => obtain ⟨a,rfl⟩ := hp; rw [rename_atom]; exact LieSubalgebra.subset_lieSpan ⟨f a,rfl⟩
  | zero => simp
  | add p q _ _ hp hq => simpa using rationalLie.add_mem hp hq
  | smul r p _ hp => simpa using rationalLie.smul_mem r hp
  | lie p q _ _ hp hq => simpa only [Ring.lie_def,map_sub,map_mul] using rationalLie.lie_mem hp hq

theorem rename_lieIntegral (f : α → β) {p : AQ α} (hp : p ∈ lieLattice) : rename f p ∈ lieLattice := by
  induction hp using LieSubalgebra.lieSpan_induction ℤ with
  | mem p hp => obtain ⟨a,rfl⟩ := hp; rw [rename_atom]; exact LieSubalgebra.subset_lieSpan ⟨f a,rfl⟩
  | zero => simp
  | add p q _ _ hp hq => simpa using lieLattice.add_mem hp hq
  | smul r p _ hp => simpa only [map_zsmul] using lieLattice.smul_mem r hp
  | lie p q _ _ hp hq => simpa only [Ring.lie_def,map_sub,map_mul] using lieLattice.lie_mem hp hq

noncomputable def kill (a : α) : AQ α →ₐ[ℚ] AQ α := by
  classical
  exact lift fun b => if a=b then 0 else atom b

theorem kill_atom (a b : α) : kill a (atom b) = if a=b then 0 else atom b := by
  classical
  simp [kill]

theorem kill_word (a : α) (w : List α) : kill a (word w) = if a ∈ w then 0 else word w := by
  classical
  induction w with
  | nil => simp
  | cons b w ih =>
    rw [word_cons,map_mul,kill_atom,ih]
    by_cases h : a=b <;> by_cases h' : a ∈ w <;> simp [h,h']

theorem kill_integral (a : α) {p : AQ α} (hp : p ∈ lattice) : kill a p ∈ lattice := by
  classical
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,rfl⟩ := hp
    rw [kill_word]
    split_ifs <;> simp [word_integral]
  | zero => simp
  | add p q _ _ hp hq => simpa using lattice.add_mem hp hq
  | smul r p _ hp => simpa only [map_zsmul] using lattice.smul_mem r hp

theorem kill_lie (a : α) {p : AQ α} (hp : p ∈ rationalLie) : kill a p ∈ rationalLie := by
  classical
  induction hp using LieSubalgebra.lieSpan_induction ℚ with
  | mem p hp =>
    obtain ⟨b,rfl⟩ := hp
    rw [kill_atom]
    split_ifs
    · exact rationalLie.zero_mem
    · exact LieSubalgebra.subset_lieSpan ⟨b,rfl⟩
  | zero => simp
  | add p q _ _ hp hq => simpa using rationalLie.add_mem hp hq
  | smul r p _ hp => simpa using rationalLie.smul_mem r hp
  | lie p q _ _ hp hq => simpa only [Ring.lie_def,map_sub,map_mul] using rationalLie.lie_mem hp hq

def tag (a b : α) : Option α := if a=b then none else some b

def untag (a : α) : Option α → α
  | none => a
  | some b => b

theorem rename_untag_tag (a : α) (p : AQ α) : rename (untag a) (rename (tag a) p) = p := by
  have h : (rename (untag a)).comp (rename (tag a)) = AlgHom.id ℚ (AQ α) := by
    apply hom_ext
    intro b
    simp only [AlgHom.comp_apply,rename_atom,AlgHom.id_apply]
    congr 1
    dsimp [tag]
    split_ifs with h
    · exact h
    · rfl
  exact AlgHom.congr_fun h p

theorem rename_extract_lower (a : α) {p : AQ α} {n : ℕ}
    (hp : p ∈ words (fun w => w.length≤n+1 ∧ a ∈ w)) :
    extract (rename (tag a) p) ∈ words (fun w => w.length≤n) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,hw,rfl⟩ := hp
    rw [rename_word]
    have hm : none ∈ w.map (tag a) := List.mem_map.mpr ⟨a,hw.2,by simp [tag]⟩
    have hc := countSome_lt hm
    apply words_mono (P := fun v => v.length=countSome (w.map (tag a))) ?_ (extract_word_length _)
    intro v hv
    simp only [List.length_map] at hc
    omega
  | zero => simp
  | add p q _ _ hp hq => simpa using (words _).add_mem hp hq
  | smul r p _ hp => simpa using (words _).smul_mem r hp

theorem kill_bound (a : α) (S : Finset α) (n : ℕ) {p : AQ α}
    (hp : p ∈ words (fun w => w.length≤n ∧ ∀ b ∈ w, b ∈ insert a S)) :
    kill a p ∈ words (fun w => w.length≤n ∧ ∀ b ∈ w, b ∈ S) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,hw,rfl⟩ := hp
    rw [kill_word]
    split_ifs with h
    · exact (words _).zero_mem
    · apply word_mem
      refine ⟨hw.1,?_⟩
      intro b hb
      rcases Finset.mem_insert.mp (hw.2 b hb) with h'|h'
      · exact (h (h' ▸ hb)).elim
      · exact h'
  | zero => simp
  | add p q _ _ hp hq => simpa using (words _).add_mem hp hq
  | smul r p _ hp => simpa using (words _).smul_mem r hp

theorem remainder_bound (a : α) {p : AQ α} {n : ℕ}
    (hp : p ∈ words (fun w => w.length≤n)) :
    p-kill a p ∈ words (fun w => w.length≤n ∧ a ∈ w) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,hw,rfl⟩ := hp
    rw [kill_word]
    split_ifs with h
    · simpa using word_mem (P := fun v => v.length≤n ∧ a ∈ v) ⟨hw,h⟩
    · simp
  | zero => simp
  | add p q _ _ hp hq =>
    rw [map_add]
    convert (words _).add_mem hp hq using 1
    abel
  | smul r p _ hp => simpa only [map_smul,smul_sub] using (words _).smul_mem r hp

theorem lie_positive {p : AQ α} (hp : p ∈ rationalLie) : p ∈ words (fun w => 0<w.length) := by
  induction hp using LieSubalgebra.lieSpan_induction ℚ with
  | mem p hp => obtain ⟨a,rfl⟩ := hp; exact word_mem (w := [a]) (by simp)
  | zero => simp
  | add p q _ _ hp hq => exact (words _).add_mem hp hq
  | smul r p _ hp => exact (words _).smul_mem r hp
  | lie p q _ _ hp hq =>
    apply (words _).sub_mem
    · exact mul_words (fun u v hu hv => by simp only [List.length_append]; omega) hp hq
    · exact mul_words (fun u v hu hv => by simp only [List.length_append]; omega) hq hp

def traceX : AQ (Option α) →ₐ[ℚ] ℚ := lift (fun | none => 1 | some _ => 0)

theorem trace_embed (q : Elimination.G ℚ α) : traceX (embed q) = (Elimination.expand q).right := by
  have h : traceX.toLieHom.comp embed =
      (LieAlgebra.SemiDirectSum.projr Elimination.action).comp (Elimination.expand : Elimination.G ℚ α →ₗ⁅ℚ⁆ Elimination.M ℚ α) := by
    apply FreeLieAlgebra.hom_ext
    intro a
    cases a <;> simp [traceX,Elimination.expand]
  exact LieHom.congr_fun h q

def collapseAssoc : AQ (ℕ×α) →ₐ[ℚ] AQ (Option α) :=
  lift (fun (i,a) => embed (Elimination.adWord i a))

theorem collapse_embed (q : Elimination.F ℚ α) :
    collapseAssoc (embed q) = embed (Elimination.collapseFiber q) := by
  have h : collapseAssoc.toLieHom.comp embed =
      (embed : Elimination.G ℚ α →ₗ⁅ℚ⁆ AQ (Option α)).comp Elimination.collapseFiber := by
    apply FreeLieAlgebra.hom_ext
    intro a
    rcases a with ⟨i,a⟩
    simp [collapseAssoc,Elimination.collapseFiber]
  exact LieHom.congr_fun h q

theorem decompose_lie {p : AQ (Option α)} (hp : p ∈ rationalLie) :
    p = collapseAssoc (extract p) + traceX p • atom none := by
  obtain ⟨q,rfl⟩ := lie_has_preimage hp
  rw [extract_embed,collapse_embed,trace_embed]
  conv_lhs => rw [← Elimination.collapse_expand q]
  change embed (Elimination.collapseFiber (Elimination.expand q).left +
    (Elimination.expand q).right • Elimination.X) = _
  simp [Elimination.X]

theorem trace_integral {p : AQ (Option α)} (hp : p ∈ lattice) : ∃ z : ℤ, traceX p = (z : ℚ) := by
  have hw : ∀ w : List (Option α), ∃ z : ℤ, traceX (word w) = (z : ℚ) := by
    intro w
    induction w with
    | nil => exact ⟨1,by simp⟩
    | cons a w ih =>
      obtain ⟨z,hz⟩ := ih
      rw [word_cons,map_mul,hz]
      cases a with
      | none => exact ⟨z,by simp [traceX]⟩
      | some a => exact ⟨0,by simp [traceX]⟩
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨w,rfl⟩ := hp; exact hw w
  | zero => exact ⟨0,by simp⟩
  | add p q _ _ hp hq =>
    obtain ⟨a,ha⟩ := hp
    obtain ⟨b,hb⟩ := hq
    exact ⟨a+b,by simp [ha,hb]⟩
  | smul r p _ hp =>
    obtain ⟨a,ha⟩ := hp
    refine ⟨r*a,?_⟩
    rw [map_zsmul,ha]
    simp [zsmul_eq_mul]

theorem adWord_integralLie (i : ℕ) (a : α) :
    embed (Elimination.adWord i a) ∈ lieLattice := by
  induction i with
  | zero =>
    simp only [Elimination.adWord,Function.iterate_zero_apply,Elimination.Y,embed_of]
    exact LieSubalgebra.subset_lieSpan ⟨some a,rfl⟩
  | succ i ih =>
    rw [Elimination.adWord_succ,LieHom.map_lie]
    apply lieLattice.lie_mem ?_ ih
    simp only [Elimination.X,embed_of]
    exact LieSubalgebra.subset_lieSpan ⟨none,rfl⟩

theorem collapse_integralLie {p : AQ (ℕ×α)} (hp : p ∈ lieLattice) : collapseAssoc p ∈ lieLattice := by
  induction hp using LieSubalgebra.lieSpan_induction ℤ with
  | mem p hp =>
    obtain ⟨⟨i,a⟩,rfl⟩ := hp
    simpa [collapseAssoc] using adWord_integralLie i a
  | zero => simp
  | add p q _ _ hp hq => simpa using lieLattice.add_mem hp hq
  | smul r p _ hp => simpa only [map_zsmul] using lieLattice.smul_mem r hp
  | lie p q _ _ hp hq => simpa only [Ring.lie_def,map_sub,map_mul] using lieLattice.lie_mem hp hq

theorem words_and {P Q : List α → Prop} {p : AQ α} (hp : p ∈ words P) (hq : p ∈ words Q) :
    p ∈ words (fun w => P w ∧ Q w) := by
  apply mem_words.mpr
  intro w hw
  exact ⟨mem_words.mp hp w hw,mem_words.mp hq w hw⟩

theorem exists_support (p : AQ α) : ∃ S : Finset α, p ∈ words (fun w => ∀ b ∈ w, b ∈ S) := by
  let S := p.coeff.support.biUnion (fun w => w.toList.toFinset)
  refine ⟨S,mem_words.mpr ?_⟩
  intro w hw b hb
  exact Finset.mem_biUnion.mpr ⟨w,Finsupp.mem_support_iff.mpr hw,by simpa using hb⟩

theorem exists_bound (p : AQ α) : ∃ n : ℕ, p ∈ words (fun w => w.length≤n) := by
  refine ⟨p.coeff.support.sup (fun w => w.toList.length),mem_words.mpr ?_⟩
  intro w hw
  exact Finset.le_sup (f := fun w => w.toList.length) (Finsupp.mem_support_iff.mpr hw)

theorem bound_zero_of_lie {p : AQ α} (hl : p ∈ rationalLie)
    (hp : p ∈ words (fun w => w.length≤0)) : p=0 := by
  ext w
  change p.coeff w = 0
  by_contra h
  have h₁ := mem_words.mp (lie_positive hl) w h
  have h₂ := mem_words.mp hp w h
  omega

theorem support_empty_of_lie {p : AQ α} (hl : p ∈ rationalLie)
    (hp : p ∈ words (fun w => ∀ b ∈ w, b ∈ (∅ : Finset α))) : p=0 := by
  ext w
  change p.coeff w = 0
  by_contra h
  have h₁ := mem_words.mp (lie_positive hl) w h
  have h₂ := mem_words.mp hp w h
  cases ht : w.toList with
  | nil => simp [ht] at h₁
  | cons b v =>
    have hb := h₂ b (by simp [ht])
    simp at hb

universe u

theorem saturation_bounded (n : ℕ) : ∀ (α : Type u) (p : AQ α),
    p ∈ rationalLie → p ∈ lattice → p ∈ words (fun w => w.length≤n) → p ∈ lieLattice := by
  induction n with
  | zero =>
    intro α p hl _ hw
    rw [bound_zero_of_lie hl hw]
    exact lieLattice.zero_mem
  | succ n ih =>
    intro α p hl hi hw
    have hs : ∀ S : Finset α, ∀ p : AQ α,
        p ∈ rationalLie → p ∈ lattice →
        p ∈ words (fun w => w.length≤n+1 ∧ ∀ b ∈ w, b ∈ S) → p ∈ lieLattice := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
        intro p hl _ hw
        have hz : p=0 := support_empty_of_lie hl (words_mono (fun _ h => h.2) hw)
        rw [hz]
        exact lieLattice.zero_mem
      | @insert a S ha ihS =>
        intro p hl hi hw
        have hl0 := kill_lie a hl
        have hi0 := kill_integral a hi
        have hp0 := ihS (kill a p) hl0 hi0 (kill_bound a S (n+1) hw)
        have hrl : p-kill a p ∈ rationalLie := rationalLie.sub_mem hl hl0
        have hri : p-kill a p ∈ lattice := lattice.sub_mem hi hi0
        have hrw := remainder_bound a (words_mono (fun _ h => h.1) hw)
        have htl := rename_lie (tag a) hrl
        have hti := rename_integral (tag a) hri
        have he := ih (ℕ×α) (extract (rename (tag a) (p-kill a p)))
          (extract_lie htl) (extract_integral hti) (rename_extract_lower a hrw)
        have ht : rename (tag a) (p-kill a p) ∈ lieLattice := by
          rw [decompose_lie htl]
          apply lieLattice.add_mem (collapse_integralLie he)
          obtain ⟨z,hz⟩ := trace_integral hti
          rw [hz,Int.cast_smul_eq_zsmul]
          exact lieLattice.smul_mem z (LieSubalgebra.subset_lieSpan ⟨none,rfl⟩)
        have hr := rename_lieIntegral (untag a) ht
        rw [rename_untag_tag] at hr
        convert lieLattice.add_mem hr hp0 using 1
        abel
    obtain ⟨S,hS⟩ := exists_support p
    exact hs S p hl hi (words_and hw hS)

theorem saturation {p : AQ α} (hl : p ∈ rationalLie) (hi : p ∈ lattice) : p ∈ lieLattice := by
  obtain ⟨n,hn⟩ := exists_bound p
  exact saturation_bounded n α p hl hi hn

end IntegralWords

namespace UniversalEmbedding
open Classical LieAlgebra AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {R α β : Type*} [CommRing R]
abbrev FL (R α : Type*) [CommRing R] := FreeLieAlgebra R α

inductive Tree (α : Type*)
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α

def Tree.leaves : Tree α → List α
  | .leaf a => [a]
  | .node t u => t.leaves ++ u.leaves

def Tree.eval : Tree α → FL R α
  | .leaf a => FreeLieAlgebra.of R a
  | .node t u => ⁅t.eval,u.eval⁆

def Tree.map (f : α → β) : Tree α → Tree β
  | .leaf a => .leaf (f a)
  | .node t u => .node (t.map f) (u.map f)

@[simp] theorem Tree.leaves_map (f : α → β) (t : Tree α) :
    (t.map f).leaves = t.leaves.map f := by
  induction t <;> simp_all [Tree.map,Tree.leaves]

theorem Tree.positive (t : Tree α) : 0<t.leaves.length := by
  induction t <;> simp_all [Tree.leaves]

def bounded (n : ℕ) (S : Finset α) : Submodule R (FL R α) :=
  Submodule.span R {p | ∃ t : Tree α, t.leaves.length≤n ∧ (∀ a ∈ t.leaves, a∈S) ∧ t.eval=p}
def small (n : ℕ) : Submodule R (FL R α) :=
  Submodule.span R {p | ∃ t : Tree α, t.leaves.length≤n ∧ t.eval=p}

theorem eval_bounded (t : Tree α) {n : ℕ} {S : Finset α}
    (hn : t.leaves.length≤n) (hS : ∀ a ∈ t.leaves, a∈S) :
    (t.eval : FL R α) ∈ bounded n S := Submodule.subset_span ⟨t,hn,hS,rfl⟩
theorem eval_small (t : Tree α) {n : ℕ} (hn : t.leaves.length≤n) :
    (t.eval : FL R α) ∈ small n := Submodule.subset_span ⟨t,hn,rfl⟩

theorem bounded_mono {n m : ℕ} {S T : Finset α} (hn : n ≤ m) (hS : S ⊆ T) :
    (bounded n S : Submodule R (FL R α)) ≤ bounded m T := by
  apply Submodule.span_le.mpr
  rintro p ⟨t,ht,hs,rfl⟩
  exact eval_bounded t (ht.trans hn) (fun a ha => hS (hs a ha))
theorem bounded_small (n : ℕ) (S : Finset α) :
    (bounded n S : Submodule R (FL R α)) ≤ small n := by
  apply Submodule.span_le.mpr
  rintro p ⟨t,ht,_,rfl⟩
  exact eval_small t ht

theorem small_mono {n m : ℕ} (h : n ≤ m) :
    (small n : Submodule R (FL R α)) ≤ small m := by
  apply Submodule.span_le.mpr
  rintro p ⟨t,ht,rfl⟩
  exact eval_small t (ht.trans h)

theorem bracket_small {n m : ℕ} {p q : FL R α} (hp : p∈small n) (hq : q∈small m) :
    ⁅p,q⁆ ∈ small (n+m) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    rcases hp with ⟨t,ht,rfl⟩
    induction hq using Submodule.span_induction with
    | mem q hq =>
      rcases hq with ⟨u,hu,rfl⟩
      exact eval_small (.node t u) (by simpa [Tree.leaves] using Nat.add_le_add ht hu)
    | zero => simp
    | add p q _ _ hp hq => simpa only [lie_add] using (small _).add_mem hp hq
    | smul r p _ hp => simpa only [lie_smul] using (small _).smul_mem r hp
  | zero => simp
  | add p q _ _ hp hq => simpa only [add_lie] using (small _).add_mem hp hq
  | smul r p _ hp => simpa only [smul_lie] using (small _).smul_mem r hp

theorem small_exists_support {p : FL R α} {n : ℕ} (hp : p∈small n) :
    ∃ S : Finset α, p∈bounded n S := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    rcases hp with ⟨t,ht,rfl⟩
    exact ⟨t.leaves.toFinset,eval_bounded t ht (by simp)⟩
  | zero => exact ⟨∅,Submodule.zero_mem _⟩
  | add p q _ _ hp hq =>
    rcases hp with ⟨S,hS⟩
    rcases hq with ⟨T,hT⟩
    exact ⟨S∪T,(bounded _ _).add_mem
      (bounded_mono le_rfl Finset.subset_union_left hS)
      (bounded_mono le_rfl Finset.subset_union_right hT)⟩
  | smul r p _ hp =>
    obtain ⟨S,hS⟩ := hp
    exact ⟨S,(bounded _ _).smul_mem r hS⟩

theorem small_exists (p : FL R α) : ∃ n, p∈small n := by
  induction p using freeLie_induction with
  | h0 => exact ⟨0,Submodule.zero_mem _⟩
  | hg a => exact ⟨1,eval_small (.leaf a) le_rfl⟩
  | ha p q hp hq =>
    obtain ⟨n,hn⟩ := hp
    obtain ⟨m,hm⟩ := hq
    exact ⟨n+m,(small _).add_mem (small_mono (Nat.le_add_right _ _) hn)
      (small_mono (Nat.le_add_left _ _) hm)⟩
  | hs r p hp => obtain ⟨n,hn⟩ := hp; exact ⟨n,(small _).smul_mem r hn⟩
  | hl p q hp hq =>
    obtain ⟨n,hn⟩ := hp
    obtain ⟨m,hm⟩ := hq
    exact ⟨n+m,bracket_small hn hm⟩

theorem small_zero {p : FL R α} (hp : p∈small 0) : p=0 := by
  have h : (small 0 : Submodule R (FL R α)) ≤ ⊥ := by
    apply Submodule.span_le.mpr
    rintro p ⟨t,ht,_⟩
    have := t.positive
    omega
  exact h hp

theorem bounded_empty {p : FL R α} {n : ℕ} (hp : p∈bounded n ∅) : p=0 := by
  have h : (bounded n ∅ : Submodule R (FL R α)) ≤ ⊥ := by
    apply Submodule.span_le.mpr
    rintro p ⟨t,_,ht,_⟩
    obtain ⟨a,ha⟩ := List.exists_mem_of_length_pos t.positive
    exact (Finset.notMem_empty a (ht a ha)).elim
  exact h hp

def rename (f : α → β) : FL R α →ₗ⁅R⁆ FL R β :=
  FreeLieAlgebra.lift R (fun a => FreeLieAlgebra.of R (f a))
def renameAssoc (f : α → β) : A R α →ₐ[R] A R β := lift (fun a => atom (f a))
@[simp] theorem rename_of (f : α → β) (a : α) :
    rename f (FreeLieAlgebra.of R a) = FreeLieAlgebra.of R (f a) := by simp [rename]
@[simp] theorem rename_eval (f : α → β) (t : Tree α) :
    rename f (t.eval : FL R α) = (t.map f).eval := by
  induction t <;> simp_all [Tree.eval,Tree.map,LieHom.map_lie]

theorem rename_embed (f : α → β) (p : FL R α) :
    embed (rename f p) = renameAssoc f (embed p) := by
  have h : (embed : FL R β →ₗ⁅R⁆ A R β).comp (rename f) =
      (renameAssoc f).toLieHom.comp embed := by
    apply FreeLieAlgebra.hom_ext
    intro a
    simp [renameAssoc]
  exact LieHom.congr_fun h p

def kill (a : α) : FL R α →ₗ⁅R⁆ FL R α :=
  FreeLieAlgebra.lift R (fun b => if b=a then 0 else FreeLieAlgebra.of R b)
def killAssoc (a : α) : A R α →ₐ[R] A R α :=
  lift (fun b => if b=a then 0 else atom b)
@[simp] theorem kill_of (a b : α) : kill a (FreeLieAlgebra.of R b) =
    if b=a then 0 else FreeLieAlgebra.of R b := by simp [kill]

theorem kill_embed (a : α) (p : FL R α) : embed (kill a p) = killAssoc a (embed p) := by
  have h : (embed : FL R α →ₗ⁅R⁆ A R α).comp (kill a) = (killAssoc a).toLieHom.comp embed := by
    apply FreeLieAlgebra.hom_ext
    intro b
    simp only [LieHom.comp_apply,kill_of,embed_of,killAssoc,lift_atom,AlgHom.toLieHom_apply]
    split_ifs <;> simp
  exact LieHom.congr_fun h p

theorem kill_eval (a : α) (t : Tree α) :
    kill a (t.eval : FL R α) = if a∈t.leaves then 0 else t.eval := by
  induction t with
  | leaf b => simp [Tree.eval,Tree.leaves,eq_comm]
  | node t u ht hu =>
    simp only [Tree.eval,LieHom.map_lie,ht,hu,Tree.leaves,List.mem_append]
    split_ifs <;> simp_all

theorem kill_bounded (a : α) (S : Finset α) {n : ℕ} {p : FL R α}
    (hp : p∈bounded n (insert a S)) : kill a p∈bounded n S := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    rcases hp with ⟨t,ht,hs,rfl⟩
    rw [kill_eval]
    split_ifs with ha
    · exact (bounded _ _).zero_mem
    · exact eval_bounded t ht (fun b hb => (Finset.mem_insert.mp (hs b hb)).resolve_left
        (fun h => ha (h ▸ hb)))
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using (bounded _ _).add_mem hp hq
  | smul r p _ hp => simpa only [map_smul] using (bounded _ _).smul_mem r hp

def fiber : Elimination.G R α →ₗ[R] Elimination.F R α :=
  { toFun := fun p => (Elimination.expand p).left
    map_add' := by intro p q; simp
    map_smul' := by intro r p; simp }

@[simp] theorem fiber_X : fiber (Elimination.X : Elimination.G R α) = 0 := by
  simp [fiber]
@[simp] theorem fiber_Y (a : α) : fiber (Elimination.Y a : Elimination.G R α) = Elimination.E 0 a := by
  simp [fiber]
theorem fiber_lie (p q : Elimination.G R α) :
    fiber ⁅p,q⁆ = ⁅fiber p,fiber q⁆ + (Elimination.expand p).right • Elimination.shift (fiber q) -
      (Elimination.expand q).right • Elimination.shift (fiber p) := by
  simp [fiber,LieHom.map_lie,Elimination.action]

theorem shift_small {p : Elimination.F R α} {n : ℕ} (hp : p∈small n) :
    Elimination.shift p∈small n := by
  have ht : ∀ t : Tree (ℕ×α), Elimination.shift (t.eval : Elimination.F R α)∈small t.leaves.length := by
    intro t
    induction t with
    | leaf a =>
      rcases a with ⟨i,a⟩
      simpa [Tree.eval,Tree.leaves,Elimination.shift,Elimination.E] using
        eval_small (R := R) (.leaf (i+1,a)) le_rfl
    | node t u ht hu =>
      simp only [Tree.eval,Tree.leaves,List.length_append,LieDerivation.apply_lie_eq_add]
      exact (small _).add_mem (bracket_small (eval_small t le_rfl) hu)
        (bracket_small ht (eval_small u le_rfl))
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨t,hn,rfl⟩ := hp; exact small_mono hn (ht t)
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using (small _).add_mem hp hq
  | smul r p _ hp => simpa only [map_smul] using (small _).smul_mem r hp

theorem countSome_append (u v : List (Option α)) :
    IntegralWords.countSome (u++v) = IntegralWords.countSome u+IntegralWords.countSome v := by
  induction u with
  | nil => simp [IntegralWords.countSome]
  | cons a u ih =>
    cases a <;> simp only [List.cons_append,IntegralWords.countSome,ih]
    omega

theorem fiber_eval (t : Tree (Option α)) :
    fiber (t.eval : Elimination.G R α)∈small (IntegralWords.countSome t.leaves) := by
  induction t with
  | leaf a =>
    cases a with
    | none =>
      change fiber (Elimination.X : Elimination.G R α)∈small 0
      simp
    | some a =>
      change fiber (Elimination.Y a : Elimination.G R α)∈small 1
      rw [fiber_Y]
      exact eval_small (.leaf (0,a)) le_rfl
  | node t u ht hu =>
    rw [Tree.eval,fiber_lie,Tree.leaves,countSome_append]
    exact (small _).sub_mem
      ((small _).add_mem (bracket_small ht hu)
        ((small _).smul_mem _ (small_mono (Nat.le_add_left _ _) (shift_small hu))))
      ((small _).smul_mem _ (small_mono (Nat.le_add_right _ _) (shift_small ht)))

theorem fiber_remainder (a : α) {p : FL R α} {n : ℕ} (hp : p∈small (n+1)) :
    fiber (rename (IntegralWords.tag a) (p-kill a p))∈small n := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨t,ht,rfl⟩ := hp
    rw [kill_eval]
    split_ifs with ha
    · rw [sub_zero,rename_eval]
      apply small_mono _ (fiber_eval (R := R) (t.map (IntegralWords.tag a)))
      have hnone : none∈(t.map (IntegralWords.tag a)).leaves := by
        rw [Tree.leaves_map]
        exact List.mem_map.mpr ⟨a,ha,by simp [IntegralWords.tag]⟩
      have hlt := IntegralWords.countSome_lt hnone
      simp only [Tree.leaves_map,List.length_map] at hlt ⊢
      omega
    · simp
  | zero => simp
  | add p q _ _ hp hq =>
    have h : p+q-kill a (p+q) = (p-kill a p)+(q-kill a q) := by rw [map_add]; abel
    rw [h,map_add,map_add]
    exact (small _).add_mem hp hq
  | smul r p _ hp =>
    simpa only [map_smul,← smul_sub] using (small _).smul_mem r hp

def traceAssoc : A R (Option α) →ₐ[R] R := lift (fun | none => 1 | some _ => 0)
theorem trace_embed (p : Elimination.G R α) :
    traceAssoc (embed p) = (Elimination.expand p).right := by
  have h : (traceAssoc : A R (Option α) →ₐ[R] R).toLieHom.comp embed =
      (SemiDirectSum.projr Elimination.action).comp Elimination.expand := by
    apply FreeLieAlgebra.hom_ext
    intro a
    cases a <;> simp [traceAssoc,Elimination.expand]
  exact LieHom.congr_fun h p

theorem untag_tag (a : α) (p : FL R α) :
    rename (IntegralWords.untag a) (rename (IntegralWords.tag a) p) = p := by
  have h : (rename (IntegralWords.untag a) : FL R (Option α) →ₗ⁅R⁆ FL R α).comp
      (rename (IntegralWords.tag a)) = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro b
    simp [IntegralWords.tag,IntegralWords.untag]
    split_ifs <;> simp_all
  exact LieHom.congr_fun h p

universe u v

theorem kernel_bounded (R : Type v) [CommRing R] (n : ℕ) :
    ∀ (α : Type u) (p : FL R α), p∈small n → embed p=0 → p=0 := by
  induction n with
  | zero => intro α p hp _; exact small_zero hp
  | succ n ih =>
    intro α p hp hzero
    have hs : ∀ S : Finset α, ∀ p : FL R α, p∈bounded (n+1) S → embed p=0 → p=0 := by
      intro S
      induction S using Finset.induction_on with
      | empty => intro p hp _; exact bounded_empty hp
      | @insert a S ha ihS =>
        intro p hp hz
        have hk : kill a p=0 := ihS (kill a p) (kill_bounded a S hp) (by rw [kill_embed,hz,map_zero])
        have ht : embed (rename (IntegralWords.tag a) p)=0 := by rw [rename_embed,hz,map_zero]
        have hf : fiber (rename (IntegralWords.tag a) p)=0 := by
          apply ih (ℕ×α) _
          · simpa only [hk,sub_zero] using fiber_remainder a (bounded_small _ _ hp)
          · change embed (Elimination.expand (rename (IntegralWords.tag a) p)).left=0
            rw [← extract_embed,ht,map_zero]
        have hr : (Elimination.expand (rename (IntegralWords.tag a) p)).right=0 := by
          rw [← trace_embed,ht,map_zero]
        have he : Elimination.expand (rename (IntegralWords.tag a) p)=0 := by
          apply SemiDirectSum.ext
          · exact hf
          · exact hr
        have hz' : rename (IntegralWords.tag a) p=0 := by
          rw [← Elimination.collapse_expand (rename (IntegralWords.tag a) p),he,map_zero]
        rw [← untag_tag a p,hz',map_zero]
    obtain ⟨S,hS⟩ := small_exists_support hp
    exact hs S p hS hzero

theorem injective : Function.Injective (embed : FL R α →ₗ⁅R⁆ A R α) := by
  intro p q h
  obtain ⟨n,hn⟩ := small_exists (p-q)
  have h0 : embed (p-q)=0 := by rw [map_sub,h,sub_self]
  exact sub_eq_zero.mp (kernel_bounded R n α (p-q) hn h0)

end UniversalEmbedding

namespace QuadraticAlphabet
open AssociativeElimination LieAlgebra
attribute [local instance] LieRing.ofAssociativeRing
abbrev F := ZMod 2
inductive Letter | a | c | b deriving DecidableEq
instance (α : Type*) : CharP (A F α) 2 :=
  charP_of_injective_ringHom (algebraMap F (A F α)).injective 2
abbrev S := A F Letter
abbrev T := A F (Option Unit)
def a : S := atom Letter.a
def c : S := atom Letter.c
def b : S := atom Letter.b
def x : T := atom none
def y : T := atom (some ())

def delta : S →ₗ[F] S := deriv (fun | .a => 0 | .c => ⁅a,b⁆ | .b => c)
@[simp] theorem delta_a : delta a=0 := by simp [delta,a]
@[simp] theorem delta_b : delta b=c := by simp [delta,b]
@[simp] theorem delta_c : delta c=⁅a,b⁆ := by simp [delta,c]
@[simp] theorem delta_one : delta 1=0 := deriv_one _
theorem delta_mul (p q : S) : delta (p*q)=delta p*q+p*delta q := deriv_mul _ _ _
theorem delta_lie (p q : S) : delta ⁅p,q⁆=⁅delta p,q⁆+⁅p,delta q⁆ := deriv_lie _ _ _

theorem algebra_induction {R α : Type*} [CommRing R] {P : A R α → Prop}
    (p : A R α) (h1 : P 1) (ha : ∀ a, P (atom a))
    (hadd : ∀ p q, P p → P q → P (p+q))
    (hs : ∀ (r : R) p, P p → P (r • p))
    (hm : ∀ p q, P p → P q → P (p*q)) : P p := by
  apply MonoidAlgebra.induction_on p ?_ hadd hs
  intro w
  change P (MonoidAlgebra.single w 1)
  have hh : ∀ v : List α, P (MonoidAlgebra.single (FreeMonoid.ofList v) 1) := by
    intro v
    induction v with
    | nil => exact h1
    | cons a v ih =>
      convert hm (atom a) (MonoidAlgebra.single (FreeMonoid.ofList v) 1) (ha a) ih using 1
      simp only [atom,MonoidAlgebra.single_mul_single,one_mul,FreeMonoid.ofList_cons]
  simpa using hh w.toList

theorem delta_square_mul (p q : S) :
    delta (delta (p*q))=delta (delta p)*q+p*delta (delta q) := by
  rw [delta_mul,map_add,delta_mul,delta_mul]
  calc
    _ = delta (delta p)*q+p*delta (delta q)+(delta p*delta q+delta p*delta q) := by abel
    _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]

theorem delta_square (p : S) : delta (delta p)=⁅a,p⁆ := by
  induction p using algebra_induction with
  | h1 => simp [Ring.lie_def]
  | ha l =>
    cases l with
    | a => change delta (delta a)=⁅a,a⁆; simp
    | c => change delta (delta c)=⁅a,c⁆; simp [delta_lie]
    | b => change delta (delta b)=⁅a,b⁆; simp
  | hadd p q hp hq => simp [hp,hq,lie_add]
  | hs r p hp => simp [hp]
  | hm p q hp hq => rw [delta_square_mul,hp,hq]; simp [Ring.lie_def]; noncomm_ring

def left : S →ₐ[F] Module.End F (S×S) where
  toFun p :=
    { toFun := fun z => (p*z.1,p*z.2)
      map_add' := by intro z w; ext <;> simp [mul_add]
      map_smul' := by intro r z; ext <;> simp }
  map_one' := by ext z <;> simp
  map_mul' := by intro p q; ext z <;> simp [mul_assoc]
  map_zero' := by ext z <;> simp
  map_add' := by intro p q; ext z <;> simp [add_mul]
  commutes' := by intro r; ext z <;> simp [Algebra.algebraMap_eq_smul_one]

@[simp] theorem left_apply (p : S) (z : S×S) : left p z=(p*z.1,p*z.2) := rfl

def root : Module.End F (S×S) where
  toFun z := (delta z.1+z.2*a,z.1+delta z.2)
  map_add' := by intro z w; apply Prod.ext <;> simp only [Prod.fst_add,Prod.snd_add,map_add,add_mul] <;> abel
  map_smul' := by intro r z; ext <;> simp [smul_add]
@[simp] theorem root_apply (z : S×S) : root z=(delta z.1+z.2*a,z.1+delta z.2) := rfl

theorem root_comm (p : S) : ⁅root,left p⁆=left (delta p) := by
  apply LinearMap.ext
  intro z
  apply Prod.ext <;> simp [Ring.lie_def,delta_mul,Module.End.mul_apply,mul_add,mul_assoc]

theorem root_square : root*root=left a := by
  apply LinearMap.ext
  intro z
  apply Prod.ext <;> simp only [Module.End.mul_apply,root_apply,left_apply,
    map_add,delta_mul,delta_square,delta_a,mul_zero,add_zero,Ring.lie_def,add_mul]
  · calc
      _ = a*z.1+(delta z.2*a+delta z.2*a) := by abel
      _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]
  · calc
      _ = a*z.2+(delta z.1+delta z.1) := by abel
      _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]

def substitution : S →ₐ[F] T := lift (fun | .a => x*x | .c => ⁅x,y⁆ | .b => y)
@[simp] theorem substitution_a : substitution a=x*x := by simp [substitution,a]
@[simp] theorem substitution_c : substitution c=⁅x,y⁆ := by simp [substitution,c]
@[simp] theorem substitution_b : substitution b=y := by simp [substitution,b]

def representation : T →ₐ[F] Module.End F (S×S) :=
  lift (fun | none => root | some _ => left b)
@[simp] theorem representation_x : representation x=root := by simp [representation,x]
@[simp] theorem representation_y : representation y=left b := by simp [representation,y]

theorem representation_substitution : representation.comp substitution=left := by
  apply hom_ext
  intro l
  cases l with
  | a => change representation (substitution a)=left a; simp [root_square]
  | c =>
    change representation (substitution c)=left c
    rw [substitution_c]
    change representation (x*y-y*x)=left c
    rw [map_sub,map_mul,map_mul,representation_x,representation_y]
    change ⁅root,left b⁆=left c
    rw [root_comm,delta_b]
  | b => change representation (substitution b)=left b; simp

theorem left_injective : Function.Injective left := by
  intro p q h
  have hh := congrArg (fun f : Module.End F (S×S) => (f (1,0)).1) h
  simpa using hh

theorem substitution_injective : Function.Injective substitution := by
  intro p q h
  apply left_injective
  rw [← representation_substitution]
  exact congrArg representation h

theorem ad_square (u v : T) : ⁅u,⁅u,v⁆⁆=⁅u*u,v⁆ := by
  simp only [Ring.lie_def,sub_eq_add_neg,CharTwo.neg_eq,mul_add,add_mul,mul_assoc]
  calc
    _ = u*(u*v)+v*(u*u)+(u*(v*u)+u*(v*u)) := by abel
    _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]

abbrev LABC := FreeLieAlgebra F Letter
def la : LABC := FreeLieAlgebra.of F Letter.a
def lc : LABC := FreeLieAlgebra.of F Letter.c
def lb : LABC := FreeLieAlgebra.of F Letter.b
def under : LABC →ₗ⁅F⁆ T := substitution.toLieHom.comp embed
@[simp] theorem under_a : under la=x*x := by simp [under,la,substitution]
@[simp] theorem under_c : under lc=⁅x,y⁆ := by simp [under,lc,substitution]
@[simp] theorem under_b : under lb=y := by simp [under,lb,substitution]

def lieDelta : LieDerivation F LABC LABC :=
  FreeDerivations.extend (fun | .a => 0 | .c => ⁅la,lb⁆ | .b => lc)
@[simp] theorem lieDelta_a : lieDelta la=0 := by simp [lieDelta,la]
@[simp] theorem lieDelta_c : lieDelta lc=⁅la,lb⁆ := by simp [lieDelta,lc]
@[simp] theorem lieDelta_b : lieDelta lb=lc := by simp [lieDelta,lb]

theorem under_delta (p : LABC) : under (lieDelta p)=⁅x,under p⁆ := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg l =>
    cases l with
    | a => change under (lieDelta la)=⁅x,under la⁆; simp [Ring.lie_def,mul_assoc]
    | c => change under (lieDelta lc)=⁅x,under lc⁆; simp [LieHom.map_lie,ad_square]
    | b => change under (lieDelta lb)=⁅x,under lb⁆; simp
  | ha p q hp hq => simp [hp,hq,lie_add]
  | hs r p hp => simp [hp]
  | hl p q hp hq =>
    simp only [LieDerivation.apply_lie_eq_add,map_add,LieHom.map_lie,hp,hq]
    simpa only [add_comm] using (leibniz_lie x (under p) (under q)).symm

def iter (i : ℕ) : LABC := lieDelta^[i] lb
@[simp] theorem iter_zero : iter 0=lb := rfl
@[simp] theorem iter_succ (i : ℕ) : iter (i+1)=lieDelta (iter i) :=
  Function.iterate_succ_apply' _ _ _

theorem under_iter (i : ℕ) : under (iter i)=embed (Elimination.adWord i () : Elimination.G F Unit) := by
  induction i with
  | zero => simp [Elimination.Y,y]
  | succ i ih =>
    rw [iter_succ,under_delta,ih,Elimination.adWord_succ,LieHom.map_lie]
    simp [Elimination.X,x]

def fiberLift : Elimination.F F Unit →ₗ⁅F⁆ LABC :=
  FreeLieAlgebra.lift F (fun (i,_) => iter i)
theorem under_fiberLift (p : Elimination.F F Unit) :
    under (fiberLift p)=embed (Elimination.collapseFiber p) := by
  have h : under.comp fiberLift = (embed : Elimination.G F Unit →ₗ⁅F⁆ T).comp Elimination.collapseFiber := by
    apply FreeLieAlgebra.hom_ext
    rintro ⟨i,u⟩
    cases u
    simp [fiberLift,Elimination.collapseFiber,under_iter]
  exact LieHom.congr_fun h p

def polynomial (p : Elimination.G F Unit) : LABC := fiberLift (Elimination.expand p).left

theorem decompose (p : Elimination.G F Unit) :
    embed p=under (polynomial p)+(Elimination.expand p).right • x := by
  rw [polynomial,under_fiberLift]
  have hx : embed (Elimination.X : Elimination.G F Unit)=x := by simp [Elimination.X,x]
  rw [← hx,← map_smul,← map_add]
  conv_lhs => rw [← Elimination.collapse_expand p]
  rfl

theorem under_injective : Function.Injective under := by
  intro p q h
  exact UniversalEmbedding.injective (substitution_injective h)

theorem represent_unique (p : Elimination.G F Unit)
    (hp : (Elimination.expand p).right=0) : ∃! q : LABC, under q=embed p := by
  refine ⟨polynomial p,?_,?_⟩
  · simpa only [hp,zero_smul,add_zero] using (decompose p).symm
  · intro q hq
    apply under_injective
    rw [hq,decompose,hp,zero_smul,add_zero]

def homogeneous (n : ℕ) : Submodule F (Elimination.G F Unit) :=
  Submodule.span F {p | ∃ t : UniversalEmbedding.Tree (Option Unit), t.leaves.length=n ∧ t.eval=p}

theorem homogeneous_trace_zero {p : Elimination.G F Unit} {n : ℕ}
    (hn : 1<n) (hp : p∈homogeneous n) : (Elimination.expand p).right=0 := by
  have hm : ∀ t : UniversalEmbedding.Tree (Option Unit), 1<t.leaves.length →
      (Elimination.expand (t.eval : Elimination.G F Unit)).right=0 := by
    intro t ht
    cases t with
    | leaf l => simp [UniversalEmbedding.Tree.leaves] at ht
    | node t u =>
      simp [UniversalEmbedding.Tree.eval,LieHom.map_lie,Ring.lie_def,mul_comm]
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨t,ht,rfl⟩ := hp; exact hm t (ht ▸ hn)
  | zero => simp
  | add p q _ _ hp hq => simp [hp,hq]
  | smul r p _ hp => simp [hp]

theorem homogeneous_representation {p : Elimination.G F Unit} {n : ℕ}
    (hn : 1<n) (hp : p∈homogeneous n) : ∃! q : LABC, under q=embed p :=
  represent_unique p (homogeneous_trace_zero hn hp)

end QuadraticAlphabet

namespace AssociativeDerivations
open LieAlgebra AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R]
local notation "FL" => FreeLieAlgebra R α

def extend (d : LieDerivation R FL FL) : Module.End R (A R α) :=
  deriv (fun a => embed (d (FreeLieAlgebra.of R a)))
@[simp] theorem extend_atom (d : LieDerivation R FL FL) (a : α) :
    extend d (atom a) = embed (d (FreeLieAlgebra.of R a)) := by simp [extend]
@[simp] theorem extend_one (d : LieDerivation R FL FL) :
    extend d 1=0 := deriv_one _
theorem extend_mul (d : LieDerivation R FL FL) (p q : A R α) :
    extend d (p*q)=extend d p*q+p*extend d q := deriv_mul _ p q

theorem extend_embed (d : LieDerivation R FL FL) (p : FL) :
    extend d (embed p)=embed (d p) := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg a => simp
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [hp]
  | hl p q hp hq =>
    simp only [LieHom.map_lie,extend,deriv_lie] at *
    rw [hp,hq,LieDerivation.apply_lie_eq_add,map_add,LieHom.map_lie,LieHom.map_lie]
    exact add_comm _ _

theorem linear_ext {f g : Module.End R (A R α)}
    (h1 : f 1=g 1) (ha : ∀ a, f (atom a)=g (atom a))
    (hf : ∀ p q, f (p*q)=f p*q+p*f q)
    (hg : ∀ p q, g (p*q)=g p*q+p*g q) : f=g := by
  apply LinearMap.ext
  intro p
  induction p using QuadraticAlphabet.algebra_induction with
  | h1 => exact h1
  | ha a => exact ha a
  | hadd p q hp hq => simp [hp,hq]
  | hs r p hp => simp [hp]
  | hm p q hp hq => rw [hf,hg,hp,hq]

theorem comm_mul (f g : Module.End R (A R α))
    (hf : ∀ p q, f (p*q)=f p*q+p*f q)
    (hg : ∀ p q, g (p*q)=g p*q+p*g q) (p q : A R α) :
    ⁅f,g⁆ (p*q)=⁅f,g⁆ p*q+p*⁅f,g⁆ q := by
  change f (g (p*q))-g (f (p*q))=(f (g p)-g (f p))*q+p*(f (g q)-g (f q))
  rw [hf,hg,map_add,map_add,hf,hf,hg,hg]
  noncomm_ring

def hom : LieDerivation R FL FL →ₗ⁅R⁆ Module.End R (A R α) where
  toFun := extend
  map_add' d e := by
    apply linear_ext
    · simp
    · intro a; simp [LieDerivation.add_apply]
    · exact extend_mul _
    · intro p q; simp only [LinearMap.add_apply,extend_mul]; noncomm_ring
  map_smul' r d := by
    apply linear_ext
    · simp
    · intro a; simp
    · exact extend_mul _
    · intro p q; simp [extend_mul,smul_add]
  map_lie' {d e} := by
    apply linear_ext
    · change extend ⁅d,e⁆ 1=extend d (extend e 1)-extend e (extend d 1)
      simp
    · intro a
      change extend ⁅d,e⁆ (atom a)=extend d (extend e (atom a))-extend e (extend d (atom a))
      simp [extend_embed]
    · exact extend_mul _
    · exact comm_mul _ _ (extend_mul d) (extend_mul e)

@[simp] theorem hom_apply (d : LieDerivation R FL FL) (p : A R α) :
    hom d p=extend d p := rfl

theorem comm_left (d : LieDerivation R FL FL) (p : A R α) :
    ⁅hom d,leftMul p⁆=leftMul (extend d p) := by
  apply LinearMap.ext
  intro q
  change extend d (p*q)-p*extend d q=extend d p*q
  rw [extend_mul,add_sub_cancel_right]
end AssociativeDerivations

namespace EnvelopingTools
open LieAlgebra
attribute [local instance] LieRing.ofAssociativeRing
variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

theorem induction (q : UniversalEnvelopingAlgebra R L)
    {P : UniversalEnvelopingAlgebra R L → Prop}
    (hs : ∀ r, P (algebraMap R _ r))
    (hi : ∀ l, P (UniversalEnvelopingAlgebra.ι R l))
    (ha : ∀ a b, P a → P b → P (a+b))
    (hm : ∀ a b, P a → P b → P (a*b)) : P q := by
  let K : Subalgebra R (UniversalEnvelopingAlgebra R L) :=
    { carrier := {a | P a}
      algebraMap_mem' := hs
      add_mem' := fun ha' hb' => ha _ _ ha' hb'
      mul_mem' := fun ha' hb' => hm _ _ ha' hb' }
  let i : L →ₗ⁅R⁆ K :=
    { (UniversalEnvelopingAlgebra.ι R).toLinearMap.codRestrict K.toSubmodule hi with
      map_lie' := by intro a b; apply Subtype.ext; exact LieHom.map_lie _ a b }
  let f := UniversalEnvelopingAlgebra.lift R i
  have h : K.val.comp f=AlgHom.id R (UniversalEnvelopingAlgebra R L) := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro l
    change (f (UniversalEnvelopingAlgebra.ι R l) : UniversalEnvelopingAlgebra R L)=
      UniversalEnvelopingAlgebra.ι R l
    rw [UniversalEnvelopingAlgebra.lift_ι_apply]
    rfl
  have hq := (f q).property
  change P ((K.val.comp f) q) at hq
  simpa only [h,AlgHom.id_apply] using hq
end EnvelopingTools

namespace FiberPBW
open AssociativeElimination LieAlgebra
open scoped TensorProduct
attribute [local instance] LieRing.ofAssociativeRing
variable {R α G : Type*} [CommRing R] [LieRing G] [LieAlgebra R G]
local notation "F" => FreeLieAlgebra R α
local notation "B" => UniversalEnvelopingAlgebra R G
variable (act : G →ₗ⁅R⁆ LieDerivation R (FreeLieAlgebra R α) (FreeLieAlgebra R α))
abbrev M := SemiDirectSum (R:=R) F G act
local notation "V" => A R α ⊗[R] B

def onLeft (f : Module.End R (A R α)) : Module.End R V :=
  f.rTensor B

def onRight (f : Module.End R B) : Module.End R V :=
  f.lTensor (A R α)

@[simp] theorem onLeft_tmul (f : Module.End R (A R α)) (p : A R α) (b : B) :
    onLeft f (p⊗ₜ b)=f p⊗ₜ b := rfl
@[simp] theorem onRight_tmul (f : Module.End R B) (p : A R α) (b : B) :
    onRight f (p⊗ₜ b)=p⊗ₜ f b := rfl

theorem commute_tensor (f : Module.End R (A R α)) (g : Module.End R B) :
    ⁅onLeft (G:=G) f,onRight (α:=α) g⁆=0 := by
  apply TensorProduct.ext'
  intro p b
  simp

def fiber : F →ₗ⁅R⁆ Module.End R V :=
  (Module.End.rTensorAlgHom R (A R α) B).toLieHom.comp (leftMul.toLieHom.comp embed)

def action : G →ₗ⁅R⁆ Module.End R V :=
  (Module.End.rTensorAlgHom R (A R α) B).toLieHom.comp (AssociativeDerivations.hom.comp act)

def baseLeft : B →ₐ[R] Module.End R B := Algebra.lsmul R R B

def constant : G →ₗ⁅R⁆ Module.End R V :=
  (Module.End.lTensorAlgHom R B (A R α)).toLieHom.comp
    (baseLeft.toLieHom.comp (UniversalEnvelopingAlgebra.ι R))

def base : G →ₗ⁅R⁆ Module.End R V where
  toFun g := action act g+constant g
  map_add' g h := by simp only [map_add]; abel
  map_smul' r g := by simp only [map_smul,smul_add,RingHom.id_apply]
  map_lie' {g h} := by
    have h1 : ⁅action act g,constant h⁆=0 := commute_tensor _ _
    have h2 : ⁅action act h,constant g⁆=0 := commute_tensor _ _
    change action act ⁅g,h⁆+constant ⁅g,h⁆= _
    rw [LieHom.map_lie,LieHom.map_lie]
    change (action act g*action act h-action act h*action act g)+
      (constant g*constant h-constant h*constant g)=
      (action act g+constant g)*(action act h+constant h)-
      (action act h+constant h)*(action act g+constant g)
    change action act g*constant h-constant h*action act g=0 at h1
    change action act h*constant g-constant g*action act h=0 at h2
    have h1' : action act g*constant h=constant h*action act g := by
      exact (sub_eq_zero (a:=action act g*constant h) (b:=constant h*action act g)).mp h1
    have h2' : action act h*constant g=constant g*action act h := by
      exact (sub_eq_zero (a:=action act h*constant g) (b:=constant g*action act h)).mp h2
    simp only [add_mul,mul_add]
    rw [h1',h2']
    abel

@[simp] theorem fiber_tmul (p : F) (q : A R α) (b : B) :
    fiber p (q⊗ₜ b)=(embed p*q)⊗ₜ b := rfl
@[simp] theorem base_tmul (g : G) (q : A R α) (b : B) :
    base act g (q⊗ₜ b)=AssociativeDerivations.extend (act g) q⊗ₜ b+
      q⊗ₜ (UniversalEnvelopingAlgebra.ι R g*b) := rfl

theorem compatibility (g : G) (p : F) :
    fiber (G:=G) (act g p)=⁅base act g,fiber (G:=G) p⁆ := by
  apply TensorProduct.ext'
  intro q b
  change fiber (act g p) (q⊗ₜ b)=
    base act g (fiber p (q⊗ₜ b))-fiber p (base act g (q⊗ₜ b))
  simp only [base_tmul,fiber_tmul,map_add,AssociativeDerivations.extend_mul,
    AssociativeDerivations.extend_embed,TensorProduct.add_tmul]
  abel

def representation : M act →ₗ⁅R⁆ Module.End R V :=
  InnerSemiDirect.lift act fiber (base act) (compatibility act)

def operators : UniversalEnvelopingAlgebra R (M act) →ₐ[R] Module.End R V :=
  UniversalEnvelopingAlgebra.lift R (representation act)

def fiberIn : A R α →ₐ[R] UniversalEnvelopingAlgebra R (M act) :=
  lift (fun a => UniversalEnvelopingAlgebra.ι R (SemiDirectSum.inl act (FreeLieAlgebra.of R a)))
def baseIn : B →ₐ[R] UniversalEnvelopingAlgebra R (M act) :=
  UniversalEnvelopingAlgebra.lift R ((UniversalEnvelopingAlgebra.ι R).comp (SemiDirectSum.inr act))

theorem operators_fiber : (operators act).comp (fiberIn act)=
    (Module.End.rTensorAlgHom R (A R α) B).comp leftMul := by
  apply AssociativeElimination.hom_ext (R:=R) (α:=α)
  intro a
  simp only [AlgHom.comp_apply,fiberIn,lift_atom,operators,UniversalEnvelopingAlgebra.lift_ι_apply,
    representation,InnerSemiDirect.lift_inl,fiber,LieHom.comp_apply,embed_of]
  rfl

theorem operators_base_one (p : B) (b : B) :
    operators act (baseIn act p) ((1 : A R α)⊗ₜ b)=1⊗ₜ (p*b) := by
  induction p using EnvelopingTools.induction generalizing b with
  | hs r => simp [Algebra.algebraMap_eq_smul_one]
  | hi g =>
    simp only [baseIn,UniversalEnvelopingAlgebra.lift_ι_apply,LieHom.comp_apply,
      operators,representation,InnerSemiDirect.lift_inr,base_tmul,
      AssociativeDerivations.extend_one,TensorProduct.zero_tmul,zero_add]
  | ha p q hp hq => simp [hp,hq,add_mul,TensorProduct.tmul_add]
  | hm p q hp hq =>
    simp only [map_mul,Module.End.mul_apply]
    rw [hq,hp,mul_assoc]

def normal : V →ₗ[R] UniversalEnvelopingAlgebra R (M act) :=
  TensorProduct.lift
    { toFun := fun p =>
        { toFun := fun b => fiberIn act p*baseIn act b
          map_add' := by intro b c; simp [mul_add]
          map_smul' := by intro r b; simp }
      map_add' := by intro p q; ext b; simp [add_mul]
      map_smul' := by intro r p; ext b; simp }
@[simp] theorem normal_tmul (p : A R α) (b : B) :
    normal act (p⊗ₜ b)=fiberIn act p*baseIn act b := rfl

def extract : UniversalEnvelopingAlgebra R (M act) →ₗ[R] V :=
  (LinearMap.applyₗ ((1 : A R α)⊗ₜ (1 : B))).comp (operators act).toLinearMap

theorem extract_normal (z : V) : extract act (normal act z)=z := by
  have h : (extract act).comp (normal act)=LinearMap.id := by
    apply TensorProduct.ext'
    intro p b
    change operators act (fiberIn act p*baseIn act b) (1⊗ₜ (1 : B))=p⊗ₜ b
    rw [map_mul,Module.End.mul_apply,operators_base_one,mul_one]
    have hh := AlgHom.congr_fun (operators_fiber act) p
    change operators act (fiberIn act p) (1⊗ₜ b)=p⊗ₜ b
    simp only [AlgHom.comp_apply] at hh
    rw [hh]
    change (p*1)⊗ₜ b=p⊗ₜ b
    rw [mul_one]
  exact LinearMap.congr_fun h z

theorem normal_injective : Function.Injective (normal act) :=
  Function.LeftInverse.injective (extract_normal act)

end FiberPBW

namespace GenericBraid
open LieAlgebra FreeDerivations
variable {R α : Type*} [CommRing R]
abbrev Free (R α : Type*) [CommRing R] := FreeLieAlgebra R (α×α)
def gen (i j : α) : Free R α := FreeLieAlgebra.of R (i,j)
def relations : Set (Free R α) := {q |
  (∃ i, q=gen (R:=R) i i) ∨ (∃ i j, q=gen (R:=R) i j-gen (R:=R) j i) ∨
  (∃ i j k l, i≠k ∧ i≠l ∧ j≠k ∧ j≠l ∧ q=⁅gen (R:=R) i j,gen (R:=R) k l⁆) ∨
  (∃ i j k, i≠j ∧ i≠k ∧ j≠k ∧ q=⁅gen (R:=R) i j,gen (R:=R) i k+gen (R:=R) j k⁆)}
def ideal : LieIdeal R (Free R α) := LieSubmodule.lieSpan R _ relations
abbrev T (R α : Type*) [CommRing R] := Free R α ⧸ (ideal (R:=R) (α:=α))
def t (i j : α) : T R α := (ideal (R:=R) (α:=α)).mkQ (gen i j)

theorem relation_zero {q : Free R α} (h : q∈relations) :
    (ideal (R:=R) (α:=α)).mkQ q=0 := by
  exact (LieSubmodule.Quotient.mk_eq_zero _).mpr (LieSubmodule.subset_lieSpan h)
@[simp] theorem t_self (i : α) : t (R:=R) i i=0 :=
  relation_zero (Or.inl ⟨i,rfl⟩)
theorem t_comm (i j : α) : t (R:=R) i j=t j i := by
  have h := relation_zero (R:=R) (Or.inr (Or.inl ⟨i,j,rfl⟩))
  simpa only [map_sub,sub_eq_zero,t] using h
theorem t_disjoint (i j k l : α) (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) :
    ⁅t (R:=R) i j,t (R:=R) k l⁆=0 := by
  change (ideal (R:=R) (α:=α)).mkQ (⁅gen i j,gen k l⁆)=0
  exact relation_zero (Or.inr (Or.inr (Or.inl ⟨i,j,k,l,hik,hil,hjk,hjl,rfl⟩)))
theorem t_three (i j k : α) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    ⁅t (R:=R) i j,t (R:=R) i k+t (R:=R) j k⁆=0 := by
  change (ideal (R:=R) (α:=α)).mkQ (⁅gen i j,gen i k+gen j k⁆)=0
  exact relation_zero (Or.inr (Or.inr (Or.inr ⟨i,j,k,hij,hik,hjk,rfl⟩)))

variable {E : Type*} [LieRing E] [LieAlgebra R E]
def lift (f : α → α → E) (hz : ∀ i, f i i=0) (hs : ∀ i j,f i j=f j i)
    (hd : ∀ i j k l,i≠k → i≠l → j≠k → j≠l → ⁅f i j,f k l⁆=0)
    (ht : ∀ i j k,i≠j → i≠k → j≠k → ⁅f i j,f i k+f j k⁆=0) : T R α →ₗ⁅R⁆ E := by
  let p := FreeLieAlgebra.lift R (fun ij : α×α => f ij.1 ij.2)
  have hker : ideal (R:=R) (α:=α) ≤ p.ker := by
    rw [ideal,LieSubmodule.lieSpan_le]
    intro q hq
    change p q=0
    rcases hq with ⟨i,rfl⟩ | ⟨i,j,rfl⟩ | ⟨i,j,k,l,hik,hil,hjk,hjl,rfl⟩ | ⟨i,j,k,hij,hik,hjk,rfl⟩
    · simpa only [p,gen,FreeLieAlgebra.lift_of_apply] using hz i
    · simpa only [map_sub,p,gen,FreeLieAlgebra.lift_of_apply,sub_eq_zero] using hs i j
    · simpa only [LieHom.map_lie,p,gen,FreeLieAlgebra.lift_of_apply] using hd i j k l hik hil hjk hjl
    · simpa only [LieHom.map_lie,map_add,p,gen,FreeLieAlgebra.lift_of_apply] using ht i j k hij hik hjk
  exact { (ideal (R:=R) (α:=α)).toSubmodule.liftQ p.toLinearMap hker with
    map_lie' := by
      intro a b
      induction a using Submodule.Quotient.induction_on with | _ a =>
        induction b using Submodule.Quotient.induction_on with | _ b =>
          exact p.map_lie a b }
@[simp] theorem lift_t (f : α → α → E) (hz hs hd ht) (i j : α) :
    lift f hz hs hd ht (t (R:=R) i j)=f i j := by
  change FreeLieAlgebra.lift R (fun ij : α×α => f ij.1 ij.2) (FreeLieAlgebra.of R (i,j))=f i j
  simp only [FreeLieAlgebra.lift_of_apply]

variable [DecidableEq α]
def action : T R α →ₗ⁅R⁆ LieDerivation R (FreeLieAlgebra R α) (FreeLieAlgebra R α) :=
  lift pair pair_self pair_comm pair_disjoint pair_three
local notation "F" => FreeLieAlgebra R α
local notation "SD" => SemiDirectSum F (T R α) action
@[simp] theorem action_t (i j : α) : action (t (R:=R) i j)=pair i j := by simp [action]
def fiber (i : α) : SD := SemiDirectSum.inl action (FreeLieAlgebra.of R i)
def base (i j : α) : SD := SemiDirectSum.inr action (t i j)
def chord : Option α → Option α → SD
  | none, none => 0
  | none, some j => fiber j
  | some i, none => fiber i
  | some i, some j => base i j
@[simp] theorem chord_nn : chord (R:=R) (α:=α) none none=0 := rfl
@[simp] theorem chord_ns (i : α) : chord (R:=R) none (some i)=fiber i := rfl
@[simp] theorem chord_sn (i : α) : chord (R:=R) (some i) none=fiber i := rfl
@[simp] theorem chord_ss (i j : α) : chord (R:=R) (some i) (some j)=base i j := rfl
@[simp] theorem chord_self (i : Option α) : chord (R:=R) i i=0 := by
  cases i <;> simp [base]
theorem chord_comm (i j : Option α) : chord (R:=R) i j=chord j i := by
  cases i <;> cases j <;> simp [base,t_comm]
theorem base_fiber (i j k : α) : ⁅base (R:=R) i j,fiber k⁆=
    SemiDirectSum.inl action (pair (R:=R) i j (FreeLieAlgebra.of R k)) := by
  simp [base,fiber]
theorem fiber_base (i j k : α) : ⁅fiber (R:=R) k,base i j⁆=
    -SemiDirectSum.inl action (pair (R:=R) i j (FreeLieAlgebra.of R k)) := by
  rw [← lie_skew,base_fiber]
theorem chord_disjoint (i j k l : Option α)
    (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) :
    ⁅chord (R:=R) i j,chord (R:=R) k l⁆=0 := by
  cases i <;> cases j <;> cases k <;> cases l <;>
    simp_all [base,fiber,t_disjoint]
  all_goals apply pair_of_other <;> intro h <;> subst_vars <;> contradiction
theorem chord_three (i j k : Option α) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    ⁅chord (R:=R) i j,chord (R:=R) i k+chord (R:=R) j k⁆=0 := by
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j =>
      cases k with
      | none => exact (hik rfl).elim
      | some k =>
        rw [chord_ns,chord_ns,chord_ss,lie_add,fiber_base]
        simp [fiber]
        grind [lie_skew]
  | some i =>
    cases j with
    | none =>
      cases k with
      | none => exact (hjk rfl).elim
      | some k =>
        rw [chord_sn,chord_ss,chord_ns,lie_add,fiber_base]
        simp [fiber]
        grind [lie_skew]
    | some j =>
      cases k with
      | none =>
        rw [chord_ss,chord_sn,chord_sn,lie_add,base_fiber,base_fiber]
        simp only [pair_of_left,pair_of_right,← map_add]
        grind [lie_skew]
      | some k =>
        simp only [chord_ss,base,← map_add,← LieHom.map_lie]
        rw [t_three _ _ _ (fun h => hij (congrArg some h))
          (fun h => hik (congrArg some h)) (fun h => hjk (congrArg some h)),map_zero]
def toSemidirect : T R (Option α) →ₗ⁅R⁆ SD :=
  lift chord chord_self chord_comm chord_disjoint chord_three
@[simp] theorem toSemidirect_t (i j : Option α) : toSemidirect (t (R:=R) i j)=chord i j := by
  simp [toSemidirect]
end GenericBraid

namespace RestrictedAlphabet
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
abbrev F := ZMod 2
inductive Letter (α : Type*) | a | c (i : α) | b (i : α)
variable {α : Type*}
abbrev S (α : Type*) := A F (Letter α)
abbrev T (α : Type*) := A F (Option α)
def a : S α := atom .a
def b (i : α) : S α := atom (.b i)
def c (i : α) : S α := atom (.c i)
def y (i : α) : T α := atom (some i)
def x : T α := atom none
def delta : Module.End F (S α) := deriv (fun (l : Letter α) => match l with | .a => 0 | .c i => ⁅(a : S α),b i⁆ | .b i => c i)
@[simp] theorem delta_a : delta (a : S α)=0 := by simp [delta,a]
@[simp] theorem delta_b (i : α) : delta (b i)=c i := by simp [delta,b]
@[simp] theorem delta_c (i : α) : delta (c i)=⁅(a : S α),b i⁆ := by simp [delta,c]
@[simp] theorem delta_one : delta (1 : S α)=0 := deriv_one _
theorem delta_mul (p q : S α) : delta (p*q)=delta p*q+p*delta q := deriv_mul _ _ _
theorem delta_lie (p q : S α) : delta ⁅p,q⁆=⁅delta p,q⁆+⁅p,delta q⁆ := deriv_lie _ _ _
theorem delta_square_mul (p q : S α) :
    delta (delta (p*q))=delta (delta p)*q+p*delta (delta q) := by
  rw [delta_mul,map_add,delta_mul,delta_mul]
  calc
    _ = delta (delta p)*q+p*delta (delta q)+(delta p*delta q+delta p*delta q) := by abel
    _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]
theorem delta_square (p : S α) : delta (delta p)=⁅(a : S α),p⁆ := by
  induction p using QuadraticAlphabet.algebra_induction with
  | h1 => simp [Ring.lie_def]
  | ha l =>
    cases l with
    | a => change delta (delta a)=⁅a,a⁆; simp
    | c i => change delta (delta (c i))=⁅a,c i⁆; simp [delta_lie]
    | b i => change delta (delta (b i))=⁅(a : S α),b i⁆; simp
  | hadd p q hp hq => simp [hp,hq,lie_add]
  | hs r p hp => simp [hp]
  | hm p q hp hq => rw [delta_square_mul,hp,hq]; simp [Ring.lie_def]; noncomm_ring

def left : S α →ₐ[F] Module.End F (S α×S α) where
  toFun p :=
    { toFun := fun z => (p*z.1,p*z.2)
      map_add' := by intro z w; ext <;> simp [mul_add]
      map_smul' := by intro r z; ext <;> simp }
  map_one' := by ext z <;> simp
  map_mul' := by intro p q; ext z <;> simp [mul_assoc]
  map_zero' := by ext z <;> simp
  map_add' := by intro p q; ext z <;> simp [add_mul]
  commutes' := by intro r; ext z <;> simp [Algebra.algebraMap_eq_smul_one]
@[simp] theorem left_apply (p : S α) (z : S α×S α) : left p z=(p*z.1,p*z.2) := rfl

def root : Module.End F (S α×S α) where
  toFun z := (delta z.1+z.2*a,z.1+delta z.2)
  map_add' := by intro z w; apply Prod.ext <;> simp only [Prod.fst_add,Prod.snd_add,map_add,add_mul] <;> abel
  map_smul' := by intro r z; ext <;> simp [smul_add]
@[simp] theorem root_apply (z : S α×S α) : root z=(delta z.1+z.2*a,z.1+delta z.2) := rfl
theorem root_comm (p : S α) : ⁅(root : Module.End F (S α×S α)),left p⁆=left (delta p) := by
  apply LinearMap.ext
  intro z
  apply Prod.ext <;> simp [Ring.lie_def,delta_mul,Module.End.mul_apply,mul_add,mul_assoc]
theorem root_square : root*root=left (a : S α) := by
  apply LinearMap.ext
  intro z
  apply Prod.ext <;> simp only [Module.End.mul_apply,root_apply,left_apply,
    map_add,delta_mul,delta_square,delta_a,mul_zero,add_zero,Ring.lie_def,add_mul]
  · calc
      _ = a*z.1+(delta z.2*a+delta z.2*a) := by abel
      _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]
  · calc
      _ = a*z.2+(delta z.1+delta z.1) := by abel
      _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]

def substitution : S α →ₐ[F] T α := lift (fun | .a => x*x | .c i => ⁅(x : T α),y i⁆ | .b i => y i)
@[simp] theorem substitution_a : substitution (a : S α)=x*x := by simp [substitution,a]
@[simp] theorem substitution_c (i : α) : substitution (c i)=⁅(x : T α),y i⁆ := by simp [substitution,c]
@[simp] theorem substitution_b (i : α) : substitution (b i)=y i := by simp [substitution,b]
def representation : T α →ₐ[F] Module.End F (S α×S α) :=
  lift (fun | none => root | some i => left (b i))
@[simp] theorem representation_x : representation (x : T α)=root := by simp [representation,x]
@[simp] theorem representation_y (i : α) : representation (y i)=left (b i) := by simp [representation,y]
theorem representation_substitution : representation.comp substitution=left (α:=α) := by
  apply hom_ext
  intro l
  cases l with
  | a => change representation (substitution a)=left a; simp [root_square]
  | c i =>
    change representation (substitution (c i))=left (c i)
    rw [substitution_c]
    change representation (x*y i-y i*x)=left (c i)
    rw [map_sub,map_mul,map_mul,representation_x,representation_y]
    exact (root_comm (b i)).trans (congrArg left (delta_b i))
  | b i => change representation (substitution (b i))=left (b i); simp

theorem injective : Function.Injective (substitution (α:=α)) := by
  intro p q hpq
  have h := congrArg representation hpq
  have hh (v : S α) : representation (substitution v)=left v := AlgHom.congr_fun representation_substitution v
  rw [hh,hh] at h
  have he := congrArg (fun f : Module.End F (S α×S α) => (f (1,0)).1) h
  simpa only [left_apply,mul_one] using he
end RestrictedAlphabet

namespace GenericBraid
open LieAlgebra AssociativeElimination
open scoped TensorProduct
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R] [DecidableEq α]
abbrev Env (R α : Type*) [CommRing R] := UniversalEnvelopingAlgebra R (T R α)

def baseLie : T R α →ₗ⁅R⁆ T R (Option α) :=
  lift (fun i j => t (some i) (some j)) (fun i => t_self (some i))
    (fun i j => t_comm (some i) (some j)) (fun i j k l hik hil hjk hjl =>
      t_disjoint (some i) (some j) (some k) (some l) (fun h => hik (Option.some.inj h))
        (fun h => hil (Option.some.inj h)) (fun h => hjk (Option.some.inj h))
        (fun h => hjl (Option.some.inj h)))
    (fun i j k hij hik hjk => t_three (some i) (some j) (some k) (fun h => hij (Option.some.inj h))
      (fun h => hik (Option.some.inj h)) (fun h => hjk (Option.some.inj h)))
omit [DecidableEq α] in
@[simp] theorem baseLie_t (i j : α) : baseLie (t (R:=R) i j)=t (some i) (some j) := by
  simp [baseLie]

omit [DecidableEq α] in
theorem hom_ext {E : Type*} [LieRing E] [LieAlgebra R E]
    {f g : T R α →ₗ⁅R⁆ E} (h : ∀ i j, f (t i j)=g (t i j)) : f=g := by
  let q : Free R α →ₗ⁅R⁆ T R α :=
    { (ideal (R:=R) (α:=α)).mkQ with map_lie' := by intros; rfl }
  have hh : f.comp q=g.comp q := by
    apply FreeLieAlgebra.hom_ext
    rintro ⟨i,j⟩
    exact h i j
  apply LieHom.ext
  intro a
  induction a using Submodule.Quotient.induction_on with | _ a =>
    exact LieHom.congr_fun hh a

def fiberIn : A R α →ₐ[R] Env R (Option α) :=
  AssociativeElimination.lift (fun i => UniversalEnvelopingAlgebra.ι R (t none (some i)))
def baseIn : Env R α →ₐ[R] Env R (Option α) :=
  UniversalEnvelopingAlgebra.lift R ((UniversalEnvelopingAlgebra.ι R).comp baseLie)
def toSemi : Env R (Option α) →ₐ[R] UniversalEnvelopingAlgebra R
    (SemiDirectSum (FreeLieAlgebra R α) (T R α) action) :=
  UniversalEnvelopingAlgebra.lift R ((UniversalEnvelopingAlgebra.ι R).comp toSemidirect)

theorem toSemi_fiber : toSemi.comp fiberIn=FiberPBW.fiberIn (action (R:=R) (α:=α)) := by
  apply AssociativeElimination.hom_ext
  intro i
  simp [toSemi,fiberIn,FiberPBW.fiberIn,fiber]

theorem toSemi_base : toSemi.comp baseIn=FiberPBW.baseIn (action (R:=R) (α:=α)) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply hom_ext
  intro i j
  simp [toSemi,baseIn,FiberPBW.baseIn,base]

def normal : A R α ⊗[R] Env R α →ₗ[R] Env R (Option α) :=
  TensorProduct.lift
    { toFun := fun p =>
        { toFun := fun b => fiberIn p*baseIn b
          map_add' := by intro b c; simp [mul_add]
          map_smul' := by intro r b; simp }
      map_add' := by intro p q; ext b; simp [add_mul]
      map_smul' := by intro r p; ext b; simp }
omit [DecidableEq α] in
@[simp] theorem normal_tmul (p : A R α) (b : Env R α) :
    normal (p⊗ₜ b)=fiberIn p*baseIn b := rfl

theorem toSemi_normal : toSemi.toLinearMap.comp normal=
    FiberPBW.normal (action (R:=R) (α:=α)) := by
  apply TensorProduct.ext'
  intro p b
  change toSemi (fiberIn p*baseIn b)=_
  rw [map_mul]
  have hf := AlgHom.congr_fun (toSemi_fiber (R:=R) (α:=α)) p
  have hb := AlgHom.congr_fun (toSemi_base (R:=R) (α:=α)) b
  exact congrArg₂ (·*·) hf hb

theorem normal_injective : Function.Injective (normal (R:=R) (α:=α)) := by
  intro a b h
  apply FiberPBW.normal_injective (action (R:=R) (α:=α))
  have he (z) := LinearMap.congr_fun (toSemi_normal (R:=R) (α:=α)) z
  rw [← he a,← he b]
  exact congrArg toSemi h
end GenericBraid

namespace RestrictedAlphabet
open LieAlgebra AssociativeElimination
open scoped TensorProduct
variable {α : Type*} [DecidableEq α]
local notation "U" => UniversalEnvelopingAlgebra F (GenericBraid.T F (Option α))

def normal : S α ⊗[F] U →ₗ[F]
    UniversalEnvelopingAlgebra F (GenericBraid.T F (Option (Option α))) :=
  GenericBraid.normal.comp (substitution.toLinearMap.rTensor U)

theorem normal_injective : Function.Injective (normal (α:=α)) :=
  GenericBraid.normal_injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap substitution.toLinearMap injective)
end RestrictedAlphabet

namespace Deletion

section
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R]
def word (w : List α) : A R α := MonoidAlgebra.single (FreeMonoid.ofList w) 1
@[simp] theorem word_nil : word ([] : List α)=(1 : A R α) := rfl
theorem word_cons (a : α) (s : List α) : word (R:=R) (a::s)=atom a*word s := by
  simp only [word,atom,MonoidAlgebra.single_mul_single,one_mul,FreeMonoid.ofList_cons]

def raw (ν : α → α → R) (l r : α) : List α → A R α
  | [] => 0
  | a::s => (ν a (s.headD r)-ν l a) • word s+atom a*raw ν a r s

def op (ν : α → α → R) (l r : α) : Module.End R (A R α) :=
  (Finsupp.linearCombination R (fun w : FreeMonoid α => raw ν l r w.toList)).comp
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap
@[simp] theorem op_word (ν : α → α → R) (l r : α) (s : List α) :
    op ν l r (word s)=raw ν l r s := by
  change Finsupp.linearCombination R (fun monoidWord : FreeMonoid α => raw ν l r monoidWord.toList) (Finsupp.single (FreeMonoid.ofList s) 1) = _; simp
@[simp] theorem op_one (ν : α → α → R) (l r : α) : op ν l r 1=0 := by
  exact op_word ν l r []
theorem op_cons (ν : α → α → R) (l r a : α) (s : List α) :
    op ν l r (word (a::s))=(ν a (s.headD r)-ν l a) • word s+atom a*op ν a r (word s) := by
  simp only [op_word,raw]
theorem op_mul_word (ν : α → α → R) (l r a : α) (s : List α) :
    op ν l r (atom a*word s)=(ν a (s.headD r)-ν l a) • word s+atom a*op ν a r (word s) := by
  rw [← word_cons,op_cons]

theorem op_two (ν : α → α → R) (l r a b : α) (p : A R α) :
    op ν l r (atom a*(atom b*p))=(ν a b-ν l a) • (atom b*p)+atom a*op ν a r (atom b*p) := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    have h := op_cons ν l r a (b::w.toList)
    simp only [word_cons,List.headD_cons] at h
    simpa only [word,FreeMonoid.ofList_toList,MonoidAlgebra.of_apply] using h
  | add p q hp hq => simp only [mul_add,map_add,smul_add,hp,hq]; abel
  | smul c p hp => simp only [mul_smul_comm,map_smul,hp,smul_add,smul_smul]; rw [mul_comm c]

def curvature (ν μ : α → α → R) (l a b c : α) : R :=
  (ν a b-ν l a)*(μ b c-μ l b)+(ν b c-ν a b)*(μ a c-μ l a)-
  (μ a b-μ l a)*(ν b c-ν l b)-(μ b c-μ a b)*(ν a c-ν l a)

theorem comm_cons (ν μ : α → α → R) (l r a b : α) (s : List α) :
    op μ l r (op ν l r (word (a::b::s)))-op ν l r (op μ l r (word (a::b::s)))=
      curvature ν μ l a b (s.headD r) • word s+
        atom a*(op μ a r (op ν a r (word (b::s)))-op ν a r (op μ a r (word (b::s)))) := by
  simp only [word_cons,op_two,op_mul_word,map_add,map_smul,mul_add,mul_smul_comm,
    mul_sub,smul_add,curvature]
  module

theorem commute_of_curvature (ν μ : α → α → R)
    (hc : ∀ l a b c,curvature ν μ l a b c=0) (l r : α) : ⁅op μ l r,op ν l r⁆=0 := by
  apply LinearMap.ext
  intro p
  have hs (s : List α) : op μ l r (op ν l r (word s))-op ν l r (op μ l r (word s))=0 := by
    induction s generalizing l with
    | nil => simp
    | cons a s ih =>
      cases s with
      | nil => simp [raw]
      | cons b s => rw [comm_cons,hc,ih]; simp
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change op μ l r (op ν l r (MonoidAlgebra.single w 1))-
      op ν l r (op μ l r (MonoidAlgebra.single w 1))=0
    simpa only [word,FreeMonoid.ofList_toList,MonoidAlgebra.of_apply] using hs w.toList
  | add p q hp hq =>
    simp only [Ring.lie_def,LinearMap.sub_apply,Module.End.mul_apply,LinearMap.zero_apply] at hp hq ⊢
    simp only [map_add]
    rw [add_sub_add_comm, hp, hq, add_zero]
  | smul c p hp => simpa using congrArg (c • ·) hp
end

open AssociativeElimination
variable {R α : Type*} [CommRing R]
theorem linear_ext {M : Type*} [AddCommGroup M] [Module R M]
    {f g : A R α →ₗ[R] M} (h : ∀ s : List α,f (word s)=g (word s)) : f=g := by
  apply LinearMap.ext
  intro p
  induction p using MonoidAlgebra.induction_on with
  | of w => simpa only [word,FreeMonoid.ofList_toList,MonoidAlgebra.of_apply] using h w.toList
  | add p q hp hq => simp only [map_add,hp,hq]
  | smul c p hp => simp only [map_smul,hp]

theorem raw_add (ν μ : α → α → R) (l r : α) (s : List α) :
    raw (fun a b => ν a b+μ a b) l r s=raw ν l r s+raw μ l r s := by
  induction s generalizing l with
  | nil => simp [raw]
  | cons a s ih => simp only [raw,ih,mul_add]; module
@[simp] theorem op_add (ν μ : α → α → R) (l r : α) :
    op (fun a b => ν a b+μ a b) l r=op ν l r+op μ l r := by
  apply linear_ext
  intro s
  simp only [LinearMap.add_apply,op_word,raw_add]
@[simp] theorem op_zero (l r : α) : op (fun _ _ => (0 : R)) l r=0 := by
  apply linear_ext
  intro s
  simp only [LinearMap.zero_apply,op_word]
  induction s generalizing l with
  | nil => rfl
  | cons a s ih => simp [raw,ih]

theorem op_list_sum {ι : Type*} (ν : ι → α → α → R) (s : List ι) (l r : α) :
    op (fun a b => (s.map (fun i => ν i a b)).sum) l r=(s.map (fun i => op (ν i) l r)).sum := by
  induction s with
  | nil => simp
  | cons i s ih => simpa only [List.map_cons,List.sum_cons,op_add] using congrArg (op (ν i) l r+·) ih
end Deletion

namespace DeletionTable
open Deletion AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
inductive Letter | o | e | p | w deriving DecidableEq
instance : Fintype Letter := ⟨{.o,.e,.p,.w}, by intro x; cases x <;> simp⟩
inductive Hyperplane | a1 | a2 | a3 | p12 | m12 | p13 | m13 | p23 | m23 deriving DecidableEq
instance : Fintype Hyperplane := ⟨{.a1,.a2,.a3,.p12,.m12,.p13,.m13,.p23,.m23}, by intro x; cases x <;> simp⟩
open Letter Hyperplane

def weight : Hyperplane → Letter → Letter → ℤ
  | .p23, .o, .p | .p23, .p, .o => 1
  | .m23, .o, .p | .m23, .p, .o => -1
  | .p12, .o, .w | .p12, .w, .o => 1
  | .m12, .o, .w | .m12, .w, .o => -1
  | .a3, .e, .p | .a3, .p, .e => 1
  | .m23, .e, .p | .m23, .p, .e => -1
  | .a1, .e, .w | .a1, .w, .e => 1
  | .m12, .e, .w | .m12, .w, .e => -1
  | .a2, .p, .w | .a2, .w, .p => 1
  | .p13, .p, .w | .p13, .w, .p => 1
  | .m12, .p, .w | .m12, .w, .p => -1
  | .m23, .p, .w | .m23, .w, .p => -1
  | _, _, _ => 0

def flat : Fin 13 → List Hyperplane :=
  ![[.a1,.a2,.p12,.m12],
    [.a1,.a3,.p13,.m13],
    [.a2,.a3,.p23,.m23],
    [.p12,.p13,.p23],
    [.p12,.m13,.m23],
    [.m12,.p13,.m23],
    [.m12,.m13,.p23],
    [.a1,.p23],
    [.a1,.m23],
    [.a2,.p13],
    [.a2,.m13],
    [.a3,.p12],
    [.a3,.m12]]

def total (i : Fin 13) (a b : Letter) : ℤ := ((flat i).map (fun h => weight h a b)).sum

theorem curvature_0 : ∀ h : Hyperplane, h∈flat 0 →
    ∀ l a b c : Letter, curvature (weight h) (total 0) l a b c=0 := by decide

theorem curvature_1 : ∀ h : Hyperplane, h∈flat 1 →
    ∀ l a b c : Letter, curvature (weight h) (total 1) l a b c=0 := by decide

theorem curvature_2 : ∀ h : Hyperplane, h∈flat 2 →
    ∀ l a b c : Letter, curvature (weight h) (total 2) l a b c=0 := by decide

theorem curvature_3 : ∀ h : Hyperplane, h∈flat 3 →
    ∀ l a b c : Letter, curvature (weight h) (total 3) l a b c=0 := by decide

theorem curvature_4 : ∀ h : Hyperplane, h∈flat 4 →
    ∀ l a b c : Letter, curvature (weight h) (total 4) l a b c=0 := by decide

theorem curvature_5 : ∀ h : Hyperplane, h∈flat 5 →
    ∀ l a b c : Letter, curvature (weight h) (total 5) l a b c=0 := by decide

theorem curvature_6 : ∀ h : Hyperplane, h∈flat 6 →
    ∀ l a b c : Letter, curvature (weight h) (total 6) l a b c=0 := by decide

theorem curvature_7 : ∀ h : Hyperplane, h∈flat 7 →
    ∀ l a b c : Letter, curvature (weight h) (total 7) l a b c=0 := by decide

theorem curvature_8 : ∀ h : Hyperplane, h∈flat 8 →
    ∀ l a b c : Letter, curvature (weight h) (total 8) l a b c=0 := by decide

theorem curvature_9 : ∀ h : Hyperplane, h∈flat 9 →
    ∀ l a b c : Letter, curvature (weight h) (total 9) l a b c=0 := by decide

theorem curvature_10 : ∀ h : Hyperplane, h∈flat 10 →
    ∀ l a b c : Letter, curvature (weight h) (total 10) l a b c=0 := by decide

theorem curvature_11 : ∀ h : Hyperplane, h∈flat 11 →
    ∀ l a b c : Letter, curvature (weight h) (total 11) l a b c=0 := by decide

theorem curvature_12 : ∀ h : Hyperplane, h∈flat 12 →
    ∀ l a b c : Letter, curvature (weight h) (total 12) l a b c=0 := by decide

theorem flat_curvature (i : Fin 13) (h : Hyperplane) (hi : h∈flat i) (l a b c : Letter) :
    curvature (weight h) (total i) l a b c=0 := by
  fin_cases i
  · exact curvature_0 h hi l a b c
  · exact curvature_1 h hi l a b c
  · exact curvature_2 h hi l a b c
  · exact curvature_3 h hi l a b c
  · exact curvature_4 h hi l a b c
  · exact curvature_5 h hi l a b c
  · exact curvature_6 h hi l a b c
  · exact curvature_7 h hi l a b c
  · exact curvature_8 h hi l a b c
  · exact curvature_9 h hi l a b c
  · exact curvature_10 h hi l a b c
  · exact curvature_11 h hi l a b c
  · exact curvature_12 h hi l a b c

theorem integral_flat (i : Fin 13) (h : Hyperplane) (hi : h∈flat i) (l r : Letter) :
    ⁅op (weight h) l r,((flat i).map (fun g => op (weight g) l r)).sum⁆=0 := by
  rw [← op_list_sum]
  change ⁅op (weight h) l r,op (total i) l r⁆=0
  have hc := commute_of_curvature (weight h) (total i) (flat_curvature i h hi) l r
  rw [← lie_skew,hc,neg_zero]
end DeletionTable

namespace GenericBraid
open LieAlgebra FreeDerivations
variable {R α : Type*} [CommRing R]

theorem induction {P : T R α → Prop} (h0 : P 0) (ht : ∀ i j,P (t i j))
    (ha : ∀ p q,P p → P q → P (p+q)) (hs : ∀ (r : R) p,P p → P (r • p))
    (hl : ∀ p q,P p → P q → P ⁅p,q⁆) (p : T R α) : P p := by
  induction p using Submodule.Quotient.induction_on with | _ p =>
    induction p using freeLie_induction with
    | h0 => exact h0
    | hg ij => exact ht ij.1 ij.2
    | ha p q hp hq => exact ha _ _ hp hq
    | hs r p hp => exact hs r _ hp
    | hl p q hp hq => exact hl _ _ hp hq

variable [DecidableEq α]
def fiberLie : FreeLieAlgebra R α →ₗ⁅R⁆ T R (Option α) :=
  FreeLieAlgebra.lift R (fun i => t none (some i))
omit [DecidableEq α] in
@[simp] theorem fiberLie_of (i : α) : fiberLie (FreeLieAlgebra.of R i)=t none (some i) := by
  simp [fiberLie]

theorem t_base_fiber_left (i j : α) :
    ⁅t (R:=R) (some i) (some j),t (R:=R) none (some i)⁆=⁅t (R:=R) none (some i),t (R:=R) none (some j)⁆ := by
  by_cases hij : i=j
  · subst j; simp
  have h := t_three (R:=R) (none : Option α) (some i) (some j) (by simp) (by simp)
    (fun h => hij (Option.some.inj h))
  rw [lie_add] at h
  grind [lie_skew]

theorem compatibility (g : T R α) (p : FreeLieAlgebra R α) :
    fiberLie (action g p)=⁅baseLie g,fiberLie p⁆ := by
  induction g using induction generalizing p with
  | h0 => simp
  | ht i j =>
    rw [action_t,baseLie_t]
    induction p using freeLie_induction with
    | h0 => simp
    | hg k =>
      by_cases hki : k=i
      · subst k; simp only [pair_of_left,LieHom.map_lie,fiberLie_of]; exact (t_base_fiber_left i j).symm
      by_cases hkj : k=j
      · subst k
        simp only [pair_of_right,LieHom.map_lie,fiberLie_of]
        rw [t_comm (some i) (some j)]
        exact (t_base_fiber_left j i).symm
      simp only [pair_of_other i j k hki hkj,map_zero,fiberLie_of]
      exact (t_disjoint _ _ _ _ (by simp) (fun h => hki (Option.some.inj h).symm)
        (by simp) (fun h => hkj (Option.some.inj h).symm)).symm
    | ha p q hp hq => simp [hp,hq,lie_add]
    | hs r p hp => simp [hp]
    | hl p q hp hq =>
      simp only [LieDerivation.apply_lie_eq_add,map_add,LieHom.map_lie,hp,hq]
      simpa only [add_comm] using (leibniz_lie (t (R:=R) (some i) (some j)) (fiberLie p) (fiberLie q)).symm
  | ha g h hg hh => simp [hg,hh,add_lie]
  | hs r g hg => simp [hg]
  | hl g h hg hh =>
    simp only [LieHom.map_lie,LieDerivation.lie_apply,map_sub,hg,hh]
    exact (lie_lie _ _ _).symm

def fromSemidirect : SemiDirectSum (FreeLieAlgebra R α) (T R α) action →ₗ⁅R⁆ T R (Option α) :=
  InnerSemiDirect.lift action fiberLie baseLie compatibility

theorem toSemidirect_fiberLie (p : FreeLieAlgebra R α) :
    toSemidirect (fiberLie p)=SemiDirectSum.inl action p := by
  have h : (toSemidirect (R:=R) (α:=α)).comp fiberLie=SemiDirectSum.inl action := by
    apply FreeLieAlgebra.hom_ext
    intro i
    simp [fiber]
  exact LieHom.congr_fun h p

theorem toSemidirect_baseLie (p : T R α) :
    toSemidirect (baseLie p)=SemiDirectSum.inr action p := by
  have h : (toSemidirect (R:=R) (α:=α)).comp baseLie=SemiDirectSum.inr action := by
    apply hom_ext
    intro i j
    simp [base]
  exact LieHom.congr_fun h p

theorem to_from (p : SemiDirectSum (FreeLieAlgebra R α) (T R α) action) :
    toSemidirect (fromSemidirect p)=p := by
  change toSemidirect (fiberLie p.left+baseLie p.right)=p
  rw [map_add,toSemidirect_fiberLie,toSemidirect_baseLie]
  ext <;> simp

theorem from_to (p : T R (Option α)) : fromSemidirect (toSemidirect p)=p := by
  have h : (fromSemidirect (R:=R) (α:=α)).comp toSemidirect=LieHom.id := by
    apply hom_ext
    intro i j
    cases i <;> cases j <;> simp [fromSemidirect,InnerSemiDirect.lift,fiber,base,t_comm]
  exact LieHom.congr_fun h p

def equivalence : T R (Option α) ≃ₗ⁅R⁆ SemiDirectSum (FreeLieAlgebra R α) (T R α) action :=
  { toSemidirect with
    invFun := fromSemidirect
    left_inv := from_to
    right_inv := to_from }
end GenericBraid

attribute [local instance 2000] FreeLieAlgebra.instLieAlgebra

namespace IntegralBaseChange
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {S α : Type*} [CommRing S]
def words : A ℤ α →+* A S α := MonoidAlgebra.mapRingHom _ (Int.castRingHom S)
@[simp] theorem words_atom (a : α) : words (atom a : A ℤ α)=(atom a : A S α) := by
  simp [words,atom]
@[simp] theorem words_coeff (p : A ℤ α) (w : FreeMonoid α) :
    (words p : A S α).coeff w=(p.coeff w : S) := by simp [words]
def lie : FreeLieAlgebra ℤ α →ₗ⁅ℤ⁆ FreeLieAlgebra S α :=
  FreeLieAlgebra.lift ℤ (FreeLieAlgebra.of S)
@[simp] theorem lie_of (a : α) : lie (FreeLieAlgebra.of ℤ a)=FreeLieAlgebra.of S a := by exact FreeLieAlgebra.lift_of_apply (FreeLieAlgebra.of S) a
theorem embed_lie (p : FreeLieAlgebra ℤ α) :
    embed (lie p : FreeLieAlgebra S α)=words (embed p) := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg a => simp
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [map_smul,hp]
  | hl p q hp hq => simp only [LieHom.map_lie,hp,hq,Ring.lie_def,map_sub,map_mul]
theorem words_rational_injective : Function.Injective (words (S:=ℚ) (α:=α)) := by
  intro p q h
  ext w
  have hc := congrArg (fun z : A ℚ α => z.coeff w) h
  simpa using hc

theorem lie_rational_injective : Function.Injective (lie (S:=ℚ) (α:=α)) := by
  intro p q h
  apply UniversalEmbedding.injective
  apply words_rational_injective
  rw [← embed_lie,← embed_lie,h]

theorem lift_integral {p : FreeLieAlgebra ℚ α} (hp : embed p∈IntegralWords.lattice) :
    ∃ q : FreeLieAlgebra ℤ α,lie q=p := by
  have hr : embed p∈IntegralWords.rationalLie := by
    clear hp
    induction p using freeLie_induction with
    | h0 => simp
    | hg a => exact LieSubalgebra.subset_lieSpan ⟨a,by simp⟩
    | ha p q hp hq => simpa using IntegralWords.rationalLie.add_mem hp hq
    | hs r p hp => simpa using IntegralWords.rationalLie.smul_mem r hp
    | hl p q hp hq => simpa only [LieHom.map_lie] using IntegralWords.rationalLie.lie_mem hp hq
  have hi := IntegralWords.saturation hr hp
  let f : FreeLieAlgebra ℤ α →ₗ⁅ℤ⁆ A ℚ α := FreeLieAlgebra.lift ℤ atom
  have he (q : FreeLieAlgebra ℤ α) : f q=embed (lie q : FreeLieAlgebra ℚ α) := by
    induction q using freeLie_induction with
    | h0 => simp
    | hg a => rw [lie_of,embed_of]; exact FreeLieAlgebra.lift_of_apply atom a
    | ha p q hp hq => simp [hp,hq]
    | hs r p hp => simp [map_smul,hp]
    | hl p q hp hq => simp [hp,hq]
  have hspan : IntegralWords.lieLattice ≤ f.range := by
    apply LieSubalgebra.lieSpan_le.mpr
    rintro a ⟨a,rfl⟩
    exact ⟨FreeLieAlgebra.of ℤ a,FreeLieAlgebra.lift_of_apply atom a⟩
  obtain ⟨q,hq⟩ := hspan hi
  refine ⟨q, UniversalEmbedding.injective ?_⟩
  rw [← he]
  exact hq
end IntegralBaseChange

namespace GenericBraid

section
variable {S α β : Type*} [CommRing S]
def cast : T ℤ α →ₗ⁅ℤ⁆ T S α :=
  lift (t (R:=S)) t_self t_comm t_disjoint t_three
@[simp] theorem cast_t (i j : α) : cast (t (R:=ℤ) i j)=t (R:=S) i j := by simp [cast]
def rename {R : Type*} [CommRing R] (e : α ≃ β) : T R α →ₗ⁅R⁆ T R β :=
  lift (fun i j => t (e i) (e j)) (fun i => t_self (e i)) (fun i j => t_comm (e i) (e j))
    (fun i j k l hik hil hjk hjl => t_disjoint (e i) (e j) (e k) (e l)
      (e.injective.ne hik) (e.injective.ne hil) (e.injective.ne hjk) (e.injective.ne hjl))
    (fun i j k hij hik hjk => t_three (e i) (e j) (e k) (e.injective.ne hij) (e.injective.ne hik) (e.injective.ne hjk))
@[simp] theorem rename_t {R : Type*} [CommRing R] (e : α ≃ β) (i j : α) :
    rename e (t (R:=R) i j)=t (e i) (e j) := by simp [rename]
theorem rename_symm {R : Type*} [CommRing R] (e : α ≃ β) (p : T R α) :
    rename e.symm (rename e p)=p := by
  induction p using induction with
  | h0 => simp
  | ht i j => simp
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [map_smul,hp]
  | hl p q hp hq => simp only [LieHom.map_lie,hp,hq]
theorem rename_injective {R : Type*} [CommRing R] (e : α ≃ β) :
    Function.Injective (rename (R:=R) e) := Function.LeftInverse.injective (rename_symm e)
theorem cast_rename (e : α ≃ β) (p : T ℤ α) :
    cast (S:=S) (rename e p)=rename e (cast p) := by
  induction p using induction with
  | h0 => simp
  | ht i j => simp
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [map_smul,hp]
  | hl p q hp hq => simp only [LieHom.map_lie,hp,hq]
variable [DecidableEq α]
omit [DecidableEq α] in
theorem cast_fiber (p : FreeLieAlgebra ℤ α) :
    cast (S:=S) (fiberLie p)=fiberLie (IntegralBaseChange.lie p) := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg a => simp
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [map_smul,hp]
  | hl p q hp hq => simp only [LieHom.map_lie,hp,hq]
omit [DecidableEq α] in
theorem cast_base (p : T ℤ α) : cast (S:=S) (baseLie p)=baseLie (cast p) := by
  induction p using induction with
  | h0 => simp
  | ht i j => simp
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [map_smul,hp]
  | hl p q hp hq => simp only [LieHom.map_lie,hp,hq]
theorem cast_option_injective (h : Function.Injective (cast (S:=ℚ) (α:=α))) :
    Function.Injective (cast (S:=ℚ) (α:=Option α)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro p hp
  have hd : p=fiberLie (toSemidirect p).left+baseLie (toSemidirect p).right := (from_to p).symm
  rw [hd,map_add,cast_fiber,cast_base] at hp
  have he := congrArg (toSemidirect (R:=ℚ) (α:=α)) hp
  rw [map_add,toSemidirect_fiberLie,toSemidirect_baseLie,map_zero] at he
  have hl := congrArg LieAlgebra.SemiDirectSum.left he
  have hr := congrArg LieAlgebra.SemiDirectSum.right he
  simp only [LieAlgebra.SemiDirectSum.add_eq_mk,LieAlgebra.SemiDirectSum.inl_eq_mk,
    LieAlgebra.SemiDirectSum.inr_eq_mk,add_zero,zero_add,LieAlgebra.SemiDirectSum.zero_eq_mk] at hl hr
  have hl0 : (toSemidirect p).left=0 := IntegralBaseChange.lie_rational_injective (hl.trans (map_zero _).symm)
  have hr0 : (toSemidirect p).right=0 := h (hr.trans (map_zero _).symm)
  rw [hd,hl0,hr0,map_zero,map_zero,add_zero]
end

variable {α : Type*}
theorem cast_fin_injective (n : ℕ) : Function.Injective (cast (S:=ℚ) (α:=Fin n)) := by
  induction n with
  | zero =>
    have hz (p : T ℤ (Fin 0)) : p=0 := by
      induction p using induction with
      | h0 => rfl
      | ht i j => exact Fin.elim0 i
      | ha p q hp hq => simp [hp,hq]
      | hs r p hp => simp [hp]
      | hl p q hp hq => simp [hp,hq]
    intro p q _
    rw [hz p,hz q]
  | succ n ih =>
    intro p q h
    apply rename_injective (finSuccEquiv' (0 : Fin (n+1)))
    apply cast_option_injective ih
    rw [cast_rename,cast_rename,h]
theorem cast_finite_injective [Fintype α] : Function.Injective (cast (S:=ℚ) (α:=α)) := by
  intro p q h
  apply rename_injective (Fintype.equivFin α)
  apply cast_fin_injective
  rw [cast_rename,cast_rename,h]

def fromT4 : T4 →ₗ⁅ℚ⁆ T ℚ (Fin 4) :=
  T4Universal.lift (t (R:=ℚ)) t_comm t_self
    (fun i j k l _ hik hil hjk hjl _ => t_disjoint i j k l hik hil hjk hjl) t_three
@[simp] theorem fromT4_t (i j : Fin 4) : fromT4 (DeligneDrinfeld.t i j)=t i j := by
  simp [fromT4]
end GenericBraid

namespace BaseChangeEquations
variable {R : Type*} [CommRing R]
def x : FreeLieAlgebra R Bool := FreeLieAlgebra.of R false
def y : FreeLieAlgebra R Bool := FreeLieAlgebra.of R true
def eval {M : Type*} [LieRing M] [LieAlgebra R M] (a b : M) : FreeLieAlgebra R Bool →ₗ⁅R⁆ M :=
  FreeLieAlgebra.lift R (fun i => if i then b else a)
@[simp] theorem eval_x {M : Type*} [LieRing M] [LieAlgebra R M] (a b : M) : eval (R:=R) a b x=a := by simp [eval,x]
@[simp] theorem eval_y {M : Type*} [LieRing M] [LieAlgebra R M] (a b : M) : eval (R:=R) a b y=b := by simp [eval,y]
def antisymmetry (q : FreeLieAlgebra R Bool) := q+eval y x q
def threeTerm (q : FreeLieAlgebra R Bool) := q+eval y (-x-y) q+eval (-x-y) x q
def pentagon (q : FreeLieAlgebra R Bool) : GenericBraid.T R (Fin 4) :=
  let t := GenericBraid.t (R:=R)
  eval (t 0 1) (t 1 2+t 1 3) q+eval (t 0 2+t 1 2) (t 2 3) q-
    eval (t 1 2) (t 2 3) q-eval (t 0 1+t 0 2) (t 1 3+t 2 3) q-eval (t 0 1) (t 1 2) q

def Equations (q : FreeLieAlgebra R Bool) : Prop :=
  antisymmetry q=0 ∧ threeTerm q=0 ∧ pentagon q=0

theorem pentagon_rational {q : L} (hq : q∈W) : pentagon q=0 := by
  have h := congrArg GenericBraid.fromT4 hq.2.2
  have he (a b : T4) : GenericBraid.fromT4 (DeligneDrinfeld.eval a b q)=
      eval (GenericBraid.fromT4 a) (GenericBraid.fromT4 b) q := by
    have hm : GenericBraid.fromT4.comp (DeligneDrinfeld.eval a b)=
        eval (GenericBraid.fromT4 a) (GenericBraid.fromT4 b) := by
      apply FreeLieAlgebra.hom_ext
      intro i
      cases i <;> simp [eval,DeligneDrinfeld.eval]
    exact LieHom.congr_fun hm q
  simp only [map_add,he,GenericBraid.fromT4_t] at h
  change _ - _ - _ - _ = 0
  rw [h]
  abel

theorem rational {q : L} (hq : q∈W) : Equations q :=
  ⟨hq.1,hq.2.1,pentagon_rational hq⟩

variable {S : Type*} [CommRing S]
theorem cast_eval_lie (a b q : FreeLieAlgebra ℤ Bool) :
    IntegralBaseChange.lie (S:=S) (eval a b q)=
      eval (R:=S) (IntegralBaseChange.lie a) (IntegralBaseChange.lie b) (IntegralBaseChange.lie q) := by
  induction q using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [eval]
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp =>
    rw [map_smul,map_smul]
    simp [map_smul,hp]
  | hl p q hp hq => simp only [LieHom.map_lie,hp,hq]
theorem cast_eval_braid (a b : GenericBraid.T ℤ (Fin 4)) (q : FreeLieAlgebra ℤ Bool) :
    GenericBraid.cast (S:=S) (eval a b q)=
      eval (R:=S) (GenericBraid.cast a) (GenericBraid.cast b) (IntegralBaseChange.lie q) := by
  induction q using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [eval]
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [map_smul,hp]
  | hl p q hp hq => simp only [LieHom.map_lie,hp,hq]
@[simp] theorem cast_x : IntegralBaseChange.lie (x : FreeLieAlgebra ℤ Bool)=(x : FreeLieAlgebra S Bool) := by simp [x]
@[simp] theorem cast_y : IntegralBaseChange.lie (y : FreeLieAlgebra ℤ Bool)=(y : FreeLieAlgebra S Bool) := by simp [y]
theorem cast_antisymmetry (q : FreeLieAlgebra ℤ Bool) :
    IntegralBaseChange.lie (S:=S) (antisymmetry q)=antisymmetry (IntegralBaseChange.lie q) := by
  simp [antisymmetry,cast_eval_lie]
theorem cast_threeTerm (q : FreeLieAlgebra ℤ Bool) :
    IntegralBaseChange.lie (S:=S) (threeTerm q)=threeTerm (IntegralBaseChange.lie q) := by
  simp [threeTerm,cast_eval_lie]
theorem cast_pentagon (q : FreeLieAlgebra ℤ Bool) :
    GenericBraid.cast (S:=S) (pentagon q)=pentagon (IntegralBaseChange.lie q) := by
  simp only [pentagon,map_sub,map_add,cast_eval_braid,GenericBraid.cast_t]

theorem integral_of_rational (q : FreeLieAlgebra ℤ Bool)
    (hq : (IntegralBaseChange.lie q : L)∈W) : Equations q := by
  have h := rational hq
  refine ⟨IntegralBaseChange.lie_rational_injective ?_,IntegralBaseChange.lie_rational_injective ?_,
    GenericBraid.cast_fin_injective 4 ?_⟩
  · rw [cast_antisymmetry,h.1,map_zero]
  · rw [cast_threeTerm,h.2.1,map_zero]
  · rw [cast_pentagon,h.2.2,map_zero]

theorem reduce (q : FreeLieAlgebra ℤ Bool)
    (hq : (IntegralBaseChange.lie q : L)∈W) : Equations (IntegralBaseChange.lie (S:=S) q) := by
  have h := integral_of_rational q hq
  refine ⟨?_,?_,?_⟩
  · rw [← cast_antisymmetry,h.1,map_zero]
  · rw [← cast_threeTerm,h.2.1,map_zero]
  · rw [← cast_pentagon,h.2.2,map_zero]
end BaseChangeEquations

namespace PolynomialOrdering
open AssociativeElimination
open scoped TensorProduct
attribute [local instance] LieRing.ofAssociativeRing
variable {R α β : Type*} [CommRing R]
abbrev V := A R α ⊗[R] A R β
variable (δ : β → α → A R α)
def fiberOp (a : α) : Module.End R (V (R:=R) (α:=α) (β:=β)) :=
  TensorProduct.map (leftMul (atom a)) LinearMap.id
def baseOp (b : β) : Module.End R (V (R:=R) (α:=α) (β:=β)) :=
  TensorProduct.map (deriv (δ b)) LinearMap.id+
    TensorProduct.map LinearMap.id (leftMul (atom b))
def op : Sum α β → Module.End R (V (R:=R) (α:=α) (β:=β)) :=
  Sum.elim fiberOp (baseOp δ)
@[simp] theorem fiberOp_tmul (a : α) (p : A R α) (q : A R β) :
    fiberOp a (p⊗ₜ q)=(atom a*p)⊗ₜ q := rfl
@[simp] theorem baseOp_tmul (b : β) (p : A R α) (q : A R β) :
    baseOp δ b (p⊗ₜ q)=deriv (δ b) p⊗ₜ q+p⊗ₜ (atom b*q) := rfl

def operators : A R (Sum α β) →ₐ[R] Module.End R (V (R:=R) (α:=α) (β:=β)) :=
  lift (op δ)
def normalize : A R (Sum α β) →ₗ[R] V (R:=R) (α:=α) (β:=β) :=
  (LinearMap.applyₗ ((1 : A R α)⊗ₜ (1 : A R β))).comp (operators δ).toLinearMap
@[simp] theorem normalize_one : normalize δ 1=1⊗ₜ 1 := by
  change operators δ 1 (1⊗ₜ 1)=_; simp
@[simp] theorem normalize_atom_mul (s : Sum α β) (p : A R (Sum α β)) :
    normalize δ (atom s*p)=op δ s (normalize δ p) := by
  change operators δ (atom s*p) (1⊗ₜ 1)=_
  rw [map_mul,Module.End.mul_apply]
  simp only [operators,lift_atom]
  rfl

variable {U : Type*} [Ring U] [Algebra R U]
def interpret (f : A R α →ₐ[R] U) (g : A R β →ₐ[R] U) : V (R:=R) (α:=α) (β:=β) →ₗ[R] U :=
  TensorProduct.lift
    { toFun := fun p =>
        { toFun := fun q => f p*g q
          map_add' := by intro q r; simp [mul_add]
          map_smul' := by intro c q; simp }
      map_add' := by intro p r; ext q; simp [add_mul]
      map_smul' := by intro c p; ext q; simp }
@[simp] theorem interpret_tmul (f : A R α →ₐ[R] U) (g : A R β →ₐ[R] U)
    (p : A R α) (q : A R β) : interpret f g (p⊗ₜ q)=f p*g q := rfl

def evaluate (f : A R α →ₐ[R] U) (g : A R β →ₐ[R] U) : A R (Sum α β) →ₐ[R] U :=
  lift (Sum.elim (fun a => f (atom a)) (fun b => g (atom b)))

variable (f : A R α →ₐ[R] U) (g : A R β →ₐ[R] U)
variable (hδ : ∀ b a,g (atom b)*f (atom a)-f (atom a)*g (atom b)=f (δ b a))
include hδ
theorem commutator (b : β) (p : A R α) :
    g (atom b)*f p-f p*g (atom b)=f (deriv (δ b) p) := by
  induction p using QuadraticAlphabet.algebra_induction with
  | h1 => simp
  | ha a => simpa using hδ b a
  | hadd p q hp hq => simp only [map_add,mul_add,add_mul]; rw [← hp,← hq]; abel
  | hs r p hp => simp only [map_smul,mul_smul_comm,smul_mul_assoc,← smul_sub,hp]
  | hm p q hp hq =>
    rw [AssociativeElimination.deriv_mul,map_add,map_mul,map_mul,map_mul,← hp,← hq]
    noncomm_ring

theorem interpret_op (s : Sum α β) (z : V (R:=R) (α:=α) (β:=β)) :
    interpret f g (op δ s z)=evaluate f g (atom s)*interpret f g z := by
  have h : (interpret f g).comp (op δ s)=
      (Algebra.lmul R U (evaluate f g (atom s))).comp (interpret f g) := by
    apply TensorProduct.ext'
    intro p q
    cases s with
    | inl a => simp [op,evaluate,mul_assoc]
    | inr b =>
      simp only [LinearMap.comp_apply,op,Sum.elim_inr,baseOp_tmul,map_add,interpret_tmul,
        evaluate,lift_atom,map_mul]
      change f (deriv (δ b) p)*g q+f p*(g (atom b)*g q)=g (atom b)*(f p*g q)
      rw [← commutator δ f g hδ b p]
      noncomm_ring
  exact LinearMap.congr_fun h z

theorem interpret_operators (p : A R (Sum α β)) (z : V (R:=R) (α:=α) (β:=β)) :
    interpret f g (operators δ p z)=evaluate f g p*interpret f g z := by
  induction p using QuadraticAlphabet.algebra_induction generalizing z with
  | h1 => simp
  | ha s => simpa [operators] using interpret_op δ f g hδ s z
  | hadd p q hp hq => simp [hp,hq,add_mul]
  | hs r p hp => simp [hp]
  | hm p q hp hq => simp only [map_mul,Module.End.mul_apply,hp,hq,mul_assoc]

theorem interpret_normalize (p : A R (Sum α β)) :
    interpret f g (normalize δ p)=evaluate f g p := by
  change interpret f g (operators δ p (1⊗ₜ 1))=_
  rw [interpret_operators δ f g hδ,interpret_tmul,map_one,map_one,mul_one,mul_one]

omit hδ
def fiberIn : A R α →ₐ[R] A R (Sum α β) := lift (fun a => atom (.inl a))
def baseIn : A R β →ₐ[R] A R (Sum α β) := lift (fun b => atom (.inr b))
theorem operators_fiber : (operators δ).comp fiberIn=
    (Module.End.rTensorAlgHom R (A R α) (A R β)).comp leftMul := by
  apply hom_ext
  intro a
  simp only [AlgHom.comp_apply,fiberIn,lift_atom,operators]
  rfl

theorem operators_base_one (q b : A R β) :
    operators δ (baseIn q) ((1 : A R α)⊗ₜ b)=1⊗ₜ (q*b) := by
  induction q using QuadraticAlphabet.algebra_induction generalizing b with
  | h1 => simp
  | ha a =>
    simp only [baseIn,lift_atom,operators,op,Sum.elim_inr,baseOp_tmul,AssociativeElimination.deriv_one,
      TensorProduct.zero_tmul,zero_add]
  | hadd p q hp hq => simp [hp,hq,add_mul,TensorProduct.tmul_add]
  | hs r p hp => simp [hp,TensorProduct.tmul_smul]
  | hm p q hp hq => simp only [map_mul,Module.End.mul_apply,hq,hp,mul_assoc]

theorem normalize_product (p : A R α) (q : A R β) :
    normalize δ (fiberIn p*baseIn q)=p⊗ₜ q := by
  change operators δ (fiberIn p*baseIn q) (1⊗ₜ (1 : A R β))=_
  rw [map_mul,Module.End.mul_apply,operators_base_one,mul_one]
  have h := AlgHom.congr_fun (operators_fiber δ) p
  simp only [AlgHom.comp_apply] at h
  rw [h]
  change (p*1)⊗ₜ q=p⊗ₜ q
  rw [mul_one]
end PolynomialOrdering

namespace WordGrading
open AssociativeElimination
variable {R α : Type*} [CommRing R]
def word (w : FreeMonoid α) : A R α := MonoidAlgebra.single w 1
@[simp] theorem word_one : word (1 : FreeMonoid α)=(1 : A R α) := rfl
@[simp] theorem word_of (a : α) : word (FreeMonoid.of a)=(atom a : A R α) := rfl
@[simp] theorem word_mul (u v : FreeMonoid α) : word (R:=R) (u*v)=word u*word v := by
  simp [word,MonoidAlgebra.single_mul_single]
def space (P : FreeMonoid α → Prop) : Submodule R (A R α) :=
  Submodule.span R {p | ∃ w,P w ∧ p=word w}
theorem word_mem {P : FreeMonoid α → Prop} (w : FreeMonoid α) (hw : P w) : word (R:=R) w∈space P :=
  Submodule.subset_span ⟨w,hw,rfl⟩
theorem space_mono {P Q : FreeMonoid α → Prop} (h : ∀ w,P w → Q w) :
    space (R:=R) P ≤ space Q := by
  apply Submodule.span_le.mpr
  rintro _ ⟨w,hw,rfl⟩
  exact word_mem w (h w hw)
theorem coeff_support {P : FreeMonoid α → Prop} {p : A R α} (hp : p∈space P)
    (w : FreeMonoid α) (hw : ¬P w) : p.coeff w=0 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨v,hv,rfl⟩ := hp
    have hne : v≠w := fun h => hw (h ▸ hv)
    simp [word,hne]
  | zero => simp
  | add p q _ _ hp hq => simp [hp,hq]
  | smul c p _ hp => simp [hp]
theorem mem_space {P : FreeMonoid α → Prop} {p : A R α}
    (h : ∀ w,p.coeff w≠0 → P w) : p∈space P := by
  classical
  rw [← MonoidAlgebra.sum_coeff_single p]
  apply Submodule.sum_mem
  intro w hw
  have hp := h w (Finsupp.mem_support_iff.mp hw)
  have he : MonoidAlgebra.single w (p.coeff w)=p.coeff w • word (R:=R) w := by simp [word]
  rw [he]
  exact (space P).smul_mem _ (word_mem w hp)
theorem mem_space_iff {P : FreeMonoid α → Prop} {p : A R α} :
    p∈space P ↔ ∀ w,p.coeff w≠0 → P w := by
  constructor
  · intro hp w hw
    by_contra h
    exact hw (coeff_support hp w h)
  · exact mem_space

theorem mul_mem {P Q T : FreeMonoid α → Prop} (h : ∀ u v,P u → Q v → T (u*v))
    {p q : A R α} (hp : p∈space P) (hq : q∈space Q) : p*q∈space T := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u,hu,rfl⟩ := hp
    induction hq using Submodule.span_induction with
    | mem q hq => obtain ⟨v,hv,rfl⟩ := hq; rw [← word_mul]; exact word_mem _ (h u v hu hv)
    | zero => simp
    | add p q _ _ hp hq => simpa only [mul_add] using (space T).add_mem hp hq
    | smul c p _ hp => simpa only [mul_smul_comm] using (space T).smul_mem c hp
  | zero => simp
  | add p q _ _ hp hq => simpa only [add_mul] using (space T).add_mem hp hq
  | smul c p _ hp => simpa only [smul_mul_assoc] using (space T).smul_mem c hp

def project (P : FreeMonoid α → Prop) [DecidablePred P] : A R α →ₗ[R] A R α :=
  (Finsupp.linearCombination R (fun w => if P w then word w else 0)).comp
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap
@[simp] theorem project_word (P : FreeMonoid α → Prop) [DecidablePred P] (w : FreeMonoid α) :
    project (R:=R) P (word w)=if P w then word w else 0 := by
  change Finsupp.linearCombination R (fun monoidWord => if P monoidWord then word monoidWord else 0) (Finsupp.single w 1) = _; simp
theorem project_coeff (P : FreeMonoid α → Prop) [DecidablePred P] (p : A R α) (w : FreeMonoid α) :
    (project P p).coeff w=if P w then p.coeff w else 0 := by
  classical
  induction p using MonoidAlgebra.induction_on with
  | of v =>
    change (project P (word v)).coeff w=_
    rw [project_word]
    by_cases hv : P v <;> by_cases hw : P w <;> simp [hv,hw,word]
    · apply Finsupp.single_eq_of_ne
      intro h
      exact hw (h ▸ hv)
    · symm
      apply Finsupp.single_eq_of_ne
      intro h
      exact hv (h ▸ hw)
  | add p q hp hq => simp only [map_add,MonoidAlgebra.coeff_add,Finsupp.add_apply,hp,hq]; split_ifs <;> simp
  | smul c p hp => simp only [map_smul,MonoidAlgebra.coeff_smul,Finsupp.smul_apply,hp]; split_ifs <;> simp

theorem project_mem (P : FreeMonoid α → Prop) [DecidablePred P] (p : A R α) : project P p∈space P := by
  apply mem_space
  intro w hw
  by_contra hn
  exact hw (by rw [project_coeff,ite_eq_right hn])
theorem project_eq_self {P : FreeMonoid α → Prop} [DecidablePred P] {p : A R α}
    (hp : p∈space P) : project P p=p := by
  ext w
  rw [project_coeff]
  split_ifs with h
  · rfl
  · exact (coeff_support hp w h).symm
theorem project_eq_zero {P Q : FreeMonoid α → Prop} [DecidablePred Q] {p : A R α}
    (hp : p∈space P) (h : ∀ w,P w → ¬Q w) : project Q p=0 := by
  ext w
  rw [project_coeff]
  split_ifs with hw
  · exact coeff_support hp w (fun hp => h w hp hw)
  · rfl

def degree (wt : α → ℕ) (w : FreeMonoid α) : ℕ := (w.toList.map wt).sum
@[simp] theorem degree_one (wt : α → ℕ) : degree wt 1=0 := rfl
@[simp] theorem degree_of (wt : α → ℕ) (a : α) : degree wt (FreeMonoid.of a)=wt a := by simp [degree]
@[simp] theorem degree_mul (wt : α → ℕ) (u v : FreeMonoid α) : degree wt (u*v)=degree wt u+degree wt v := by
  simp [degree]
def homogeneous (wt : α → ℕ) (n : ℕ) := space (R:=R) (fun w => degree wt w=n)
def above (wt : α → ℕ) (n : ℕ) := space (R:=R) (fun w => n≤degree wt w)
def below (wt : α → ℕ) (n : ℕ) := space (R:=R) (fun w => degree wt w≤n)
def piece (wt : α → ℕ) (n : ℕ) : A R α →ₗ[R] A R α := project (fun w => degree wt w=n)
theorem homogeneous_mul {wt : α → ℕ} {n m : ℕ} {p q : A R α}
    (hp : p∈homogeneous wt n) (hq : q∈homogeneous wt m) : p*q∈homogeneous wt (n+m) :=
  mul_mem (by intros; simp_all) hp hq
theorem above_mul {wt : α → ℕ} {n m : ℕ} {p q : A R α}
    (hp : p∈above wt n) (hq : q∈above wt m) : p*q∈above wt (n+m) :=
  mul_mem (by intros; simp_all; omega) hp hq
theorem below_mul {wt : α → ℕ} {n m : ℕ} {p q : A R α}
    (hp : p∈below wt n) (hq : q∈below wt m) : p*q∈below wt (n+m) :=
  mul_mem (by intros; simp_all; omega) hp hq
theorem map_space {M : Type*} [AddCommGroup M] [Module R M]
    {P : FreeMonoid α → Prop} (f : A R α →ₗ[R] M) (T : Submodule R M)
    (h : ∀ w,P w → f (word w)∈T) {p : A R α} (hp : p∈space P) : f p∈T := by
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨w,hw,rfl⟩ := hp; exact h w hw
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using T.add_mem hp hq
  | smul c p _ hp => simpa only [map_smul] using T.smul_mem c hp

theorem deriv_homogeneous {wt : α → ℕ} {c : ℕ} {f : α → A R α}
    (hf : ∀ a,f a∈homogeneous wt (wt a+c)) {n : ℕ} {p : A R α}
    (hp : p∈homogeneous wt n) : deriv f p∈homogeneous wt (n+c) := by
  have hw (w : FreeMonoid α) : deriv f (word w)∈homogeneous wt (degree wt w+c) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      rw [word_mul,word_of,AssociativeElimination.deriv_mul,deriv_atom]
      have h1 := homogeneous_mul (hf a) (word_mem (R:=R) w rfl : word w∈homogeneous wt (degree wt w))
      have h2 := homogeneous_mul (word_mem (R:=R) (FreeMonoid.of a) (degree_of wt a) : atom a∈homogeneous wt (wt a)) ih
      simp only [degree_mul,degree_of]
      apply (homogeneous wt (wt a+degree wt w+c)).add_mem
      · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
      · simpa only [word_of,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2
  exact map_space (deriv f) _ (by intro w hw'; simpa only [hw'] using hw w) hp

theorem homogeneous_above {wt : α → ℕ} {n : ℕ} {p : A R α}
    (hp : p∈homogeneous wt n) : p∈above wt n := space_mono (by intros; omega) hp
theorem homogeneous_below {wt : α → ℕ} {n : ℕ} {p : A R α}
    (hp : p∈homogeneous wt n) : p∈below wt n := space_mono (by intros; omega) hp

theorem deriv_above {wt : α → ℕ} {c : ℕ} {f : α → A R α}
    (hf : ∀ a,f a∈above wt (wt a+c)) {n : ℕ} {p : A R α}
    (hp : p∈above wt n) : deriv f p∈above wt (n+c) := by
  have hw (w : FreeMonoid α) : deriv f (word w)∈above wt (degree wt w+c) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      rw [word_mul,word_of,AssociativeElimination.deriv_mul,deriv_atom]
      have h1 := above_mul (hf a) (homogeneous_above (word_mem (R:=R) w rfl : word w∈homogeneous wt (degree wt w)))
      have h2 := above_mul (homogeneous_above (word_mem (R:=R) (FreeMonoid.of a) (degree_of wt a) : atom a∈homogeneous wt (wt a))) ih
      simp only [degree_mul,degree_of]
      apply (above wt (wt a+degree wt w+c)).add_mem
      · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
      · simpa only [word_of,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2
  apply map_space (deriv f) _ ?_ hp
  intro w hn
  exact space_mono (by intro v hv; omega) (hw w)

theorem deriv_below {wt : α → ℕ} {c : ℕ} {f : α → A R α}
    (hf : ∀ a,f a∈below wt (wt a+c)) {n : ℕ} {p : A R α}
    (hp : p∈below wt n) : deriv f p∈below wt (n+c) := by
  have hw (w : FreeMonoid α) : deriv f (word w)∈below wt (degree wt w+c) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      rw [word_mul,word_of,AssociativeElimination.deriv_mul,deriv_atom]
      have h1 := below_mul (hf a) (homogeneous_below (word_mem (R:=R) w rfl : word w∈homogeneous wt (degree wt w)))
      have h2 := below_mul (homogeneous_below (word_mem (R:=R) (FreeMonoid.of a) (degree_of wt a) : atom a∈homogeneous wt (wt a))) ih
      simp only [degree_mul,degree_of]
      apply (below wt (wt a+degree wt w+c)).add_mem
      · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
      · simpa only [word_of,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2
  apply map_space (deriv f) _ ?_ hp
  intro w hn
  exact space_mono (by intro v hv; omega) (hw w)

theorem deriv_sub (f g : α → A R α) (p : A R α) : deriv (fun a => f a-g a) p=deriv f p-deriv g p := by
  have hw (w : FreeMonoid α) : deriv (fun a => f a-g a) (word w)=deriv f (word w)-deriv g (word w) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      simp only [word_mul,word_of,AssociativeElimination.deriv_mul,deriv_atom,ih,mul_sub,sub_mul]
      abel
  induction p using MonoidAlgebra.induction_on with
  | of w => exact hw w
  | add p q hp hq => simp only [map_add,hp,hq]; abel
  | smul c p hp => simp only [map_smul,hp,smul_sub]
end WordGrading

namespace TriangularWords
open AssociativeElimination WordGrading
variable {R α V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
def action (f : α → Module.End R V) : A R α →ₐ[R] Module.End R V := lift f
@[simp] theorem action_atom (f : α → Module.End R V) (a : α) : action f (atom a)=f a := lift_atom f a

def apply (f : α → Module.End R V) (v : V) : A R α →ₗ[R] V :=
  (LinearMap.applyₗ v).comp (action f).toLinearMap
@[simp] theorem apply_word_one (f : α → Module.End R V) (v : V) : apply f v (word 1)=v := by simp [apply]
@[simp] theorem apply_word_cons (f : α → Module.End R V) (v : V) (a : α) (w : FreeMonoid α) :
    apply f v (word (FreeMonoid.of a*w))=f a (apply f v (word w)) := by
  simp [apply,Module.End.mul_apply]

theorem comparison (wt : α → ℕ) (H E : ℕ → Submodule R V)
    (f g : α → Module.End R V) (v : V) (hv : v∈H 0)
    (hg : ∀ a n z,z∈H n → g a z∈H (wt a+n))
    (hf : ∀ a n z,z∈E n → f a z∈E (wt a+n))
    (hfg : ∀ a n z,z∈H n → f a z-g a z∈E (wt a+n))
    {n : ℕ} {p : A R α} (hp : p∈homogeneous wt n) :
    apply g v p∈H n ∧ apply f v p-apply g v p∈E n := by
  have hw (w : FreeMonoid α) : apply g v (word w)∈H (degree wt w) ∧
      apply f v (word w)-apply g v (word w)∈E (degree wt w) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simpa [apply] using And.intro hv ((E 0).zero_mem)
    | of_mul a w ih =>
      simp only [degree_mul,degree_of,apply_word_cons]
      refine ⟨hg a _ _ ih.1,?_⟩
      have h1 := hf a _ _ ih.2
      have h2 := hfg a _ _ ih.1
      have he : f a (apply f v (word w))-g a (apply g v (word w))=
          f a (apply f v (word w)-apply g v (word w))+
          (f a (apply g v (word w))-g a (apply g v (word w))) := by rw [map_sub]; abel
      rw [he]
      exact (E _).add_mem h1 h2
  constructor
  · exact map_space (apply g v) _ (by intro w hw'; simpa only [hw'] using (hw w).1) hp
  · exact map_space (apply f v-apply g v) _ (by intro w hw'; simpa only [hw',LinearMap.sub_apply] using (hw w).2) hp
end TriangularWords
namespace WordGrading
open AssociativeElimination
variable {R α : Type*} [CommRing R]
def strictlyBelow (wt : α → ℕ) (n : ℕ) := space (R:=R) (fun w => degree wt w<n)
theorem homogeneous_mul_strictlyBelow {wt : α → ℕ} {n m : ℕ} {p q : A R α}
    (hp : p∈homogeneous wt n) (hq : q∈strictlyBelow wt m) : p*q∈strictlyBelow wt (n+m) :=
  mul_mem (by intros; simp_all) hp hq
theorem strictlyBelow_mul_homogeneous {wt : α → ℕ} {n m : ℕ} {p q : A R α}
    (hp : p∈strictlyBelow wt n) (hq : q∈homogeneous wt m) : p*q∈strictlyBelow wt (n+m) :=
  mul_mem (by intros; simp_all) hp hq

theorem deriv_strictlyBelow {wt : α → ℕ} {c : ℕ} {f : α → A R α}
    (hf : ∀ a,f a∈strictlyBelow wt (wt a+c)) {n : ℕ} {p : A R α}
    (hp : p∈homogeneous wt n) : deriv f p∈strictlyBelow wt (n+c) := by
  have hw (w : FreeMonoid α) : deriv f (word w)∈strictlyBelow wt (degree wt w+c) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      rw [word_mul,word_of,AssociativeElimination.deriv_mul,deriv_atom]
      have h1 := strictlyBelow_mul_homogeneous (hf a) (word_mem (R:=R) w rfl : word w∈homogeneous wt (degree wt w))
      have h2 := homogeneous_mul_strictlyBelow (word_mem (R:=R) (FreeMonoid.of a) (degree_of wt a) : atom a∈homogeneous wt (wt a)) ih
      simp only [degree_mul,degree_of]
      apply (strictlyBelow wt (wt a+degree wt w+c)).add_mem
      · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
      · simpa only [word_of,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2
  exact map_space (deriv f) _ (by intro w hw'; simpa only [hw'] using hw w) hp
end WordGrading
namespace TensorGrading
open AssociativeElimination WordGrading
open scoped TensorProduct
variable {R α β : Type*} [CommRing R]
abbrev V := A R α ⊗[R] A R β
def space (P : FreeMonoid α → FreeMonoid β → Prop) : Submodule R (V (R:=R) (α:=α) (β:=β)) :=
  Submodule.span R {z | ∃ u v,P u v ∧ z=word u⊗ₜ word v}
theorem tmul_word_mem {P : FreeMonoid α → FreeMonoid β → Prop} (u : FreeMonoid α) (v : FreeMonoid β)
    (h : P u v) : word (R:=R) u⊗ₜ word (R:=R) v∈space P :=
  Submodule.subset_span ⟨u,v,h,rfl⟩
theorem space_mono {P Q : FreeMonoid α → FreeMonoid β → Prop} (h : ∀ u v,P u v → Q u v) :
    space (R:=R) P ≤ space Q := by
  apply Submodule.span_le.mpr
  rintro _ ⟨u,v,huv,rfl⟩
  exact tmul_word_mem u v (h u v huv)
theorem tmul_mem {P : FreeMonoid α → Prop} {Q : FreeMonoid β → Prop}
    {T : FreeMonoid α → FreeMonoid β → Prop} (h : ∀ u v,P u → Q v → T u v)
    {p : A R α} {q : A R β} (hp : p∈WordGrading.space P) (hq : q∈WordGrading.space Q) :
    p⊗ₜ q∈space T := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u,hu,rfl⟩ := hp
    induction hq using Submodule.span_induction with
    | mem q hq => obtain ⟨v,hv,rfl⟩ := hq; exact tmul_word_mem _ _ (h u v hu hv)
    | zero => simp
    | add p q _ _ hp hq => simpa only [TensorProduct.tmul_add] using (space T).add_mem hp hq
    | smul c p _ hp => simpa only [TensorProduct.tmul_smul] using (space T).smul_mem c hp
  | zero => simp
  | add p q _ _ hp hq => simpa only [TensorProduct.add_tmul] using (space T).add_mem hp hq
  | smul c p _ hp => simpa only [TensorProduct.smul_tmul'] using (space T).smul_mem c hp

def homogeneous (wa : α → ℕ) (wb : β → ℕ) (n : ℕ) :=
  space (R:=R) (fun u v => degree wa u+degree wb v=n)
def above (wa : α → ℕ) (wb : β → ℕ) (n : ℕ) :=
  space (R:=R) (fun u v => n≤degree wa u+degree wb v)
def below (wa : α → ℕ) (wb : β → ℕ) (n : ℕ) :=
  space (R:=R) (fun u v => degree wa u+degree wb v≤n)
def strictlyBelow (wa : α → ℕ) (wb : β → ℕ) (n : ℕ) :=
  space (R:=R) (fun u v => degree wa u+degree wb v<n)

theorem map_space {M : Type*} [AddCommGroup M] [Module R M] (f : V (R:=R) (α:=α) (β:=β) →ₗ[R] M)
    {P : FreeMonoid α → FreeMonoid β → Prop} (Q : Submodule R M)
    (hf : ∀ u v,P u v → f (word u⊗ₜ word v)∈Q) {p : V (R:=R) (α:=α) (β:=β)} (hp : p∈space P) : f p∈Q := by
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨u,v,h,rfl⟩ := hp; exact hf u v h
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using Q.add_mem hp hq
  | smul c p _ hp => simpa only [map_smul] using Q.smul_mem c hp

theorem homo_tmul {wa : α → ℕ} {wb : β → ℕ} {n m : ℕ} {p : A R α} {q : A R β}
    (hp : p∈WordGrading.homogeneous wa n) (hq : q∈WordGrading.homogeneous wb m) :
    p⊗ₜ q∈homogeneous wa wb (n+m) := tmul_mem (by intros; simp_all) hp hq
theorem above_tmul {wa : α → ℕ} {wb : β → ℕ} {n m : ℕ} {p : A R α} {q : A R β}
    (hp : p∈WordGrading.above wa n) (hq : q∈WordGrading.above wb m) :
    p⊗ₜ q∈above wa wb (n+m) := tmul_mem (by intros; omega) hp hq
theorem below_tmul {wa : α → ℕ} {wb : β → ℕ} {n m : ℕ} {p : A R α} {q : A R β}
    (hp : p∈WordGrading.below wa n) (hq : q∈WordGrading.below wb m) :
    p⊗ₜ q∈below wa wb (n+m) := tmul_mem (by intros; omega) hp hq
theorem strict_homo_tmul {wa : α → ℕ} {wb : β → ℕ} {n m : ℕ} {p : A R α} {q : A R β}
    (hp : p∈WordGrading.strictlyBelow wa n) (hq : q∈WordGrading.homogeneous wb m) :
    p⊗ₜ q∈strictlyBelow wa wb (n+m) := tmul_mem (by intros; omega) hp hq

variable {wa : α → ℕ} {wb : β → ℕ} {δ : β → α → A R α}
theorem op_homogeneous (hδ : ∀ b a,δ b a∈WordGrading.homogeneous wa (wb b+wa a))
    (s : Sum α β) {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈homogeneous wa wb n) :
    PolynomialOrdering.op δ s z∈homogeneous wa wb (Sum.elim wa wb s+n) := by
  apply map_space (PolynomialOrdering.op δ s) _ ?_ hz
  intro u v huv
  have hu : word (R:=R) u∈WordGrading.homogeneous wa (degree wa u) := word_mem u rfl
  have hv : word (R:=R) v∈WordGrading.homogeneous wb (degree wb v) := word_mem v rfl
  cases s with
  | inl a =>
    have ha : atom (R:=R) a∈WordGrading.homogeneous wa (wa a) := word_mem (FreeMonoid.of a) (degree_of wa a)
    have h := homo_tmul (WordGrading.homogeneous_mul ha hu) hv
    simpa only [PolynomialOrdering.op,Sum.elim_inl,PolynomialOrdering.fiberOp_tmul,← huv,Nat.add_assoc] using h
  | inr b =>
    have hd := WordGrading.deriv_homogeneous (c:=wb b) (f:=δ b) (by intro a; simpa only [Nat.add_comm] using hδ b a) hu
    have hb : atom (R:=R) b∈WordGrading.homogeneous wb (wb b) := word_mem (FreeMonoid.of b) (degree_of wb b)
    have h1 := homo_tmul hd hv
    have h2 := homo_tmul hu (WordGrading.homogeneous_mul hb hv)
    change deriv (δ b) (word u)⊗ₜ word v+word u⊗ₜ (atom b*word v)∈homogeneous wa wb (wb b+n)
    apply (homogeneous wa wb (wb b+n)).add_mem
    · simpa only [← huv,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
    · simpa only [← huv,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2

theorem op_above (hδ : ∀ b a,δ b a∈WordGrading.above wa (wb b+wa a))
    (s : Sum α β) {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈above wa wb n) :
    PolynomialOrdering.op δ s z∈above wa wb (Sum.elim wa wb s+n) := by
  apply map_space (PolynomialOrdering.op δ s) _ ?_ hz
  intro u v huv
  have hu : word (R:=R) u∈WordGrading.above wa (degree wa u) := word_mem u (by rfl)
  have hv : word (R:=R) v∈WordGrading.above wb (degree wb v) := word_mem v (by rfl)
  cases s with
  | inl a =>
    have ha : atom (R:=R) a∈WordGrading.above wa (wa a) := word_mem (FreeMonoid.of a) (by simp)
    have h := above_tmul (WordGrading.above_mul ha hu) hv
    have hm : above (R:=R) wa wb (wa a+degree wa u+degree wb v) ≤ above wa wb (wa a+n) :=
      space_mono (by intro u' v' hh; change n ≤ degree wa u+degree wb v at huv; omega)
    exact hm h
  | inr b =>
    have hd := WordGrading.deriv_above (c:=wb b) (f:=δ b) (by intro a; simpa only [Nat.add_comm] using hδ b a) hu
    have hb : atom (R:=R) b∈WordGrading.above wb (wb b) := word_mem (FreeMonoid.of b) (by simp)
    have h1 := above_tmul hd hv
    have h2 := above_tmul hu (WordGrading.above_mul hb hv)
    have hm : above (R:=R) wa wb (degree wa u+degree wb v+wb b) ≤ above wa wb (wb b+n) :=
      space_mono (by intro u' v' hh; change n ≤ degree wa u+degree wb v at huv; omega)
    change deriv (δ b) (word u)⊗ₜ word v+word u⊗ₜ (atom b*word v)∈above wa wb (wb b+n)
    apply ( above wa wb (wb b+n)).add_mem
    · apply hm; simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
    · apply hm; simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2

theorem op_below (hδ : ∀ b a,δ b a∈WordGrading.below wa (wb b+wa a))
    (s : Sum α β) {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈below wa wb n) :
    PolynomialOrdering.op δ s z∈below wa wb (Sum.elim wa wb s+n) := by
  apply map_space (PolynomialOrdering.op δ s) _ ?_ hz
  intro u v huv
  have hu : word (R:=R) u∈WordGrading.below wa (degree wa u) := word_mem u (by rfl)
  have hv : word (R:=R) v∈WordGrading.below wb (degree wb v) := word_mem v (by rfl)
  cases s with
  | inl a =>
    have ha : atom (R:=R) a∈WordGrading.below wa (wa a) := word_mem (FreeMonoid.of a) (by simp)
    have h := below_tmul (WordGrading.below_mul ha hu) hv
    have hm : below (R:=R) wa wb (wa a+degree wa u+degree wb v) ≤ below wa wb (wa a+n) :=
      space_mono (by intro u' v' hh; change degree wa u+degree wb v ≤ n at huv; omega)
    exact hm h
  | inr b =>
    have hd := WordGrading.deriv_below (c:=wb b) (f:=δ b) (by intro a; simpa only [Nat.add_comm] using hδ b a) hu
    have hb : atom (R:=R) b∈WordGrading.below wb (wb b) := word_mem (FreeMonoid.of b) (by simp)
    have h1 := below_tmul hd hv
    have h2 := below_tmul hu (WordGrading.below_mul hb hv)
    have hm : below (R:=R) wa wb (degree wa u+degree wb v+wb b) ≤ below wa wb (wb b+n) :=
      space_mono (by intro u' v' hh; change degree wa u+degree wb v ≤ n at huv; omega)
    change deriv (δ b) (word u)⊗ₜ word v+word u⊗ₜ (atom b*word v)∈below wa wb (wb b+n)
    apply ( below wa wb (wb b+n)).add_mem
    · apply hm; simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
    · apply hm; simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2

theorem op_strictlyBelow (hδ : ∀ b a,δ b a∈WordGrading.below wa (wb b+wa a))
    (s : Sum α β) {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈strictlyBelow wa wb n) :
    PolynomialOrdering.op δ s z∈strictlyBelow wa wb (Sum.elim wa wb s+n) := by
  apply map_space (PolynomialOrdering.op δ s) _ ?_ hz
  intro u v huv
  have hh : word (R:=R) u⊗ₜ word (R:=R) v∈below wa wb (degree wa u+degree wb v) := tmul_word_mem u v (by rfl)
  have h := op_below hδ s hh
  have hm : below (R:=R) wa wb (Sum.elim wa wb s+(degree wa u+degree wb v)) ≤
      strictlyBelow wa wb (Sum.elim wa wb s+n) :=
    space_mono (by intro u' v' hh; change degree wa u+degree wb v<n at huv; omega)
  exact hm h

variable {δ₀ : β → α → A R α}
theorem op_difference (s : Sum α β) (u : FreeMonoid α) (v : FreeMonoid β) :
    (PolynomialOrdering.op δ s-PolynomialOrdering.op δ₀ s) (word u⊗ₜ word v)=
    Sum.elim (fun _ => 0) (fun b => deriv (fun a => δ b a-δ₀ b a) (word u)⊗ₜ word v) s := by
  cases s with
  | inl a => simp [PolynomialOrdering.op]
  | inr b =>
    simp only [PolynomialOrdering.op,Sum.elim_inr,LinearMap.sub_apply,PolynomialOrdering.baseOp_tmul,
      WordGrading.deriv_sub,TensorProduct.sub_tmul]
    abel

theorem op_difference_above (hδ : ∀ b a,δ b a-δ₀ b a∈WordGrading.above wa (wb b+wa a+1))
    (s : Sum α β) {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈homogeneous wa wb n) :
    PolynomialOrdering.op δ s z-PolynomialOrdering.op δ₀ s z∈above wa wb (Sum.elim wa wb s+n+1) := by
  apply map_space (PolynomialOrdering.op δ s-PolynomialOrdering.op δ₀ s) _ ?_ hz
  intro u v huv
  rw [op_difference]
  cases s with
  | inl a => exact (above wa wb _).zero_mem
  | inr b =>
    have hu : word (R:=R) u∈WordGrading.above wa (degree wa u) := word_mem u (by rfl)
    have hv : word (R:=R) v∈WordGrading.above wb (degree wb v) := word_mem v (by rfl)
    have hd := WordGrading.deriv_above (c:=wb b+1) (f:=fun a => δ b a-δ₀ b a)
      (by intro a; simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hδ b a) hu
    have hh := above_tmul hd hv
    simpa only [Sum.elim_inr,← huv,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem op_difference_below (hδ : ∀ b a,δ b a-δ₀ b a∈WordGrading.strictlyBelow wa (wb b+wa a))
    (s : Sum α β) {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈homogeneous wa wb n) :
    PolynomialOrdering.op δ s z-PolynomialOrdering.op δ₀ s z∈strictlyBelow wa wb (Sum.elim wa wb s+n) := by
  apply map_space (PolynomialOrdering.op δ s-PolynomialOrdering.op δ₀ s) _ ?_ hz
  intro u v huv
  rw [op_difference]
  cases s with
  | inl a => exact (strictlyBelow wa wb _).zero_mem
  | inr b =>
    have hu : word (R:=R) u∈WordGrading.homogeneous wa (degree wa u) := word_mem u rfl
    have hv : word (R:=R) v∈WordGrading.homogeneous wb (degree wb v) := word_mem v rfl
    have hd := WordGrading.deriv_strictlyBelow (c:=wb b) (f:=fun a => δ b a-δ₀ b a)
      (by intro a; simpa only [Nat.add_comm] using hδ b a) hu
    have hh := strict_homo_tmul hd hv
    simpa only [Sum.elim_inr,← huv,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem comparison_above (h0 : ∀ b a,δ₀ b a∈WordGrading.homogeneous wa (wb b+wa a))
    (hδ : ∀ b a,δ b a∈WordGrading.above wa (wb b+wa a))
    (hd : ∀ b a,δ b a-δ₀ b a∈WordGrading.above wa (wb b+wa a+1))
    {n : ℕ} {p : A R (Sum α β)} (hp : p∈WordGrading.homogeneous (Sum.elim wa wb) n) :
    PolynomialOrdering.normalize δ₀ p∈homogeneous wa wb n ∧
    PolynomialOrdering.normalize δ p-PolynomialOrdering.normalize δ₀ p∈above wa wb (n+1) := by
  apply TriangularWords.comparison (Sum.elim wa wb) (homogeneous wa wb) (fun n => above wa wb (n+1))
    (PolynomialOrdering.op δ) (PolynomialOrdering.op δ₀) (1⊗ₜ 1) ?_ ?_ ?_ ?_ hp
  · exact tmul_word_mem 1 1 (by simp)
  · intro a n z hz; exact op_homogeneous h0 a hz
  · intro a n z hz; simpa only [Nat.add_assoc] using op_above hδ a hz
  · intro a n z hz; exact op_difference_above hd a hz

theorem comparison_below (h0 : ∀ b a,δ₀ b a∈WordGrading.homogeneous wa (wb b+wa a))
    (hδ : ∀ b a,δ b a∈WordGrading.below wa (wb b+wa a))
    (hd : ∀ b a,δ b a-δ₀ b a∈WordGrading.strictlyBelow wa (wb b+wa a))
    {n : ℕ} {p : A R (Sum α β)} (hp : p∈WordGrading.homogeneous (Sum.elim wa wb) n) :
    PolynomialOrdering.normalize δ₀ p∈homogeneous wa wb n ∧
    PolynomialOrdering.normalize δ p-PolynomialOrdering.normalize δ₀ p∈strictlyBelow wa wb n := by
  apply TriangularWords.comparison (Sum.elim wa wb) (homogeneous wa wb) (strictlyBelow wa wb)
    (PolynomialOrdering.op δ) (PolynomialOrdering.op δ₀) (1⊗ₜ 1) ?_ ?_ ?_ ?_ hp
  · exact tmul_word_mem 1 1 (by simp)
  · intro a n z hz; exact op_homogeneous h0 a hz
  · intro a n z hz; exact op_strictlyBelow hδ a hz
  · intro a n z hz; exact op_difference_below hd a hz
end TensorGrading
namespace CountTables

section
open AssociativeElimination
abbrev K := ZMod 2
abbrev F := Fin 5
abbrev B := Fin 4

def H : A K F := atom 0
def U (i : Fin 2) : A K F := atom ⟨i.val+1,by omega⟩
def V (i : Fin 2) : A K F := atom ⟨i.val+3,by omega⟩
def bracket {R α : Type*} [CommRing R] (p q : A R α) := p*q-q*p
def R' (i : Fin 2) := bracket H (U i)
def Q (i : Fin 2) := bracket (H+V i) (U i)
def W := bracket (V 0) (U 1)+bracket (U 0) (V 1)
def common : B → F → A K F
  | 0,0 => bracket H (V 0)
  | 0,1 => Q 0
  | 0,3 => bracket H (V 0)
  | 1,0 => bracket H (V 1)
  | 1,2 => Q 1
  | 1,4 => bracket H (V 1)
  | 2,1 | 2,2 => bracket (U 0) (U 1)
  | 2,3 | 2,4 => W
  | 3,1 => bracket (U 0) (V 1)
  | 3,2 => bracket (U 1) (V 0)
  | 3,3 | 3,4 => bracket (V 0) (V 1)
  | _,_ => 0
def higher : B → F → A K F
  | 0,0 => bracket (R' 0) (U 0)
  | 0,3 => bracket (bracket (V 0) (U 0)) (U 0)
  | 0,4 => bracket (Q 0) (U 1)
  | 1,0 => bracket (R' 1) (U 1)
  | 1,4 => bracket (bracket (V 1) (U 1)) (U 1)
  | 1,3 => bracket (Q 1) (U 0)
  | 3,0 => bracket H (bracket (U 0) (U 1))
  | 3,3 => bracket W (U 0)+bracket (U 0) (R' 1)
  | 3,4 => bracket W (U 1)+bracket (U 1) (R' 0)
  | _,_ => 0
def lower : B → F → A K F
  | 2,3 | 2,4 => bracket (V 0) (V 1)
  | _,_ => 0
def source (b : B) (a : F) := common b a+higher b a
def target (b : B) (a : F) := common b a+lower b a

def fiberCount : F → ℕ | 1 | 2 => 1 | _ => 0
def baseCount : B → ℕ | 2 => 1 | _ => 0

open WordGrading

theorem bracket_homo {n m : ℕ} {p q : A K F}
    (hp : p∈homogeneous fiberCount n) (hq : q∈homogeneous fiberCount m) :
    bracket p q∈homogeneous fiberCount (n+m) := by
  apply (homogeneous fiberCount (n+m)).sub_mem (homogeneous_mul hp hq)
  simpa only [Nat.add_comm] using homogeneous_mul hq hp

theorem H_homo : H∈homogeneous fiberCount 0 := word_mem (FreeMonoid.of 0) rfl
theorem U_homo (i : Fin 2) : U i∈homogeneous fiberCount 1 := by
  apply word_mem
  fin_cases i <;> rfl
theorem V_homo (i : Fin 2) : V i∈homogeneous fiberCount 0 := by
  apply word_mem
  fin_cases i <;> rfl
theorem R_homo (i : Fin 2) : R' i∈homogeneous fiberCount 1 := by
  have h := bracket_homo H_homo (U_homo i)
  exact h
theorem Q_homo (i : Fin 2) : Q i∈homogeneous fiberCount 1 :=
  by
    have h := bracket_homo ((homogeneous fiberCount 0).add_mem H_homo (V_homo i)) (U_homo i)
    exact h
theorem W_homo : W∈homogeneous fiberCount 1 :=
  by
    have h1 := bracket_homo (V_homo 0) (U_homo 1)
    have h2 := bracket_homo (U_homo 0) (V_homo 1)
    exact (homogeneous fiberCount 1).add_mem h1 h2

theorem common_homo_0 (a : F) : common 0 a∈homogeneous fiberCount (baseCount 0+fiberCount a) := by
  fin_cases a
  · have h := bracket_homo H_homo (V_homo 0)
    exact h
  · have h := Q_homo 0
    exact h
  · exact (homogeneous fiberCount _).zero_mem
  · have h := bracket_homo H_homo (V_homo 0)
    exact h
  · exact (homogeneous fiberCount _).zero_mem
theorem common_homo_1 (a : F) : common 1 a∈homogeneous fiberCount (baseCount 1+fiberCount a) := by
  fin_cases a
  · have h := bracket_homo H_homo (V_homo 1)
    exact h
  · exact (homogeneous fiberCount _).zero_mem
  · have h := Q_homo 1
    exact h
  · exact (homogeneous fiberCount _).zero_mem
  · have h := bracket_homo H_homo (V_homo 1)
    exact h
theorem common_homo_2 (a : F) : common 2 a∈homogeneous fiberCount (baseCount 2+fiberCount a) := by
  fin_cases a
  · exact (homogeneous fiberCount _).zero_mem
  · have h := bracket_homo (U_homo 0) (U_homo 1)
    exact h
  · have h := bracket_homo (U_homo 0) (U_homo 1)
    exact h
  · have h := W_homo
    exact h
  · have h := W_homo
    exact h
theorem common_homo_3 (a : F) : common 3 a∈homogeneous fiberCount (baseCount 3+fiberCount a) := by
  fin_cases a
  · exact (homogeneous fiberCount _).zero_mem
  · have h := bracket_homo (U_homo 0) (V_homo 1)
    exact h
  · have h := bracket_homo (U_homo 1) (V_homo 0)
    exact h
  · have h := bracket_homo (V_homo 0) (V_homo 1)
    exact h
  · have h := bracket_homo (V_homo 0) (V_homo 1)
    exact h
theorem common_homo (b : B) (a : F) : common b a∈homogeneous fiberCount (baseCount b+fiberCount a) := by
  fin_cases b
  · exact common_homo_0 a
  · exact common_homo_1 a
  · exact common_homo_2 a
  · exact common_homo_3 a
theorem higher_homo_0 (a : F) : higher 0 a∈homogeneous fiberCount (baseCount 0+fiberCount a+2) := by
  fin_cases a
  · have h := bracket_homo (R_homo 0) (U_homo 0)
    exact h
  · exact (homogeneous fiberCount _).zero_mem
  · exact (homogeneous fiberCount _).zero_mem
  · have h := bracket_homo (bracket_homo (V_homo 0) (U_homo 0)) (U_homo 0)
    exact h
  · have h := bracket_homo (Q_homo 0) (U_homo 1)
    exact h
theorem higher_homo_1 (a : F) : higher 1 a∈homogeneous fiberCount (baseCount 1+fiberCount a+2) := by
  fin_cases a
  · have h := bracket_homo (R_homo 1) (U_homo 1)
    exact h
  · exact (homogeneous fiberCount _).zero_mem
  · exact (homogeneous fiberCount _).zero_mem
  · have h := bracket_homo (Q_homo 1) (U_homo 0)
    exact h
  · have h := bracket_homo (bracket_homo (V_homo 1) (U_homo 1)) (U_homo 1)
    exact h
theorem higher_homo_2 (a : F) : higher 2 a∈homogeneous fiberCount (baseCount 2+fiberCount a+2) := by
  fin_cases a
  · exact (homogeneous fiberCount _).zero_mem
  · exact (homogeneous fiberCount _).zero_mem
  · exact (homogeneous fiberCount _).zero_mem
  · exact (homogeneous fiberCount _).zero_mem
  · exact (homogeneous fiberCount _).zero_mem
theorem higher_homo_3 (a : F) : higher 3 a∈homogeneous fiberCount (baseCount 3+fiberCount a+2) := by
  fin_cases a
  · have h := bracket_homo H_homo (bracket_homo (U_homo 0) (U_homo 1))
    exact h
  · exact (homogeneous fiberCount _).zero_mem
  · exact (homogeneous fiberCount _).zero_mem
  · have h1 := bracket_homo W_homo (U_homo 0)
    have h2 := bracket_homo (U_homo 0) (R_homo 1)
    exact (homogeneous fiberCount 2).add_mem h1 h2
  · have h1 := bracket_homo W_homo (U_homo 1)
    have h2 := bracket_homo (U_homo 1) (R_homo 0)
    exact (homogeneous fiberCount 2).add_mem h1 h2
theorem higher_homo (b : B) (a : F) : higher b a∈homogeneous fiberCount (baseCount b+fiberCount a+2) := by
  fin_cases b
  · exact higher_homo_0 a
  · exact higher_homo_1 a
  · exact higher_homo_2 a
  · exact higher_homo_3 a

theorem lower_strict (b : B) (a : F) : lower b a∈strictlyBelow fiberCount (baseCount b+fiberCount a) := by
  fin_cases b <;> fin_cases a <;> simp only [lower,baseCount,fiberCount,Nat.reduceAdd]
  all_goals first
    | exact (strictlyBelow fiberCount _).zero_mem
    | exact (space_mono (P:=fun w => degree fiberCount w=0) (Q:=fun w => degree fiberCount w<1)
        (by intros; omega)) (bracket_homo (n:=0) (m:=0) (V_homo 0) (V_homo 1))

theorem source_above (b : B) (a : F) : source b a∈above fiberCount (baseCount b+fiberCount a) := by
  apply (above fiberCount _).add_mem
  · apply space_mono (P:=fun w => degree fiberCount w=baseCount b+fiberCount a) (by intros; omega)
    exact common_homo b a
  · apply space_mono (P:=fun w => degree fiberCount w=baseCount b+fiberCount a+2) (by intros; omega)
    exact higher_homo b a

theorem source_difference (b : B) (a : F) :
    source b a-common b a∈above fiberCount (baseCount b+fiberCount a+1) := by
  rw [source,add_sub_cancel_left]
  apply space_mono (P:=fun w => degree fiberCount w=baseCount b+fiberCount a+2) (by intros; omega)
  exact higher_homo b a

theorem target_below (b : B) (a : F) : target b a∈below fiberCount (baseCount b+fiberCount a) := by
  apply (below fiberCount _).add_mem
  · apply space_mono (P:=fun w => degree fiberCount w=baseCount b+fiberCount a) (by intros; omega)
    exact common_homo b a
  · apply space_mono (P:=fun w => degree fiberCount w<baseCount b+fiberCount a) (by intros; omega)
    exact lower_strict b a

theorem target_difference (b : B) (a : F) :
    target b a-common b a∈strictlyBelow fiberCount (baseCount b+fiberCount a) := by
  rw [target,add_sub_cancel_left]
  exact lower_strict b a

theorem source_comparison {n : ℕ} {p : A K (Sum F B)}
    (hp : p∈homogeneous (Sum.elim fiberCount baseCount) n) :
    PolynomialOrdering.normalize common p∈TensorGrading.homogeneous fiberCount baseCount n ∧
    PolynomialOrdering.normalize source p-PolynomialOrdering.normalize common p∈TensorGrading.above fiberCount baseCount (n+1) :=
  TensorGrading.comparison_above common_homo source_above source_difference hp

theorem target_comparison {n : ℕ} {p : A K (Sum F B)}
    (hp : p∈homogeneous (Sum.elim fiberCount baseCount) n) :
    PolynomialOrdering.normalize common p∈TensorGrading.homogeneous fiberCount baseCount n ∧
    PolynomialOrdering.normalize target p-PolynomialOrdering.normalize common p∈TensorGrading.strictlyBelow fiberCount baseCount n :=
  TensorGrading.comparison_below common_homo target_below target_difference hp
end

open AssociativeElimination
abbrev G := Fin 3
def X : A K G := atom 0
def Y (i : Fin 2) : A K G := atom ⟨i.val+1,by omega⟩
def C (i : Fin 2) := bracket X (Y i)
def realize : A K F →ₐ[K] A K G := lift (fun a => match a with
  | 0 => X*X | 1 => Y 0 | 2 => Y 1 | 3 => C 0 | _ => C 1)
def δ (i : Fin 2) : A K G →ₗ[K] A K G := deriv (fun a => if a=0 ∨ a.val=i.val+1 then C i else 0)
def ε : A K G →ₗ[K] A K G := deriv (fun a => if a=0 then 0 else bracket (Y 0) (Y 1))
def baseDeriv : B → A K G →ₗ[K] A K G
  | 0 => (δ 0).comp (δ 0)
  | 1 => (δ 1).comp (δ 1)
  | 2 => ε
  | _ => (δ 0).comp ε-ε.comp (δ 0)

@[simp] theorem realize_H : realize H=X*X := by simp [realize,H]
@[simp] theorem realize_U (i : Fin 2) : realize (U i)=Y i := by fin_cases i <;> simp [realize,U]
@[simp] theorem realize_V (i : Fin 2) : realize (V i)=C i := by fin_cases i <;> simp [realize,V]
@[simp] theorem realize_bracket (p q : A K F) : realize (bracket p q)=bracket (realize p) (realize q) := by simp [bracket]
@[simp] theorem deriv_bracket {R α : Type*} [CommRing R] (f : α → A R α) (p q : A R α) :
    deriv f (bracket p q)=bracket (deriv f p) q+bracket p (deriv f q) := by
  simp only [bracket,map_sub,AssociativeElimination.deriv_mul]; abel

@[simp] theorem bracket_add_left (p q r : A K G) : bracket (p+q) r=bracket p r+bracket q r := by simp [bracket,add_mul,mul_add]; abel
@[simp] theorem bracket_add_right (p q r : A K G) : bracket p (q+r)=bracket p q+bracket p r := by simp [bracket,add_mul,mul_add]; abel
@[simp] theorem bracket_sub_left (p q r : A K G) : bracket (p-q) r=bracket p r-bracket q r := by simp [bracket,sub_mul,mul_sub]; abel
@[simp] theorem bracket_sub_right (p q r : A K G) : bracket p (q-r)=bracket p q-bracket p r := by simp [bracket,sub_mul,mul_sub]; abel
@[simp] theorem bracket_zero_left (r : A K G) : bracket 0 r=0 := by simp [bracket]
@[simp] theorem bracket_zero_right (r : A K G) : bracket r 0=0 := by simp [bracket]
@[simp] theorem bracket_self (r : A K G) : bracket r r=0 := by simp [bracket]
theorem bracket_swap (p q : A K G) : bracket p q=bracket q p := by simp [bracket,CharTwo.sub_eq_add,add_comm]
theorem bracket_ad_square (u v : A K G) : bracket u (bracket u v)=bracket (u*u) v := by
  simp only [bracket,sub_eq_add_neg,CharTwo.neg_eq,mul_add,add_mul,mul_assoc]
  calc
    _ = u*(u*v)+v*(u*u)+(u*(v*u)+u*(v*u)) := by abel
    _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]
theorem bracket_leibniz (p q r : A K G) : bracket p (bracket q r)=bracket (bracket p q) r+bracket q (bracket p r) := by
  simp only [bracket]; noncomm_ring
@[simp] theorem δ_X (i : Fin 2) : δ i X=C i := by simp [δ,X]
@[simp] theorem δ_Y_self (i : Fin 2) : δ i (Y i)=C i := by simp [δ,Y]
@[simp] theorem δ_Y_other (i j : Fin 2) (h : j≠i) : δ i (Y j)=0 := by
  have hv : j.val≠i.val := fun he => h (Fin.ext he)
  simp [δ,Y,hv]
theorem δ_mul (i : Fin 2) (p q : A K G) : δ i (p*q)=δ i p*q+p*δ i q := deriv_mul _ _ _
@[simp] theorem δ_bracket (i : Fin 2) (p q : A K G) : δ i (bracket p q)=bracket (δ i p) q+bracket p (δ i q) := deriv_bracket _ _ _
@[simp] theorem δ_H (i : Fin 2) : δ i (X*X)=bracket (X*X) (Y i) := by
  rw [δ_mul,δ_X,← bracket_ad_square]
  change C i*X+X*C i=bracket X (C i)
  simp [bracket,CharTwo.sub_eq_add,add_comm]
theorem bracket_X_Y (i : Fin 2) : bracket X (Y i)=C i := rfl
theorem bracket_X_C (i : Fin 2) : bracket X (C i)=bracket (X*X) (Y i) := bracket_ad_square _ _
@[simp] theorem δ_C_self (i : Fin 2) : δ i (C i)=bracket (X*X+C i) (Y i) := by
  change δ i (bracket X (Y i))=_
  rw [δ_bracket,δ_X,δ_Y_self,bracket_X_C,bracket_add_left]
  exact add_comm _ _
@[simp] theorem δ_C_other (i j : Fin 2) (h : j≠i) : δ i (C j)=bracket (C i) (Y j) := by
  rw [C,δ_bracket,δ_X,δ_Y_other i j h,bracket_zero_right,add_zero]
@[simp] theorem ε_X : ε X=0 := by simp [ε,X]
@[simp] theorem ε_Y (i : Fin 2) : ε (Y i)=bracket (Y 0) (Y 1) := by simp [ε,Y]
@[simp] theorem ε_bracket (p q : A K G) : ε (bracket p q)=bracket (ε p) q+bracket p (ε q) := deriv_bracket _ _ _
@[simp] theorem ε_H : ε (X*X)=0 := by simp [ε,AssociativeElimination.deriv_mul,X]
theorem ε_C (i : Fin 2) : ε (C i)=bracket (C 0) (Y 1)+bracket (Y 0) (C 1) := by
  rw [C,ε_bracket,ε_X,ε_Y,bracket_zero_left,zero_add,bracket_leibniz]
  rfl

def J := baseDeriv 3
@[simp] theorem J_X : J X=bracket (C 0) (Y 1)+bracket (Y 0) (C 1) := by
  simp only [J,baseDeriv,LinearMap.sub_apply,LinearMap.comp_apply,ε_X,map_zero,δ_X,ε_C]
  simp only [zero_sub,CharTwo.neg_eq]
@[simp] theorem J_Y_zero : J (Y 0)=bracket (Y 0) (C 1) := by
  simp only [J,baseDeriv,LinearMap.sub_apply,LinearMap.comp_apply,ε_Y,δ_bracket,δ_Y_self,
    δ_Y_other 0 1 (by decide),bracket_zero_right,add_zero,ε_C]
  simp only [sub_add_eq_sub_sub,sub_self,zero_sub,CharTwo.neg_eq]
@[simp] theorem J_Y_one : J (Y 1)=bracket (Y 1) (C 0) := by
  simp only [J,baseDeriv,LinearMap.sub_apply,LinearMap.comp_apply,ε_Y,δ_bracket,δ_Y_self,
    δ_Y_other 0 1 (by decide),bracket_zero_right,add_zero,map_zero,sub_zero]
  exact bracket_swap _ _
@[simp] theorem J_bracket (p q : A K G) : J (bracket p q)=bracket (J p) q+bracket p (J q) := by
  simp only [J,baseDeriv,LinearMap.sub_apply,LinearMap.comp_apply,ε_bracket,δ_bracket,map_add,
    bracket_sub_left,bracket_sub_right]
  abel
@[simp] theorem J_mul (p q : A K G) : J (p*q)=J p*q+p*J q := by
  simp only [J,baseDeriv,LinearMap.sub_apply,LinearMap.comp_apply,ε,δ,AssociativeElimination.deriv_mul,
    map_add,sub_mul,mul_sub]
  abel
@[simp] theorem J_H : J (X*X)=bracket (X*X) (bracket (Y 0) (Y 1)) := by
  rw [J_mul,J_X]
  have h : bracket (C 0) (Y 1)+bracket (Y 0) (C 1)=bracket X (bracket (Y 0) (Y 1)) :=
    (bracket_leibniz X (Y 0) (Y 1)).symm
  rw [h,← bracket_ad_square]
  simp only [bracket,CharTwo.sub_eq_add]
  exact add_comm _ _
@[simp] theorem J_C_zero : J (C 0)=bracket (C 0) (C 1)+
    bracket (bracket (C 0) (Y 1)+bracket (Y 0) (C 1)) (Y 0)+bracket (Y 0) (bracket (X*X) (Y 1)) := by
  change J (bracket X (Y 0))=_
  rw [J_bracket,J_X,J_Y_zero,bracket_leibniz,bracket_X_C]
  rw [bracket_X_Y 0,add_left_comm,← add_assoc]
@[simp] theorem J_C_one : J (C 1)=bracket (C 0) (C 1)+
    bracket (bracket (C 0) (Y 1)+bracket (Y 0) (C 1)) (Y 1)+bracket (Y 1) (bracket (X*X) (Y 0)) := by
  change J (bracket X (Y 1))=_
  rw [J_bracket,J_X,J_Y_one,bracket_leibniz,bracket_X_C]
  rw [bracket_X_Y 1,bracket_swap (C 1) (C 0),add_left_comm,← add_assoc]

@[simp] theorem δ_square_H (i : Fin 2) : δ i (δ i (X*X))=
    bracket (X*X) (C i)+bracket (bracket (X*X) (Y i)) (Y i) := by
  rw [δ_H,δ_bracket,δ_H,δ_Y_self]
  exact add_comm _ _
@[simp] theorem δ_H_add_C (i : Fin 2) : δ i (X*X+C i)=bracket (C i) (Y i) := by
  rw [map_add,δ_H,δ_C_self,bracket_add_left,CharTwo.add_cancel_left]
@[simp] theorem δ_square_C_self (i : Fin 2) : δ i (δ i (C i))=
    bracket (X*X) (C i)+bracket (bracket (C i) (Y i)) (Y i) := by
  rw [δ_C_self,δ_bracket,δ_H_add_C,δ_Y_self,bracket_add_left,bracket_self,add_zero]
  exact add_comm _ _
@[simp] theorem δ_square_C_other (i j : Fin 2) (h : j≠i) : δ i (δ i (C j))=
    bracket (bracket (X*X+C i) (Y i)) (Y j) := by
  rw [δ_C_other i j h,δ_bracket,δ_C_self,δ_Y_other i j h,bracket_zero_right,add_zero]

@[simp] theorem realize_atom_zero : realize (atom (0 : F))=X*X := realize_H
@[simp] theorem realize_atom_one : realize (atom (1 : F))=Y 0 := realize_U 0
@[simp] theorem realize_atom_two : realize (atom (2 : F))=Y 1 := realize_U 1
@[simp] theorem realize_atom_three : realize (atom (3 : F))=C 0 := realize_V 0
@[simp] theorem realize_atom_four : realize (atom (4 : F))=C 1 := realize_V 1

attribute [local irreducible] X Y C H U V
 theorem source_realization_a0 (a : F) : baseDeriv 0 (realize (atom a))=realize (source 0 a) := by
  fin_cases a <;> simp [source,common,higher,R',Q,baseDeriv,δ_Y_other 0 1 (by decide)]
  · exact add_comm _ _
  · rw [add_add_add_comm,CharTwo.add_self_eq_zero,zero_add]
 theorem source_realization_a1 (a : F) : baseDeriv 1 (realize (atom a))=realize (source 1 a) := by
  fin_cases a <;> simp [source,common,higher,R',Q,baseDeriv,δ_Y_other 1 0 (by decide)]
  · exact add_comm _ _
  · rw [add_add_add_comm,CharTwo.add_self_eq_zero,zero_add]
 theorem source_realization_u (a : F) : baseDeriv 2 (realize (atom a))=realize (source 2 a) := by
  fin_cases a <;> simp [source,common,higher,W,baseDeriv,ε_C]
 theorem source_realization_v (a : F) : baseDeriv 3 (realize (atom a))=realize (source 3 a) := by
  change J (realize (atom a))=_
  fin_cases a <;> simp [source,common,higher,R',W,add_assoc]
  have h := J_H
  rw [J_mul,J_X] at h
  exact h
theorem source_realization (b : B) (a : F) : baseDeriv b (realize (atom a))=realize (source b a) := by
  fin_cases b
  · exact source_realization_a0 a
  · exact source_realization_a1 a
  · exact source_realization_u a
  · exact source_realization_v a
end CountTables
namespace WeightedDeletion
open AssociativeElimination WordGrading
variable {R α : Type*} [CommRing R]
def raw (κ : α → α → α → R) (l r : α) : List α → A R α
  | [] => 0
  | a::s => κ l a (s.headD r) • word (FreeMonoid.ofList s)+atom a*raw κ a r s

def op (κ : α → α → α → R) (l r : α) : Module.End R (A R α) :=
  (Finsupp.linearCombination R (fun w : FreeMonoid α => raw κ l r w.toList)).comp
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap
@[simp] theorem op_word (κ : α → α → α → R) (l r : α) (s : List α) :
    op κ l r (word (FreeMonoid.ofList s))=raw κ l r s := by change Finsupp.linearCombination R (fun monoidWord : FreeMonoid α => raw κ l r monoidWord.toList) (Finsupp.single (FreeMonoid.ofList s) 1) = _; simp

inductive Step (κ : α → α → α → R) (r : α) : α → List α → List α → Prop
  | head (l a : α) (s : List α) (h : κ l a (s.headD r)≠0) : Step κ r l (a::s) s
  | tail (l a : α) (s t : List α) (h : Step κ r a s t) : Step κ r l (a::s) (a::t)

theorem raw_mem_space (κ : α → α → α → R) (l r : α) (s : List α)
    (P : FreeMonoid α → Prop) (h : ∀ t,Step κ r l s t → P (FreeMonoid.ofList t)) :
    raw κ l r s∈space P := by
  classical
  induction s generalizing l P with
  | nil => exact (space P).zero_mem
  | cons a s ih =>
    apply (space P).add_mem
    · by_cases hc : κ l a (s.headD r)=0
      · simp only [hc,zero_smul]; exact (space P).zero_mem
      · exact (space P).smul_mem _ (word_mem _ (h s (.head l a s hc)))
    · have ht := ih a (fun w => P (FreeMonoid.of a*w)) (by
        intro t ht
        simpa only [FreeMonoid.ofList_cons] using h (a::t) (.tail l a s t ht))
      exact map_space (Algebra.lmul R (A R α) (atom a)) (space P) (by
        intro w hw
        change atom a*word w∈space P
        rw [← word_of a,← word_mul]
        exact word_mem _ hw) ht

theorem Step.length {κ : α → α → α → R} {r l : α} {s t : List α}
    (h : Step κ r l s t) : t.length+1=s.length := by
  induction h with
  | head => simp
  | tail _ _ _ _ _ ih => simp only [List.length_cons]; omega

theorem raw_length (κ : α → α → α → R) (l r : α) (s : List α) :
    raw κ l r s∈space (fun w => w.toList.length+1=s.length) :=
  raw_mem_space κ l r s _ (by intro t ht; simpa only [FreeMonoid.toList_ofList] using ht.length)

def count (wt : α → ℕ) (s : List α) : ℕ := (s.map wt).sum
@[simp] theorem count_nil (wt : α → ℕ) : count wt []=0 := rfl
@[simp] theorem count_cons (wt : α → ℕ) (a : α) (s : List α) : count wt (a::s)=wt a+count wt s := rfl

theorem Step.count_bound {κ : α → α → α → R} {r l : α} {s t : List α}
    (wt : α → ℕ) (c : ℕ) (hc : ∀ l a b,κ l a b≠0 → wt a≤c)
    (h : Step κ r l s t) : count wt s≤c+count wt t := by
  induction h with
  | head l a s h => simpa only [count_cons] using Nat.add_le_add_right (hc l a _ h) (count wt s)
  | tail l a s t h ih => simp only [count_cons]; omega

theorem raw_count_bound (κ : α → α → α → R) (l r : α) (s : List α)
    (wt : α → ℕ) (c : ℕ) (hc : ∀ l a b,κ l a b≠0 → wt a≤c) :
    raw κ l r s∈space (fun w => count wt s≤c+degree wt w) :=
  raw_mem_space κ l r s _ (by
    intro t ht
    simpa only [degree,FreeMonoid.toList_ofList,count] using ht.count_bound wt c hc)
end WeightedDeletion

end DeligneDrinfeld

end

end OAI
