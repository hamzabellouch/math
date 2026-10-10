import OAI.Geometry.PeriodicTiling.GraphTests
import OAI.Geometry.PeriodicTiling.CyclicCRT
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.Ring

namespace OAI

universe uι uA uB

noncomputable section

namespace PeriodicTilingThree

section CoordinateReplacement

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type uA} {B : Type uB}

theorem eq_of_update_invariant (f : (∀ i, A i) → B)
    (hf : ∀ x i (a : A i), f (Function.update x i a) = f x)
    (x y : ∀ i, A i) : f x = f y := by
  have h : ∀ s : Finset ι, f (s.piecewise x y) = f y := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => rw [Finset.piecewise_insert, hf, ih]
  simpa using h Finset.univ

theorem eq_of_update_invariant_off (f : (∀ i, A i) → B) (i : ι)
    (hf : ∀ j, j ≠ i → ∀ x (a : A j), f (Function.update x j a) = f x)
    (x y : ∀ i, A i) (hxy : x i = y i) : f x = f y := by
  have h : ∀ s : Finset ι, f (s.piecewise x y) = f y := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.piecewise_insert]
      by_cases hji : j = i
      · subst j
        have hv : s.piecewise x y i = x i := by
          by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi, hxy]
        rw [← hv, Function.update_eq_self]
        exact ih
      · exact (hf j hji _ _).trans ih
  simpa using h Finset.univ

end CoordinateReplacement

section Activity

variable {A : Type uA} {B : Type uB} [AddGroup A]

def DigitActive (g : A → B) (U : AddSubgroup A) : Prop :=
  ∃ w w', w - w' ∈ U ∧ g w ≠ g w'

theorem not_digitActive_iff (g : A → B) (U : AddSubgroup A) :
    ¬ DigitActive g U ↔ ∀ w w', w - w' ∈ U → g w = g w' := by
  simp only [DigitActive, not_exists, not_and, not_not]

end Activity

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

def seedResidue (p : ℕ) (x : Plane) : Residues p :=
  ((x.1 : ZMod (p ^ 2)), (x.2 : ZMod (p ^ 2)))

def seedRepresentative (p : ℕ) (s : Residues p) : Plane :=
  ((s.1.val : ℤ), (s.2.val : ℤ))

@[simp] theorem seedResidue_representative (s : Residues p) :
    seedResidue p (seedRepresentative p s) = s := by
  apply Prod.ext <;> simp [seedResidue, seedRepresentative]

def usefulAt (o : Outputs E) (i : Channel p) (x : Plane) (w : K E i) : P E i :=
  o.c (x, Function.update 0 i w) i

def ordinaryFactor (o : Outputs E) (n : Column p) (m : ℤ)
    (w : K E (.inl n)) : P E (.inl n) :=
  usefulAt E o (.inl n) (0, m) w

def seedFactor (o : Outputs E) (t : Fin 2) (s : Residues p)
    (w : K E (.inr t)) : P E (.inr t) :=
  usefulAt E o (.inr t) (seedRepresentative p s) w

def HasDependence (o : Outputs E) : Prop :=
  (∀ n x k, o.c (x, k) (.inl n) =
    ordinaryFactor E o n (lineValue n x) (k (.inl n))) ∧
  (∀ t x k, o.c (x, k) (.inr t) =
    seedFactor E o t (seedResidue p x) (k (.inr t)))

theorem ordinaryFactor_spec {o : Outputs E} (h : HasDependence E o)
    (n : Column p) (x : Plane) (k : Low E) :
    o.c (x, k) (.inl n) = ordinaryFactor E o n (lineValue n x) (k (.inl n)) :=
  h.1 n x k

theorem seedFactor_spec {o : Outputs E} (h : HasDependence E o)
    (t : Fin 2) (x : Plane) (k : Low E) :
    o.c (x, k) (.inr t) = seedFactor E o t (seedResidue p x) (k (.inr t)) :=
  h.2 t x k

theorem usefulAt_factor {o : Outputs E} (h : HasDependence E o)
    (x : Plane) (k : Low E) (i : Channel p) :
    o.c (x, k) i = usefulAt E o i x (k i) := by
  cases i with
  | inl n =>
    rw [h.1 n x k]
    symm
    simpa [usefulAt] using h.1 n x (Function.update 0 (.inl n) (k (.inl n)))
  | inr t =>
    rw [h.2 t x k]
    symm
    simpa [usefulAt] using h.2 t x (Function.update 0 (.inr t) (k (.inr t)))

theorem usefulAt_eq_of_lineValue_eq {o : Outputs E} (h : HasDependence E o)
    (n : Column p) {x y : Plane} (hxy : lineValue n x = lineValue n y)
    (w : K E (.inl n)) :
    usefulAt E o (.inl n) x w = usefulAt E o (.inl n) y w := by
  unfold usefulAt
  rw [h.1 n x _, h.1 n y _, hxy]

theorem usefulAt_eq_of_seedResidue_eq {o : Outputs E} (h : HasDependence E o)
    (t : Fin 2) {x y : Plane} (hxy : seedResidue p x = seedResidue p y)
    (w : K E (.inr t)) :
    usefulAt E o (.inr t) x w = usefulAt E o (.inr t) y w := by
  unfold usefulAt
  rw [h.2 t x _, h.2 t y _, hxy]

def Active (o : Outputs E) (i : Channel p) (x : Plane) (j : Label p i) : Prop :=
  DigitActive (usefulAt E o i x) (digitSubgroup E i j)

theorem digitActive_iff_coordinates (i : Channel p) (g : K E i → P E i)
    (j : Label p i) :
    DigitActive g (digitSubgroup E i j) ↔
      ∃ w w', (∀ q, q ≠ j → digitEquiv E i w q = digitEquiv E i w' q) ∧
        g w ≠ g w' := by
  simp only [DigitActive, sub_mem_digitSubgroup_iff]

theorem no_digitActive_iff_constant (i : Channel p) (g : K E i → P E i) :
    (∀ j, ¬ DigitActive g (digitSubgroup E i j)) ↔ ∃ c, ∀ w, g w = c := by
  constructor
  · intro h
    let e := digitEquiv E i
    have hu : ∀ z j (a : ZMod (E.digitPrime i j)),
        g (e.symm (Function.update z j a)) = g (e.symm z) := by
      intro z j a
      apply (not_digitActive_iff g (digitSubgroup E i j)).mp (h j)
      apply (sub_mem_digitSubgroup_iff E i j _ _).mpr
      intro q hq
      simp [e, hq]
    refine ⟨g 0, fun w => ?_⟩
    simpa [e] using eq_of_update_invariant (fun z => g (e.symm z)) hu (e w) (e 0)
  · rintro ⟨c, hc⟩ j
    apply (not_digitActive_iff g (digitSubgroup E i j)).mpr
    intro w w' _hww'
    exact (hc w).trans (hc w').symm

theorem no_active_iff_constant (o : Outputs E) (i : Channel p) (x : Plane) :
    (∀ j, ¬ Active E o i x j) ↔ ∃ c, ∀ w, usefulAt E o i x w = c :=
  no_digitActive_iff_constant E i (usefulAt E o i x)

theorem active_ordinary_iff {o : Outputs E} (h : HasDependence E o)
    (n : Column p) {x y : Plane} (hxy : lineValue n x = lineValue n y)
    (j : Label p (.inl n)) : Active E o (.inl n) x j ↔ Active E o (.inl n) y j := by
  have he : usefulAt E o (.inl n) x = usefulAt E o (.inl n) y :=
    funext (usefulAt_eq_of_lineValue_eq E h n hxy)
  unfold Active
  rw [he]

theorem active_seed_iff {o : Outputs E} (h : HasDependence E o)
    (t : Fin 2) {x y : Plane} (hxy : seedResidue p x = seedResidue p y)
    (j : Label p (.inr t)) : Active E o (.inr t) x j ↔ Active E o (.inr t) y j := by
  have he : usefulAt E o (.inr t) x = usefulAt E o (.inr t) y :=
    funext (usefulAt_eq_of_seedResidue_eq E h t hxy)
  unfold Active
  rw [he]

abbrev DependenceIndex (p : ℕ) :=
  (Σ i : Channel p, {j : Channel p // j ≠ i}) ⊕
    (Column p ⊕ (Fin 2 × Bool))

def lowGenerator (j : Channel p) : Base E :=
  (0, Function.update 0 j 1)

def seedStep (p : ℕ) (second : Bool) : Plane :=
  if second then (0, ((p ^ 2 : ℕ) : ℤ)) else (((p ^ 2 : ℕ) : ℤ), 0)

def dependenceChannel : DependenceIndex p → Channel p
  | .inl ⟨i, _⟩ => i
  | .inr (.inl n) => .inl n
  | .inr (.inr (t, _)) => .inr t

def dependenceShift : DependenceIndex p → Base E
  | .inl ⟨_, j⟩ => lowGenerator E j.1
  | .inr (.inl n) => (lineKernelStep n, 0)
  | .inr (.inr (_, axis)) => (seedStep p axis, 0)

def dependenceTile (d : DependenceIndex p) : Finset (G E) :=
  invarianceTile E (dependenceChannel d) (dependenceShift E d)

theorem dependenceTile_nonempty (d : DependenceIndex p) :
    (dependenceTile E d).Nonempty :=
  invarianceTile_nonempty E (dependenceChannel d) (dependenceShift E d)

theorem dependenceTile_card (d : DependenceIndex p) :
    (dependenceTile E d).card = (kernelTile E).card :=
  invarianceTile_card E (dependenceChannel d) (dependenceShift E d)

def dependenceTiles : Finset (Finset (G E)) := by
  classical
  exact Finset.univ.image (dependenceTile E)

def DependenceTests (o : Outputs E) : Prop :=
  ∀ d : DependenceIndex p, Tiles (dependenceTile E d) (graph o)

def DependenceInvariance (o : Outputs E) : Prop :=
  ∀ d : DependenceIndex p, ∀ b : Base E,
    o.c (b - dependenceShift E d) (dependenceChannel d) = o.c b (dependenceChannel d)

private theorem periodic_of_sub_eq {A : Type uA} {B : Type uB} [AddGroup A]
    (f : A → B) (v : A) (h : ∀ x, f (x - v) = f x) : Function.Periodic f v := by
  intro x
  simpa using (h (x + v)).symm

private theorem useful_update_of_generator (o : Outputs E) (i j : Channel p)
    (h : ∀ b, o.c (b - lowGenerator E j) i = o.c b i)
    (x : Plane) (k : Low E) (w : K E j) :
    o.c (x, Function.update k j w) i = o.c (x, k) i := by
  obtain ⟨a, ha⟩ := ZMod.intCast_surjective (k j - w)
  have he : (x, Function.update k j w) = (x, k) - a • lowGenerator E j := by
    apply Prod.ext
    · simp [lowGenerator]
    · funext l
      by_cases hlj : l = j
      · subst l
        simp [lowGenerator, zsmul_eq_mul, ha]
      · simp [lowGenerator, hlj]
  rw [he]
  exact (periodic_of_sub_eq (fun b => o.c b i) (lowGenerator E j) h).sub_zsmul_eq a

private theorem usefulAt_factor_of_generators (o : Outputs E)
    (h : ∀ i j, j ≠ i → ∀ b, o.c (b - lowGenerator E j) i = o.c b i)
    (x : Plane) (k : Low E) (i : Channel p) :
    o.c (x, k) i = usefulAt E o i x (k i) := by
  unfold usefulAt
  apply eq_of_update_invariant_off (fun k => o.c (x, k) i) i
  · intro j hji k' w
    exact useful_update_of_generator E o i j (h i j hji) x k' w
  · simp

@[simp] theorem seedResidue_sub_step
    {p : ℕ} [NeZero p]
    (x : Plane) (axis : Bool) :
    seedResidue p (x - seedStep p axis) = seedResidue p x := by
  have hp2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  cases axis <;> apply Prod.ext <;> simp [seedResidue, seedStep, hp2]

theorem dependenceInvariance_iff (o : Outputs E) :
    DependenceInvariance E o ↔ HasDependence E o := by
  constructor
  · intro h
    have hlow : ∀ i j, j ≠ i → ∀ b, o.c (b - lowGenerator E j) i = o.c b i := by
      intro i j hji b
      exact h (.inl ⟨i, ⟨j, hji⟩⟩) b
    have hfactor := usefulAt_factor_of_generators E o hlow
    constructor
    · intro n x k
      have hstep : ∀ b : Base E,
          o.c (b - (lineKernelStep n, 0)) (.inl n) = o.c b (.inl n) :=
        h (.inr (.inl n))
      have hp := periodic_of_sub_eq (fun b : Base E => o.c b (.inl n))
        (lineKernelStep n, 0) hstep
      have he : (x, k) - x.1 • (lineKernelStep n, (0 : Low E)) =
          ((0, lineValue n x), k) := by
        apply Prod.ext
        · apply Prod.ext
          · simp [lineKernelStep]
          · simp [lineKernelStep, lineValue]
            ring
        · simp
      have hs := hp.sub_zsmul_eq (x := (x, k)) x.1
      rw [he] at hs
      exact hs.symm.trans (hfactor (0, lineValue n x) k (.inl n))
    · intro t x k
      have hfirst : ∀ b : Base E,
          o.c (b - (seedStep p false, 0)) (.inr t) = o.c b (.inr t) :=
        h (.inr (.inr (t, false)))
      have hsecond : ∀ b : Base E,
          o.c (b - (seedStep p true, 0)) (.inr t) = o.c b (.inr t) :=
        h (.inr (.inr (t, true)))
      have hp := periodic_of_sub_eq (fun b : Base E => o.c b (.inr t))
        (seedStep p false, 0) hfirst
      have hq := periodic_of_sub_eq (fun b : Base E => o.c b (.inr t))
        (seedStep p true, 0) hsecond
      obtain ⟨a, ha⟩ := (ZMod.intCast_eq_iff (p ^ 2) x.1 (seedResidue p x).1).mp rfl
      obtain ⟨b, hb⟩ := (ZMod.intCast_eq_iff (p ^ 2) x.2 (seedResidue p x).2).mp rfl
      have he : (x, k) - a • (seedStep p false, (0 : Low E)) -
          b • (seedStep p true, (0 : Low E)) =
          (seedRepresentative p (seedResidue p x), k) := by
        apply Prod.ext
        · apply Prod.ext
          · simpa [seedStep, seedRepresentative, zsmul_eq_mul,
              sub_eq_iff_eq_add, mul_comm] using ha
          · simpa [seedStep, seedRepresentative, zsmul_eq_mul,
              sub_eq_iff_eq_add, mul_comm] using hb
        · simp
      have hs := (hq.sub_zsmul_eq
        (x := (x, k) - a • (seedStep p false, (0 : Low E))) b).trans
          (hp.sub_zsmul_eq (x := (x, k)) a)
      rw [he] at hs
      exact hs.symm.trans (hfactor (seedRepresentative p (seedResidue p x)) k (.inr t))
  · intro h d xb
    rcases xb with ⟨x, k⟩
    rcases d with ⟨i, j⟩ | d
    · change o.c ((x, k) - (0, Function.update (0 : Low E) j.1 1)) i = o.c (x, k) i
      simp only [Prod.mk_sub_mk, sub_zero]
      rw [usefulAt_factor E h, usefulAt_factor E h]
      simp [Ne.symm j.property]
    · rcases d with n | ⟨t, axis⟩
      · change o.c ((x, k) - (lineKernelStep n, 0)) (.inl n) = o.c (x, k) (.inl n)
        simp only [Prod.mk_sub_mk, sub_zero]
        rw [h.1 n (x - lineKernelStep n) k, h.1 n x k]
        have he : lineValue n (x - lineKernelStep n) = lineValue n x := by
          simp [lineValue, lineKernelStep] ; ring
        rw [he]
      · change o.c ((x, k) - (seedStep p axis, 0)) (.inr t) = o.c (x, k) (.inr t)
        simp only [Prod.mk_sub_mk, sub_zero]
        rw [h.2 t (x - seedStep p axis) k, h.2 t x k, seedResidue_sub_step]

theorem dependenceTests_iff (o : Outputs E) :
    DependenceTests E o ↔ HasDependence E o := by
  have he : DependenceTests E o ↔ DependenceInvariance E o := by
    unfold DependenceTests DependenceInvariance dependenceTile
    simp only [invarianceTile_iff]
  exact he.trans (dependenceInvariance_iff E o)

theorem dependenceTiles_iff (o : Outputs E) :
    (∀ F ∈ dependenceTiles E, Tiles F (graph o)) ↔ HasDependence E o := by
  classical
  rw [← dependenceTests_iff E o]
  constructor
  · intro h d
    apply h (dependenceTile E d)
    exact Finset.mem_image.mpr ⟨d, Finset.mem_univ d, rfl⟩
  · intro h F hF
    obtain ⟨d, _hd, rfl⟩ := Finset.mem_image.mp hF
    exact h d

end PeriodicTilingThree

end

end OAI
