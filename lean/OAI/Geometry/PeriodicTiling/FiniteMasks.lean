import OAI.Geometry.PeriodicTiling.TilingBasic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Abel

namespace OAI

universe uG uR uι

noncomputable section

open scoped BigOperators Classical

namespace PeriodicTilingThree

variable {G : Type uG}

def tileIndicator (R : Type uR) [Zero R] [One R] (A : Set G) (x : G) : R :=
  if x ∈ A then 1 else 0

theorem tileIndicator_nonneg (A : Set G) (x : G) :
    0 ≤ tileIndicator ℝ A x := by
  classical
  unfold tileIndicator
  split_ifs <;> simp

theorem tileIndicator_le_one (A : Set G) (x : G) :
    tileIndicator ℝ A x ≤ 1 := by
  classical
  unfold tileIndicator
  split_ifs <;> simp

theorem tileIndicator_nat_le_one (A : Set G) (x : G) :
    tileIndicator ℕ A x ≤ 1 := by
  classical
  unfold tileIndicator
  split_ifs <;> simp

theorem sum_tileIndicator_cast (R : Type uR) [AddCommMonoidWithOne R]
    {ι : Type uι} (s : Finset ι) (A : Set G) (v : ι → G) :
    ((∑ i ∈ s, tileIndicator ℕ A (v i) : ℕ) : R) =
      ∑ i ∈ s, tileIndicator R A (v i) := by
  classical
  simp only [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : v i ∈ A <;> simp [tileIndicator, h]

section Counts

variable [AddCommGroup G]

def tileCount (F : Finset G) (A : Set G) (x : G) : ℕ :=
  ∑ f ∈ F, tileIndicator ℕ A (x - f)

theorem tileCount_eq_card_filter (F : Finset G) (A : Set G) (x : G) :
    tileCount F A x = (F.filter fun f => x - f ∈ A).card := by
  classical
  simp [tileCount, tileIndicator]

theorem tileCount_le_card (F : Finset G) (A : Set G) (x : G) :
    tileCount F A x ≤ F.card := by
  classical
  rw [tileCount_eq_card_filter]
  exact Finset.card_filter_le _ _

theorem tileCount_cast (R : Type uR) [AddCommMonoidWithOne R]
    (F : Finset G) (A : Set G) (x : G) :
    (tileCount F A x : R) = ∑ f ∈ F, tileIndicator R A (x - f) :=
  sum_tileIndicator_cast R F A (fun f => x - f)

theorem tiles_iff_tileCount_eq_one {F : Finset G} {A : Set G} :
    Tiles F A ↔ ∀ x : G, tileCount F A x = 1 := by
  classical
  rw [tiles_iff_unique_tile]
  constructor
  · intro h x
    obtain ⟨f, hf, hu⟩ := h x
    have he : (F.filter fun g => x - g ∈ A) = {f.val} := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hg, hga⟩
        exact congrArg Subtype.val (hu ⟨g, hg⟩ hga)
      · intro hg
        subst g
        exact ⟨f.property, hf⟩
    rw [tileCount_eq_card_filter, he, Finset.card_singleton]
  · intro h x
    obtain ⟨f, hf⟩ := Finset.card_eq_one.mp ((tileCount_eq_card_filter F A x).symm.trans (h x))
    have hm : f ∈ F ∧ x - f ∈ A := by
      apply Finset.mem_filter.mp
      rw [hf]
      exact Finset.mem_singleton_self f
    refine ⟨⟨f, hm.1⟩, hm.2, ?_⟩
    intro g hg
    apply Subtype.ext
    have hg' : g.val ∈ F.filter fun f => x - f ∈ A :=
      Finset.mem_filter.mpr ⟨g.property, hg⟩
    simpa only [hf, Finset.mem_singleton] using hg'

theorem Tiles.tileCount_eq_one {F : Finset G} {A : Set G}
    (h : Tiles F A) (x : G) : tileCount F A x = 1 :=
  tiles_iff_tileCount_eq_one.mp h x

theorem Tiles.sum_tileIndicator_eq_one {F : Finset G} {A : Set G}
    (h : Tiles F A) (R : Type uR) [AddCommMonoidWithOne R] (x : G) :
    (∑ f ∈ F, tileIndicator R A (x - f)) = 1 := by
  rw [← tileCount_cast, h.tileCount_eq_one x, Nat.cast_one]

end Counts

section MaskAction

variable {R : Type uR} [Semiring R] [AddCommGroup G]

def maskAction (m : AddMonoidAlgebra R G) (a : G → R) (x : G) : R :=
  m.coeff.sum fun y c => c * a (x - y)

@[simp] theorem maskAction_zero (a : G → R) (x : G) :
    maskAction (0 : AddMonoidAlgebra R G) a x = 0 := by
  simp [maskAction]

@[simp] theorem maskAction_single (y : G) (c : R) (a : G → R) (x : G) :
    maskAction (AddMonoidAlgebra.single y c) a x = c * a (x - y) := by
  simp [maskAction]

theorem maskAction_add (m n : AddMonoidAlgebra R G) (a : G → R) (x : G) :
    maskAction (m + n) a x = maskAction m a x + maskAction n a x := by
  simpa only [maskAction, AddMonoidAlgebra.coeff_add] using
    (Finsupp.sum_add_index' (f := m.coeff) (g := n.coeff)
      (h := fun y c => c * a (x - y))
      (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _))

theorem maskAction_sum {ι : Type uι} (s : Finset ι)
    (m : ι → AddMonoidAlgebra R G) (a : G → R) (x : G) :
    maskAction (∑ i ∈ s, m i) a x = ∑ i ∈ s, maskAction (m i) a x := by
  simpa only [maskAction, AddMonoidAlgebra.coeff_sum] using
    (Finsupp.sum_finsetSum_index (s := s) (g := fun i => (m i).coeff)
      (h := fun y c => c * a (x - y))
      (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)).symm

private theorem maskAction_single_mul (y : G) (c : R)
    (m : AddMonoidAlgebra R G) (a : G → R) (x : G) :
    maskAction (AddMonoidAlgebra.single y c * m) a x =
      c * maskAction m a (x - y) := by
  induction m using AddMonoidAlgebra.induction with
  | zero => simp
  | single_add z d m hz hd ih =>
    rw [mul_add, maskAction_add, maskAction_add, mul_add, ih]
    rw [AddMonoidAlgebra.single_mul_single, maskAction_single, maskAction_single]
    rw [mul_assoc, sub_sub]

theorem maskAction_mul (m n : AddMonoidAlgebra R G) (a : G → R) (x : G) :
    maskAction (m * n) a x = maskAction m (fun y => maskAction n a y) x := by
  induction m using AddMonoidAlgebra.induction with
  | zero => simp
  | single_add y c m hy hc ih =>
    rw [add_mul, maskAction_add, maskAction_add, ih]
    rw [maskAction_single_mul, maskAction_single]

@[simp] theorem maskAction_one (a : G → R) (x : G) :
    maskAction (1 : AddMonoidAlgebra R G) a x = a x := by
  rw [AddMonoidAlgebra.one_def, maskAction_single]
  simp

theorem maskAction_translate (m : AddMonoidAlgebra R G) (a : G → R) (x v : G) :
    maskAction m (fun y => a (y + v)) x = maskAction m a (x + v) := by
  unfold maskAction
  apply Finsupp.sum_congr
  intro y hy
  congr 2
  abel_nf

def familyMask (R : Type uR) [Semiring R] {ι : Type uι} (s : Finset ι) (v : ι → G) :
    AddMonoidAlgebra R G :=
  ∑ i ∈ s, AddMonoidAlgebra.single (v i) 1

def tileMask (R : Type uR) [Semiring R] (F : Finset G) : AddMonoidAlgebra R G :=
  familyMask R F id

theorem maskAction_familyMask {ι : Type uι} (s : Finset ι) (v : ι → G)
    (a : G → R) (x : G) :
    maskAction (familyMask R s v) a x = ∑ i ∈ s, a (x - v i) := by
  simp only [familyMask, maskAction_sum, maskAction_single, one_mul]

theorem maskAction_tileMask (F : Finset G) (a : G → R) (x : G) :
    maskAction (tileMask R F) a x = ∑ f ∈ F, a (x - f) :=
  maskAction_familyMask F id a x

theorem maskAction_familyMask_const {ι : Type uι} (s : Finset ι) (v : ι → G)
    (c : R) (x : G) :
    maskAction (familyMask R s v) (fun _ => c) x = (s.card : R) * c := by
  simp [maskAction_familyMask, nsmul_eq_mul]

theorem maskAction_familyMask_pow_const {ι : Type uι} (s : Finset ι) (v : ι → G)
    (n : ℕ) (c : R) (x : G) :
    maskAction (familyMask R s v ^ n) (fun _ => c) x = (s.card : R) ^ n * c := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', maskAction_mul]
    simp_rw [ih]
    rw [maskAction_familyMask_const, pow_succ', mul_assoc]

theorem maskAction_familyMask_pow_succ {ι : Type uι} (s : Finset ι) (v : ι → G)
    (a : G → R) (h : ∀ x, (∑ i ∈ s, a (x - v i)) = 1) (n : ℕ) (x : G) :
    maskAction (familyMask R s v ^ (n + 1)) a x = (s.card : R) ^ n := by
  rw [pow_succ, maskAction_mul]
  simp_rw [maskAction_familyMask, h]
  rw [maskAction_familyMask_pow_const, mul_one]

end MaskAction

end PeriodicTilingThree

end

end OAI
