import Mathlib

namespace OAI

/-!
Polynomial congruence groups, truncation ideals, and finite nilpotent quotients.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix

namespace CoboundaryExpanders.Construction

section
abbrev R (q : ℕ) := Polynomial (ZMod q)
def powerIdeal (q m : ℕ) : Ideal (R q) := Ideal.span {Polynomial.X ^ m}
def Gamma (q a m : ℕ) : Subgroup (Matrix.SpecialLinearGroup (Fin a) (R q)) :=
  (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal q m))).ker
abbrev Trunc (q m : ℕ) := R q ⧸ powerIdeal q m

instance finiteTrunc (q m : ℕ) [NeZero q] : Finite (Trunc q m) := by
  let : Module.Finite (ZMod q) (Trunc q m) :=
    (Polynomial.monic_X.pow m).finite_quotient
  exact Module.finite_of_finite (ZMod q)

def tbar (q m : ℕ) : Trunc q m := Ideal.Quotient.mk (powerIdeal q m) Polynomial.X

@[simp] theorem tbar_pow (q m : ℕ) : tbar q m ^ m = 0 := by
  rw [tbar, ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem exists_prime_power_unipotent {A : Type*} [Ring A] {p : ℕ}
    (hp : p.Prime) (hp0 : (p : A) = 0) (x : A) (hx : IsNilpotent x) :
    ∃ r : ℕ, (1 + x) ^ p ^ r = 1 := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  obtain ⟨z, hz⟩ := (Commute.one_left x).exists_add_pow_prime_pow_eq hp n
  rw [hz, hp0, zero_mul, zero_mul, zero_mul, add_zero, one_pow,
    pow_eq_zero_of_le (Nat.le_of_lt (Nat.lt_pow_self hp.one_lt)) hn, add_zero]

theorem matrix_nilpotent_of_entries {A : Type*} [CommRing A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (x : A) (hx : IsNilpotent x)
    (M : Matrix ι ι A) (hM : ∀ i j, x ∣ M i j) : IsNilpotent M := by
  classical
  choose B hB using hM
  let B' : Matrix ι ι A := B
  have he : M = x • B' := by ext i j; exact hB i j
  obtain ⟨r, hr⟩ := hx
  refine ⟨r, ?_⟩
  rw [he, smul_pow, hr, zero_smul]

theorem strict_upper_pow_zero {A : Type*} [Semiring A] (a : ℕ)
    (M : Matrix (Fin a) (Fin a) A) (hM : ∀ i j, j ≤ i → M i j = 0) :
    M ^ a = 0 := by
  have hpow : ∀ r : ℕ, ∀ i j : Fin a, j.val < i.val + r → (M ^ r) i j = 0 := by
    intro r
    induction r with
    | zero =>
      intro i j hij
      have hne : i ≠ j := by intro h; subst j; omega
      simp [hne]
    | succ r ih =>
      intro i j hij
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : l.val < i.val + r
      · rw [ih i l hl, zero_mul]
      · have hjl : j ≤ l := by omega
        rw [hM l j hjl, mul_zero]
  ext i j
  exact hpow a i j (by omega)

theorem prime_cast_trunc (p m : ℕ) : (p : Trunc p m) = 0 := by
  have h : (p : R p) = 0 := by simp
  rw [← map_natCast (Ideal.Quotient.mk (powerIdeal p m)), h, map_zero]

theorem mem_gamma_iff (q a m : ℕ) (A : Matrix.SpecialLinearGroup (Fin a) (R q)) :
    A ∈ Gamma q a m ↔ ∀ i j,
      Polynomial.X ^ m ∣ (A : Matrix (Fin a) (Fin a) (R q)) i j -
        (1 : Matrix (Fin a) (Fin a) (R q)) i j := by
  rw [Gamma, MonoidHom.mem_ker, Matrix.SpecialLinearGroup.ext_iff]
  constructor
  · intro h i j
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mk (powerIdeal q m) _ = 0
    rw [map_sub]
    change Ideal.Quotient.mk (powerIdeal q m) _ -
      Ideal.Quotient.mk (powerIdeal q m) ((1 : Matrix (Fin a) (Fin a) (R q)) i j) = 0
    have he := h i j
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.SpecialLinearGroup.coe_one] at he
    rw [he]
    simp [Matrix.one_apply]
  · intro h i j
    have he := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr (h i j))
    change Ideal.Quotient.mk (powerIdeal q m) _ = 0 at he
    rw [map_sub, sub_eq_zero] at he
    simpa [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply] using he

theorem gamma_antitone (q a : ℕ) : Antitone (Gamma q a) := by
  intro m n hmn A hA
  rw [mem_gamma_iff] at hA ⊢
  intro i j
  exact dvd_trans (pow_dvd_pow _ hmn) (hA i j)

theorem reduction_sub_one_nilpotent (q a m : ℕ)
    (A : Matrix.SpecialLinearGroup (Fin a) (R q)) (hA : A ∈ Gamma q a 1) :
    IsNilpotent
      ((Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal q m)) A :
        Matrix (Fin a) (Fin a) (Trunc q m)) - 1) := by
  apply matrix_nilpotent_of_entries (tbar q m) ⟨m, tbar_pow q m⟩
  intro i j
  have hd := (mem_gamma_iff q a 1 A).mp hA i j
  rw [pow_one] at hd
  obtain ⟨b, hb⟩ := hd
  refine ⟨Ideal.Quotient.mk (powerIdeal q m) b, ?_⟩
  have he := congrArg (Ideal.Quotient.mk (powerIdeal q m)) hb
  simp only [map_sub, map_mul] at he
  simpa [Matrix.sub_apply, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply, tbar] using he

theorem reduction_prime_power (p a m : ℕ) (hp : p.Prime)
    (A : Matrix.SpecialLinearGroup (Fin a) (R p)) (hA : A ∈ Gamma p a 1) :
    ∃ r : ℕ, (Matrix.SpecialLinearGroup.map
      (Ideal.Quotient.mk (powerIdeal p m)) A) ^ p ^ r = 1 := by
  let B := Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m)) A
  have hc : (p : Matrix (Fin a) (Fin a) (Trunc p m)) = 0 := by
    ext i j
    simp [Matrix.natCast_apply, prime_cast_trunc]
  obtain ⟨r, hr⟩ := exists_prime_power_unipotent hp hc
    ((B : Matrix (Fin a) (Fin a) (Trunc p m)) - 1)
    (reduction_sub_one_nilpotent p a m A hA)
  refine ⟨r, ?_⟩
  apply Subtype.ext
  simpa only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one,
    add_sub_cancel] using hr

def congruenceReduction (p a m n : ℕ) : Gamma p a m →*
    Matrix.SpecialLinearGroup (Fin a) (Trunc p n) :=
  (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p n))).comp
    (Gamma p a m).subtype

def deeperCongruence (p a m n : ℕ) : Subgroup (Gamma p a m) :=
  (congruenceReduction p a m n).ker

theorem deeperCongruence_eq (p a m n : ℕ) :
    deeperCongruence p a m n = (Gamma p a n).subgroupOf (Gamma p a m) := rfl

instance normalDeeper (p a m n : ℕ) : (deeperCongruence p a m n).Normal :=
  MonoidHom.normal_ker _

instance finiteCongruenceQuotient (p a m n : ℕ) [NeZero p] :
    Finite (Gamma p a m ⧸ deeperCongruence p a m n) :=
  Finite.of_injective
    (QuotientGroup.quotientKerEquivRange (congruenceReduction p a m n))
    (QuotientGroup.quotientKerEquivRange (congruenceReduction p a m n)).injective

theorem isPGroup_congruenceRange (p a m n : ℕ) (hp : p.Prime) (hm : 1 ≤ m) :
    IsPGroup p (congruenceReduction p a m n).range := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  obtain ⟨A, hA⟩ := g.property
  obtain ⟨r, hr⟩ := reduction_prime_power p a n hp A
    (gamma_antitone p a hm A.property)
  refine ⟨r, Subtype.ext ?_⟩
  change (g : Matrix.SpecialLinearGroup (Fin a) (Trunc p n)) ^ p ^ r = 1
  rw [← hA]
  exact hr

theorem isPGroup_congruenceQuotient (p a m n : ℕ) (hp : p.Prime) (hm : 1 ≤ m) :
    IsPGroup p (Gamma p a m ⧸ deeperCongruence p a m n) :=
  (isPGroup_congruenceRange p a m n hp hm).of_surjective
    (QuotientGroup.quotientKerEquivRange (congruenceReduction p a m n)).symm.toMonoidHom
    (QuotientGroup.quotientKerEquivRange (congruenceReduction p a m n)).symm.surjective

theorem odd_congruence_index (p a m n : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hm : 1 ≤ m) : Odd (Nat.card (Gamma p a m ⧸ deeperCongruence p a m n)) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr⟩ := (isPGroup_congruenceQuotient p a m n hp hm).exists_card_eq
  rw [hr]
  exact hodd.pow

def IsUpperUnitriangular {A : Type*} [CommRing A] (a : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin a) A) : Prop :=
  ∀ i j, j ≤ i → (g : Matrix (Fin a) (Fin a) A) i j =
    (1 : Matrix (Fin a) (Fin a) A) i j

def upperUnitriangularMonoid (p a : ℕ) :
    Submonoid (Matrix.SpecialLinearGroup (Fin a) (ZMod p)) where
  carrier := {g | IsUpperUnitriangular a g}
  one_mem' := by intro i j h; rfl
  mul_mem' := by
    intro g h hg hh i j hij
    change ((g : Matrix (Fin a) (Fin a) (ZMod p)) *
      (h : Matrix (Fin a) (Fin a) (ZMod p))) i j = _
    rw [Matrix.mul_apply]
    by_cases he : i = j
    · subst j
      rw [Finset.sum_eq_single i]
      · rw [hg i i le_rfl, hh i i le_rfl]
        simp
      · intro l _ hli
        rcases lt_or_gt_of_ne hli with hl | hl
        · rw [hg i l hl.le]
          simp [ne_of_gt hl]
        · rw [hh l i hl.le]
          simp [ne_of_gt hl]
      · simp
    · rw [Matrix.one_apply_ne he]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : l < i
      · rw [hg i l hl.le]
        simp [ne_of_gt hl]
      · have hjl : j < l := lt_of_lt_of_le (lt_of_le_of_ne hij (Ne.symm he)) (le_of_not_gt hl)
        rw [hh l j hjl.le]
        simp [ne_of_gt hjl]

def upperUnitriangular (p a : ℕ) [NeZero p] :
    Subgroup (Matrix.SpecialLinearGroup (Fin a) (ZMod p)) :=
  { upperUnitriangularMonoid p a with
    inv_mem' := by
      intro g hg
      change g⁻¹ ∈ upperUnitriangularMonoid p a
      rw [← one_mul g⁻¹, ← pow_one g, ← pow_orderOf_eq_one g,
        ← pow_sub g (orderOf_pos g)]
      exact (upperUnitriangularMonoid p a).pow_mem hg (orderOf g - 1) }

def evalZero (p a : ℕ) : Matrix.SpecialLinearGroup (Fin a) (R p) →*
    Matrix.SpecialLinearGroup (Fin a) (ZMod p) :=
  Matrix.SpecialLinearGroup.map (Polynomial.evalRingHom 0)

def U (p a : ℕ) [NeZero p] : Subgroup (Matrix.SpecialLinearGroup (Fin a) (R p)) :=
  (upperUnitriangular p a).comap (evalZero p a)

theorem gamma_one_eq_ker_evalZero (p a : ℕ) : Gamma p a 1 = (evalZero p a).ker := by
  ext g
  rw [mem_gamma_iff, MonoidHom.mem_ker, Matrix.SpecialLinearGroup.ext_iff]
  simp [pow_one, Polynomial.X_dvd_iff, evalZero,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply, Matrix.one_apply, apply_ite, Polynomial.coeff_zero_eq_eval_zero,
    sub_eq_zero]

theorem gamma_le_U (p a m : ℕ) [NeZero p] (hm : 1 ≤ m) : Gamma p a m ≤ U p a := by
  intro g hg
  have h1 := gamma_antitone p a hm hg
  rw [gamma_one_eq_ker_evalZero, MonoidHom.mem_ker] at h1
  change evalZero p a g ∈ upperUnitriangular p a
  rw [h1]
  exact (upperUnitriangular p a).one_mem

theorem upperUnitriangular_isPGroup (p a : ℕ) (hp : p.Prime) [NeZero p] :
    IsPGroup p (upperUnitriangular p a) := by
  intro g
  have hn : IsNilpotent ((g.val : Matrix (Fin a) (Fin a) (ZMod p)) - 1) := by
    refine ⟨a, strict_upper_pow_zero a _ ?_⟩
    intro i j hij
    rw [Matrix.sub_apply, g.property i j hij, sub_self]
  have hc : (p : Matrix (Fin a) (Fin a) (ZMod p)) = 0 := by
    ext i j
    simp [Matrix.natCast_apply]
  obtain ⟨r, hr⟩ := exists_prime_power_unipotent hp hc _ hn
  refine ⟨r, Subtype.ext (Subtype.ext ?_)⟩
  simpa only [Subgroup.coe_pow, Matrix.SpecialLinearGroup.coe_pow,
    Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one, add_sub_cancel] using hr

def uReduction (p a m : ℕ) [NeZero p] : U p a →*
    Matrix.SpecialLinearGroup (Fin a) (Trunc p m) :=
  (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m))).comp (U p a).subtype

def Gquot (p a m : ℕ) [NeZero p] := U p a ⧸ (uReduction p a m).ker
instance (p a m : ℕ) [NeZero p] : Group (Gquot p a m) := inferInstanceAs (Group (_ ⧸ _))
instance (p a m : ℕ) [NeZero p] : Finite (Gquot p a m) :=
  Finite.of_injective (QuotientGroup.quotientKerEquivRange (uReduction p a m))
    (QuotientGroup.quotientKerEquivRange (uReduction p a m)).injective

theorem gquot_isPGroup (p a m : ℕ) (hp : p.Prime) [NeZero p] : IsPGroup p (Gquot p a m) := by
  have himage : IsPGroup p (uReduction p a m).range := by
    intro g
    obtain ⟨A, hA⟩ := g.property
    have hpU := upperUnitriangular_isPGroup p a hp
      ⟨evalZero p a A.val, A.property⟩
    obtain ⟨r, hr⟩ := hpU
    have hgamma : A.val ^ p ^ r ∈ Gamma p a 1 := by
      rw [gamma_one_eq_ker_evalZero, MonoidHom.mem_ker, map_pow]
      exact congrArg Subtype.val hr
    obtain ⟨s, hs⟩ := reduction_prime_power p a m hp _ hgamma
    refine ⟨r + s, Subtype.ext ?_⟩
    change g.val ^ p ^ (r + s) = 1
    rw [← hA, pow_add, pow_mul]
    simpa only [map_pow, uReduction, MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.coe_subtype] using hs
  exact himage.of_surjective
    (QuotientGroup.quotientKerEquivRange (uReduction p a m)).symm.toMonoidHom
    (QuotientGroup.quotientKerEquivRange (uReduction p a m)).symm.surjective

theorem odd_gquot_card (p a m : ℕ) (hp : p.Prime) (hodd : Odd p) [NeZero p] :
    Odd (Nat.card (Gquot p a m)) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr⟩ := (gquot_isPGroup p a m hp).exists_card_eq
  rw [hr]
  exact hodd.pow

variable (p n : ℕ) [Fact p.Prime]
abbrev Frac := FractionRing (R p)

def diagonalUnits {ι K : Type*} [Fintype ι] [DecidableEq ι] [CommRing K]
    (u : ι → Kˣ) : Matrix.GeneralLinearGroup ι K where
  val := Matrix.diagonal (fun i => (u i).val)
  inv := Matrix.diagonal (fun i => (u i).inv)
  val_inv := by simp [Matrix.diagonal_mul_diagonal]
  inv_val := by simp [Matrix.diagonal_mul_diagonal]

@[simp] theorem diagonalUnits_val {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing K] (u : ι → Kˣ) :
    (diagonalUnits u).val = Matrix.diagonal (fun i => (u i).val) := rfl

@[simp] theorem diagonalUnits_inv_val {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing K] (u : ι → Kˣ) :
    (diagonalUnits u)⁻¹.val = Matrix.diagonal (fun i => (u i).inv) := rfl

def cutUnit (cut i : Fin (n + 1)) : (Frac p)ˣ :=
  if i.val < cut.val then
    Units.mk0 (algebraMap (R p) (Frac p) Polynomial.X)
      (by exact fun h => Polynomial.X_ne_zero ((IsFractionRing.injective (R p) (Frac p)) (h.trans (map_zero _).symm)))
  else 1

def edgeSource (j : Fin (n + 1)) : Fin (n + 1) :=
  if h : j = 0 then Fin.last n else ⟨j.val - 1, by omega⟩

theorem edgeSource_ne (hn : 1 ≤ n) (j : Fin (n + 1)) : edgeSource n j ≠ j := by
  unfold edgeSource
  split_ifs with h
  · subst j
    intro he
    have := congrArg Fin.val he
    simp only [Fin.val_last, Fin.val_zero] at this
    omega
  · intro he
    have := congrArg Fin.val he
    have hj : j.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using h
    dsimp only at this
    omega

def cycleRoot (hn : 1 ≤ n) (j : Fin (n + 1)) :
    Matrix.SpecialLinearGroup (Fin (n + 1)) (R p) :=
  Matrix.SpecialLinearGroup.transvection (edgeSource_ne n hn j)
    (if j = 0 then Polynomial.X else 1)

def localGroup (hn : 1 ≤ n) (cut : Fin (n + 1)) :
    Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) (R p)) :=
  Subgroup.closure {g | ∃ j, j ≠ cut ∧ g = cycleRoot p n hn j}

def cutConjugation (cut : Fin (n + 1)) :
    Matrix.SpecialLinearGroup (Fin (n + 1)) (R p) →*
      Matrix.GeneralLinearGroup (Fin (n + 1)) (Frac p) :=
  (MulAut.conj (diagonalUnits (cutUnit p n cut))).toMonoidHom.comp
    (Matrix.SpecialLinearGroup.mapGL (Frac p))

theorem cutConjugation_injective (cut : Fin (n + 1)) :
    Function.Injective (cutConjugation p n cut) := by
  apply (MulAut.conj _).injective.comp
  intro A B h
  exact (Matrix.SpecialLinearGroup.mapGL_inj (S := Frac p) A B).mp h

theorem diagonal_conj_transvection {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing K] (u : ι → Kˣ) {i j : ι} (hij : i ≠ j) (b : K) :
    MulAut.conj (diagonalUnits u) (Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.transvection hij b)) =
    Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij
      ((u i).val * b * (u j).inv)) := by
  apply Matrix.GeneralLinearGroup.ext
  intro a c
  change ((diagonalUnits u).val *
    (1 + Matrix.single i j b) * (diagonalUnits u).inv) a c =
      (1 + Matrix.single i j ((u i).val * b * (u j).inv)) a c
  simp only [diagonalUnits, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases ha : a = i <;> by_cases hc : c = j <;> by_cases hac : a = c
  all_goals simp_all [mul_add, add_mul]

theorem cut_root_coefficient (cut j : Fin (n + 1)) (hj : j ≠ cut) :
    (cutUnit p n cut (edgeSource n j)).val *
      (algebraMap (R p) (Frac p)) (if j = 0 then Polynomial.X else 1) *
      (cutUnit p n cut j).inv = 1 := by
  by_cases h0 : j = 0
  · subst j
    have hc : 0 < cut.val := by
      have : cut.val ≠ 0 := fun h => hj (Fin.ext h.symm)
      omega
    have hncut : ¬ n < cut.val := by omega
    simp [edgeSource, cutUnit, hncut, hc]
  · have hj0 : 0 < j.val := by
      have : j.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using h0
      omega
    have hne : j.val ≠ cut.val := fun h => hj (Fin.ext h)
    have heq : j.val - 1 < cut.val ↔ j.val < cut.val := by omega
    simp only [edgeSource, dite_eq_right h0, cutUnit, Fin.val_mk, heq, ite_eq_right h0, map_one]
    split_ifs <;> simp

theorem map_transvection {ι A B : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing A] [CommRing B] (f : A →+* B) {i j : ι} (hij : i ≠ j) (b : A) :
    Matrix.SpecialLinearGroup.map f (Matrix.SpecialLinearGroup.transvection hij b) =
    Matrix.SpecialLinearGroup.transvection hij (f b) := by
  ext a c
  simp [Matrix.SpecialLinearGroup.map_apply_coe,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply,
    Matrix.one_apply, apply_ite f]

theorem cutConjugation_root (hn : 1 ≤ n) (cut j : Fin (n + 1)) (hj : j ≠ cut) :
    cutConjugation p n cut (cycleRoot p n hn j) =
    Matrix.GeneralLinearGroup.map (algebraMap (ZMod p) (Frac p))
      (Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.transvection (edgeSource_ne n hn j) (1 : ZMod p))) := by
  change MulAut.conj (diagonalUnits (cutUnit p n cut))
    (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map _ _)) = _
  rw [cycleRoot, map_transvection, diagonal_conj_transvection,
    cut_root_coefficient p n cut j hj]
  apply Matrix.GeneralLinearGroup.ext
  intro a c
  simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.GeneralLinearGroup.map,
    Matrix.single_apply, Matrix.one_apply]

theorem localGroup_le_constant (hn : 1 ≤ n) (cut : Fin (n + 1)) :
    localGroup p n hn cut ≤
      (Matrix.GeneralLinearGroup.map (n := Fin (n + 1)) (algebraMap (ZMod p) (Frac p))).range.comap
        (cutConjugation p n cut) := by
  apply (Subgroup.closure_le _).2
  rintro g ⟨j, hj, rfl⟩
  exact ⟨Matrix.SpecialLinearGroup.toGL
    (Matrix.SpecialLinearGroup.transvection (edgeSource_ne n hn j) 1),
      (cutConjugation_root p n hn cut j hj).symm⟩

def localGroupEmbedding (hn : 1 ≤ n) (cut : Fin (n + 1)) :
    localGroup p n hn cut ↪
      (Matrix.GeneralLinearGroup.map (n := Fin (n + 1)) (algebraMap (ZMod p) (Frac p))).range where
  toFun g := ⟨cutConjugation p n cut g, localGroup_le_constant p n hn cut g.property⟩
  inj' := by
    intro a b h
    apply Subtype.ext
    exact cutConjugation_injective p n cut (congrArg Subtype.val h)

instance localGroup_finite (hn : 1 ≤ n) (cut : Fin (n + 1)) :
    Finite (localGroup p n hn cut) :=
  Finite.of_injective (localGroupEmbedding p n hn cut)
    (localGroupEmbedding p n hn cut).injective

end

variable (p n : ℕ) [Fact p.Prime]

theorem localGroup_card_le (hn : 1 ≤ n) (cut : Fin (n + 1)) :
    Nat.card (localGroup p n hn cut) ≤
      Nat.card (Matrix.GeneralLinearGroup (Fin (n + 1)) (ZMod p)) := by
  exact (Nat.card_le_card_of_injective (localGroupEmbedding p n hn cut)
    (localGroupEmbedding p n hn cut).injective).trans
    (Nat.card_le_card_of_surjective _
      (Matrix.GeneralLinearGroup.map (n := Fin (n + 1))
        (algebraMap (ZMod p) (Frac p))).rangeRestrict_surjective)

theorem upper_transvection_mem_U {a : ℕ} {i j : Fin a} (hij : i < j) (f : R p) :
    Matrix.SpecialLinearGroup.transvection hij.ne f ∈ U p a := by
  change IsUpperUnitriangular a (evalZero p a _) 
  rw [evalZero, map_transvection]
  intro b c hcb
  change (1 + Matrix.single i j (Polynomial.evalRingHom 0 f)) b c = (1 : Matrix _ _ _) b c
  simp only [Matrix.add_apply]
  suffices Matrix.single i j (Polynomial.evalRingHom 0 f) b c = 0 by rw [this, add_zero]
  simp only [Matrix.single_apply]
  split_ifs with h
  · rcases h with ⟨rfl, rfl⟩
    exact False.elim (not_le_of_gt hij hcb)
  · rfl

theorem cycleRoot_mem_U (hn : 1 ≤ n) (j : Fin (n + 1)) :
    cycleRoot p n hn j ∈ U p (n + 1) := by
  by_cases h : j = 0
  · subst j
    have he : evalZero p (n + 1) (cycleRoot p n hn 0) = 1 := by
      simp [evalZero, cycleRoot, map_transvection]
    change evalZero p (n + 1) (cycleRoot p n hn 0) ∈ upperUnitriangular p (n + 1)
    rw [he]
    exact (upperUnitriangular p (n + 1)).one_mem
  · have hlt : edgeSource n j < j := by
      have hj : j.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using h
      simp only [edgeSource, dite_eq_right h, Fin.lt_def]
      omega
    simpa only [cycleRoot, ite_eq_right h] using upper_transvection_mem_U p hlt (1 : R p)

theorem localGroup_le_U (hn : 1 ≤ n) (cut : Fin (n + 1)) :
    localGroup p n hn cut ≤ U p (n + 1) := by
  apply (Subgroup.closure_le _).2
  rintro g ⟨j, _, rfl⟩
  exact cycleRoot_mem_U p n hn j

def uLocalGroup (hn : 1 ≤ n) (cut : Fin (n + 1)) : Subgroup (U p (n + 1)) :=
  (localGroup p n hn cut).subgroupOf (U p (n + 1))

def uLocalEmbedding (hn : 1 ≤ n) (cut : Fin (n + 1)) :
    uLocalGroup p n hn cut ↪ localGroup p n hn cut where
  toFun g := ⟨g.val.val, g.property⟩
  inj' := by
    intro g h he
    have hv : g.val.val = h.val.val := congrArg
      (fun x : localGroup p n hn cut => (x : Matrix.SpecialLinearGroup (Fin (n + 1)) (R p))) he
    exact Subtype.ext (Subtype.ext hv)

instance uLocalGroup_finite (hn : 1 ≤ n) (cut : Fin (n + 1)) :
    Finite (uLocalGroup p n hn cut) :=
  Finite.of_injective (uLocalEmbedding p n hn cut) (uLocalEmbedding p n hn cut).injective

def reducedLocalGroup (hn : 1 ≤ n) (m : ℕ) (cut : Fin (n + 1)) :
    Subgroup (Gquot p (n + 1) m) :=
  (uLocalGroup p n hn cut).map (QuotientGroup.mk' (uReduction p (n + 1) m).ker)

def reducedLocalMap (hn : 1 ≤ n) (m : ℕ) (cut : Fin (n + 1)) :
    uLocalGroup p n hn cut → reducedLocalGroup p n hn m cut :=
  fun g => ⟨QuotientGroup.mk' (uReduction p (n + 1) m).ker g.val, ⟨g.val, g.property, rfl⟩⟩

theorem reducedLocalMap_surjective (hn : 1 ≤ n) (m : ℕ) (cut : Fin (n + 1)) :
    Function.Surjective (reducedLocalMap p n hn m cut) := by
  rintro ⟨g, h⟩
  obtain ⟨u, hu, e⟩ := h
  exact ⟨⟨u, hu⟩, Subtype.ext e⟩

theorem reducedLocalGroup_card_le (hn : 1 ≤ n) (m : ℕ) (cut : Fin (n + 1)) :
    Nat.card (reducedLocalGroup p n hn m cut) ≤
      Nat.card (Matrix.GeneralLinearGroup (Fin (n + 1)) (ZMod p)) := by
  exact (Nat.card_le_card_of_surjective _ (reducedLocalMap_surjective p n hn m cut)).trans
    ((Nat.card_le_card_of_injective _ (uLocalEmbedding p n hn cut).injective).trans
      (localGroup_card_le p n hn cut))

theorem card_trunc (m : ℕ) : Nat.card (Trunc p m) = p ^ m := by
  let : Module.Finite (ZMod p) (Trunc p m) :=
    (Polynomial.monic_X.pow m).finite_quotient
  rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  congr 1
  change Module.finrank (ZMod p) (R p ⧸ Ideal.span {(Polynomial.X : R p) ^ m}) = m
  rw [finrank_quotient_span_eq_natDegree]
  simp

def reducedRoot {a : ℕ} {i j : Fin a} (hij : i < j) (m : ℕ) (f : Trunc p m) :
    (uReduction p a m).range :=
  ⟨Matrix.SpecialLinearGroup.transvection hij.ne f, by
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective f
    refine ⟨⟨Matrix.SpecialLinearGroup.transvection hij.ne F,
      upper_transvection_mem_U p hij F⟩, ?_⟩
    change Matrix.SpecialLinearGroup.map _ _ = _
    exact map_transvection _ _ _⟩

theorem reducedRoot_injective {a : ℕ} {i j : Fin a} (hij : i < j) (m : ℕ) :
    Function.Injective (reducedRoot p hij m) := by
  intro f g he
  have h := congrArg (fun x : (uReduction p a m).range => x.val i j) he
  simpa [reducedRoot, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.one_apply_ne hij.ne] using h

theorem gquot_card_lower (hn : 1 ≤ n) (m : ℕ) :
    p ^ m ≤ Nat.card (Gquot p (n + 1) m) := by
  let i : Fin (n + 1) := 0
  let j : Fin (n + 1) := ⟨1, by omega⟩
  have hij : i < j := by change (0 : ℕ) < 1; omega
  rw [← card_trunc p m]
  exact Nat.card_le_card_of_injective
    ((QuotientGroup.quotientKerEquivRange (uReduction p (n + 1) m)).symm ∘
      reducedRoot p hij m)
    ((QuotientGroup.quotientKerEquivRange (uReduction p (n + 1) m)).symm.injective.comp
      (reducedRoot_injective p hij m))

def cutPolynomial (cut i : Fin (n + 1)) : R p :=
  if i.val < cut.val then Polynomial.X else 1

@[simp] theorem cutUnit_coe (cut i : Fin (n + 1)) :
    (cutUnit p n cut i).val = algebraMap (R p) (Frac p) (cutPolynomial p n cut i) := by
  simp only [cutUnit, cutPolynomial]
  split_ifs <;> simp

theorem cutConjugation_apply (cut : Fin (n + 1))
    (A : Matrix.SpecialLinearGroup (Fin (n + 1)) (R p)) (i j : Fin (n + 1)) :
    cutConjugation p n cut A i j =
      (cutUnit p n cut i).val * algebraMap (R p) (Frac p) (A i j) *
        (cutUnit p n cut j).inv := by
  change ((diagonalUnits (cutUnit p n cut)).val *
    (A.val.map (algebraMap (R p) (Frac p))) *
    (diagonalUnits (cutUnit p n cut)).inv) i j = _
  simp [diagonalUnits, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem localGroup_entry_equation (hn : 1 ≤ n) (cut : Fin (n + 1))
    (A : localGroup p n hn cut) (i j : Fin (n + 1)) :
    ∃ c : ZMod p, cutPolynomial p n cut i * A.val i j =
      Polynomial.C c * cutPolynomial p n cut j := by
  obtain ⟨B, hB⟩ := localGroup_le_constant p n hn cut A.property
  refine ⟨B i j, IsFractionRing.injective (R p) (Frac p) ?_⟩
  have he := congrArg (fun g : Matrix.GeneralLinearGroup (Fin (n + 1)) (Frac p) => g i j) hB
  change algebraMap (ZMod p) (Frac p) (B i j) = cutConjugation p n cut A.val i j at he
  rw [cutConjugation_apply] at he
  have he' := congrArg (fun x : Frac p => x * (cutUnit p n cut j).val) he
  simp only [mul_assoc, Units.inv_val, mul_one] at he'
  rw [map_mul, map_mul, ← cutUnit_coe, ← cutUnit_coe]
  simpa only [IsScalarTower.algebraMap_apply (ZMod p) (R p) (Frac p), Polynomial.algebraMap_eq] using he'.symm

theorem localGroup_entry_degree_le_one (hn : 1 ≤ n) (cut : Fin (n + 1))
    (A : localGroup p n hn cut) (i j : Fin (n + 1)) :
    (A.val i j).natDegree ≤ 1 := by
  obtain ⟨c, hc⟩ := localGroup_entry_equation p n hn cut A i j
  unfold cutPolynomial at hc
  by_cases hi : i.val < cut.val
  · rw [ite_eq_left hi] at hc
    by_cases ha : A.val i j = 0
    · simp [ha]
    · have hd := congrArg Polynomial.natDegree hc
      rw [Polynomial.natDegree_mul Polynomial.X_ne_zero ha, Polynomial.natDegree_X] at hd
      have hright : (Polynomial.C c * (if j.val < cut.val then Polynomial.X else 1)).natDegree ≤ 1 := by
        exact (Polynomial.natDegree_C_mul_le _ _).trans (by split_ifs <;> simp)
      omega
  · rw [ite_eq_right hi, one_mul] at hc
    rw [hc]
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by split_ifs <;> simp)

theorem eq_of_small_degree_congruent {m : ℕ} (hm : 2 ≤ m) (f g : R p)
    (hf : f.natDegree ≤ 1) (hg : g.natDegree ≤ 1)
    (he : Ideal.Quotient.mk (powerIdeal p m) f = Ideal.Quotient.mk (powerIdeal p m) g) :
    f = g := by
  have hdvd : Polynomial.X ^ m ∣ f - g := by
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  by_contra hfg
  have hfg0 : f - g ≠ 0 := sub_ne_zero.mpr hfg
  have hle := Polynomial.natDegree_le_of_dvd hdvd hfg0
  rw [Polynomial.natDegree_X_pow] at hle
  have hsmall := Polynomial.natDegree_sub_le f g
  omega

theorem localGroups_reduction_injective (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m)
    (cut cut' : Fin (n + 1)) (A : localGroup p n hn cut) (B : localGroup p n hn cut')
    (he : Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m)) A.val =
      Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m)) B.val) :
    A.val = B.val := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  apply eq_of_small_degree_congruent p hm _ _
    (localGroup_entry_degree_le_one p n hn cut A i j)
    (localGroup_entry_degree_le_one p n hn cut' B i j)
  exact congrArg (fun g : Matrix.SpecialLinearGroup (Fin (n + 1)) (Trunc p m) => g i j) he

def localQuotientMap (hn : 1 ≤ n) (m : ℕ) (cut : Fin (n + 1)) :
    localGroup p n hn cut →* Gquot p (n + 1) m :=
  (QuotientGroup.mk' (uReduction p (n + 1) m).ker).comp
    (Subgroup.inclusion (localGroup_le_U p n hn cut))

theorem localQuotientMap_injective (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m)
    (cut : Fin (n + 1)) : Function.Injective (localQuotientMap p n hn m cut) := by
  intro A B h
  apply Subtype.ext
  apply localGroups_reduction_injective p n hn hm cut cut A B
  exact congrArg (fun g : Gquot p (n + 1) m =>
    (QuotientGroup.quotientKerEquivRange (uReduction p (n + 1) m) g).val) h

theorem localGroup_isPGroup (hn : 1 ≤ n) (cut : Fin (n + 1)) :
    IsPGroup p (localGroup p n hn cut) :=
  (gquot_isPGroup p (n + 1) 2 Fact.out).of_injective
    (localQuotientMap p n hn 2 cut) (localQuotientMap_injective p n hn le_rfl cut)

theorem localGroup_odd (hn : 1 ≤ n) (hp : Odd p) (cut : Fin (n + 1)) :
    Odd (Nat.card (localGroup p n hn cut)) := by
  obtain ⟨r, hr⟩ := (localGroup_isPGroup p n hn cut).exists_card_eq
  rw [hr]
  exact hp.pow

theorem reducedLocalGroup_intersection (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m)
    (i j : Fin (n + 1)) :
    (uLocalGroup p n hn i ⊓ uLocalGroup p n hn j).map
        (QuotientGroup.mk' (uReduction p (n + 1) m).ker) =
      reducedLocalGroup p n hn m i ⊓ reducedLocalGroup p n hn m j := by
  apply le_antisymm
  · exact le_inf (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right)
  · rintro g ⟨hi, hj⟩
    obtain ⟨a, ha, ha'⟩ := Subgroup.mem_map.mp hi
    obtain ⟨b, hb, hb'⟩ := Subgroup.mem_map.mp hj
    have he : a.val = b.val := by
      apply localGroups_reduction_injective p n hn hm i j ⟨a.val, ha⟩ ⟨b.val, hb⟩
      exact congrArg (fun g : Gquot p (n + 1) m =>
        (QuotientGroup.quotientKerEquivRange (uReduction p (n + 1) m) g).val)
        (ha'.trans hb'.symm)
    have hab : a = b := Subtype.ext he
    exact Subgroup.mem_map.mpr ⟨a, ⟨ha, hab.symm ▸ hb⟩, ha'⟩

end CoboundaryExpanders.Construction

end

end OAI
