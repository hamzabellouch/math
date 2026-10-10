import OAI.RepresentationTheory.KazhdanLusztig.CanonicalKL

namespace OAI

/-!
Interval restrictions, dihedral Coxeter and Hecke calculations, and the genuine square-parameter R normalization.
-/

section

namespace KLInvariance

universe u₁ v₁ u₂ v₂
variable {B : Type u₁} {W : Type v₁} [Group W] {M : CoxeterMatrix B}
variable {B' : Type u₂} {W' : Type v₂} [Group W'] {M' : CoxeterMatrix B'}

/-- Restriction of the actual interval isomorphism to any subinterval. This
is the same unlabeled map, not a new isomorphism with extra structure. -/
def intervalIso_restrict (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')
    {u b : W} {u' b' : W'} (ι : Interval cs u b ≃o Interval cs' u' b')
    (x y : Interval cs u b) :
    Interval cs x.val y.val ≃o Interval cs' (ι x).val (ι y).val where
  toFun z :=
    let zI : Interval cs u b := ⟨z.val, bruhat_trans cs x.property.1 z.property.1,
      bruhat_trans cs z.property.2 y.property.2⟩
    ⟨(ι zI).val, ι.monotone (show x ≤ zI from z.property.1),
      ι.monotone (show zI ≤ y from z.property.2)⟩
  invFun z :=
    let zI : Interval cs' u' b' := ⟨z.val,
      bruhat_trans cs' (ι x).property.1 z.property.1,
      bruhat_trans cs' z.property.2 (ι y).property.2⟩
    ⟨(ι.symm zI).val,
      by
        change x ≤ ι.symm zI
        simpa only [OrderIso.symm_apply_apply] using
          ι.symm.monotone (show ι x ≤ zI from z.property.1),
      by
        change ι.symm zI ≤ y
        simpa only [OrderIso.symm_apply_apply] using
          ι.symm.monotone (show zI ≤ ι y from z.property.2)⟩
  left_inv z := by
    apply Subtype.ext
    let zI : Interval cs u b := ⟨z.val, bruhat_trans cs x.property.1 z.property.1,
      bruhat_trans cs z.property.2 y.property.2⟩
    change (ι.symm (ι zI)).val = zI.val
    rw [ι.symm_apply_apply]
  right_inv z := by
    apply Subtype.ext
    let zI : Interval cs' u' b' := ⟨z.val,
      bruhat_trans cs' (ι x).property.1 z.property.1,
      bruhat_trans cs' z.property.2 (ι y).property.2⟩
    change (ι (ι.symm zI)).val = zI.val
    rw [ι.apply_symm_apply]
  map_rel_iff' := by
    intro z w
    exact ι.map_rel_iff

@[simp] theorem intervalIso_restrict_val (cs : CoxeterSystem M W)
    (cs' : CoxeterSystem M' W') {u b : W} {u' b' : W'}
    (ι : Interval cs u b ≃o Interval cs' u' b') (x y : Interval cs u b)
    (z : Interval cs x.val y.val) :
    (intervalIso_restrict cs cs' ι x y z).val =
      (ι ⟨z.val, bruhat_trans cs x.property.1 z.property.1,
        bruhat_trans cs z.property.2 y.property.2⟩).val := rfl

end KLInvariance

namespace KLInvariance.Dihedral

variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}

/-- The alternating expression starting with `i`, unlike Mathlib's
`alternatingWord`, which specifies the final letter. -/
def alt (i : Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => i :: alt (!i) n

@[simp] theorem alt_zero (i : Bool) : alt i 0 = [] := rfl
@[simp] theorem alt_succ (i : Bool) (n : ℕ) : alt i (n+1) = i :: alt (!i) n := rfl
@[simp] theorem length_alt (i : Bool) (n : ℕ) : (alt i n).length = n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [ih]

@[simp] theorem take_alt (i : Bool) (k n : ℕ) : (alt i n).take k = alt i (min k n) := by
  induction n generalizing i k with
  | zero => simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k => simp [ih]

theorem reduced_cons_cons_ne (cs : CoxeterSystem M W) {i j : Bool} {ω : List Bool}
    (h : cs.IsReduced (i :: j :: ω)) : i ≠ j := by
  rintro rfl
  have hlen := cs.length_wordProd_le ω
  have heq := h.eq
  simp only [cs.wordProd_cons, cs.simple_mul_simple_cancel_left, List.length_cons] at heq
  omega

theorem reduced_cons_eq_alt (cs : CoxeterSystem M W) (i : Bool) (ω : List Bool)
    (h : cs.IsReduced (i :: ω)) : i :: ω = alt i (ω.length + 1) := by
  induction ω generalizing i with
  | nil => simp
  | cons j ω ih =>
    have hj : j = !i := by
      have := reduced_cons_cons_ne cs h
      cases i <;> cases j <;> simp_all
    have hω : cs.IsReduced (j :: ω) := by simpa using h.drop 1
    rw [show (j :: ω).length + 1 = (ω.length + 1) + 1 by rfl, alt_succ]
    congr 1
    rw [ih j hω, hj]

theorem reduced_eq_alt (cs : CoxeterSystem M W) (ω : List Bool)
    (h : cs.IsReduced ω) : ∃ i, ω = alt i ω.length := by
  cases ω with
  | nil => exact ⟨false, rfl⟩
  | cons i ω => exact ⟨i, reduced_cons_eq_alt cs i ω h⟩

theorem exists_alt (cs : CoxeterSystem M W) (w : W) :
    ∃ i, w = cs.wordProd (alt i (cs.length w)) := by
  obtain ⟨ω, hω, hw⟩ := cs.exists_isReduced w
  obtain ⟨i, hi⟩ := reduced_eq_alt cs ω hω
  refine ⟨i, ?_⟩
  rw [hw, hω.eq, ← hi]

theorem reduced_alt_take (cs : CoxeterSystem M W) {i : Bool} {k n : ℕ}
    (h : cs.IsReduced (alt i n)) (hk : k ≤ n) : cs.IsReduced (alt i k) := by
  simpa only [take_alt, Nat.min_eq_left hk] using h.take k

theorem alt_sublist (i : Bool) {k n : ℕ} (h : k ≤ n) : (alt i k).Sublist (alt i n) := by
  simpa only [take_alt, Nat.min_eq_left h] using List.take_sublist k (alt i n)

end KLInvariance.Dihedral

namespace KLInvariance.Dihedral

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}

/-- In a rank-two Coxeter system, every strictly shorter element lies below
every longer element. This uses the actual Bruhat subword theorem. -/
theorem shorter_bruhat (cs : CoxeterSystem M W) {x w : W}
    (h : cs.length x < cs.length w) : BruhatLE cs x w := by
  obtain ⟨i, hi⟩ := exists_alt cs w
  obtain ⟨j, hj⟩ := exists_alt cs x
  have hr : cs.IsReduced (alt i (cs.length w)) := by
    change cs.length (cs.wordProd (alt i (cs.length w))) = (alt i (cs.length w)).length
    rw [← hi, length_alt]
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (show cs.length w ≠ 0 by omega)
  rw [hn] at hi hr h
  rw [hi, hj]
  apply bruhat_of_subword cs _ hr
  by_cases hji : j = i
  · subst j
    exact alt_sublist i (by omega)
  · have hj' : j = !i := by cases i <;> cases j <;> first | rfl | exact (hji rfl).elim
    rw [hj', alt_succ]
    exact (alt_sublist (!i) (by omega)).cons i

theorem bruhat_iff_length_lt_or_eq (cs : CoxeterSystem M W) (x w : W) :
    BruhatLE cs x w ↔ cs.length x < cs.length w ∨ x = w := by
  constructor
  · intro h
    by_cases he : x = w
    · exact Or.inr he
    · exact Or.inl (length_lt_of_bruhat_ne cs h he)
  · rintro (h | rfl)
    · exact shorter_bruhat cs h
    · exact bruhat_refl cs _

theorem eq_alt_of_descent (cs : CoxeterSystem M W) (i : Bool) {w : W}
    (h : cs.length (cs.simple i * w) < cs.length w) :
    w = cs.wordProd (alt i (cs.length w)) := by
  obtain ⟨ω, hω, hw⟩ := cs.exists_isReduced (cs.simple i * w)
  have hlen : cs.length w = ω.length + 1 := by
    have := cs.length_simple_mul w i
    rw [hw, hω.eq] at this h
    omega
  have hp : cs.wordProd (i :: ω) = w := by
    simp only [cs.wordProd_cons, ← hw, cs.simple_mul_simple_cancel_left]
  have hr : cs.IsReduced (i :: ω) := by
    simpa only [CoxeterSystem.IsReduced, hp, List.length_cons] using hlen
  rw [hlen, ← reduced_cons_eq_alt cs i ω hr, hp]

end KLInvariance.Dihedral

namespace KLInvariance.Dihedral

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

open Hecke (Space basis)
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
variable {C : Type*} [CommRing C]

noncomputable def lowerSum (cs : CoxeterSystem M W) (w : W) : Space W C :=
  ∑ z ∈ lowerFinset cs w, basis z

@[simp] theorem lowerSum_coeff (cs : CoxeterSystem M W) (w x : W) :
    (lowerSum cs w : Space W C) x = if BruhatLE cs x w then 1 else 0 := by
  classical
  simp [lowerSum, basis, Finsupp.single_apply, eq_comm]

@[simp] theorem lowerSum_one (cs : CoxeterSystem M W) :
    (lowerSum cs 1 : Space W C) = basis 1 := by
  classical
  ext x
  simp only [lowerSum_coeff, basis, Finsupp.single_apply]
  have h : BruhatLE cs x 1 ↔ 1 = x := by
    rw [bruhat_iff_length_lt_or_eq]
    simp [eq_comm]
  rw [h]

/-- The two members of an s-string enter a lower ideal together precisely
on the common lower interval appearing in the source's rank-two product. -/
theorem double_string (cs : CoxeterSystem M W) (i : Bool) (n : ℕ)
    (hr : cs.IsReduced (alt i (n+2))) (x : W) :
    (BruhatLE cs x (cs.wordProd (alt (!i) (n+1))) ∧
      BruhatLE cs (cs.simple i * x) (cs.wordProd (alt (!i) (n+1)))) ↔
    (0 < n ∧ BruhatLE cs x (cs.wordProd (alt i n))) := by
  have hr' : cs.IsReduced (alt (!i) (n+1)) := by simpa using hr.drop 1
  have hrp := reduced_alt_take cs hr (show n ≤ n+2 by omega)
  have hlenw : cs.length (cs.wordProd (alt i (n+2))) = n+2 := by
    simpa only [length_alt] using hr.eq
  have hlenz : cs.length (cs.wordProd (alt (!i) (n+1))) = n+1 := by
    simpa only [length_alt] using hr'.eq
  have hlenp : cs.length (cs.wordProd (alt i n)) = n := by
    simpa only [length_alt] using hrp.eq
  have hsz : cs.simple i * cs.wordProd (alt (!i) (n+1)) =
      cs.wordProd (alt i (n+2)) := by rw [alt_succ i (n+1), cs.wordProd_cons]
  constructor
  · rintro ⟨hx, hsx⟩
    have hxlen := length_le_of_bruhat cs hx
    have hsxlen := length_le_of_bruhat cs hsx
    have hxl : cs.length x < n+1 := by
      rcases (bruhat_iff_length_lt_or_eq cs _ _).mp hx with h | rfl
      · omega
      · rw [hsz, hlenw] at hsxlen
        omega
    have hsxl : cs.length (cs.simple i * x) < n+1 := by
      rcases (bruhat_iff_length_lt_or_eq cs _ _).mp hsx with h | h
      · omega
      · have heq : x = cs.wordProd (alt i (n+2)) := by
          rw [← hsz, ← h, cs.simple_mul_simple_cancel_left]
        rw [heq, hlenw] at hxl
        omega
    have hchange := cs.length_simple_mul x i
    have hn : 0 < n := by omega
    refine ⟨hn, ?_⟩
    by_cases hxlt : cs.length x < n
    · exact shorter_bruhat cs (by omega)
    · have hxi : cs.length x = n := by omega
      have hdesc : cs.length (cs.simple i * x) < cs.length x := by omega
      have heq := eq_alt_of_descent cs i hdesc
      rw [hxi] at heq
      rw [heq]
      exact bruhat_refl cs _
  · rintro ⟨hn, hx⟩
    have hxlen := length_le_of_bruhat cs hx
    constructor
    · exact shorter_bruhat cs (by omega)
    · by_cases hxlt : cs.length x < n
      · have := cs.length_simple_mul x i
        exact shorter_bruhat cs (by omega)
      · have heq : x = cs.wordProd (alt i n) := by
          rcases (bruhat_iff_length_lt_or_eq cs _ _).mp hx with h | h
          · omega
          · exact h
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
        have hrpt : cs.IsReduced (alt (!i) k) := by simpa using hrp.drop 1
        have hpk : cs.length (cs.simple i * x) = k := by
          rw [heq, alt_succ, cs.wordProd_cons, cs.simple_mul_simple_cancel_left,
            hrpt.eq, length_alt]
        exact shorter_bruhat cs (by omega)

end KLInvariance.Dihedral

namespace KLInvariance.Dihedral

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

open Hecke (Space basis)
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
variable {C : Type*} [CommRing C]

theorem left_plus_coeff (cs : CoxeterSystem M W) (q : Cˣ) (i : Bool)
    (v : Space W C) (x : W) :
    (v + HeckeQ.left cs (q : C) i v) x =
      if cs.length (cs.simple i * x) < cs.length x then
        v (cs.simple i * x) + (q : C) * v x
      else v x + (q : C) * v (cs.simple i * x) := by
  have h := congrArg (fun t : Space W C => (q : C) * t x)
    (HeckeQ.leftInv_apply cs q i v)
  simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.sub_apply, ← mul_assoc,
    q.mul_inv, one_mul] at h
  rw [HeckeQ.leftInv_coeff] at h
  simp only [Finsupp.add_apply]
  split_ifs at h ⊢
  · linear_combination -h + v (cs.simple i * x) * q.mul_inv
  · linear_combination -h + v x * q.mul_inv

theorem union_string (cs : CoxeterSystem M W) (i : Bool) {z : W}
    (hz : cs.length z < cs.length (cs.simple i * z)) (x : W) :
    BruhatLE cs x (cs.simple i * z) ↔
      BruhatLE cs x z ∨ BruhatLE cs (cs.simple i * x) z := by
  have hsz : cs.length (cs.simple i * (cs.simple i * z)) <
      cs.length (cs.simple i * z) := by simpa using hz
  constructor
  · intro h
    have hh := lowerSimple_mono cs i h
    simp only [lowerSimple, cs.simple_mul_simple_cancel_left] at hh
    split_ifs at hh with hx
    · exact Or.inr hh
    · exact Or.inl hh
  · rintro (h | h)
    · apply bruhat_trans cs h
      exact Relation.ReflTransGen.single ⟨hz, cs.simple i, cs.isReflection_simple i, rfl⟩
    · simpa only [cs.simple_mul_simple_cancel_left] using
        Hecke.simple_mul_le_ascent cs i h hz

noncomputable def correction (cs : CoxeterSystem M W) (i : Bool) (n : ℕ) : Space W C :=
  if n = 0 then 0 else lowerSum cs (cs.wordProd (alt i n))

@[simp] theorem correction_coeff (cs : CoxeterSystem M W) (i : Bool) (n : ℕ) (x : W) :
    (correction cs i n : Space W C) x =
      if 0 < n ∧ BruhatLE cs x (cs.wordProd (alt i n)) then 1 else 0 := by
  classical
  by_cases h : n = 0
  · simp [correction, h]
  · have hn : 0 < n := Nat.pos_of_ne_zero h
    simp [correction, h, hn]

/-- The Hecke sum identity `loc:dihedral-product`, before normalization by
q to a half-integer power. Every interval here is genuine strong Bruhat. -/
theorem lowerSum_product (cs : CoxeterSystem M W) (q : Cˣ) (i : Bool) (n : ℕ)
    (hr : cs.IsReduced (alt i (n+2))) :
    lowerSum cs (cs.wordProd (alt (!i) (n+1))) +
      HeckeQ.left cs (q : C) i (lowerSum cs (cs.wordProd (alt (!i) (n+1)))) =
    lowerSum cs (cs.wordProd (alt i (n+2))) + (q : C) • correction cs i n := by
  classical
  have hr' : cs.IsReduced (alt (!i) (n+1)) := by simpa using hr.drop 1
  have hz : cs.length (cs.wordProd (alt (!i) (n+1))) <
      cs.length (cs.simple i * cs.wordProd (alt (!i) (n+1))) := by
    rw [← cs.wordProd_cons, ← alt_succ, hr.eq, hr'.eq, length_alt, length_alt]
    omega
  ext x
  rw [left_plus_coeff, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    correction_coeff, lowerSum_coeff, lowerSum_coeff, lowerSum_coeff]
  have hu := union_string cs i hz x
  rw [← cs.wordProd_cons, ← alt_succ] at hu
  have hd := double_string cs i n hr x
  simp only [hu, ← hd]
  by_cases hdesc : cs.length (cs.simple i * x) < cs.length x
  · have hclosure : BruhatLE cs x (cs.wordProd (alt (!i) (n+1))) →
        BruhatLE cs (cs.simple i * x) (cs.wordProd (alt (!i) (n+1))) := by
      intro h
      apply bruhat_trans cs _ h
      exact Relation.ReflTransGen.single
        ⟨hdesc, cs.simple i, cs.isReflection_simple i, by simp⟩
    by_cases hx : BruhatLE cs x (cs.wordProd (alt (!i) (n+1)))
    · simp [-alt_succ, hdesc, hx, hclosure hx]
    · by_cases hs : BruhatLE cs (cs.simple i * x) (cs.wordProd (alt (!i) (n+1))) <;>
        simp [-alt_succ, hdesc, hx, hs]
  · have hasc : cs.length x < cs.length (cs.simple i * x) := by
      have := cs.length_simple_mul x i
      omega
    have hclosure : BruhatLE cs (cs.simple i * x) (cs.wordProd (alt (!i) (n+1))) →
        BruhatLE cs x (cs.wordProd (alt (!i) (n+1))) := by
      intro h
      apply bruhat_trans cs _ h
      exact Relation.ReflTransGen.single
        ⟨hasc, cs.simple i, cs.isReflection_simple i, rfl⟩
    by_cases hs : BruhatLE cs (cs.simple i * x) (cs.wordProd (alt (!i) (n+1)))
    · simp [-alt_succ, hdesc, hs, hclosure hs]
    · by_cases hx : BruhatLE cs x (cs.wordProd (alt (!i) (n+1))) <;>
        simp [-alt_succ, hdesc, hx, hs]

end KLInvariance.Dihedral

namespace KLInvariance.HeckeQ

universe uR vR
variable {B : Type uR} {W : Type vR} [Group W] {M : CoxeterMatrix B}
variable {C : Type*} [CommRing C]

noncomputable def dualR (cs : CoxeterSystem M W) (q : Cˣ) (x y : W) : C :=
  (-(q : C)) ^ cs.length y * (-(↑q⁻¹ : C)) ^ cs.length x * rValue cs q⁻¹ x y

@[simp] theorem dualR_diagonal (cs : CoxeterSystem M W) (q : Cˣ) (x : W) :
    dualR cs q x x = 1 := by
  rw [dualR, rValue_diagonal, mul_one, ← mul_pow]
  simp

theorem dualR_zero (cs : CoxeterSystem M W) (q : Cˣ) (x y : W)
    (h : ¬BruhatLE cs x y) : dualR cs q x y = 0 := by
  simp [dualR, rValue_zero cs q⁻¹ x y h]

theorem dualR_recursion (cs : CoxeterSystem M W) (q : Cˣ) (x y : W) (i : B)
    (hy : cs.length (cs.simple i * y) < cs.length y) :
    dualR cs q x y =
      if cs.length (cs.simple i * x) < cs.length x then
        dualR cs q (cs.simple i * x) (cs.simple i * y)
      else ((q : C) - 1) * dualR cs q x (cs.simple i * y) +
        (q : C) * dualR cs q (cs.simple i * x) (cs.simple i * y) := by
  have hyl : cs.length y = cs.length (cs.simple i * y) + 1 := by
    have := cs.length_simple_mul y i
    omega
  unfold dualR
  rw [rValue_recursion cs q⁻¹ x y i hy]
  split_ifs with hx
  · have hxl : cs.length x = cs.length (cs.simple i * x) + 1 := by
      have := cs.length_simple_mul x i
      omega
    rw [hyl, hxl, pow_succ, pow_succ]
    calc
      _ = (-(q:C)) ^ cs.length (cs.simple i * y) *
          (-(↑q⁻¹:C)) ^ cs.length (cs.simple i * x) *
          rValue cs q⁻¹ (cs.simple i * x) (cs.simple i * y) *
          ((q:C) * (↑q⁻¹:C)) := by ring
      _ = _ := by rw [q.mul_inv, mul_one]
  · have hxl : cs.length (cs.simple i * x) = cs.length x + 1 := by
      have := cs.length_simple_mul x i
      omega
    rw [hyl, hxl, pow_succ, pow_succ]
    have hq : (-(q:C)) * ((↑q⁻¹:C) - 1) = (q:C) - 1 := by
      rw [mul_sub, neg_mul, q.mul_inv, mul_one]
      ring
    calc
      _ = (-(q:C)) ^ cs.length (cs.simple i * y) *
          (-(↑q⁻¹:C)) ^ cs.length x *
          ((-(q:C)) * ((↑q⁻¹:C) - 1)) * rValue cs q⁻¹ x (cs.simple i * y) +
          (q:C) * ((-(q:C)) ^ cs.length (cs.simple i * y) *
          ((-(↑q⁻¹:C)) ^ cs.length x * (-(↑q⁻¹:C))) *
          rValue cs q⁻¹ (cs.simple i * x) (cs.simple i * y)) := by ring
      _ = _ := by rw [hq]; ring

/-- Signed inversion symmetry of actual equal-parameter R-values, proved
from all-descent recurrence, not imposed as an additional normalization. -/
theorem rValue_eq_dualR (cs : CoxeterSystem M W) (q : Cˣ) (x y : W) :
    rValue cs q x y = dualR cs q x y := by
  suffices ∀ n : ℕ, ∀ y : W, cs.length y = n → ∀ x,
      rValue cs q x y = dualR cs q x y by
    exact this _ y rfl x
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hy x
    by_cases hy1 : y = 1
    · subst y
      by_cases hx1 : x = 1
      · subst x
        simp
      · have hnot : ¬BruhatLE cs x 1 := by
          intro h
          have hl := length_le_of_bruhat cs h
          have hl0 : cs.length x = 0 := by simpa using hl
          exact hx1 (cs.length_eq_zero_iff.mp hl0)
        rw [rValue_zero cs q x 1 hnot, dualR_zero cs q x 1 hnot]
    · obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one hy1
      have hsmall : cs.length (cs.simple i * y) < n := hy ▸ hi
      rw [rValue_recursion cs q x y i hi, dualR_recursion cs q x y i hi,
        ih _ hsmall _ rfl x, ih _ hsmall _ rfl (cs.simple i * x)]

/-- R at the inverse parameter is exactly the corresponding bar coefficient
with the bottom q-power. This is the coefficient form used below. -/
theorem rValue_inverse_eq_barBasis (cs : CoxeterSystem M W) (q : Cˣ) (x y : W) :
    rValue cs q⁻¹ x y = (q:C) ^ cs.length x * barBasis cs q y x := by
  rw [rValue_eq_dualR cs q⁻¹, dualR, inv_inv, rValue]
  simp only [neg_pow (↑q⁻¹:C), neg_pow (q:C)]
  have hsign (n : ℕ) : (-1:C)^n * (-1:C)^n = 1 := by
    rw [← mul_pow]; simp
  calc
    _ = ((-1:C)^cs.length y * (-1:C)^cs.length y) *
        ((-1:C)^cs.length x * (-1:C)^cs.length x) *
        (((↑q⁻¹:C) * (q:C)) ^ cs.length y) *
        (q:C)^cs.length x * barBasis cs q y x := by ring
    _ = _ := by rw [hsign, hsign, q.inv_mul]; simp

end KLInvariance.HeckeQ

namespace KLInvariance.Dihedral

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

open Hecke (Space basis)
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
variable {C : Type*} [CommRing C]

@[simp] theorem lowerSum_simple (cs : CoxeterSystem M W) (i : Bool) :
    (lowerSum cs (cs.simple i) : Space W C) = basis 1 + basis (cs.simple i) := by
  classical
  ext x
  rw [lowerSum_coeff, bruhat_iff_length_lt_or_eq, cs.length_simple]
  simp only [Nat.lt_one_iff, cs.length_eq_zero_iff, Finsupp.add_apply, basis,
    Finsupp.single_apply]
  have hi : cs.simple i ≠ 1 := by
    intro h
    have := cs.length_simple i
    simp [h] at this
  by_cases hx : x = 1
  · subst x
    simp [hi]
  · by_cases hs : x = cs.simple i
    · subst x
      simp [hi, Ne.symm hi]
    · simp [hx, hs, Ne.symm hx, Ne.symm hs]

theorem plus_leftInv (cs : CoxeterSystem M W) (q : Cˣ) (i : Bool)
    (v : Space W C) :
    v + HeckeQ.leftInv cs q i v =
      (↑q⁻¹:C) • (v + HeckeQ.left cs (q:C) i v) := by
  rw [HeckeQ.leftInv_apply, smul_sub, smul_smul, mul_sub, q.inv_mul, mul_one]
  module

/-- Unnormalized form of bar invariance of the dihedral constant sums. -/
theorem bar_lowerSum_alt (cs : CoxeterSystem M W) (q : Cˣ) (i : Bool) (n : ℕ)
    (hr : cs.IsReduced (alt i n)) :
    HeckeQ.barLinear cs q (lowerSum cs (cs.wordProd (alt i n))) =
      (↑q⁻¹:C)^n • lowerSum cs (cs.wordProd (alt i n)) := by
  induction n using Nat.strong_induction_on generalizing i with
  | h n ih =>
    rcases n with _ | (_ | n)
    · simp
    · have hasc : cs.length (1:W) < cs.length (cs.simple i * 1) := by simp
      have hb := HeckeQ.barBasis_simple_mul_ascent cs q i 1 hasc
      simp only [mul_one, HeckeQ.barBasis_one] at hb
      simp only [alt_succ, alt_zero, cs.wordProd_singleton, lowerSum_simple,
        map_add, HeckeQ.barLinear_basis, HeckeQ.barBasis_one, hb]
      rw [plus_leftInv, HeckeQ.left_basis]
      simp
    · have hr' : cs.IsReduced (alt (!i) (n+1)) := by simpa using hr.drop 1
      have hrp := reduced_alt_take cs hr (show n ≤ n+2 by omega)
      have hz := ih (n+1) (by omega) (!i) hr'
      have hc : HeckeQ.barLinear cs q (correction cs i n) =
          (↑q⁻¹:C)^n • correction cs i n := by
        by_cases hn : n = 0
        · simp [correction, hn]
        · simp only [correction, ite_eq_right hn]
          exact ih n (by omega) i hrp
      have hprod := lowerSum_product cs q i n hr
      have hbar := congrArg (HeckeQ.barLinear cs q)
        (lowerSum_product cs q⁻¹ i n hr)
      have hinter := congrArg (fun f : Module.End C (Space W C) =>
          f (lowerSum cs (cs.wordProd (alt (!i) (n+1)))))
        (HeckeQ.barLinear_left cs q i)
      simp only [map_add, map_smul, Module.End.mul_apply] at hbar hinter
      rw [hinter, hz, map_smul, ← smul_add, plus_leftInv, hprod] at hbar
      simp only [smul_add, smul_smul, hc] at hbar
      have hq1 : (↑q⁻¹:C)^(n+1) * (↑q⁻¹:C) = (↑q⁻¹:C)^(n+2) := by
        exact (pow_succ (↑q⁻¹:C) (n+1)).symm
      have hq2 : (↑q⁻¹:C)^(n+1) * ((↑q⁻¹:C) * (q:C)) =
          (↑q⁻¹:C) * (↑q⁻¹:C)^n := by rw [q.inv_mul, mul_one, pow_succ'];
      rw [hq1, hq2] at hbar
      exact add_right_cancel hbar.symm

theorem bar_lowerSum (cs : CoxeterSystem M W) (q : Cˣ) (w : W) :
    HeckeQ.barLinear cs q (lowerSum cs w) =
      (↑q⁻¹:C)^cs.length w • lowerSum cs w := by
  obtain ⟨i, hi⟩ := exists_alt cs w
  have hr : cs.IsReduced (alt i (cs.length w)) := by
    simp only [CoxeterSystem.IsReduced, ← hi, length_alt]
  simpa only [← hi] using bar_lowerSum_alt cs q i (cs.length w) hr

end KLInvariance.Dihedral

namespace KLInvariance.Dihedral

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

open Hecke (Space basis)
open Polynomial
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
variable {C : Type*} [CommRing C]

theorem rValue_sum (cs : CoxeterSystem M W) (q : Cˣ) (x y : W)
    (hxy : BruhatLE cs x y) :
    ∑ z ∈ lowerFinset cs y, HeckeQ.rValue cs q x z =
      (q:C) ^ rankDifference cs x y := by
  classical
  have hb := congrArg (fun f : Space W C => f x) (bar_lowerSum cs q⁻¹ y)
  simp only [Finsupp.smul_apply, smul_eq_mul, inv_inv, lowerSum_coeff,
    ite_eq_left hxy, mul_one] at hb
  rw [lowerSum, map_sum] at hb
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, HeckeQ.barLinear_basis] at hb
  have hlen : cs.length y = cs.length x + rankDifference cs x y := by
    have := length_le_of_bruhat cs hxy
    unfold rankDifference
    omega
  calc
    _ = (↑q⁻¹:C)^cs.length x *
        ∑ z ∈ lowerFinset cs y, HeckeQ.barBasis cs q⁻¹ z x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      simpa using HeckeQ.rValue_inverse_eq_barBasis cs q⁻¹ x z
    _ = (↑q⁻¹:C)^cs.length x * (q:C)^cs.length y := by rw [hb]
    _ = _ := by
      rw [hlen, pow_add]
      calc
        _ = ((↑q⁻¹:C) * (q:C))^cs.length x * (q:C)^rankDifference cs x y := by
          rw [mul_pow]; ring
        _ = _ := by rw [q.inv_mul]; simp

theorem rPolynomial_sum (cs : CoxeterSystem M W) (x y : W)
    (hxy : BruhatLE cs x y) :
    ∑ z ∈ lowerFinset cs y, OrdinaryR.polynomial cs x z =
      (X:ℤ[X]) ^ rankDifference cs x y := by
  apply Polynomial.toLaurent_injective
  simpa using rValue_sum cs OrdinaryR.variableUnit x y hxy

noncomputable def constantP (cs : CoxeterSystem M W) (x y : W) : ℤ[X] :=
  if BruhatLE cs x y then 1 else 0

theorem constant_normalizedKL (cs : CoxeterSystem M W) :
    NormalizedKL cs (OrdinaryR.polynomial cs, constantP cs) where
  R_diagonal := OrdinaryR.polynomial_diagonal cs
  R_zero := OrdinaryR.polynomial_zero cs
  R_recursion := OrdinaryR.polynomial_recursion cs
  P_diagonal := by intro x; simp [constantP, bruhat_refl cs x]
  P_zero := by intro x y h; simp [constantP, h]
  P_degree := by
    intro x y hxy hne
    have := length_lt_of_bruhat_ne cs hxy hne
    simp only [constantP, ite_eq_left hxy, natDegree_one, mul_zero]
    unfold rankDifference
    omega
  reciprocity := by
    intro x y hxy
    simp only [constantP, ite_eq_left hxy, reflect_one]
    classical
    let := interval_finite cs x y
    let : Fintype (Interval cs x y) := Fintype.ofFinite _
    rw [finsum_eq_sum_of_fintype]
    have heq : (∑ z : Interval cs x y,
        OrdinaryR.polynomial cs x z.val * (if BruhatLE cs z.val y then 1 else 0)) =
        ∑ z : Interval cs x y, OrdinaryR.polynomial cs x z.val := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [ite_eq_left z.property.2, mul_one]
    rw [heq]
    have hsum := Finset.sum_subtype (F := (inferInstance : Fintype (Interval cs x y)))
      ((lowerFinset cs y).filter (fun z => BruhatLE cs x z))
      (fun z => by simp only [Finset.mem_filter, mem_lowerFinset]; exact and_comm)
      (fun z => OrdinaryR.polynomial cs x z)
    symm
    refine hsum.symm.trans (Eq.trans ?_ (rPolynomial_sum cs x y hxy))
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro z hz hnot
    have hnxz : ¬BruhatLE cs x z := fun hxz => hnot (Finset.mem_filter.mpr ⟨hz, hxz⟩)
    exact OrdinaryR.polynomial_zero cs x z hnxz

/-- The manuscript's necessary dihedral calculation (`loc:dihedral-kl`),
for the actual KL family, with the exact standard normalization. This is
support for localization, not a substitute for general invariance. -/
theorem klPolynomial_eq_one (cs : CoxeterSystem M W) (x y : W)
    (hxy : BruhatLE cs x y) : klPolynomial cs x y = 1 := by
  have heq := normalizedKL_unique cs (klFamilies_spec cs) (constant_normalizedKL cs)
  have hp := congrArg (fun RP : PolynomialFamilies W => RP.2 x y) heq
  simpa only [klPolynomial, constantP, ite_eq_left hxy] using hp

end KLInvariance.Dihedral

end

section

namespace KLInvariance
open Polynomial
universe u v
variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}

/-- The exact square-parameter normalization, proved from the two genuine
Hecke recurrences. Integer exponents let the formula include incomparable
pairs without silently changing the R-polynomial definition. -/
theorem rPolynomial_normalization {C : Type*} [Field C]
    (cs : CoxeterSystem M W) (v : C) (hv : v ≠ 0) (x y : W) :
    eval₂ (Int.castRingHom C) (v^2) (rPolynomial cs x y) =
      v ^ ((cs.length y : ℤ) - cs.length x) *
        eval₂ (Int.castRingHom C) (v-v⁻¹) (Hecke.rTilde cs x y) := by
  rw [rPolynomial_eq_constructed]
  suffices ∀ n : ℕ, ∀ y : W, cs.length y = n → ∀ x,
    eval₂ (Int.castRingHom C) (v^2) (OrdinaryR.polynomial cs x y) =
      v ^ ((cs.length y : ℤ) - cs.length x) *
        eval₂ (Int.castRingHom C) (v-v⁻¹) (Hecke.rTilde cs x y) from
    this _ y rfl x
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hy x
    by_cases h1 : y=1
    · subst y
      by_cases hx : x=1
      · subst x; simp
      · have hn : ¬BruhatLE cs x 1 := by
          intro h
          have hl := length_le_of_bruhat cs h
          have hx0 : cs.length x=0 := by simpa using hl
          exact hx (cs.length_eq_zero_iff.mp hx0)
        rw [OrdinaryR.polynomial_zero cs _ _ hn,Hecke.rTilde_zero cs _ _ hn]
        simp
    · obtain ⟨i,hi⟩ := cs.exists_leftDescent_of_ne_one h1
      have hlt : cs.length (cs.simple i*y)<n := hy ▸ hi
      have hylen : cs.length (cs.simple i*y)+1=cs.length y := by
        have := cs.length_simple_mul y i; omega
      rw [OrdinaryR.polynomial_recursion cs x y i hi,Hecke.rTilde_recursion cs x y i hi]
      by_cases hx : cs.length (cs.simple i*x)<cs.length x
      · rw [ite_eq_left hx,ite_eq_left hx,ih _ hlt _ rfl (cs.simple i*x)]
        congr 2
        have := cs.length_simple_mul x i
        omega
      · rw [ite_eq_right hx,ite_eq_right hx]
        simp only [eval₂_add,eval₂_mul,eval₂_sub,eval₂_X,eval₂_one]
        rw [ih _ hlt _ rfl x,ih _ hlt _ rfl (cs.simple i*x)]
        have hxlen : cs.length (cs.simple i*x)=cs.length x+1 := by
          have := cs.length_simple_mul x i; omega
        have h1 : (cs.length (cs.simple i*y) : ℤ)-cs.length x =
            ((cs.length y : ℤ)-cs.length x)-1 := by omega
        have h2 : (cs.length (cs.simple i*y) : ℤ)-cs.length (cs.simple i*x) =
            ((cs.length y : ℤ)-cs.length x)-2 := by omega
        rw [h1,h2,zpow_sub₀ hv ((cs.length y : ℤ)-cs.length x) 1,
          zpow_sub₀ hv ((cs.length y : ℤ)-cs.length x) 2]
        simp only [zpow_ofNat]
        field_simp [hv]
        ; ring

/-- The manuscript's q^{-d/2} P(q), written with t^2=q so no square-root
branch is hidden. This is an evaluation of the already constructed genuine
KL polynomial, not a new combinatorial invariant. -/
noncomputable def scaledKL {C : Type*} [Field C]
    (cs : CoxeterSystem M W) (t : C) (x b : W) : C :=
  t ^ ((cs.length x : ℤ)-cs.length b) *
    eval₂ (Int.castRingHom C) (t^2) (klPolynomial cs x b)

/-- Exact normalized reciprocity in the direction useful for reversing the
parameter. No path formula and no moment-graph assumption occurs here. -/
theorem scaledKL_reciprocity_inverse {C : Type*} [Field C]
    (cs : CoxeterSystem M W) (v : C) (hv : v ≠ 0)
    (x b : W) (hxb : BruhatLE cs x b) :
    scaledKL cs v⁻¹ x b = ∑ᶠ z : Interval cs x b,
      eval₂ (Int.castRingHom C) (v-v⁻¹) (Hecke.rTilde cs x z.val) *
        scaledKL cs v z.val b := by
  classical
  let : Finite (Interval cs x b) := interval_finite cs x b
  let : Fintype (Interval cs x b) := Fintype.ofFinite _
  have hrec := (klFamilies_spec cs).reciprocity x b hxb
  change reflect (rankDifference cs x b) (klPolynomial cs x b) =
      ∑ᶠ z : Interval cs x b, rPolynomial cs x z.val * klPolynomial cs z.val b at hrec
  have hdeg : (klPolynomial cs x b).natDegree ≤ rankDifference cs x b := by
    rw [klPolynomial_eq_constructed]
    exact CanonicalP.polynomial_degree cs x b
  let q : Cˣ := Units.mk0 (v^2) (pow_ne_zero 2 hv)
  have heval := congrArg (eval₂ (Int.castRingHom C) (q : C)) hrec
  rw [eval₂_reflect_unit q _ _ hdeg] at heval
  simp only [finsum_eq_sum_of_fintype,eval₂_finsetSum,eval₂_mul] at heval ⊢
  have hq : (q : C) = v^2 := rfl
  have hqi : (↑q⁻¹ : C) = (v⁻¹)^2 := by simp [q,inv_pow]
  rw [hq,hqi] at heval
  have heq := congrArg (fun a : C => v ^ ((cs.length x : ℤ)-cs.length b)*a) heval
  have hd : (rankDifference cs x b : ℤ) = (cs.length b : ℤ)-cs.length x := by
    have hlen := length_le_of_bruhat cs hxb
    simp [rankDifference,Int.ofNat_sub hlen]
  have hscale : v ^ ((cs.length x : ℤ)-cs.length b) *
      (v^2)^(rankDifference cs x b) =
        (v⁻¹) ^ ((cs.length x : ℤ)-cs.length b) := by
    rw [←pow_mul,←zpow_natCast,←zpow_add₀ hv,inv_zpow,←zpow_neg]
    congr 1
    push_cast
    omega
  rw [←mul_assoc,hscale,Finset.mul_sum] at heq
  change (v⁻¹)^((cs.length x : ℤ)-cs.length b)*
      eval₂ (Int.castRingHom C) ((v⁻¹)^2) (klPolynomial cs x b) = _
  rw [heq]
  apply Finset.sum_congr rfl
  intro z _
  rw [rPolynomial_normalization cs v hv]
  unfold scaledKL
  calc
    _ = (v ^ ((cs.length x : ℤ)-cs.length b) *
        v ^ ((cs.length z.val : ℤ)-cs.length x)) *
        eval₂ (Int.castRingHom C) (v-v⁻¹) (Hecke.rTilde cs x z.val) *
        eval₂ (Int.castRingHom C) (v^2) (klPolynomial cs z.val b) := by ring
    _ = _ := by
      rw [←zpow_add₀ hv,show (cs.length x : ℤ)-cs.length b+
        ((cs.length z.val : ℤ)-cs.length x) =
        (cs.length z.val : ℤ)-cs.length b by ring]
      ring


theorem scaledKL_reciprocity {C : Type*} [Field C]
    (cs : CoxeterSystem M W) (v : C) (hv : v ≠ 0)
    (x b : W) (hxb : BruhatLE cs x b) :
    scaledKL cs v x b = ∑ᶠ z : Interval cs x b,
      eval₂ (Int.castRingHom C) (v⁻¹-v) (Hecke.rTilde cs x z.val) *
        scaledKL cs v⁻¹ z.val b := by
  simpa only [inv_inv] using scaledKL_reciprocity_inverse cs v⁻¹ (inv_ne_zero hv) x b hxb

end KLInvariance


end

end OAI
