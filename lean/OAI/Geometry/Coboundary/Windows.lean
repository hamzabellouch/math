import OAI.Geometry.Coboundary.Polynomial
import OAI.Combinatorics.Coboundary.Cones

namespace OAI

/-!
Affine windows, residue chambers, lattice flags, and chamber parametrizations.
-/

noncomputable section
open scoped Polynomial BigOperators

namespace CoboundaryExpanders.AffineWindow

variable {N : ℕ}

structure Window (N : ℕ) where
  entry : Fin N → ℤ
  residues : Function.Injective (fun i => entry i % (N : ℤ))

def pairCost (N : ℕ) (a b : ℤ) : ℕ := ((b-a)/(N : ℤ)).natAbs

def length (p : Fin N → ℤ) : ℕ :=
  ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (i < ·), pairCost N (p i) (p j)

lemma sub_not_dvd {a b : ℤ} (h : a % (N : ℤ) ≠ b % (N : ℤ)) :
    ¬ (N : ℤ) ∣ b-a := by
  intro hd
  have he := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd hd)
  exact h he.symm

lemma div_neg_nondiv (hN : 0 < N) {z : ℤ} (hz : ¬ (N : ℤ) ∣ z) :
    (-z)/(N : ℤ) = -(z/(N : ℤ))-1 := by
  have hpos : (0 : ℤ) < N := by exact_mod_cast hN
  have hm := Int.emod_nonneg z (ne_of_gt hpos)
  have hm' := Int.emod_lt_of_pos z hpos
  have hne : z % (N : ℤ) ≠ 0 := by
    intro he
    exact hz (Int.dvd_of_emod_eq_zero he)
  have hmp : 0 < z % (N : ℤ) := by omega
  have he := Int.mul_ediv_add_emod z (N : ℤ)
  apply (Int.ediv_eq_iff_of_pos hpos).2
  constructor <;> nlinarith

lemma pairCost_reverse (hN : 0 < N) {a b : ℤ}
    (hr : a % (N : ℤ) ≠ b % (N : ℤ)) (hab : a < b) :
    pairCost N b a = pairCost N a b + 1 := by
  have hq : 0 ≤ (b-a)/(N : ℤ) := Int.ediv_nonneg (by omega) (by omega)
  have hn := div_neg_nondiv hN (sub_not_dvd hr)
  rw [neg_sub] at hn
  unfold pairCost
  rw [hn]
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [abs_of_nonneg hq]
  have hneg : -((b-a)/(N : ℤ))-1 ≤ 0 := by omega
  rw [abs_of_nonpos hneg]
  omega

lemma pairCost_rotate (hN : 0 < N) {a b : ℤ}
    (hr : a % (N : ℤ) ≠ b % (N : ℤ)) :
    pairCost N b (a+N) = pairCost N a b := by
  have hp : (N : ℤ) ≠ 0 := by omega
  have hn := div_neg_nondiv hN (sub_not_dvd hr)
  have he : (a+(N : ℤ)-b)/(N : ℤ) = -((b-a)/(N : ℤ)) := by
    have hs : a+(N : ℤ)-b = -(b-a) + N := by ring
    rw [hs, Int.add_ediv_of_dvd_right (dvd_refl (N : ℤ)), Int.ediv_self hp, hn]
    omega
  unfold pairCost
  rw [he, Int.natAbs_neg]

lemma pairCost_zero_of_bounds {a b : ℤ}
    (hab : a ≤ b) (hb : b < a+N) : pairCost N a b = 0 := by
  unfold pairCost
  rw [Int.ediv_eq_zero_of_lt (by omega) (by omega)]
  rfl

lemma length_zero_of_bounds (p : Fin N → ℤ)
    (hp : StrictMono p) (hspan : ∀ i j, p j < p i+N) : length p = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  exact pairCost_zero_of_bounds (hp (Finset.mem_filter.mp hj).2).le (hspan i j)

lemma pairCost_eq_zero_iff (hN : 0 < N) (a b : ℤ) :
    pairCost N a b = 0 ↔ a ≤ b ∧ b < a+N := by
  unfold pairCost
  rw [Int.natAbs_eq_zero, Int.ediv_eq_iff_of_pos (show (0 : ℤ) < N by omega)]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

lemma pairCost_shift (a b c : ℤ) : pairCost N (a+c) (b+c) = pairCost N a b := by
  unfold pairCost
  congr 2
  ring

def inversion : List ℤ → ℕ
  | [] => 0
  | a :: l => (l.map (pairCost N a)).sum + inversion l

lemma inversion_append (l r : List ℤ) :
    inversion (N := N) (l++r) = inversion (N := N) l + inversion (N := N) r +
      ((l.map (fun a => (r.map (pairCost N a)).sum))).sum := by
  induction l with
  | nil => simp [inversion]
  | cons a l ih => simp only [List.cons_append,inversion,List.map_append,List.sum_append,
      List.map_cons,List.sum_cons,ih]; omega

lemma inversion_adjacent (l r : List ℤ) (a b : ℤ) :
    inversion (N := N) (l++a::b::r) + pairCost N b a =
      inversion (N := N) (l++b::a::r) + pairCost N a b := by
  induction l with
  | nil => simp [inversion]; omega
  | cons c l ih =>
    simp only [List.cons_append,inversion,List.map_append,List.sum_append,List.map_cons,
      List.sum_cons] at *
    omega

lemma inversion_adjacent_increase (hN : 0 < N) (l r : List ℤ) {a b : ℤ}
    (hr : a % (N : ℤ) ≠ b % (N : ℤ)) (hab : a < b) :
    inversion (N := N) (l++b::a::r) = inversion (N := N) (l++a::b::r)+1 := by
  have h := inversion_adjacent (N := N) l r a b
  rw [pairCost_reverse hN hr hab] at h
  omega

lemma inversion_rotate (hN : 0 < N) (a : ℤ) (l : List ℤ)
    (hr : ∀ b ∈ l, a % (N : ℤ) ≠ b % (N : ℤ)) :
    inversion (N := N) (l++[a+N]) = inversion (N := N) (a::l) := by
  rw [inversion_append,inversion]
  have he : (l.map (fun b => ([a+(N:ℤ)].map (pairCost N b)).sum)).sum =
      (l.map (pairCost N a)).sum := by
    congr 1
    apply List.map_congr_left
    intro b hb
    simpa using pairCost_rotate hN (hr b hb)
  rw [he]
  simp [inversion,Nat.add_comm]

lemma inversion_shift (l : List ℤ) (c : ℤ) :
    inversion (N := N) (l.map (·+c)) = inversion (N := N) l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons,inversion,ih,List.map_map]
    congr 2
    exact List.map_congr_left fun b _ => pairCost_shift a b c

lemma inversion_zero_iff (hN : 0 < N) (l : List ℤ) :
    inversion (N := N) l = 0 ↔ l.Pairwise (fun a b => a ≤ b ∧ b < a+(N : ℤ)) := by
  induction l with
  | nil => simp [inversion]
  | cons a l ih =>
    simp only [inversion,Nat.add_eq_zero_iff,List.sum_eq_zero_iff,List.mem_map,
      List.pairwise_cons,ih]
    constructor
    · rintro ⟨hs,hl⟩
      refine ⟨?_,hl⟩
      intro b hb
      exact (pairCost_eq_zero_iff hN a b).mp (hs _ ⟨b,hb,rfl⟩)
    · rintro ⟨hs,hl⟩
      refine ⟨?_,hl⟩
      rintro _ ⟨b,hb,rfl⟩
      exact (pairCost_eq_zero_iff hN a b).mpr (hs b hb)

lemma consecutive_of_bounds (hN : 0 < N) (p : Fin N → ℤ)
    (hp : StrictMono p) (hspan : ∀ i, p i < p ⟨0,hN⟩+N) :
    ∀ i, p i = p ⟨0,hN⟩ + i.val := by
  let f (i : Fin N) : Fin N := ⟨(p i-p ⟨0,hN⟩).toNat, by
    have hn : 0 ≤ p i-p ⟨0,hN⟩ := sub_nonneg.mpr (hp.monotone (show (⟨0,hN⟩ : Fin N) ≤ i from Nat.zero_le _))
    have := hspan i
    omega⟩
  have hf : StrictMono f := by
    intro i j hij
    change (p i-p ⟨0,hN⟩).toNat < (p j-p ⟨0,hN⟩).toNat
    have hn := hp.monotone (show (⟨0,hN⟩ : Fin N) ≤ i from Nat.zero_le _)
    have hh := hp hij
    omega
  intro i
  have he := congrArg Fin.val (congr_fun hf.eq_id i)
  have hn := hp.monotone (show (⟨0,hN⟩ : Fin N) ≤ i from Nat.zero_le _)
  change (p i-p ⟨0,hN⟩).toNat = i.val at he
  omega

end CoboundaryExpanders.AffineWindow

namespace CoboundaryExpanders.AffineWindow
variable {N : ℕ}

def pairs (f : ℤ → ℤ → ℕ) : List ℤ → ℕ
  | [] => 0
  | a :: l => (l.map (f a)).sum + pairs f l

def sortedCost (N : ℕ) (a b : ℤ) : ℕ := pairCost N (min a b) (max a b)
def disorder (a b : ℤ) : ℕ := if b < a then 1 else 0

lemma pairs_perm (f : ℤ → ℤ → ℕ) (hf : ∀ a b, f a b = f b a)
    {l r : List ℤ} (h : l.Perm r) : pairs f l = pairs f r := by
  induction h with
  | nil => rfl
  | cons a h ih =>
      simp only [pairs,ih]
      exact congrArg (·+pairs f _) (h.map (f a)).sum_eq
  | swap a b l => simp [pairs,hf a b]; omega
  | trans h h' ih ih' => exact ih.trans ih'

lemma sortedCost_comm (a b : ℤ) : sortedCost N a b = sortedCost N b a := by
  simp only [sortedCost,min_comm,max_comm]

lemma pairCost_decompose (hN : 0 < N) {a b : ℤ}
    (hr : a % (N : ℤ) ≠ b % (N : ℤ)) :
    pairCost N a b = sortedCost N a b + disorder a b := by
  have hne : a ≠ b := fun h => hr (congrArg (· % (N : ℤ)) h)
  rcases lt_or_gt_of_ne hne with h | h
  · simp only [sortedCost,min_eq_left h.le,max_eq_right h.le,disorder,ite_eq_right (not_lt_of_ge h.le),Nat.add_zero]
  · rw [pairCost_reverse hN (Ne.symm hr) h]
    simp only [sortedCost,min_eq_right h.le,max_eq_left h.le,disorder,ite_eq_left h]

lemma inversion_decompose (hN : 0 < N) (l : List ℤ)
    (hr : l.Pairwise (fun a b => a % (N : ℤ) ≠ b % (N : ℤ))) :
    inversion (N := N) l = pairs (sortedCost N) l + pairs disorder l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.pairwise_cons] at hr
    rw [inversion,pairs,pairs,ih hr.2]
    have he : (l.map (pairCost N a)).sum =
        (l.map (sortedCost N a)).sum + (l.map (disorder a)).sum := by
      rw [← List.sum_map_add]
      apply congrArg List.sum
      exact List.map_congr_left fun b hb => pairCost_decompose hN (hr.1 b hb)
    omega

lemma disorder_zero_iff (l : List ℤ) : pairs disorder l = 0 ↔ l.Pairwise (· ≤ ·) := by
  induction l with
  | nil => simp [pairs]
  | cons a l ih =>
    simp only [pairs,Nat.add_eq_zero_iff,List.sum_eq_zero_iff,List.mem_map,
      List.pairwise_cons,ih]
    constructor
    · rintro ⟨hs,hl⟩
      refine ⟨?_,hl⟩
      intro b hb
      have hh := hs _ ⟨b,hb,rfl⟩
      simp only [disorder,ite_eq_right_iff,one_ne_zero,imp_false] at hh
      omega
    · rintro ⟨hs,hl⟩
      refine ⟨?_,hl⟩
      rintro _ ⟨b,hb,rfl⟩
      simp only [disorder,ite_eq_right (not_lt_of_ge (hs b hb))]

theorem inversion_minimal_perm (hN : 0 < N) {l r : List ℤ}
    (hperm : l.Perm r) (hs : l.Pairwise (· ≤ ·))
    (hr : r.Pairwise (fun a b => a % (N : ℤ) ≠ b % (N : ℤ))) :
    inversion (N := N) r = inversion (N := N) l + pairs disorder r := by
  have hl : l.Pairwise (fun a b => a % (N : ℤ) ≠ b % (N : ℤ)) :=
    (hperm.pairwise_iff (fun h => Ne.symm h)).mpr hr
  rw [inversion_decompose hN r hr,inversion_decompose hN l hl,
    (disorder_zero_iff l).mpr hs,Nat.add_zero,pairs_perm (sortedCost N) sortedCost_comm hperm]

lemma inversion_minimal_unique (hN : 0 < N) {l r : List ℤ}
    (hperm : l.Perm r) (hs : l.Pairwise (· ≤ ·))
    (hr : r.Pairwise (fun a b => a % (N : ℤ) ≠ b % (N : ℤ))) :
    inversion (N := N) r = inversion (N := N) l ↔ r = l := by
  constructor
  · intro he
    have hz : pairs disorder r = 0 := by have := inversion_minimal_perm hN hperm hs hr; omega
    exact (hperm.eq_of_pairwise' hs ((disorder_zero_iff r).mp hz)).symm
  · rintro rfl; rfl

lemma inversion_permute_middle (l r p q : List ℤ) (hpq : p.Perm q) :
    inversion (N := N) (l++q++r) + inversion (N := N) p =
      inversion (N := N) (l++p++r) + inversion (N := N) q := by
  induction l with
  | nil =>
      simp only [List.nil_append]
      rw [inversion_append,inversion_append]
      have hh := (hpq.map (fun a => (r.map (pairCost N a)).sum)).sum_eq
      omega
  | cons a l ih =>
      simp only [List.cons_append,inversion,List.map_append,List.sum_append]
      have hh := (hpq.map (pairCost N a)).sum_eq
      omega

lemma inversion_sorted_middle (hN : 0 < N) (l r : List ℤ) {p q : List ℤ}
    (hpq : p.Perm q) (hs : p.Pairwise (· ≤ ·))
    (hr : q.Pairwise (fun a b => a % (N : ℤ) ≠ b % (N : ℤ))) :
    inversion (N := N) (l++q++r) = inversion (N := N) (l++p++r) + pairs disorder q := by
  have h₁ := inversion_permute_middle (N := N) l r p q hpq
  have h₂ := inversion_minimal_perm hN hpq hs hr
  omega

end CoboundaryExpanders.AffineWindow

namespace CoboundaryExpanders.AffineWindow
variable {N : ℕ}

def periodicEnd (hN : 0 < N) (p : Fin N → ℤ) (r : Fin (N+1)) : ℤ :=
  if hr : r.val < N then p ⟨r.val,hr⟩ else p ⟨0,hN⟩ + N

@[simp] lemma periodicEnd_castSucc (hN : 0 < N) (p : Fin N → ℤ) (r : Fin N) :
    periodicEnd hN p r.castSucc = p r := by
  simp only [periodicEnd,Fin.val_castSucc,dite_eq_left r.isLt]

@[simp] lemma periodicEnd_last (hN : 0 < N) (p : Fin N → ℤ) :
    periodicEnd hN p (Fin.last N) = p ⟨0,hN⟩ + N := by
  simp only [periodicEnd,Fin.val_last,lt_self_iff_false,dite_eq_right,not_false_eq_true]

@[simp] lemma periodicEnd_zero (hN : 0 < N) (p : Fin N → ℤ) :
    periodicEnd hN p 0 = p ⟨0,hN⟩ := by
  change (if hr : 0 < N then p ⟨0,hr⟩ else p ⟨0,hN⟩ + N) = p ⟨0,hN⟩
  rw [dite_eq_left hN]

noncomputable def descents (hN : 0 < N) (p : Fin N → ℤ) : Finset (Fin N) :=
  Finset.univ.filter fun r => periodicEnd hN p r.succ < p r

lemma periodicEnd_mono_iff (hN : 0 < N) (p : Fin N → ℤ) :
    Monotone (periodicEnd hN p) ↔ descents hN p = ∅ := by
  classical
  rw [Fin.monotone_iff_le_succ,Finset.eq_empty_iff_forall_notMem]
  simp only [descents,Finset.mem_filter,Finset.mem_univ,true_and,not_lt,periodicEnd_castSucc]

lemma last_ne_periodic_start (hN : 0 < N) (p : Fin N → ℤ)
    (hp : Function.Injective (fun r => p r % (N : ℤ))) :
    p ⟨N-1,by omega⟩ ≠ p ⟨0,hN⟩ + N := by
  intro he
  have hm := congrArg (· % (N : ℤ)) he
  simp only [Int.add_emod_right] at hm
  have hi := hp hm
  have hv := congrArg p hi
  have hpos : (0 : ℤ) < N := by exact_mod_cast hN
  omega

lemma inversion_zero_of_no_descents (hN : 0 < N) (p : Fin N → ℤ)
    (hp : Function.Injective (fun r => p r % (N : ℤ)))
    (hd : descents hN p = ∅) : inversion (N := N) (List.ofFn p) = 0 := by
  have hm := (periodicEnd_mono_iff hN p).mpr hd
  have hpmono : Monotone p := by
    intro i j hij
    simpa only [periodicEnd_castSucc] using hm (show i.castSucc ≤ j.castSucc from hij)
  have hl : p ⟨N-1,by omega⟩ < p ⟨0,hN⟩ + N := by
    have hle := hm (show (⟨N-1,by omega⟩ : Fin N).castSucc ≤ Fin.last N from Fin.le_last _)
    simp only [periodicEnd_castSucc,periodicEnd_last] at hle
    exact lt_of_le_of_ne hle (last_ne_periodic_start hN p hp)
  apply (inversion_zero_iff hN _).mpr
  apply List.pairwise_ofFn.mpr
  intro i j hij
  refine ⟨hpmono hij.le,?_⟩
  have hj := hpmono (show j ≤ ⟨N-1,by omega⟩ from by change j.val ≤ N-1; omega)
  have hi := hpmono (show (⟨0,hN⟩ : Fin N) ≤ i from Nat.zero_le _)
  omega

theorem descents_nonempty (hN : 0 < N) (p : Fin N → ℤ)
    (hp : Function.Injective (fun r => p r % (N : ℤ)))
    (hl : 0 < inversion (N := N) (List.ofFn p)) : (descents hN p).Nonempty := by
  by_contra hn
  have hz := inversion_zero_of_no_descents hN p hp (Finset.not_nonempty_iff_eq_empty.mp hn)
  omega

theorem descents_ne_univ (hN : 0 < N) (p : Fin N → ℤ) :
    descents hN p ≠ Finset.univ := by
  classical
  intro he
  have ha : StrictMono (fun r => -periodicEnd hN p r) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro r
    have hr : r ∈ descents hN p := by rw [he]; exact Finset.mem_univ _
    have hh := (Finset.mem_filter.mp hr).2
    simpa only [periodicEnd_castSucc,neg_lt_neg_iff] using hh
  have hlt := ha (show (0 : Fin (N+1)) < Fin.last N from hN)
  dsimp only at hlt
  rw [periodicEnd_zero,periodicEnd_last] at hlt
  have hpos : (0 : ℤ) < N := by exact_mod_cast hN
  omega

lemma inversion_zero_no_descents (hN : 0 < N) (p : Fin N → ℤ)
    (hl : inversion (N := N) (List.ofFn p) = 0) : descents hN p = ∅ := by
  classical
  have hh := List.pairwise_ofFn.mp ((inversion_zero_iff hN _).mp hl)
  apply (periodicEnd_mono_iff hN p).mp
  apply Fin.monotone_iff_le_succ.mpr
  intro r
  rw [periodicEnd_castSucc]
  dsimp only [periodicEnd]
  split_ifs with hr
  · exact (hh (show r < (⟨r.val+1,hr⟩ : Fin N) from Nat.lt_succ_self _)).1
  · have he : r.val = N-1 := by
      have hv : ¬r.val+1 < N := hr
      have := r.isLt
      omega
    by_cases hz : r.val = 0
    · have hi : r = ⟨0,hN⟩ := Fin.ext hz
      rw [hi]
      have hpos : (0 : ℤ) < N := by exact_mod_cast hN
      omega
    · exact (hh (show (⟨0,hN⟩ : Fin N) < r from by change 0 < r.val; omega)).2.le

end CoboundaryExpanders.AffineWindow

namespace CoboundaryExpanders.AffineWindow
variable {N : ℕ}

lemma window_entry_consecutive (hN : 0 < N) (p : Fin N → ℤ)
    (hp : Function.Injective (fun r => p r % (N : ℤ)))
    (hz : inversion (N := N) (List.ofFn p) = 0) :
    ∀ i, p i = p ⟨0,hN⟩ + i.val := by
  have hh := List.pairwise_ofFn.mp ((inversion_zero_iff hN _).mp hz)
  have hstrict : StrictMono p := by
    intro i j hij
    apply lt_of_le_of_ne (hh hij).1
    intro he
    exact (ne_of_lt hij) (hp (congrArg (· % (N : ℤ)) he))
  apply consecutive_of_bounds hN p hstrict
  intro i
  by_cases hi : i.val = 0
  · have he : i = ⟨0,hN⟩ := Fin.ext hi
    rw [he]
    have hpos : (0 : ℤ) < N := by exact_mod_cast hN
    omega
  · exact (hh (show (⟨0,hN⟩ : Fin N) < i from by change 0 < i.val; omega)).2

lemma same_residue_short_interval {x y c i : ℕ}
    (hx : c ≤ N*x+i ∧ N*x+i < c+N)
    (hy : c ≤ N*y+i ∧ N*y+i < c+N) : x = y := by
  rcases lt_trichotomy x y with h | h | h
  · have hh := Nat.mul_le_mul_left N (show x+1 ≤ y from h)
    rw [Nat.mul_add,Nat.mul_one] at hh
    omega
  · exact h
  · have hh := Nat.mul_le_mul_left N (show y+1 ≤ x from h)
    rw [Nat.mul_add,Nat.mul_one] at hh
    omega

lemma cyclic_cut_exponents (hN : 0 < N) (a : Fin N → ℕ)
    (σ : Equiv.Perm (Fin N)) (c : ℕ)
    (hc : ∀ r : Fin N, N*a (σ r)+(σ r).val = c+r.val)
    (r : ℕ) (hr : r ≤ N) (i : Fin N) :
    a i + (if (σ.symm i).val < r then 1 else 0) =
      (c+r)/N + (if i.val < (c+r)%N then 1 else 0) := by
  have hbase := hc (σ.symm i)
  rw [σ.apply_symm_apply] at hbase
  apply same_residue_short_interval (N := N) (c := c+r) (i := i.val)
  · have hj := (σ.symm i).isLt
    split_ifs with h
    · rw [Nat.mul_add,Nat.mul_one]
      omega
    · rw [Nat.add_zero]
      omega
  · have hmod := Nat.mod_lt (c+r) hN
    have hdiv := Nat.mod_add_div (c+r) N
    have hi := i.isLt
    split_ifs with h
    · rw [Nat.mul_add,Nat.mul_one]
      omega
    · rw [Nat.add_zero]
      omega

theorem zero_window_cut_flag (hN : 0 < N) (a : Fin N → ℕ)
    (σ : Equiv.Perm (Fin N))
    (hz : inversion (N := N) (List.ofFn (fun r => (N*a (σ r)+(σ r).val : ℕ))) = 0) :
    ∃ c : ℕ, ∀ r : Fin (N+1), ∀ i : Fin N,
      a i + (if (σ.symm i).val < r.val then 1 else 0) =
        (c+r.val)/N + (if i.val < (c+r.val)%N then 1 else 0) := by
  let p (r : Fin N) : ℤ := (N*a (σ r)+(σ r).val : ℕ)
  have hp : Function.Injective (fun r => p r % (N : ℤ)) := by
    intro r s he
    have hmod (j : Fin N) : p j % (N : ℤ) = ((σ j).val : ℤ) := by
      dsimp only [p]
      push_cast
      have h0 : 0 ≤ ((σ j).val : ℤ) := Int.natCast_nonneg _
      have hlt : ((σ j).val : ℤ) < N := by exact_mod_cast (σ j).isLt
      simp only [Int.add_emod,Int.mul_emod_right,Int.zero_add,Int.emod_eq_of_lt h0 hlt]
    dsimp only at he
    rw [hmod,hmod] at he
    exact σ.injective (Fin.ext (by exact_mod_cast he))
  let c : ℕ := N*a (σ ⟨0,hN⟩)+(σ ⟨0,hN⟩).val
  have hc : ∀ r : Fin N, N*a (σ r)+(σ r).val = c+r.val := by
    intro r
    have hh := window_entry_consecutive hN p hp hz r
    dsimp [p,c] at hh ⊢
    exact_mod_cast hh
  exact ⟨c,fun r i => cyclic_cut_exponents hN a σ c hc r.val (by omega) i⟩

end CoboundaryExpanders.AffineWindow

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

structure ResidueChamber where
  top : Submodule K[X] (V K N)
  hasTop : HasPivots top
  stage : Fin (N+1) → Submodule K[X] (V K N)
  hasStage : ∀ r, HasPivots (stage r)
  strict : StrictAnti stage
  initial : stage 0 = top
  lower : ∀ r, powerShift top 1 ≤ stage r

namespace ResidueChamber
variable (C : ResidueChamber (K := K) (N := N))

noncomputable def word : Equiv.Perm (Fin N) :=
  (full_flag_increment_permutation C.top C.hasTop C.stage C.hasStage C.strict C.initial C.lower).choose

lemma word_spec (r : Fin N) :
    incrementSet C.top (C.stage r.succ) C.hasTop (C.hasStage r.succ) =
      insert (C.word r) (incrementSet C.top (C.stage r.castSucc) C.hasTop (C.hasStage r.castSucc)) ∧
    C.word r ∉ incrementSet C.top (C.stage r.castSucc) C.hasTop (C.hasStage r.castSucc) :=
  (full_flag_increment_permutation C.top C.hasTop C.stage C.hasStage C.strict C.initial C.lower).choose_spec r

lemma increments (r : Fin (N+1)) :
    incrementSet C.top (C.stage r) C.hasTop (C.hasStage r) =
      Finset.univ.filter (fun i => (C.word.symm i).val < r.val) := by
  classical
  induction r using Fin.induction with
  | zero =>
    rw [show incrementSet C.top (C.stage 0) C.hasTop (C.hasStage 0) = ∅ from by
      ext i
      simp only [incrementSet,Finset.mem_filter,Finset.mem_univ,true_and,Finset.notMem_empty,iff_false,not_lt]
      simpa only [C.initial] using (le_refl (pivotDegree C.top C.hasTop i))]
    simp
  | succ r ih =>
    rw [(C.word_spec r).1,ih]
    ext i
    simp only [Finset.mem_insert,Finset.mem_filter,Finset.mem_univ,true_and,Fin.val_succ,Fin.val_castSucc]
    constructor
    · rintro (rfl|hi)
      · simp
      · omega
    · intro hi
      by_cases he : C.word.symm i = r
      · exact Or.inl (by rw [← he]; exact (C.word.apply_symm_apply i).symm)
      · have hn : (C.word.symm i).val ≠ r.val := fun h => he (Fin.ext h)
        exact Or.inr (by omega)

lemma stage_degree (r : Fin (N+1)) (i : Fin N) :
    pivotDegree (C.stage r) (C.hasStage r) i = pivotDegree C.top C.hasTop i +
      (if (C.word.symm i).val < r.val then 1 else 0) := by
  classical
  have ht : C.stage r ≤ C.top := by rw [← C.initial]; exact C.strict.antitone (Fin.zero_le r)
  have hh := interval_pivot_increment C.hasTop (C.hasStage r) ht (C.lower r) i
  have hm := Finset.ext_iff.mp (C.increments r) i
  simp only [incrementSet,Finset.mem_filter,Finset.mem_univ,true_and] at hm
  split_ifs with h
  · have hg := hm.mpr h
    omega
  · have hg : ¬pivotDegree C.top C.hasTop i < pivotDegree (C.stage r) (C.hasStage r) i := mt hm.mp h
    omega

lemma terminal : C.stage (Fin.last N) = powerShift C.top 1 := by
  apply eq_of_le_same_pivots (C.hasStage (Fin.last N))
    (powerShift_hasPivots C.top C.hasTop 1) (C.lower (Fin.last N))
  intro i
  rw [C.stage_degree,pivotDegree_powerShift C.top C.hasTop]
  simp only [Fin.val_last,ite_eq_left (C.word.symm i).isLt]

noncomputable def window : Fin N → ℤ := fun r =>
  (N*pivotDegree C.top C.hasTop (C.word r)+(C.word r).val : ℕ)

noncomputable def length : ℕ := AffineWindow.inversion (N := N) (List.ofFn C.window)

theorem zero_flag (hN : 0 < N) (hz : C.length = 0) :
    ∃ c : ℕ, ∀ r : Fin (N+1), ∀ i : Fin N,
      pivotDegree (C.stage r) (C.hasStage r) i =
        (c+r.val)/N + (if i.val < (c+r.val)%N then 1 else 0) := by
  obtain ⟨c,hc⟩ := AffineWindow.zero_window_cut_flag hN
    (pivotDegree C.top C.hasTop) C.word hz
  exact ⟨c,fun r i => (C.stage_degree r i).trans (hc r i)⟩

end ResidueChamber
end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices
variable (K : Type) [Field K] (N : ℕ)

lemma exponent_cut (cut : Fin N) : exponentLattice K N (cutExponent N cut) = cutLattice K N cut := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩ j
    by_cases hj : j = i
    · subst j
      exact ⟨1,by simp⟩
    · exact ⟨0,by simp [Pi.single_eq_of_ne hj]⟩
  · intro v hv
    choose f hf using hv
    have he : v = ∑ i : Fin N, (f i) • Pi.single i (uniformizer K ^ cutExponent N cut i) := by
      funext j
      simp only [Finset.sum_apply,Algebra.smul_def,Pi.mul_apply,Pi.algebraMap_apply,
        Pi.single_apply,mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
      exact (hf j).symm
    rw [he]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩))

lemma shift_exponent (a : Fin N → ℕ) :
    shift K N (exponentLattice K N a) = exponentLattice K N (fun i => a i+1) := by
  classical
  change (Submodule.span K[X] (Set.range fun i : Fin N => Pi.single i (uniformizer K ^ a i))).map
    (shiftLinear K N).toLinearMap = _
  rw [Submodule.map_span,← Set.range_comp]
  apply congrArg (Submodule.span K[X])
  apply congrArg Set.range
  funext i j
  by_cases hij : j = i
  · subst j
    simp [uniformizer,pow_succ,mul_comm]
  · simp [Function.comp_apply,hij]

lemma level_exponent (a : Fin N → ℕ) (m : ℕ) :
    level (shift K N) (exponentLattice K N a) m = exponentLattice K N (fun i => a i+m) := by
  induction m with
  | zero => simp [level]
  | succ m ih =>
    rw [level_succ,ih,shift_exponent]
    rfl

lemma exponent_cut_level (cut : Fin N) (m : ℕ) :
    exponentLattice K N (fun i => m+cutExponent N cut i) = level (shift K N) (cutLattice K N cut) m := by
  rw [← exponent_cut,level_exponent]
  congr 1
  funext i
  exact Nat.add_comm _ _

theorem zero_pivots_common_orbit {M : ℕ} (hN : 0 < N) (B : Fin (M+1) → Vertex K N)
    (hanti : Antitone (fun r => (B r).val))
    (hbelow : ∀ r, level (shift K N) (B 0).val 1 ≤ (B r).val)
    (cut : Fin (M+1) → Fin N) (m : Fin (M+1) → ℕ)
    (hdeg : ∀ r i, diagonalExponents K N (B r) i = m r+cutExponent N (cut r) i) :
    ∃ g : Matrix.SpecialLinearGroup (Fin N) K[X],
      (∀ i j : Fin N, j ≤ i → Polynomial.eval 0 (g i j) = (1 : Matrix (Fin N) (Fin N) K) i j) ∧
      ∀ r, B r = actVertex K N hN g (cutVertex K N (cut r)) := by
  obtain ⟨g,hg,hB⟩ := lattice_flag_birkhoff K N M B hanti hbelow
  refine ⟨g,fun i j hij => by simpa only [Polynomial.coeff_zero_eq_eval_zero] using hg i j hij,?_⟩
  intro r
  have hexp : exponentLattice K N (diagonalExponents K N (B r)) =
      level (shift K N) (cutVertex K N (cut r)).val (m r) := by
    rw [show diagonalExponents K N (B r) = fun i => m r+cutExponent N (cut r) i from funext (hdeg r)]
    exact exponent_cut_level K N _ _
  have hh : Homothetic (shift K N) (B r).val
      (positiveAction K N g (cutVertex K N (cut r)).val) := by
    refine ⟨0,m r,?_⟩
    rw [level_zero,← map_level _ _ (positiveAction_shift K N g)]
    rw [← hexp]
    exact (hB r).symm
  apply (homothetic_normalized_iff (shift K N) (standard K N) (shift_standard_le K N) _ _).mp
  exact homothetic_trans _ hh (actVertex_homothetic K N hN g (cutVertex K N (cut r)))

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable (K : Type) [Field K] (N : ℕ)

lemma polynomialLattice_injective : Function.Injective (polynomialLattice K N) := by
  intro A B he
  apply Subtype.ext
  have hh := congrArg (fun P => P.map (polynomialEmbedding K N)) he
  simpa only [polynomialLattice_map] using hh

lemma polynomialLattice_strict {A B : Vertex K N} (hBA : B.val < A.val) :
    polynomialLattice K N B < polynomialLattice K N A := by
  apply lt_of_le_of_ne (polynomialLattice_mono K N hBA.le)
  intro he
  exact hBA.ne (congrArg Subtype.val (polynomialLattice_injective K N he))

lemma polynomialLattice_power_map (A : Vertex K N) (m : ℕ) :
    (powerShift (polynomialLattice K N A) m).map (polynomialEmbedding K N) =
      level (shift K N) A.val m := by
  ext v
  constructor
  · rintro ⟨w,⟨z,hz,rfl⟩,rfl⟩
    apply (mem_level K N _ _ _).mpr
    exact ⟨polynomialEmbedding K N z,hz,by rw [← map_smul]; rfl⟩
  · intro hv
    obtain ⟨w,hw,rfl⟩ := (mem_level K N _ _ _).mp hv
    have hw' : w ∈ (polynomialLattice K N A).map (polynomialEmbedding K N) := by
      rwa [polynomialLattice_map]
    obtain ⟨z,hz,rfl⟩ := hw'
    exact ⟨powerLinear m z,⟨z,hz,rfl⟩,by change polynomialEmbedding K N ((Polynomial.X^m : K[X]) • z) = _; rw [map_smul]⟩

structure FullChamber (hN : 0 < N) where
  vertex : Fin N → Vertex K N
  strict : StrictAnti (fun r => (vertex r).val)
  lower : ∀ r, shift K N (vertex ⟨0,hN⟩).val ≤ (vertex r).val

namespace FullChamber
variable {K N} {hN : 0 < N} (C : FullChamber K N hN)

def topIndex (_C : FullChamber K N hN) : Fin N := ⟨0,hN⟩

noncomputable def stage (r : Fin (N+1)) : Submodule K[X] (PolynomialVectors.V K N) :=
  if hr : r.val < N then polynomialLattice K N (C.vertex ⟨r.val,hr⟩)
  else powerShift (polynomialLattice K N (C.vertex C.topIndex)) 1

lemma stage_castSucc (r : Fin N) : C.stage r.castSucc = polynomialLattice K N (C.vertex r) := by
  simp only [stage,Fin.val_castSucc,dite_eq_left r.isLt]

lemma stage_last : C.stage (Fin.last N) = powerShift (polynomialLattice K N (C.vertex C.topIndex)) 1 := by
  unfold stage
  split_ifs with h
  · exact False.elim (Nat.lt_irrefl N h)
  · rfl

lemma hasStage (r : Fin (N+1)) : HasPivots (C.stage r) := by
  unfold stage
  split_ifs
  · exact polynomialHasPivots K N _
  · exact powerShift_hasPivots _ (polynomialHasPivots K N _) 1

lemma lower_stage (r : Fin (N+1)) : powerShift (polynomialLattice K N (C.vertex C.topIndex)) 1 ≤ C.stage r := by
  unfold stage
  split_ifs
  · exact polynomialLattice_power_le K N (C.lower _)
  · exact le_rfl

lemma stage_strict : StrictAnti C.stage := by
  intro r s hrs
  have hrN : r.val < N := by have hs := s.isLt; change r.val < s.val at hrs; omega
  rw [show C.stage r = polynomialLattice K N (C.vertex ⟨r.val,hrN⟩) from dite_eq_left hrN]
  unfold stage
  split_ifs with hsN
  · exact polynomialLattice_strict K N (C.strict (show (⟨r.val,hrN⟩ : Fin N) < ⟨s.val,hsN⟩ from hrs))
  · apply lt_of_le_of_ne (polynomialLattice_power_le K N (C.lower _))
    intro he
    have hh := congrArg (fun P => P.map (polynomialEmbedding K N)) he
    rw [polynomialLattice_power_map,polynomialLattice_map] at hh
    have hle : (C.vertex ⟨r.val,hrN⟩).val ≤ shift K N (standard K N) := by
      rw [← hh]
      exact (shift K N).monotone (vertex_le (shift K N) (standard K N) _)
    exact vertex_normalized (shift K N) (standard K N) _ hle

noncomputable def polynomialChamber : ResidueChamber (K := K) (N := N) where
  top := polynomialLattice K N (C.vertex C.topIndex)
  hasTop := polynomialHasPivots K N _
  stage := C.stage
  hasStage := C.hasStage
  strict := C.stage_strict
  initial := by
    unfold stage
    split_ifs with h
    · rfl
    · exact False.elim (h hN)
  lower := C.lower_stage

noncomputable def length : ℕ := C.polynomialChamber.length

lemma zero_pivots (hz : C.length = 0) :
    ∃ c : ℕ, ∀ r : Fin N, ∀ i : Fin N,
      diagonalExponents K N (C.vertex r) i = (c+r.val)/N + (if i.val < (c+r.val)%N then 1 else 0) := by
  obtain ⟨c,hc⟩ := C.polynomialChamber.zero_flag hN hz
  refine ⟨c,fun r i => ?_⟩
  have hh := hc r.castSucc i
  simpa only [polynomialChamber,stage_castSucc,Fin.val_castSucc,diagonalExponents] using hh

theorem zero_common_orbit (hz : C.length = 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin N) K[X],
      (∀ i j : Fin N, j ≤ i → Polynomial.eval 0 (g i j) = (1 : Matrix (Fin N) (Fin N) K) i j) ∧
      ∃ c : ℕ, ∀ r : Fin N,
        C.vertex r = actVertex K N hN g (cutVertex K N ⟨(c+r.val)%N,Nat.mod_lt _ hN⟩) := by
  obtain ⟨c,hc⟩ := C.zero_pivots hz
  cases N with
  | zero => omega
  | succ M =>
    have hh := zero_pivots_common_orbit K (M+1) hN C.vertex C.strict.antitone C.lower
      (fun r => ⟨(c+r.val)%(M+1),Nat.mod_lt _ hN⟩) (fun r => (c+r.val)/(M+1)) hc
    obtain ⟨g,hg,hv⟩ := hh
    exact ⟨g,hg,c,hv⟩

end FullChamber
end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable (K : Type) [Field K] (N : ℕ)

lemma polynomialEmbedding_injective : Function.Injective (polynomialEmbedding K N) := by
  intro v w he
  funext i
  exact RatFunc.algebraMap_injective K (congr_fun he i)

lemma powerShift_map_embedding (P : Submodule K[X] (PolynomialVectors.V K N)) (m : ℕ) :
    (powerShift P m).map (polynomialEmbedding K N) =
      level (shift K N) (P.map (polynomialEmbedding K N)) m := by
  ext v
  constructor
  · rintro ⟨w,⟨z,hz,rfl⟩,rfl⟩
    apply (mem_level K N _ _ _).mpr
    refine ⟨polynomialEmbedding K N z,⟨z,hz,rfl⟩,?_⟩
    rw [← map_smul]
    rfl
  · intro hv
    obtain ⟨w,⟨z,hz,rfl⟩,rfl⟩ := (mem_level K N _ _ _).mp hv
    refine ⟨powerLinear m z,⟨z,hz,rfl⟩,?_⟩
    change polynomialEmbedding K N ((Polynomial.X^m : K[X]) • z) = _
    rw [map_smul]

lemma reciprocal_reflect (f : K[X]) (M : ℕ) (hf : f.natDegree ≤ M) :
    positive K f * uniformizer K^M = algebraMap K[X] (RatFunc K) (Polynomial.reflect M f) := by
  have hh := positive_reflect_uniformizer K (Polynomial.reflect M f) M
    (Polynomial.natDegree_reflect_le.trans (max_le le_rfl hf))
  simpa only [Polynomial.reflect_reflect] using hh

noncomputable def reflectedMatrix (g : Matrix (Fin N) (Fin N) K[X]) (M : ℕ) :
    Matrix (Fin N) (Fin N) K[X] := fun i j => Polynomial.reflect M (g i j)

lemma reflectedMatrix_embedding (g : Matrix.SpecialLinearGroup (Fin N) K[X]) (M : ℕ)
    (hg : ∀ i j, (g i j).natDegree ≤ M) (v : PolynomialVectors.V K N) :
    polynomialEmbedding K N ((reflectedMatrix K N g.val M).mulVec v) =
      (Polynomial.X^M : K[X]) • positiveLinear K N g (polynomialEmbedding K N v) := by
  classical
  funext i
  change algebraMap K[X] (RatFunc K) (∑ j, Polynomial.reflect M (g i j) * v j) = _
  simp only [map_sum,map_mul,Pi.smul_apply,Algebra.smul_def,map_pow,positiveLinear_apply]
  change (∑ j, algebraMap K[X] (RatFunc K) (Polynomial.reflect M (g i j)) *
    algebraMap K[X] (RatFunc K) (v j)) =
    uniformizer K^M * ∑ j, positive K (g i j) * algebraMap K[X] (RatFunc K) (v j)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← reciprocal_reflect K _ M (hg i j)]
  ring

lemma reflectedLattice_map_embedding (g : Matrix.SpecialLinearGroup (Fin N) K[X]) (M : ℕ)
    (hg : ∀ i j, (g i j).natDegree ≤ M) (P : Submodule K[X] (PolynomialVectors.V K N)) :
    (P.map (matrixLinear (reflectedMatrix K N g.val M))).map (polynomialEmbedding K N) =
      level (shift K N) (positiveAction K N g (P.map (polynomialEmbedding K N))) M := by
  ext v
  constructor
  · rintro ⟨w,⟨z,hz,rfl⟩,rfl⟩
    apply (mem_level K N _ _ _).mpr
    refine ⟨positiveLinear K N g (polynomialEmbedding K N z),?_,?_⟩
    · exact (mem_positiveAction K N g _ _).mpr ⟨polynomialEmbedding K N z,⟨z,hz,rfl⟩,rfl⟩
    · exact (reflectedMatrix_embedding K N g M hg z).symm
  · intro hv
    obtain ⟨w,hw,rfl⟩ := (mem_level K N _ _ _).mp hv
    obtain ⟨y,⟨z,hz,rfl⟩,rfl⟩ := (mem_positiveAction K N g _ _).mp hw
    exact ⟨matrixLinear (reflectedMatrix K N g.val M) z,⟨z,hz,rfl⟩,
      reflectedMatrix_embedding K N g M hg z⟩

lemma matrix_degree_bound (g : Matrix (Fin N) (Fin N) K[X]) :
    ∃ M : ℕ, ∀ i j, (g i j).natDegree ≤ M := by
  classical
  refine ⟨Finset.univ.sup (fun i => Finset.univ.sup (fun j => (g i j).natDegree)),?_⟩
  intro i j
  exact (Finset.le_sup (f := fun j => (g i j).natDegree) (Finset.mem_univ j)).trans
    (Finset.le_sup (f := fun i => Finset.univ.sup (fun j => (g i j).natDegree)) (Finset.mem_univ i))

theorem homothetic_action_pivots (g : Matrix.SpecialLinearGroup (Fin N) K[X])
    (hg : ∀ i j : Fin N, j ≤ i → (g i j).coeff 0 = (1 : Matrix (Fin N) (Fin N) K) i j)
    (A B : Vertex K N) (a b : ℕ)
    (he : level (shift K N) (positiveAction K N g A.val) a = level (shift K N) B.val b) :
    ∀ i, diagonalExponents K N A i+a = diagonalExponents K N B i+b := by
  obtain ⟨M,hM⟩ := matrix_degree_bound K N g.val
  let R := reflectedMatrix K N g.val M
  have hR : ∀ j, Leading (fun i => R i j) j M := reflected_columns_leading g.val M hM hg
  let P := (polynomialLattice K N A).map (matrixLinear R)
  have hP : HasPivots P := image_hasPivots R M hR _ (polynomialHasPivots K N A)
  have hmap : P.map (polynomialEmbedding K N) =
      level (shift K N) (positiveAction K N g A.val) M := by
    rw [show P = (polynomialLattice K N A).map (matrixLinear (reflectedMatrix K N g.val M)) from rfl,
      reflectedLattice_map_embedding K N g M hM,polynomialLattice_map]
  have hpow : powerShift P a = powerShift (polynomialLattice K N B) (b+M) := by
    apply Submodule.map_injective_of_injective (polynomialEmbedding_injective K N)
    rw [powerShift_map_embedding,hmap,powerShift_map_embedding,polynomialLattice_map]
    rw [level_swap,he,← level_add]
  intro i
  have hdeg : pivotDegree (powerShift P a) (powerShift_hasPivots P hP a) i =
      pivotDegree (powerShift (polynomialLattice K N B) (b+M))
        (powerShift_hasPivots _ (polynomialHasPivots K N B) (b+M)) i := by
    simp only [hpow]
  rw [pivotDegree_powerShift P hP a,
    pivotDegree_powerShift _ (polynomialHasPivots K N B) (b+M),
    pivotDegree_image R M hR _ (polynomialHasPivots K N A)] at hdeg
  change diagonalExponents K N A i+M+a = diagonalExponents K N B i+(b+M) at hdeg
  omega

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable (K : Type) [Field K] (N : ℕ)

lemma diagonalExponents_cut (cut : Fin N) (i : Fin N) :
    diagonalExponents K N (cutVertex K N cut) i = cutExponent N cut i := by
  classical
  let A := polynomialLattice K N (cutVertex K N cut)
  let hA := polynomialHasPivots K N (cutVertex K N cut)
  change pivotDegree A hA i = cutExponent N cut i
  apply le_antisymm
  · apply pivotDegree_min A hA i (v := Pi.single i (Polynomial.X ^ cutExponent N cut i))
    · intro j
      by_cases hji : j = i
      · subst j
        exact ⟨1,by simp [polynomialEmbedding_apply,uniformizer]⟩
      · exact ⟨0,by simp [polynomialEmbedding_apply,hji]⟩
    · exact leading_monomial _ _
  · by_cases hc : i.val < cut.val
    · suffices hn : pivotDegree A hA i ≠ 0 by simpa only [cutExponent,ite_eq_left hc] using Nat.one_le_iff_ne_zero.mpr hn
      intro hz
      obtain ⟨f,hf⟩ := pivot_mem A hA i i
      have hp : f * Polynomial.X = (pivot A hA i) i := by
        apply RatFunc.algebraMap_injective K
        simpa only [polynomialEmbedding_apply,
          cutExponent,ite_eq_left hc,pow_one,map_mul,uniformizer] using hf
      have hn := (pivot_leading A hA i).1
      rw [hz,← hp] at hn
      simp at hn
    · simp only [cutExponent,ite_eq_right hc,Nat.zero_le]

lemma orbit_cut_pivots (hN : 0 < N) (g : Matrix.SpecialLinearGroup (Fin N) K[X])
    (hg : ∀ i j : Fin N, j ≤ i → (g i j).coeff 0 = (1 : Matrix (Fin N) (Fin N) K) i j)
    (cut : Fin N) : ∃ m : ℕ, ∀ i,
      diagonalExponents K N (actVertex K N hN g (cutVertex K N cut)) i = m+cutExponent N cut i := by
  let B := actVertex K N hN g (cutVertex K N cut)
  obtain ⟨a,b,he⟩ := actVertex_homothetic K N hN g (cutVertex K N cut)
  have hh := homothetic_action_pivots K N g hg (cutVertex K N cut) B a b he
  have hl : N-1 < N := by omega
  let last : Fin N := ⟨N-1,hl⟩
  have hc : ¬last.val < cut.val := by dsimp [last]; have := cut.isLt; omega
  have ht := hh last
  rw [diagonalExponents_cut] at ht
  simp only [cutExponent,ite_eq_right hc,zero_add] at ht
  refine ⟨diagonalExponents K N B last,fun i => ?_⟩
  change diagonalExponents K N B i = _
  have hi := hh i
  rw [diagonalExponents_cut] at hi
  omega

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.AffineWindow
open scoped BigOperators
variable {N : ℕ}

def cutDegree (N t : ℕ) (i : Fin N) : ℕ := t/N + if i.val < t%N then 1 else 0

lemma sum_indicator_lt (r : ℕ) (hr : r ≤ N) :
    (∑ i : Fin N, if i.val < r then 1 else 0 : ℕ) = r := by
  simp only [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const,
    smul_eq_mul,mul_one,Fin.card_filter_val_lt,min_eq_right hr]

lemma sum_cut_shift (m : ℕ) (cut : Fin N) :
    (∑ i : Fin N, (m + (if i.val < cut.val then 1 else 0))) = N*m+cut.val := by
  rw [Finset.sum_add_distrib,sum_indicator_lt cut.val cut.isLt.le]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]

lemma sum_cutDegree (hN : 0 < N) (t : ℕ) : ∑ i : Fin N, cutDegree N t i = t := by
  change (∑ i : Fin N, (t/N + (if i.val < t%N then 1 else 0))) = t
  rw [sum_cut_shift (t/N) ⟨t%N,Nat.mod_lt _ hN⟩]
  exact Nat.div_add_mod t N

lemma cutDegree_succ (hN : 0 < N) (t : ℕ) (i : Fin N) :
    cutDegree N (t+1) i = cutDegree N t i + if i.val = t%N then 1 else 0 := by
  have hm := Nat.mod_lt t hN
  have hi := i.isLt
  have hr := Nat.mod_add_div t N
  by_cases hs : t%N+1 < N
  · have hd : (t+1)/N = t/N := by
      rw [show t+1 = N*(t/N)+(t%N+1) by omega,Nat.mul_add_div hN,
        Nat.div_eq_of_lt hs,Nat.add_zero]
    have hl : (t+1)%N = t%N+1 := by rw [Nat.add_mod,Nat.mod_eq_of_lt (show 1<N by omega),Nat.mod_eq_of_lt hs]
    simp only [cutDegree,hd,hl]
    split_ifs <;> omega
  · have he : t%N+1 = N := by omega
    have hl : (t+1)%N = 0 := by
      rw [← Nat.mod_add_mod t N 1,he,Nat.mod_self]
    have hd : (t+1)/N = t/N+1 := by
      have hh := Nat.div_add_mod (t+1) N
      rw [hl] at hh
      nlinarith [Nat.div_add_mod t N]
    simp only [cutDegree,hd,hl,not_lt_zero,ite_false]
    split_ifs <;> omega

lemma cut_shift_identify (hN : 0 < N) (t m : ℕ) (cut : Fin N)
    (he : N*m+cut.val = t) :
    (fun i : Fin N => m+if i.val < cut.val then 1 else 0) = cutDegree N t := by
  have hd : t/N = m := by rw [← he,Nat.mul_add_div hN,Nat.div_eq_of_lt cut.isLt,Nat.add_zero]
  have hm : t%N = cut.val := by rw [← he,Nat.mul_add_mod,Nat.mod_eq_of_lt cut.isLt]
  funext i
  simp only [cutDegree,hd,hm]

lemma flag_height (a : Fin N → ℕ) (p : Equiv.Perm (Fin N)) (r : Fin (N+1)) :
    (∑ i : Fin N, (a i + (if (p.symm i).val < r.val then 1 else 0))) = (∑ i : Fin N, a i)+r.val := by
  rw [Finset.sum_add_distrib]
  congr 1
  calc
    (∑ i : Fin N, if (p.symm i).val < r.val then 1 else 0) =
        (∑ i : Fin N, if i.val < r.val then 1 else 0) :=
      p.symm.sum_comp (fun i => if i.val < r.val then 1 else 0)
    _ = r.val := sum_indicator_lt r.val (by omega : r.val ≤ N)

theorem inversion_zero_of_cut_flag (hN : 0 < N) (a : Fin N → ℕ)
    (p : Equiv.Perm (Fin N))
    (hc : ∀ r : Fin (N+1), ∃ m : ℕ, ∃ cut : Fin N, ∀ i,
      a i + (if (p.symm i).val < r.val then 1 else 0) = m+if i.val < cut.val then 1 else 0) :
    inversion (N := N) (List.ofFn (fun r => (N*a (p r)+(p r).val : ℕ) : Fin N → ℤ)) = 0 := by
  let c := ∑ i : Fin N, a i
  have hflag (r : Fin (N+1)) : ∀ i,
      a i + (if (p.symm i).val < r.val then 1 else 0) = cutDegree N (c+r.val) i := by
    obtain ⟨m,cut,hh⟩ := hc r
    have hs := congrArg (fun f : Fin N → ℕ => ∑ i, f i) (funext hh)
    rw [flag_height,sum_cut_shift] at hs
    have he := cut_shift_identify hN (c+r.val) m cut hs.symm
    intro i
    exact (hh i).trans (congr_fun he i)
  have hres (r : Fin N) : (p r).val = (c+r.val)%N := by
    have hs := hflag r.succ (p r)
    have ht := hflag r.castSucc (p r)
    simp only [Equiv.symm_apply_apply,Fin.val_succ,Fin.val_castSucc,Nat.lt_succ_self,ite_true,
      lt_self_iff_false,ite_false,Nat.add_zero] at hs ht
    rw [← Nat.add_assoc,cutDegree_succ hN,← ht] at hs
    split_ifs at hs with he
    · exact he
    · omega
  have hw (r : Fin N) : N*a (p r)+(p r).val = c+r.val := by
    have ht := hflag r.castSucc (p r)
    simp only [Equiv.symm_apply_apply,Fin.val_castSucc,lt_self_iff_false,ite_false,Nat.add_zero,
      cutDegree,hres r,lt_self_iff_false,ite_false,Nat.add_zero] at ht
    rw [ht,hres]
    exact Nat.div_add_mod _ _
  apply (inversion_zero_iff hN _).mpr
  apply List.pairwise_ofFn.mpr
  intro i j hij
  simp only [hw]
  have hi := i.isLt
  have hj := j.isLt
  constructor
  · exact_mod_cast (show c+i.val ≤ c+j.val by omega)
  · exact_mod_cast (show c+j.val < c+i.val+N by omega)

end CoboundaryExpanders.AffineWindow

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable (K : Type) [Field K] (N : ℕ)

def OpposedVertex (hN : 0 < N) (A : Vertex K N) : Prop :=
  ∃ g : Matrix.SpecialLinearGroup (Fin N) K[X],
    (∀ i j : Fin N, j ≤ i → (g i j).coeff 0 = (1 : Matrix (Fin N) (Fin N) K) i j) ∧
    ∃ cut : Fin N, A = actVertex K N hN g (cutVertex K N cut)

lemma opposed_pivots (hN : 0 < N) (A : Vertex K N) (hA : OpposedVertex K N hN A) :
    ∃ m : ℕ, ∃ cut : Fin N, ∀ i, diagonalExponents K N A i = m+cutExponent N cut i := by
  obtain ⟨g,hg,cut,rfl⟩ := hA
  obtain ⟨m,hm⟩ := orbit_cut_pivots K N hN g hg cut
  exact ⟨m,cut,hm⟩

theorem opposed_flag_common_orbit {M : ℕ} (hN : 0 < N) (B : Fin (M+1) → Vertex K N)
    (hanti : Antitone (fun r => (B r).val))
    (hbelow : ∀ r, level (shift K N) (B 0).val 1 ≤ (B r).val)
    (hop : ∀ r, OpposedVertex K N hN (B r)) :
    ∃ g : Matrix.SpecialLinearGroup (Fin N) K[X],
      (∀ i j : Fin N, j ≤ i → Polynomial.eval 0 (g i j) = (1 : Matrix (Fin N) (Fin N) K) i j) ∧
      ∃ cut : Fin (M+1) → Fin N, ∀ r,
        B r = actVertex K N hN g (cutVertex K N (cut r)) := by
  choose m cut hi using fun r => opposed_pivots K N hN (B r) (hop r)
  obtain ⟨g,hg,hv⟩ := zero_pivots_common_orbit K N hN B hanti hbelow cut m hi
  exact ⟨g,hg,cut,hv⟩

namespace FullChamber
variable {K N} {hN : 0 < N} (C : FullChamber K N hN)

theorem zero_of_cut_pivots
    (hc : ∀ r : Fin N, ∃ m : ℕ, ∃ cut : Fin N, ∀ i,
      diagonalExponents K N (C.vertex r) i = m+cutExponent N cut i) :
    C.length = 0 := by
  apply AffineWindow.inversion_zero_of_cut_flag hN
    (pivotDegree C.polynomialChamber.top C.polynomialChamber.hasTop) C.polynomialChamber.word
  intro r
  have he : ∃ m : ℕ, ∃ cut : Fin N, ∀ i,
      pivotDegree (C.stage r) (C.hasStage r) i = m+cutExponent N cut i := by
    by_cases hr : r.val < N
    · obtain ⟨m,cut,hh⟩ := hc ⟨r.val,hr⟩
      refine ⟨m,cut,?_⟩
      intro i
      have hstage : C.stage r = polynomialLattice K N (C.vertex ⟨r.val,hr⟩) := dite_eq_left hr
      simpa only [hstage,diagonalExponents] using hh i
    · have hre : r = Fin.last N := Fin.ext (by change r.val = N; have := r.isLt; omega)
      subst r
      obtain ⟨m,cut,hh⟩ := hc C.topIndex
      refine ⟨m+1,cut,?_⟩
      intro i
      have hp : pivotDegree (C.stage (Fin.last N)) (C.hasStage _) i =
          diagonalExponents K N (C.vertex C.topIndex) i+1 := by
        simpa only [C.stage_last,diagonalExponents] using
          pivotDegree_powerShift _ (polynomialHasPivots K N (C.vertex C.topIndex)) 1 i
      rw [hp]
      have hi := hh i
      omega
  obtain ⟨m,cut,he⟩ := he
  refine ⟨m,cut,?_⟩
  intro i
  exact (C.polynomialChamber.stage_degree r i).symm.trans (he i)

theorem zero_iff_vertexwise_opposed :
    C.length = 0 ↔ ∀ r, OpposedVertex K N hN (C.vertex r) := by
  constructor
  · intro hz
    obtain ⟨g,hg,c,hv⟩ := C.zero_common_orbit hz
    intro r
    refine ⟨g,?_,⟨(c+r.val)%N,Nat.mod_lt _ hN⟩,hv r⟩
    intro i j hij
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using hg i j hij
  · intro hc
    exact C.zero_of_cut_pivots (fun r => opposed_pivots K N hN (C.vertex r) (hc r))

end FullChamber
end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders

lemma finite_chain_enumeration {P : Type} [PartialOrder P] [DecidableEq P] (s : Finset P) (hs : s.Nonempty)
    (hc : ∀ a ∈ s, ∀ b ∈ s, a ≤ b ∨ b ≤ a) :
    ∃ M : ℕ, ∃ B : Fin (M+1) → P, StrictAnti B ∧ Finset.univ.image B = s := by
  classical
  have hchain : IsChain (· ≤ ·) (s : Set P) := fun a ha b hb _ => hc a ha b hb
  let : LinearOrder (s : Set P) := hchain.lt_of_le.linearOrder
  obtain ⟨M,hM⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Finset.card_pos.mpr hs))
  have hcard : Fintype.card (OrderDual (s : Set P)) = M+1 := by
    change Fintype.card {p // p ∈ s} = M+1
    simpa only [Fintype.card_coe] using hM
  let e := Fintype.orderIsoFinOfCardEq (OrderDual (s : Set P)) hcard
  let B (r : Fin (M+1)) : P := (e r).val
  refine ⟨M,B,?_,?_⟩
  · intro r t hrt
    exact e.strictMono hrt
  · ext a
    constructor
    · rintro ha
      obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp ha
      exact (e r).property
    · intro ha
      obtain ⟨r,hr⟩ := e.surjective (⟨a,ha⟩ : (s : Set P))
      exact Finset.mem_image.mpr ⟨r,Finset.mem_univ _,(show B r = a from congrArg Subtype.val hr)⟩

end CoboundaryExpanders

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
open AffineLattices
variable (K : Type) [Field K] (N : ℕ)

theorem common_orbit_iff_induced (hN : 0 < N) (s : Finset (Vertex K N)) :
    (∃ g : Matrix.SpecialLinearGroup (Fin N) K[X],
      (∀ i j : Fin N, j ≤ i → (g i j).coeff 0 = (1 : Matrix (Fin N) (Fin N) K) i j) ∧
      ∃ A : Finset (Fin N),
        A.image (fun cut => actVertex K N hN g (cutVertex K N cut)) = s) ↔
    s ∈ (building K N).faces ∧ ∀ A ∈ s, OpposedVertex K N hN A := by
  classical
  constructor
  · rintro ⟨g,hg,A,rfl⟩
    constructor
    · change A.image (actVertex K N hN g ∘ cutVertex K N) ∈ _
      rw [← Finset.image_image]
      exact actVertex_face K N hN g _ ((building K N).downward
        (baseChamber_face K N) (Finset.image_subset_image (Finset.subset_univ A)))
    · intro B hB
      obtain ⟨cut,_,rfl⟩ := Finset.mem_image.mp hB
      exact ⟨g,hg,cut,rfl⟩
  · rintro ⟨hs,hop⟩
    by_cases hempty : s = ∅
    · subst s
      refine ⟨1,?_,∅,Finset.image_empty _⟩
      intro i j hij
      simp only [Matrix.SpecialLinearGroup.coe_one,Matrix.one_apply]
      split_ifs <;> simp
    · obtain ⟨M,B,hanti,hB⟩ := CoboundaryExpanders.finite_chain_enumeration s
        (Finset.nonempty_iff_ne_empty.mpr hempty) hs.1
      have hmem (r : Fin (M+1)) : B r ∈ s := by
        rw [← hB]
        exact Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩
      have hbelow (r : Fin (M+1)) : level (shift K N) (B 0).val 1 ≤ (B r).val := by
        simpa only [level_succ,level_zero] using hs.2 (B 0) (hmem 0) (B r) (hmem r)
      obtain ⟨g,hg,cut,hv⟩ := opposed_flag_common_orbit K N hN B
        (fun r t hrt => hanti.antitone hrt) hbelow (fun r => hop (B r) (hmem r))
      refine ⟨g,?_,Finset.univ.image cut,?_⟩
      · intro i j hij
        simpa only [Polynomial.coeff_zero_eq_eval_zero] using hg i j hij
      · rw [Finset.image_image]
        convert hB using 1
        apply Finset.image_congr
        intro r hr
        exact (hv r).symm

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
variable (K : Type) [Field K] (N : ℕ)
attribute [local irreducible] residueMap latticeBasis

abbrev ResidueInterval (A : Vertex K N) := Set.Icc (shift K N A.val) A.val

noncomputable def liftResidue (A : Vertex K N) (W : Submodule K (Fin N → K)) : LatticeSpace K N where
  carrier := {v | ∃ h : v ∈ A.val, residueMap K N A ⟨v,h⟩ ∈ W}
  zero_mem' := by
    refine ⟨A.val.zero_mem,?_⟩
    change residueMap K N A (0 : A.val) ∈ W
    rw [map_zero]
    exact W.zero_mem
  add_mem' := by
    rintro v w ⟨hv,hv'⟩ ⟨hw,hw'⟩
    refine ⟨A.val.add_mem hv hw,?_⟩
    change residueMap K N A ((⟨v,hv⟩ : A.val) + ⟨w,hw⟩) ∈ W
    exact ((residueMap K N A).map_add ⟨v,hv⟩ ⟨w,hw⟩).symm ▸ W.add_mem hv' hw'
  smul_mem' := by
    rintro f v ⟨hv,hv'⟩
    refine ⟨A.val.smul_mem f hv,?_⟩
    change residueMap K N A (f • (⟨v,hv⟩ : A.val)) ∈ W
    rw [residueMap_smul_polynomial]
    exact W.smul_mem _ hv'

lemma liftResidue_le (A : Vertex K N) (W : Submodule K (Fin N → K)) :
    liftResidue K N A W ≤ A.val := fun _ hv => hv.choose

lemma shift_le_liftResidue (A : Vertex K N) (W : Submodule K (Fin N → K)) :
    shift K N A.val ≤ liftResidue K N A W := by
  intro v hv
  have hvA := shift_le_self K N A.val hv
  refine ⟨hvA,?_⟩
  rw [(residueMap_eq_zero_iff K N A ⟨v,hvA⟩).mpr hv]
  exact W.zero_mem

lemma mem_liftResidue (A : Vertex K N) (W : Submodule K (Fin N → K)) (v : A.val) :
    v.val ∈ liftResidue K N A W ↔ residueMap K N A v ∈ W := by
  constructor
  · rintro ⟨hv,h⟩; exact h
  · intro h; exact ⟨v.property,h⟩

noncomputable def intervalSubspace (A : Vertex K N) (B : ResidueInterval K N A) : Submodule K (Fin N → K) :=
  (((B.val.restrictScalars K).comap (A.val.subtype.restrictScalars K)).map (residueMap K N A))

lemma mem_intervalSubspace (A : Vertex K N) (B : ResidueInterval K N A) (w : Fin N → K) :
    w ∈ intervalSubspace K N A B ↔ ∃ v : A.val, v.val ∈ B.val ∧ residueMap K N A v = w := Iff.rfl

lemma lift_intervalSubspace (A : Vertex K N) (B : ResidueInterval K N A) :
    liftResidue K N A (intervalSubspace K N A B) = B.val := by
  ext v
  constructor
  · rintro ⟨hv,hv'⟩
    obtain ⟨w,hw,he⟩ := (mem_intervalSubspace K N A B _).mp hv'
    have hz : residueMap K N A ((⟨v,hv⟩ : A.val) - w) = 0 := by rw [map_sub,he,sub_self]
    have hd : v - w.val ∈ B.val := B.property.1 ((residueMap_eq_zero_iff K N A _).mp hz)
    have hh := B.val.add_mem hd hw
    simpa only [sub_add_cancel] using hh
  · intro hv
    refine ⟨B.property.2 hv,?_⟩
    exact (mem_intervalSubspace K N A B _).mpr ⟨⟨v,B.property.2 hv⟩,hv,rfl⟩

lemma intervalSubspace_lift (A : Vertex K N) (W : Submodule K (Fin N → K)) :
    intervalSubspace K N A ⟨liftResidue K N A W,shift_le_liftResidue K N A W,liftResidue_le K N A W⟩ = W := by
  ext w
  rw [mem_intervalSubspace]
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact (mem_liftResidue K N A W v).mp hv
  · intro hw
    obtain ⟨v,rfl⟩ := residueMap_surjective K N A w
    exact ⟨v,(mem_liftResidue K N A W v).mpr hw,rfl⟩

noncomputable def residueIntervalIso (A : Vertex K N) :
    ResidueInterval K N A ≃o Submodule K (Fin N → K) where
  toFun := intervalSubspace K N A
  invFun W := ⟨liftResidue K N A W,shift_le_liftResidue K N A W,liftResidue_le K N A W⟩
  left_inv B := Subtype.ext (lift_intervalSubspace K N A B)
  right_inv := intervalSubspace_lift K N A
  map_rel_iff' := by
    intro B D
    constructor
    · intro h v hv
      have hvA := B.property.2 hv
      have hv' : residueMap K N A ⟨v,hvA⟩ ∈ intervalSubspace K N A D :=
        h ((mem_intervalSubspace K N A B _).mpr ⟨⟨v,hvA⟩,hv,rfl⟩)
      rw [← lift_intervalSubspace K N A D]
      exact ⟨hvA,hv'⟩
    · intro h w hw
      obtain ⟨v,hv,rfl⟩ := (mem_intervalSubspace K N A B w).mp hw
      exact (mem_intervalSubspace K N A D _).mpr ⟨v,h hv,rfl⟩

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
open AffineLattices
variable (K : Type) [Field K] (N : ℕ)

lemma interval_exists_normalized (hN : 0 < N) (A : Vertex K N) (B : ResidueInterval K N A) :
    ∃ D : Vertex K N, Homothetic (shift K N) B.val D.val := by
  obtain ⟨m,hm⟩ := vertex_bounded (shift K N) (standard K N) A
  obtain ⟨D,j,_,hj⟩ := exists_normalized (shift K N) (standard K N)
    (shift_standard_le K N) (standard_not_le_shift K N hN) (m+1) B.val
    (B.property.2.trans (vertex_le _ _ A))
    ((shift K N).monotone hm |>.trans B.property.1) (shift_le_self K N B.val)
  exact ⟨D,0,j,hj⟩

noncomputable def intervalNormalize (hN : 0 < N) (A : Vertex K N) (B : ResidueInterval K N A) :
    Vertex K N := (interval_exists_normalized K N hN A B).choose

lemma intervalNormalize_homothetic (hN : 0 < N) (A : Vertex K N) (B : ResidueInterval K N A) :
    Homothetic (shift K N) B.val (intervalNormalize K N hN A B).val :=
  (interval_exists_normalized K N hN A B).choose_spec

lemma intervalNormalize_vertex (hN : 0 < N) (A D : Vertex K N)
    (hd : shift K N A.val ≤ D.val) (hu : D.val ≤ A.val) :
    intervalNormalize K N hN A ⟨D.val,hd,hu⟩ = D := by
  apply ((homothetic_normalized_iff (shift K N) (standard K N) (shift_standard_le K N) _ _).mp)
  exact homothetic_symm _ (intervalNormalize_homothetic K N hN A ⟨D.val,hd,hu⟩)

lemma intervalNormalize_injOn (hN : 0 < N) (A : Vertex K N) :
    Set.InjOn (intervalNormalize K N hN A) {B | B.val ≠ shift K N A.val} := by
  intro B hB D hD he
  have hb : ¬ B.val ≤ shift K N A.val := fun h => hB (le_antisymm h B.property.1)
  have hd : ¬ D.val ≤ shift K N A.val := fun h => hD (le_antisymm h D.property.1)
  let VB : AffineLattices.Vertex (shift K N) A.val :=
    ⟨B.val,B.property.2,hb,⟨1,B.property.1⟩,(shift K N).monotone B.property.2 |>.trans B.property.1⟩
  let VD : AffineLattices.Vertex (shift K N) A.val :=
    ⟨D.val,D.property.2,hd,⟨1,D.property.1⟩,(shift K N).monotone D.property.2 |>.trans D.property.1⟩
  have hh : Homothetic (shift K N) VB.val VD.val :=
    homothetic_trans _ (intervalNormalize_homothetic K N hN A B)
      (he ▸ homothetic_symm _ (intervalNormalize_homothetic K N hN A D))
  have hBD := (homothetic_normalized_iff (shift K N) A.val (shift_le_self K N A.val) VB VD).mp hh
  exact Subtype.ext (congrArg (fun Z : AffineLattices.Vertex (shift K N) A.val => Z.val) hBD)

lemma intervalNormalize_face (hN : 0 < N) (A : Vertex K N)
    (s : Finset (ResidueInterval K N A))
    (hc : ∀ B ∈ s, ∀ D ∈ s, B ≤ D ∨ D ≤ B) :
    s.image (intervalNormalize K N hN A) ∈ (building K N).faces := by
  classical
  apply (isFace_iff_compatible (shift K N) (standard K N) (shift_standard_le K N) _).mpr
  intro B hB D hD
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hB
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hD
  apply compatible_homothetic _ (intervalNormalize_homothetic K N hN A b)
    (intervalNormalize_homothetic K N hN A d)
  rcases hc b hb d hd with hBD | hDB
  · apply compatible_symm
    exact ⟨0,0,(shift K N).monotone d.property.2 |>.trans b.property.1,hBD⟩
  · exact ⟨0,0,(shift K N).monotone b.property.2 |>.trans d.property.1,hDB⟩

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders
open Module
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

lemma covBy_finrank {U W : Submodule K V} (h : U ⋖ W) :
    finrank K W = finrank K U + 1 := by
  obtain ⟨v,hvW,hvU⟩ := SetLike.exists_of_lt h.lt
  have hle : U ⊔ K ∙ v ≤ W := sup_le h.le ((Submodule.span_singleton_le_iff_mem v W).mpr hvW)
  have hlt : U < U ⊔ K ∙ v := lt_of_le_of_ne le_sup_left (by
    intro he
    exact hvU (he.symm ▸ (show v ∈ U ⊔ K ∙ v from (show K ∙ v ≤ U ⊔ K ∙ v from le_sup_right) (Submodule.mem_span_singleton_self v))))
  have he : U ⊔ K ∙ v = W := (h.eq_or_eq le_sup_left hle).resolve_left (ne_of_gt hlt)
  rw [← he,Submodule.finrank_sup_span_singleton hvU]

theorem ambient_chain_complete_flag (s : Finset (Submodule K V))
    (hc : ∀ A ∈ s, ∀ B ∈ s, A ≤ B ∨ B ≤ A) :
    ∃ F : Fin (finrank K V + 1) → Submodule K V,
      StrictMono F ∧ (∀ i, finrank K (F i) = i.val) ∧
      F 0 = ⊥ ∧ F (Fin.last (finrank K V)) = ⊤ ∧
      ∀ W ∈ s, ∃ i, F i = W := by
  classical
  have hc' : ∀ A ∈ insert (⊥ : Submodule K V) s, ∀ B ∈ insert ⊥ s, A ≤ B ∨ B ≤ A := by
    intro A hA B hB
    rcases Finset.mem_insert.mp hA with rfl | hA
    · exact Or.inl bot_le
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact Or.inr bot_le
    exact hc A hA B hB
  obtain ⟨M,B,hB,hBi⟩ := finite_chain_enumeration (insert (⊥ : Submodule K V) s)
    (Finset.insert_nonempty _ _) hc'
  let c : LTSeries (Submodule K V) := LTSeries.mk M (fun i => B i.rev)
    (fun i j hij => hB (Fin.rev_lt_rev.mpr hij))
  obtain ⟨t,e,hte,ht0,htN⟩ := c.exists_relSeries_covBy_and_head_eq_bot_and_last_eq_bot
  have htstrict : StrictMono t := Fin.strictMono_iff_lt_succ.mpr (fun i => (t.step i).lt)
  have htrank (i : Fin (t.length+1)) : finrank K (t i) = i.val := by
    induction i using Fin.induction with
    | zero => change finrank K t.head = 0; rw [ht0,finrank_bot]
    | succ i ih =>
      rw [covBy_finrank (t.step i),ih]
      rfl
  have hlen : t.length = finrank K V := by
    have hh := htrank (Fin.last t.length)
    change finrank K t.last = t.length at hh
    rw [htN,finrank_top] at hh
    exact hh.symm
  let F (i : Fin (finrank K V+1)) : Submodule K V :=
    t (Fin.cast (congrArg (·+1) hlen.symm) i)
  refine ⟨F,?_,?_,?_,?_,?_⟩
  · exact fun i j hij => htstrict (show Fin.cast _ i < Fin.cast _ j from hij)
  · intro i
    exact htrank _
  · simpa only [F,Fin.cast_zero,RelSeries.head] using ht0
  · simpa only [F,Fin.cast_last,RelSeries.last] using htN
  · intro W hW
    have hm : W ∈ Finset.univ.image B := by rw [hBi]; exact Finset.mem_insert_of_mem hW
    obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hm
    refine ⟨Fin.cast (congrArg (·+1) hlen) (e r.rev),?_⟩
    change t (Fin.cast _ (Fin.cast _ (e r.rev))) = W
    have hcanc : Fin.cast (congrArg (·+1) hlen.symm)
        (Fin.cast (congrArg (·+1) hlen) (e r.rev)) = e r.rev := Fin.ext rfl
    apply (congrArg t hcanc).trans
    have hh := congr_fun hte r.rev
    change t (e r.rev) = B r.rev.rev at hh
    simpa only [Fin.rev_rev,hr] using hh

end CoboundaryExpanders

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
open AffineLattices Module
variable (K : Type) [Field K] (N : ℕ)

theorem ambient_face_extend (hN : 0 < N) (s : Finset (Vertex K N))
    (hs : s ∈ (building K N).faces) :
    ∃ t : Finset (Vertex K N), s ⊆ t ∧ t ∈ (building K N).faces ∧ t.card = N := by
  classical
  by_cases hempty : s = ∅
  · subst s
    exact ⟨baseChamber K N,Finset.empty_subset _,baseChamber_face K N,baseChamber_card K N⟩
  obtain ⟨M,B,hB,hBi⟩ := CoboundaryExpanders.finite_chain_enumeration s
    (Finset.nonempty_iff_ne_empty.mpr hempty) hs.1
  have hbmem (r : Fin (M+1)) : B r ∈ s := by
    rw [← hBi]
    exact Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩
  let A := B 0
  let D (r : Fin (M+1)) : ResidueInterval K N A :=
    ⟨(B r).val,hs.2 (B 0) (hbmem 0) (B r) (hbmem r),hB.antitone (Fin.zero_le r)⟩
  let e := residueIntervalIso K N A
  have hc : ∀ W ∈ Finset.univ.image (fun r => e (D r)),
      ∀ Z ∈ Finset.univ.image (fun r => e (D r)), W ≤ Z ∨ Z ≤ W := by
    intro W hW Z hZ
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hW
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hZ
    rcases le_total r t with hrt | htr
    · exact Or.inr (e.monotone (hB.antitone hrt))
    · exact Or.inl (e.monotone (hB.antitone htr))
  have hfull : ∃ F : Fin (N+1) → Submodule K (Fin N → K),
      StrictMono F ∧ (∀ i, finrank K (F i) = i.val) ∧
      F 0 = ⊥ ∧ F (Fin.last N) = ⊤ ∧
      ∀ W ∈ Finset.univ.image (fun r => e (D r)), ∃ i, F i = W := by
    have hdim : finrank K (Fin N → K) = N := Module.finrank_fin_fun K
    have hh := CoboundaryExpanders.ambient_chain_complete_flag (K := K) (V := Fin N → K)
      (Finset.univ.image (fun r => e (D r))) hc
    rw [hdim] at hh
    exact hh
  obtain ⟨F,hF,hFr,hF0,hFN,hFs⟩ := hfull
  let G (i : Fin N) : ResidueInterval K N A := e.symm (F i.succ)
  have hG : StrictMono G := fun i j hij => e.symm.strictMono (hF (Fin.succ_lt_succ_iff.mpr hij))
  let L : ResidueInterval K N A := ⟨shift K N A.val,le_rfl,shift_le_self K N A.val⟩
  have heL : e L = ⊥ := by
    apply le_antisymm _ bot_le
    have hh : L ≤ e.symm ⊥ := (e.symm ⊥).property.1
    simpa only [e.apply_symm_apply] using e.monotone hh
  have hGbot (i : Fin N) : (G i).val ≠ shift K N A.val := by
    intro he
    have hh : G i = L := Subtype.ext he
    have hf : F i.succ = ⊥ := by
      simpa only [G,e.apply_symm_apply,heL] using congrArg e hh
    have hr := hFr i.succ
    rw [hf,finrank_bot] at hr
    have hi : i.succ.val = i.val+1 := rfl
    omega
  let v (i : Fin N) := intervalNormalize K N hN A (G i)
  have hv : Function.Injective v := by
    intro i j hij
    exact hG.injective (intervalNormalize_injOn K N hN A (hGbot i) (hGbot j) hij)
  have htface : Finset.univ.image v ∈ (building K N).faces := by
    have hh := intervalNormalize_face K N hN A (Finset.univ.image G) (by
      intro Y hY Z hZ
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hY
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hZ
      rcases le_total i j with hij | hji
      · exact Or.inl (hG.monotone hij)
      · exact Or.inr (hG.monotone hji))
    simpa only [Finset.image_image,Function.comp_def,v] using hh
  refine ⟨Finset.univ.image v,?_,htface,by rw [Finset.card_image_of_injective _ hv]; simp⟩
  intro W hW
  have hBW : W ∈ Finset.univ.image B := by rw [hBi]; exact hW
  obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hBW
  obtain ⟨j,hj⟩ := hFs (e (D r)) (Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩)
  have hj0 : j ≠ 0 := by
    intro he
    subst j
    have hh : D r = L := e.injective (by simpa only [heL,hF0] using hj.symm)
    have hval := congrArg (fun Y : ResidueInterval K N A => Y.val) hh
    apply vertex_normalized (shift K N) (standard K N) (B r)
    change (B r).val = shift K N A.val at hval
    rw [hval]
    exact (shift K N).monotone (vertex_le _ _ A)
  have hjpos : 0 < j.val := by
    have hh : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
    omega
  let i : Fin N := ⟨j.val-1,by have := j.isLt; omega⟩
  have hi : i.succ = j := Fin.ext (by simp only [Fin.val_succ,i]; omega)
  have hGi : G i = D r := by
    apply e.injective
    change e (e.symm (F i.succ)) = e (D r)
    rw [e.apply_symm_apply,hi,hj]
  refine Finset.mem_image.mpr ⟨i,Finset.mem_univ _,?_⟩
  change intervalNormalize K N hN A (G i) = B r
  rw [hGi]
  exact intervalNormalize_vertex K N hN A (B r) (D r).property.1 (D r).property.2

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders
lemma finite_chain_enumeration_of_card {P : Type} [PartialOrder P] [DecidableEq P]
    {N : ℕ} (s : Finset P) (hs : s.card = N)
    (hc : ∀ a ∈ s, ∀ b ∈ s, a ≤ b ∨ b ≤ a) :
    ∃ B : Fin N → P, StrictAnti B ∧ Finset.univ.image B = s := by
  classical
  have hchain : IsChain (· ≤ ·) (s : Set P) := fun a ha b hb _ => hc a ha b hb
  let : LinearOrder (s : Set P) := hchain.lt_of_le.linearOrder
  have hcard : Fintype.card (OrderDual (s : Set P)) = N := by
    change Fintype.card {p // p ∈ s} = N
    simpa only [Fintype.card_coe] using hs
  let e := Fintype.orderIsoFinOfCardEq (OrderDual (s : Set P)) hcard
  let B (r : Fin N) : P := (e r).val
  refine ⟨B,fun _ _ h => e.strictMono h,?_⟩
  ext a
  constructor
  · rintro ha
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp ha
    exact (e r).property
  · intro ha
    obtain ⟨r,hr⟩ := e.surjective (⟨a,ha⟩ : (s : Set P))
    exact Finset.mem_image.mpr ⟨r,Finset.mem_univ _,congrArg Subtype.val hr⟩
end CoboundaryExpanders

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
open AffineLattices
variable (K : Type) [Field K] (N : ℕ)
namespace FullChamber
variable {K N} {hN : 0 < N} (C : FullChamber K N hN)
noncomputable def face : Finset (Vertex K N) := Finset.univ.image C.vertex
lemma mem_face (r : Fin N) : C.vertex r ∈ C.face := by
  classical
  exact Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩
lemma vertex_injective : Function.Injective C.vertex := by
  intro i j h
  exact C.strict.injective (congrArg Subtype.val h)
lemma card_face : C.face.card = N := by
  classical
  rw [face,Finset.card_image_of_injective _ C.vertex_injective]
  simp
lemma face_mem : C.face ∈ (building K N).faces := by
  classical
  constructor
  · intro A hA B hB
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hB
    rcases le_total i j with hij | hji
    · exact Or.inr (C.strict.antitone hij)
    · exact Or.inl (C.strict.antitone hji)
  · intro A hA B hB
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hB
    exact ((shift K N).monotone (C.strict.antitone (show C.topIndex ≤ i from Nat.zero_le _))).trans (C.lower j)
end FullChamber

theorem ambient_face_in_chamber (hN : 0 < N) (s : Finset (Vertex K N))
    (hs : s ∈ (building K N).faces) :
    ∃ C : FullChamber K N hN, s ⊆ C.face := by
  classical
  obtain ⟨t,hst,ht,htN⟩ := ambient_face_extend K N hN s hs
  obtain ⟨B,hB,hBt⟩ := CoboundaryExpanders.finite_chain_enumeration_of_card t htN ht.1
  have hmem (r : Fin N) : B r ∈ t := by
    rw [← hBt]
    exact Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩
  let C : FullChamber K N hN := ⟨B,hB,fun r => ht.2 _ (hmem ⟨0,hN⟩) _ (hmem r)⟩
  refine ⟨C,?_⟩
  change s ⊆ Finset.univ.image B
  rw [hBt]
  exact hst

def codistanceStage (hN : 0 < N) (m : ℕ) : Set (Finset (Vertex K N)) :=
  {s | ∃ C : FullChamber K N hN, C.length ≤ m ∧ s ⊆ C.face}

lemma codistanceStage_mono (hN : 0 < N) : Monotone (codistanceStage K N hN) := by
  rintro m n hmn s ⟨C,hC,hs⟩
  exact ⟨C,hC.trans hmn,hs⟩

lemma codistanceStage_downward (hN : 0 < N) (m : ℕ) {s t : Finset (Vertex K N)}
    (hs : s ∈ codistanceStage K N hN m) (ht : t ⊆ s) :
    t ∈ codistanceStage K N hN m := by
  obtain ⟨C,hC,hs⟩ := hs
  exact ⟨C,hC,ht.trans hs⟩

lemma codistanceStage_exhaust (hN : 0 < N) :
    (⋃ m, codistanceStage K N hN m) = (building K N).faces := by
  ext s
  constructor
  · intro hs
    obtain ⟨m,C,_,hs⟩ := Set.mem_iUnion.mp hs
    exact (building K N).downward C.face_mem hs
  · intro hs
    obtain ⟨C,hC⟩ := ambient_face_in_chamber K N hN s hs
    exact Set.mem_iUnion.mpr ⟨C.length,C,le_rfl,hC⟩

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
open AffineLattices
variable (K : Type) [Field K] (N : ℕ)
lemma actVertex_injective (hN : 0 < N) (g : Matrix.SpecialLinearGroup (Fin N) K[X]) :
    Function.Injective (actVertex K N hN g) :=
  mapVertex_injective (shift K N) (standard K N) (shift_standard_le K N)
    (standard_not_le_shift K N hN) (positiveAction K N g) (positiveAction_shift K N g)
    (positiveAction_upper K N g) (positiveAction_lower K N g)

lemma fullChamber_of_face_card (hN : 0 < N) (s : Finset (Vertex K N))
    (hs : s ∈ (building K N).faces) (hcard : s.card = N) :
    ∃ C : FullChamber K N hN, C.face = s := by
  classical
  obtain ⟨B,hB,hBs⟩ := CoboundaryExpanders.finite_chain_enumeration_of_card s hcard hs.1
  have hmem (r : Fin N) : B r ∈ s := by
    rw [← hBs]
    exact Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩
  exact ⟨⟨B,hB,fun r => hs.2 _ (hmem ⟨0,hN⟩) _ (hmem r)⟩,hBs⟩

theorem codistanceStage_zero (hN : 0 < N) (s : Finset (Vertex K N)) :
    s ∈ codistanceStage K N hN 0 ↔
    s ∈ (building K N).faces ∧ ∀ A ∈ s, OpposedVertex K N hN A := by
  classical
  constructor
  · rintro ⟨C,hC,hs⟩
    refine ⟨(building K N).downward C.face_mem hs,?_⟩
    intro A hA
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp (hs hA)
    exact C.zero_iff_vertexwise_opposed.mp (Nat.eq_zero_of_le_zero hC) r
  · intro hs
    obtain ⟨g,hg,A,hA⟩ := (common_orbit_iff_induced K N hN s).mpr hs
    let f (i : Fin N) := actVertex K N hN g (cutVertex K N i)
    let t := Finset.univ.image f
    have ht : t ∈ (building K N).faces := by
      have hh := actVertex_face K N hN g _ (baseChamber_face K N)
      simpa only [baseChamber,Finset.image_image,Function.comp_def,t,f] using hh
    have htN : t.card = N := by
      change (Finset.univ.image (actVertex K N hN g ∘ cutVertex K N)).card = N
      rw [Finset.card_image_of_injective _ ((actVertex_injective K N hN g).comp (cutVertex_injective K N))]
      simp
    obtain ⟨C,hC⟩ := fullChamber_of_face_card K N hN t ht htN
    refine ⟨C,?_,?_⟩
    · apply Nat.le_zero.mpr
      apply C.zero_iff_vertexwise_opposed.mpr
      intro r
      have hm : C.vertex r ∈ t := hC ▸ C.mem_face r
      obtain ⟨cut,_,he⟩ := Finset.mem_image.mp hm
      exact ⟨g,hg,cut,he.symm⟩
    · rw [hC,← hA]
      exact Finset.image_subset_image (Finset.subset_univ A)

end CoboundaryExpanders.RationalLattices

end

end OAI
