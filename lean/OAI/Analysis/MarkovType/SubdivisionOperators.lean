import OAI.Analysis.MarkovType.C00FiniteCoordinates
import OAI.Analysis.MarkovType.SubdivisionProfileExpansion
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Find
import Mathlib.Order.Monotone.Basic
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity.C00

def blockOffset (J : ℕ → ℕ) (i : ℕ) : ℕ := ∑ k ∈ Finset.range i, J k

@[simp] theorem blockOffset_zero (J : ℕ → ℕ) : blockOffset J 0 = 0 := by
  simp [blockOffset]

theorem blockOffset_succ (J : ℕ → ℕ) (i : ℕ) :
    blockOffset J (i + 1) = blockOffset J i + J i :=
  Finset.sum_range_succ J i

theorem blockOffset_mono (J : ℕ → ℕ) : Monotone (blockOffset J) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [blockOffset_succ]
  exact Nat.le_add_right _ _

theorem blockOffset_strictMono (J : ℕ → ℕ) (hJ : ∀ i, 0 < J i) :
    StrictMono (blockOffset J) := by
  apply strictMono_nat_of_lt_succ
  intro i
  rw [blockOffset_succ]
  have hi := hJ i
  omega

theorem le_blockOffset (J : ℕ → ℕ) (hJ : ∀ i, 0 < J i) (i : ℕ) :
    i ≤ blockOffset J i := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [blockOffset_succ]
      have hi := hJ i
      omega

@[simp] theorem blockOffset_const (q i : ℕ) :
    blockOffset (fun _ => q) i = q * i := by
  simp [blockOffset, Nat.mul_comm]

theorem blockOffset_mul (r : ℕ) (J : ℕ → ℕ) (i : ℕ) :
    blockOffset (fun k => r * J k) i = r * blockOffset J i := by
  simp only [blockOffset, Finset.mul_sum]

theorem sum_range_blockOffset {A : Type*} [AddCommMonoid A]
    (J : ℕ → ℕ) (m : ℕ) (f : ℕ → A) :
    (∑ k ∈ Finset.range (blockOffset J m), f k) =
      ∑ i : Fin m, ∑ t : Fin (J i.val), f (blockOffset J i.val + t.val) := by
  have h (m : ℕ) :
      (∑ k ∈ Finset.range (blockOffset J m), f k) =
        ∑ i ∈ Finset.range m, ∑ t ∈ Finset.range (J i), f (blockOffset J i + t) := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [blockOffset_succ, Finset.sum_range_add, Finset.sum_range_succ, ih]
  calc
    _ = ∑ i ∈ Finset.range m, ∑ t ∈ Finset.range (J i),
        f (blockOffset J i + t) := h m
    _ = _ := by
      rw [Finset.sum_range]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_range (fun t => f (blockOffset J i.val + t))

def blockIndex (J : ℕ → ℕ) (t : Σ i : ℕ, Fin (J i)) : ℕ :=
  blockOffset J t.1 + t.2.val

theorem blockOffset_le_blockIndex (J : ℕ → ℕ) (t : Σ i : ℕ, Fin (J i)) :
    blockOffset J t.1 ≤ blockIndex J t :=
  Nat.le_add_right _ _

theorem blockIndex_lt_blockOffset_succ (J : ℕ → ℕ) (t : Σ i : ℕ, Fin (J i)) :
    blockIndex J t < blockOffset J (t.1 + 1) := by
  rw [blockOffset_succ]
  exact Nat.add_lt_add_left t.2.isLt _

theorem blockIndex_injective (J : ℕ → ℕ) : Function.Injective (blockIndex J) := by
  rintro ⟨i, t⟩ ⟨j, u⟩ he
  have hi : i = j := by
    rcases lt_trichotomy i j with hij | hij | hji
    · have hlt : blockIndex J ⟨i, t⟩ < blockIndex J ⟨j, u⟩ := by
        calc
          _ < blockOffset J (i + 1) := blockIndex_lt_blockOffset_succ J ⟨i, t⟩
          _ ≤ blockOffset J j := blockOffset_mono J (Nat.succ_le_of_lt hij)
          _ ≤ _ := blockOffset_le_blockIndex J ⟨j, u⟩
      exact False.elim ((ne_of_lt hlt) he)
    · exact hij
    · have hlt : blockIndex J ⟨j, u⟩ < blockIndex J ⟨i, t⟩ := by
        calc
          _ < blockOffset J (j + 1) := blockIndex_lt_blockOffset_succ J ⟨j, u⟩
          _ ≤ blockOffset J i := blockOffset_mono J (Nat.succ_le_of_lt hji)
          _ ≤ _ := blockOffset_le_blockIndex J ⟨i, t⟩
      exact False.elim ((ne_of_lt hlt) he.symm)
  subst j
  change blockOffset J i + t.val = blockOffset J i + u.val at he
  have htu : t = u := Fin.ext (Nat.add_left_cancel he)
  subst u
  rfl

theorem exists_blockInterval (J : ℕ → ℕ) (hJ : ∀ i, 0 < J i) (n : ℕ) :
    ∃ i, blockOffset J i ≤ n ∧ n < blockOffset J (i + 1) := by
  have hex : ∃ i, n < blockOffset J (i + 1) :=
    ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) (le_blockOffset J hJ (n + 1))⟩
  let i := Nat.find hex
  have hupper : n < blockOffset J (i + 1) := Nat.find_spec hex
  have hlower : blockOffset J i ≤ n := by
    by_cases hi : i = 0
    · simp [hi]
    · have hpred : i - 1 < Nat.find hex := by
        change i - 1 < i
        omega
      have hnot := Nat.find_min hex hpred
      have hsucc : i - 1 + 1 = i := by omega
      rw [hsucc] at hnot
      omega
  exact ⟨i, hlower, hupper⟩

theorem blockIndex_surjective (J : ℕ → ℕ) (hJ : ∀ i, 0 < J i) :
    Function.Surjective (blockIndex J) := by
  intro n
  obtain ⟨i, hlower, hupper⟩ := exists_blockInterval J hJ n
  rw [blockOffset_succ] at hupper
  have ht : n - blockOffset J i < J i := by omega
  refine ⟨⟨i, ⟨n - blockOffset J i, ht⟩⟩, ?_⟩
  change blockOffset J i + (n - blockOffset J i) = n
  omega

theorem blockIndex_bijective (J : ℕ → ℕ) (hJ : ∀ i, 0 < J i) :
    Function.Bijective (blockIndex J) :=
  ⟨blockIndex_injective J, blockIndex_surjective J hJ⟩

theorem existsUnique_blockIndex (J : ℕ → ℕ) (hJ : ∀ i, 0 < J i) (n : ℕ) :
    ∃! t : Σ i : ℕ, Fin (J i), blockIndex J t = n := by
  obtain ⟨t, ht⟩ := blockIndex_surjective J hJ n
  refine ⟨t, ht, ?_⟩
  intro u hu
  exact blockIndex_injective J (hu.trans ht.symm)

def uniformBlockLift (q : ℕ) (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  q * f (n / q) + n % q

theorem uniformBlockLift_apply (q : ℕ) (f : ℕ → ℕ) (hq : 0 < q)
    (i t : ℕ) (ht : t < q) :
    uniformBlockLift q f (q * i + t) = q * f i + t := by
  have hqr : (q * i + t) / q = i ∧ (q * i + t) % q = t :=
    (Nat.div_mod_unique hq).2 ⟨Nat.add_comm _ _, ht⟩
  simp only [uniformBlockLift, hqr.1, hqr.2]

theorem uniformBlockLift_strictMono (q : ℕ) (f : ℕ → ℕ) (hq : 0 < q)
    (hf : StrictMono f) : StrictMono (uniformBlockLift q f) := by
  intro a b hab
  have hdiv : a / q ≤ b / q := Nat.div_le_div_right hab.le
  by_cases he : a / q = b / q
  · have ha := Nat.div_add_mod a q
    have hb := Nat.div_add_mod b q
    rw [he] at ha
    have hrem : a % q < b % q := by omega
    simp only [uniformBlockLift, he]
    exact Nat.add_lt_add_left hrem _
  · have hstrict : a / q < b / q := lt_of_le_of_ne hdiv he
    have hstep : f (a / q) + 1 ≤ f (b / q) := hf hstrict
    change q * f (a / q) + a % q < q * f (b / q) + b % q
    calc
      _ < q * f (a / q) + q := Nat.add_lt_add_left (Nat.mod_lt a hq) _
      _ = q * (f (a / q) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ ≤ q * f (b / q) := Nat.mul_le_mul_left q hstep
      _ ≤ _ := Nat.le_add_right _ _

def subdivide (J : ℕ → ℕ) : C00 →ₗ[ℝ] C00 :=
  Finsupp.linearCombination ℝ fun i =>
    ∑ t : Fin (J i), Finsupp.single (blockOffset J i + t.val) ((J i : ℝ)⁻¹)

def uniformSubdivision (q : ℕ) : C00 →ₗ[ℝ] C00 := subdivide (fun _ => q)

@[simp] theorem subdivide_single (J : ℕ → ℕ) (i : ℕ) (a : ℝ) :
    subdivide J (Finsupp.single i a) =
      ∑ t : Fin (J i), Finsupp.single (blockOffset J i + t.val) (a / (J i : ℝ)) := by
  simp [subdivide, Finset.smul_sum, Finsupp.smul_single, div_eq_mul_inv]

@[simp] theorem uniformSubdivision_single (q i : ℕ) (a : ℝ) :
    uniformSubdivision q (Finsupp.single i a) =
      ∑ t : Fin q, Finsupp.single (q * i + t.val) (a / (q : ℝ)) := by
  simp [uniformSubdivision, blockOffset, Nat.mul_comm]

theorem subdivide_ofArray (J : ℕ → ℕ) {m : ℕ} (a : Fin m → ℝ) :
    subdivide J (ofArray a) =
      ∑ i : Fin m, ∑ t : Fin (J i.val),
        Finsupp.single (blockOffset J i.val + t.val) (a i / (J i.val : ℝ)) := by
  simp only [ofArray, place, map_sum, subdivide_single]

theorem subdivide_ofArray_eq_finiteSubdivision (J : ℕ → ℕ) {m : ℕ}
    (a : Fin m → ℝ) :
    subdivide J (ofArray a) = Subdivision.finiteSubdivision a (fun i => J i.val) := by
  simp only [subdivide_ofArray, Subdivision.finiteSubdivision_eq, blockOffset]

theorem subdivide_single_apply_block (J : ℕ → ℕ) (i j : ℕ)
    (t : Fin (J i)) (a : ℝ) :
    subdivide J (Finsupp.single j a) (blockOffset J i + t.val) =
      (Finsupp.single j a i) / (J i : ℝ) := by
  classical
  rw [subdivide_single]
  by_cases hji : j = i
  · subst j
    simp only [Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single t]
    · simp
    · intro u _ hut
      have hne : blockOffset J i + u.val ≠ blockOffset J i + t.val := by
        intro h
        exact hut (Fin.ext (Nat.add_left_cancel h))
      simp only [Finsupp.single_apply, ite_eq_right hne]
    · simp
  · have hne (u : Fin (J j)) :
        blockOffset J j + u.val ≠ blockOffset J i + t.val := by
      intro h
      have he : (⟨j, u⟩ : Σ k, Fin (J k)) = ⟨i, t⟩ := blockIndex_injective J h
      exact hji (congrArg Sigma.fst he)
    simp [Finsupp.finsetSum_apply, hne, hji]

theorem subdivide_apply_block (J : ℕ → ℕ) (x : C00) (i : ℕ) (t : Fin (J i)) :
    subdivide J x (blockOffset J i + t.val) = x i / (J i : ℝ) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, add_div]
  | single j a => exact subdivide_single_apply_block J i j t a

theorem sum_subdivide_block (J : ℕ → ℕ) (x : C00) (i : ℕ) (hi : 0 < J i) :
    (∑ t : Fin (J i), subdivide J x (blockOffset J i + t.val)) = x i := by
  have hne : (J i : ℝ) ≠ 0 := by exact_mod_cast hi.ne'
  simp only [subdivide_apply_block, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel₀ (x i) hne

theorem prefixCut_subdivide (J : ℕ → ℕ) (hJ : ∀ i, 0 < J i) (x : C00) (k : ℕ) :
    prefixCut (subdivide J x) (blockOffset J k) = prefixCut x k := by
  rw [prefixCut, sum_range_blockOffset]
  simp_rw [sum_subdivide_block J x _ (hJ _)]
  simpa only [prefixCut] using (Fin.sum_univ_eq_sum_range (fun i => x i) k)

theorem subdivide_ofArray_apply_of_ge (J : ℕ → ℕ) {m : ℕ} (a : Fin m → ℝ)
    (k : ℕ) (hk : blockOffset J m ≤ k) : subdivide J (ofArray a) k = 0 := by
  classical
  rw [subdivide_ofArray]
  simp only [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro t _
  have hlt : blockOffset J i.val + t.val < blockOffset J m := by
    calc
      blockOffset J i.val + t.val < blockOffset J i.val + J i.val :=
        Nat.add_lt_add_left t.isLt _
      _ = blockOffset J (i.val + 1) := (blockOffset_succ J i.val).symm
      _ ≤ blockOffset J m := blockOffset_mono J (Nat.succ_le_of_lt i.isLt)
  have hne : blockOffset J i.val + t.val ≠ k := Nat.ne_of_lt (lt_of_lt_of_le hlt hk)
  simp [hne]

def l1Mass (x : C00) : ℝ := x.sum (fun _ a => |a|)

theorem l1Mass_eq_sum_range (x : C00) (m : ℕ) (h : ∀ k, m ≤ k → x k = 0) :
    l1Mass x = ∑ k ∈ Finset.range m, |x k| := by
  apply Finsupp.sum_of_support_subset x
  · intro k hk
    apply Finset.mem_range.mpr
    by_contra hkm
    have hx := h k (Nat.le_of_not_gt hkm)
    exact (Finsupp.mem_support_iff.mp hk) hx
  · intro _ _
    exact abs_zero

theorem l1Mass_ofArray {m : ℕ} (a : Fin m → ℝ) :
    l1Mass (ofArray a) = ∑ i : Fin m, |a i| := by
  rw [l1Mass_eq_sum_range (ofArray a) m (ofArray_apply_of_ge a)]
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [ofArray_apply]

theorem l1Mass_subdivide (J : ℕ → ℕ) (hJ : ∀ i, 0 < J i) (x : C00) :
    l1Mass (subdivide J x) = l1Mass x := by
  obtain ⟨m, a, rfl⟩ := exists_ofArray x
  rw [l1Mass_eq_sum_range _ (blockOffset J m)
    (subdivide_ofArray_apply_of_ge J a), sum_range_blockOffset, l1Mass_ofArray]
  apply Finset.sum_congr rfl
  intro i _
  simp only [subdivide_apply_block, ofArray_apply, abs_div,
    abs_of_nonneg (show 0 ≤ (J i.val : ℝ) from Nat.cast_nonneg _), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hne : (J i.val : ℝ) ≠ 0 := by exact_mod_cast (hJ i.val).ne'
  exact mul_div_cancel₀ |a i| hne

@[simp] theorem uniformSubdivision_apply (q : ℕ) (hq : 0 < q) (x : C00) (k : ℕ) :
    uniformSubdivision q x k = x (k / q) / (q : ℝ) := by
  have h := subdivide_apply_block (fun _ => q) x (k / q)
    ⟨k % q, Nat.mod_lt k hq⟩
  have hk : q * (k / q) + k % q = k := Nat.div_add_mod k q
  simpa only [uniformSubdivision, blockOffset_const, hk] using h

theorem uniformSubdivision_subdivide (r : ℕ) (hr : 0 < r) (J : ℕ → ℕ)
    (hJ : ∀ i, 0 < J i) (x : C00) :
    uniformSubdivision r (subdivide J x) = subdivide (fun i => r * J i) x := by
  ext k
  obtain ⟨⟨i, t⟩, rfl⟩ := blockIndex_surjective (fun i => r * J i)
    (fun i => Nat.mul_pos hr (hJ i)) k
  change uniformSubdivision r (subdivide J x)
      (blockOffset (fun i => r * J i) i + t.val) =
    subdivide (fun i => r * J i) x (blockOffset (fun i => r * J i) i + t.val)
  rw [subdivide_apply_block (fun i => r * J i) x i t,
    uniformSubdivision_apply r hr, blockOffset_mul]
  have ht : t.val / r < J i := by
    apply (Nat.div_lt_iff_lt_mul hr).mpr
    simpa only [Nat.mul_comm] using t.isLt
  have hdiv : (r * blockOffset J i + t.val) / r = blockOffset J i + t.val / r := by
    rw [Nat.add_comm (r * blockOffset J i) t.val, Nat.add_mul_div_left _ _ hr,
      Nat.add_comm]
  rw [hdiv, subdivide_apply_block J x i ⟨t.val / r, ht⟩]
  simp only [div_div, Nat.cast_mul, mul_comm]

theorem uniformSubdivision_comp_subdivide (r : ℕ) (hr : 0 < r) (J : ℕ → ℕ)
    (hJ : ∀ i, 0 < J i) :
    (uniformSubdivision r).comp (subdivide J) = subdivide (fun i => r * J i) := by
  apply LinearMap.ext
  intro x
  exact uniformSubdivision_subdivide r hr J hJ x

theorem uniformSubdivision_mapDomain (q : ℕ) (hq : 0 < q)
    (f : ℕ → ℕ) (x : C00) :
    uniformSubdivision q (Finsupp.mapDomain f x) =
      Finsupp.mapDomain (uniformBlockLift q f) (uniformSubdivision q x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp [Finsupp.mapDomain_zero]
  | add x y hx hy => simp only [Finsupp.mapDomain_add, map_add, hx, hy]
  | single i a =>
    rw [Finsupp.mapDomain_single, uniformSubdivision_single,
      uniformSubdivision_single, Finsupp.mapDomain_finsetSum]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finsupp.mapDomain_single, uniformBlockLift_apply q f hq i t.val t.isLt]

theorem uniformSubdivision_reindex (q : ℕ) (hq : 0 < q)
    (f : ℕ → ℕ) (hf : StrictMono f) (x : C00) :
    ∃ g : ℕ → ℕ, StrictMono g ∧
      uniformSubdivision q (Finsupp.mapDomain f x) =
        Finsupp.mapDomain g (uniformSubdivision q x) :=
  ⟨uniformBlockLift q f, uniformBlockLift_strictMono q f hq hf,
    uniformSubdivision_mapDomain q hq f x⟩

theorem subdivide_injective (J : ℕ → ℕ) (hJ : ∀ i, 0 < J i) :
    Function.Injective (subdivide J) := by
  intro x y hxy
  ext i
  have h := congrArg (fun z : C00 => z (blockOffset J i)) hxy
  have hx := subdivide_apply_block J x i ⟨0, hJ i⟩
  have hy := subdivide_apply_block J y i ⟨0, hJ i⟩
  simp only [Nat.add_zero] at hx hy
  rw [hx, hy] at h
  have hne : (J i : ℝ) ≠ 0 := by exact_mod_cast (hJ i).ne'
  exact (div_left_inj' hne).mp h

@[simp] theorem prefixCut_uniformSubdivision (q : ℕ) (hq : 0 < q)
    (x : C00) (k : ℕ) :
    prefixCut (uniformSubdivision q x) (q * k) = prefixCut x k := by
  simpa only [uniformSubdivision, blockOffset_const] using
    prefixCut_subdivide (fun _ => q) (fun _ => hq) x k

@[simp] theorem l1Mass_uniformSubdivision (q : ℕ) (hq : 0 < q) (x : C00) :
    l1Mass (uniformSubdivision q x) = l1Mass x :=
  l1Mass_subdivide (fun _ => q) (fun _ => hq) x

theorem uniformSubdivision_ofArray_apply_of_ge (q : ℕ) {m : ℕ} (a : Fin m → ℝ)
    (k : ℕ) (hk : q * m ≤ k) : uniformSubdivision q (ofArray a) k = 0 := by
  exact subdivide_ofArray_apply_of_ge (fun _ => q) a k
    (by simpa only [blockOffset_const] using hk)

end MarkovSuperreflexivity.C00

end

end OAI
