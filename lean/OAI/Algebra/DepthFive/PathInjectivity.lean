import OAI.Algebra.DepthFive.MatrixPaths

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ ι : Type*}

/-- The recursive path enumeration never repeats a path. -/
private theorem matrixEntryPaths_nodup_local [Fintype ι] [DecidableEq ι]
    (labels : List σ) (i j : ι) : (matrixEntryPaths labels i j).Nodup := by
  induction labels generalizing i with
  | nil => by_cases hij : i = j <;> simp [matrixEntryPaths, hij]
  | cons t ts ih =>
      cases ts with
      | nil => simp [matrixEntryPaths]
      | cons u us =>
          rw [matrixEntryPaths, List.nodup_flatMap]
          constructor
          · intro k hk
            apply List.Nodup.map
            · intro p q hpq
              exact List.cons.inj hpq |>.2
            · exact ih k
          · apply List.Pairwise.imp _ (Finset.nodup_toList (Finset.univ : Finset ι))
            intro k l hkl
            apply List.disjoint_iff_ne.mpr
            intro p hp q hq hpq
            obtain ⟨rp, _, rfl⟩ := List.mem_map.mp hp
            obtain ⟨rq, _, rfl⟩ := List.mem_map.mp hq
            exact hkl (congrArg (fun e : σ × ι × ι => e.2.2) (List.cons.inj hpq).1)

/-- Differentiated coordinates have sign -1, multiplied coordinates sign +1. -/
def edgeListShift (side : σ → Bool) : List (σ × ι × ι) → ((σ × ι × ι) →₀ ℤ)
  | [] => 0
  | e :: p => Finsupp.single e (if side e.1 then -1 else 1) + edgeListShift side p

@[simp] theorem edgeListShift_nil (side : σ → Bool) :
    edgeListShift (ι := ι) side [] = 0 := rfl

@[simp] theorem edgeListShift_cons (side : σ → Bool) (e : σ × ι × ι)
    (p : List (σ × ι × ι)) :
    edgeListShift side (e :: p) =
      Finsupp.single e (if side e.1 then -1 else 1) + edgeListShift side p := rfl

/-- A layer absent from a path has no coordinate shift. -/
theorem edgeListShift_apply_eq_zero (side : σ → Bool) (p : List (σ × ι × ι))
    (e : σ × ι × ι) (he : e.1 ∉ p.map Prod.fst) : edgeListShift side p e = 0 := by
  classical
  induction p with
  | nil => simp
  | cons a p ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at he
      have hae : a ≠ e := by
        intro h
        apply he.1
        exact congrArg Prod.fst h.symm
      simp [edgeListShift, hae, ih he.2]

/-- A coordinate absent from the edge list receives no shift. -/
theorem edgeListShift_apply_of_not_mem (side : σ → Bool) (p : List (σ × ι × ι))
    (e : σ × ι × ι) (he : e ∉ p) : edgeListShift side p e = 0 := by
  classical
  induction p with
  | nil => simp
  | cons a p ih =>
      simp only [List.mem_cons, not_or] at he
      simp [edgeListShift, Ne.symm he.1, ih he.2]

/-- With a fixed nonrepeating layer list, the signed shift determines the whole path. -/
theorem edgeListShift_injective_of_labels (side : σ → Bool)
    (labels : List σ) (hlabels : labels.Nodup)
    (p q : List (σ × ι × ι)) (hp : p.map Prod.fst = labels)
    (hq : q.map Prod.fst = labels) (hshift : edgeListShift side p = edgeListShift side q) :
    p = q := by
  classical
  induction labels generalizing p q with
  | nil =>
      have hp0 : p = [] := List.map_eq_nil_iff.mp hp
      have hq0 : q = [] := List.map_eq_nil_iff.mp hq
      simp [hp0, hq0]
  | cons t ts ih =>
      cases p with
      | nil => simp at hp
      | cons a p =>
          cases q with
          | nil => simp at hq
          | cons b q =>
              simp only [List.map_cons, List.cons.injEq] at hp hq
              have ha : a.1 ∉ ts := by simpa [hp.1] using (List.nodup_cons.mp hlabels).1
              have hpa := edgeListShift_apply_eq_zero side p a (by simpa [hp.2] using ha)
              have hqa := edgeListShift_apply_eq_zero side q a (by simpa [hq.2] using ha)
              have heval := congrArg (fun f : (σ × ι × ι) →₀ ℤ => f a) hshift
              have hba : b = a := by
                by_contra hba
                simp only [edgeListShift_cons, Finsupp.add_apply, Finsupp.single_apply,
                  ite_eq_right hba, hpa, hqa, add_zero] at heval
                cases hside : side a.1 <;> simp [hside] at heval
              subst b
              have htail : edgeListShift side p = edgeListShift side q := add_left_cancel hshift
              exact congrArg (List.cons a) (ih hlabels.of_cons p q hp.2 hq.2 htail)

/-- A selected coordinate occurs with its single creation/annihilation sign. -/
theorem edgeListShift_apply_of_mem (side : σ → Bool) (p : List (σ × ι × ι))
    (hlabels : (p.map Prod.fst).Nodup) (e : σ × ι × ι) (he : e ∈ p) :
    edgeListShift side p e = if side e.1 then -1 else 1 := by
  classical
  induction p with
  | nil => simp at he
  | cons a p ih =>
      have hnd := List.nodup_cons.mp hlabels
      rcases List.mem_cons.mp he with hae | hep
      · subst e
        have hz := edgeListShift_apply_eq_zero side p a hnd.1
        simp [edgeListShift, hz]
      · have hae : a ≠ e := by
          intro h
          subst a
          exact hnd.1 (List.mem_map.mpr ⟨e, hep, rfl⟩)
        simp [edgeListShift, hae, ih hnd.2 hep]

/-- With one edge per layer, coordinate shifts are precisely signed membership. -/
theorem edgeListShift_apply [DecidableEq σ] [DecidableEq ι] (side : σ → Bool) (p : List (σ × ι × ι))
    (hlabels : (p.map Prod.fst).Nodup) (e : σ × ι × ι) :
    edgeListShift side p e = if e ∈ p then (if side e.1 then -1 else 1) else 0 := by
  classical
  by_cases he : e ∈ p
  · rw [ite_eq_left he]
    exact edgeListShift_apply_of_mem side p hlabels e he
  · rw [ite_eq_right he]
    exact edgeListShift_apply_of_not_mem side p e he

/-- Finite path indices are distinguished by their signed exponent shifts. -/
theorem matrixEntryPaths_shift_injective [Fintype ι] [DecidableEq ι]
    (side : σ → Bool) (labels : List σ) (hlabels : labels.Nodup) (i j : ι) :
    Function.Injective (fun p : Fin (matrixEntryPaths labels i j).length =>
      edgeListShift side ((matrixEntryPaths labels i j).get p)) := by
  intro p q hpq
  apply (matrixEntryPaths_nodup_local labels i j).get_inj_iff.mp
  exact edgeListShift_injective_of_labels side labels hlabels _ _
    (matrixEntryPaths_get_labels labels i j p)
    (matrixEntryPaths_get_labels labels i j q) hpq

/-- From any fixed input exponent, two distinct paths reach distinct output exponents. -/
theorem matrixEntryPaths_translated_shift_injective [Fintype ι] [DecidableEq ι]
    (side : σ → Bool) (labels : List σ) (hlabels : labels.Nodup) (i j : ι)
    (input : (σ × ι × ι) →₀ ℤ) :
    Function.Injective (fun p : Fin (matrixEntryPaths labels i j).length =>
      input + edgeListShift side ((matrixEntryPaths labels i j).get p)) := by
  intro p q hpq
  exact matrixEntryPaths_shift_injective side labels hlabels i j
    (add_left_cancel hpq)

/-- The signed list shift is the sum of the individual signed coordinates. -/
theorem edgeListShift_eq_sum (side : σ → Bool) (p : List (σ × ι × ι)) :
    edgeListShift side p =
      (p.map (fun e => Finsupp.single e (if side e.1 then (-1 : ℤ) else 1))).sum := by
  induction p with
  | nil => rfl
  | cons e p ih => simp [edgeListShift, ih]

/-- A list containing all layer labels in order has the expected length. -/
theorem edgeList_length {n : ℕ} (p : List (Fin n × ι × ι))
    (hp : p.map Prod.fst = List.finRange n) : p.length = n := by
  simpa using congrArg List.length hp

/-- Convert an edge list ordered by layer into its finite coordinate profile. -/
def edgeProfile {n : ℕ} (p : List (Fin n × ι × ι))
    (hp : p.map Prod.fst = List.finRange n) (t : Fin n) : ι × ι :=
  (p[t.val]'(by rw [edgeList_length p hp]; exact t.isLt)).2

/-- In an ordered edge list, the edge in position `t` is labelled by `t`. -/
theorem edgeProfile_label {n : ℕ} (p : List (Fin n × ι × ι))
    (hp : p.map Prod.fst = List.finRange n) (t : Fin n) :
    (p[t.val]'(by rw [edgeList_length p hp]; exact t.isLt)).1 = t := by
  have hidx : t.val < (p.map Prod.fst).length := by
    simp only [List.length_map, edgeList_length p hp]
    exact t.isLt
  have h : (p.map Prod.fst)[t.val]'hidx = t := by simp [hp]
  simpa only [List.getElem_map] using h

/-- Rebuilding the ordered edge list from its profile changes nothing. -/
theorem edgeList_eq_ofFn_profile {n : ℕ} (p : List (Fin n × ι × ι))
    (hp : p.map Prod.fst = List.finRange n) :
    p = List.ofFn (fun t : Fin n => (t, edgeProfile p hp t)) := by
  apply List.ext_getElem (by simp [edgeList_length p hp])
  intro k hk hk'
  have hkn : k < n := by simpa using hk'
  simp only [List.getElem_ofFn]
  exact Prod.ext (edgeProfile_label p hp ⟨k, hkn⟩) rfl

/-- The list shift agrees with the layerwise finite sum used by profile operators. -/
theorem edgeListShift_eq_sum_profile {n : ℕ} (side : Fin n → Bool)
    (p : List (Fin n × ι × ι)) (hp : p.map Prod.fst = List.finRange n) :
    edgeListShift side p = ∑ t : Fin n,
      Finsupp.single (t, edgeProfile p hp t) (if side t then (-1 : ℤ) else 1) := by
  rw [edgeListShift_eq_sum]
  conv_lhs => rw [edgeList_eq_ofFn_profile p hp, List.map_ofFn, Fin.sum_ofFn]
  rfl

/-- Ordered edge-list indices have distinct layer profiles. -/
theorem matrixEntryPaths_profile_injective [Fintype ι] [DecidableEq ι]
    (n : ℕ) (i j : ι) :
    Function.Injective (fun p : Fin (matrixEntryPaths (List.finRange n) i j).length =>
      edgeProfile ((matrixEntryPaths (List.finRange n) i j).get p)
        (matrixEntryPaths_get_labels (List.finRange n) i j p)) := by
  intro p q hpq
  dsimp only at hpq
  apply (matrixEntryPaths_nodup_local (List.finRange n) i j).get_inj_iff.mp
  rw [edgeList_eq_ofFn_profile _ (matrixEntryPaths_get_labels (List.finRange n) i j p),
    edgeList_eq_ofFn_profile _ (matrixEntryPaths_get_labels (List.finRange n) i j q)]
  rw [hpq]

/-- The signed output is nonnegative exactly when every requested derivative is available. -/
theorem edgeListShift_nonnegative_iff [DecidableEq σ] [DecidableEq ι]
    (side : σ → Bool) (p : List (σ × ι × ι))
    (hlabels : (p.map Prod.fst).Nodup) (input : (σ × ι × ι) → ℕ) :
    (∀ e, 0 ≤ (input e : ℤ) + edgeListShift side p e) ↔
      ∀ e ∈ p, side e.1 = true → 1 ≤ input e := by
  constructor
  · intro h e he hs
    have hnonneg := h e
    rw [edgeListShift_apply side p hlabels e, ite_eq_left he] at hnonneg
    simp only [hs, ite_true] at hnonneg
    omega
  · intro h e
    rw [edgeListShift_apply side p hlabels e]
    by_cases he : e ∈ p
    · rw [ite_eq_left he]
      cases hs : side e.1 with
      | false => simp only [Bool.false_eq_true, ite_false]; omega
      | true =>
          have hi := h e he hs
          simp only [ite_true]
          omega
    · simp [he]

/-- Read a signed edge-list shift using its unique coordinate profile in one layer. -/
theorem edgeListShift_apply_profile [DecidableEq ι] {n : ℕ}
    (side : Fin n → Bool) (p : List (Fin n × ι × ι))
    (hp : p.map Prod.fst = List.finRange n) (t : Fin n) (a b : ι) :
    edgeListShift side p (t, a, b) =
      if edgeProfile p hp t = (a, b) then (if side t then -1 else 1) else 0 := by
  classical
  rw [edgeListShift_eq_sum_profile side p hp, Finsupp.finsetSum_apply,
    Finset.sum_eq_single t]
  · simp [Finsupp.single_apply]
  · intro j hj hjt
    simp [hjt]
  · simp

/-- Four ordered edge lists have compatible global shifts exactly when their
coordinate differences agree separately in every layer. -/
theorem edgeListShift_sub_eq_iff {n : ℕ} (side : Fin n → Bool)
    (p q r s : List (Fin n × ι × ι))
    (hp : p.map Prod.fst = List.finRange n)
    (hq : q.map Prod.fst = List.finRange n)
    (hr : r.map Prod.fst = List.finRange n)
    (hs : s.map Prod.fst = List.finRange n) :
    edgeListShift side p - edgeListShift side q =
      edgeListShift side r - edgeListShift side s ↔
      ∀ t : Fin n,
        Finsupp.single (edgeProfile p hp t) (1 : ℤ) -
          Finsupp.single (edgeProfile q hq t) 1 =
        Finsupp.single (edgeProfile r hr t) 1 -
          Finsupp.single (edgeProfile s hs t) 1 := by
  classical
  have hsign (t : Fin n) : (if side t then (-1 : ℤ) else 1) ≠ 0 := by
    cases h : side t <;> simp
  constructor
  · intro heq t
    ext ab
    rcases ab with ⟨a, b⟩
    have h := congrArg (fun f : (Fin n × ι × ι) →₀ ℤ => f (t, a, b)) heq
    simp only [Finsupp.sub_apply, edgeListShift_apply_profile side p hp,
      edgeListShift_apply_profile side q hq, edgeListShift_apply_profile side r hr,
      edgeListShift_apply_profile side s hs] at h
    apply mul_left_cancel₀ (hsign t)
    simpa only [Finsupp.sub_apply, Finsupp.single_apply, mul_sub, mul_ite,
      mul_one, mul_zero] using h
  · intro heq
    ext tab
    rcases tab with ⟨t, a, b⟩
    have h := congrArg (fun f : (ι × ι) →₀ ℤ =>
      (if side t then (-1 : ℤ) else 1) * f (a, b)) (heq t)
    simpa only [Finsupp.sub_apply, edgeListShift_apply_profile side p hp,
      edgeListShift_apply_profile side q hq, edgeListShift_apply_profile side r hr,
      edgeListShift_apply_profile side s hs, Finsupp.single_apply,
      mul_sub, mul_ite, mul_one, mul_zero] using h

end Problem335

end

end OAI
