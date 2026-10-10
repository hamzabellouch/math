import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.Profile

namespace OAI

namespace MatchingFPRAS.Subdivision
open Finset

theorem last_hole_terminal {m : ℕ} (hm : Even m) {U : Finset (Fin m)}
    {b : Selection m} (hb : Valid U b) (j : Fin m) (hj : j ∈ U)
    (hlast : ∀ i ∈ U, i ≤ j) :
    b (Fin.last m) = true ↔ j.val % 2 = 0 := by
  have hv := valid_interval hb (j.val+1) (m-(j.val+1)) (by omega) (by
    intro i hi hij him
    have hh := hlast i him
    have : i.val ≤ j.val := hh
    omega)
  have hz : b j.succ = false := by
    have h := hb j
    simp only [hj,↓reduceIte] at h
    exact h.2
  have he : b (Fin.last m) = alternating false (m-(j.val+1)) := by
    have e1 : (⟨j.val+1+(m-(j.val+1)),by omega⟩ : Fin (m+1)) = Fin.last m := by
      apply Fin.ext; dsimp; omega
    have e2 : (⟨j.val+1,by omega⟩ : Fin (m+1)) = j.succ := rfl
    rw [e1,e2,hz] at hv
    exact hv
  have hme := Nat.even_iff.mp hm
  by_cases h : j.val%2=0
  · have hk : (m-(j.val+1))%2=1 := by omega
    simp [he,alternating,h,hk]
  · have hk : (m-(j.val+1))%2=0 := by omega
    simp [he,alternating,h,hk]

theorem successive_holes_parity {m : ℕ} {U : Finset (Fin m)} {b : Selection m}
    (hb : Valid U b) (i j : Fin m) (hi : i ∈ U) (hj : j ∈ U) (hij : i < j)
    (hbetween : ∀ k ∈ U, ¬ (i < k ∧ k < j)) :
    i.val % 2 ≠ j.val % 2 := by
  have hv := valid_interval hb (i.val+1) (j.val-(i.val+1)) (by omega) (by
    intro k hk hkj hku
    apply hbetween k hku
    constructor <;> omega)
  have hi0 : b i.succ = false := by
    have h := hb i
    simp only [hi,↓reduceIte] at h
    exact h.2
  have hj0 : b j.castSucc = false := by
    have h := hb j
    simp only [hj,↓reduceIte] at h
    exact h.1
  have he : false = alternating false (j.val-(i.val+1)) := by
    convert hv using 1
    · rw [show (⟨i.val+1+(j.val-(i.val+1)),by omega⟩ : Fin (m+1)) = j.castSucc
        by apply Fin.ext; dsimp; omega,hj0]
    · rw [show (⟨i.val+1,by omega⟩ : Fin (m+1)) = i.succ by rfl,hi0]
  have heven : (j.val-(i.val+1))%2=0 := by
    by_contra h
    simp [alternating,h] at he
  omega

theorem sorted_holes_alternate {m : ℕ} {U : Finset (Fin m)} {b : Selection m}
    (hb : Valid U b) :
    (U.sort (· ≤ ·)).IsChain (fun i j => i.val%2 ≠ j.val%2) := by
  let xs := U.sort (· ≤ ·)
  have hsort : xs.Pairwise (· < ·) := (Finset.sortedLT_sort U).pairwise
  rw [List.isChain_iff_getElem]
  intro r hr
  have hri : r < xs.length := by exact Nat.lt_trans (Nat.lt_succ_self r) hr
  have him : xs[r] ∈ U := (Finset.mem_sort _).mp (List.getElem_mem hri)
  have hjm : xs[r+1] ∈ U := (Finset.mem_sort _).mp (List.getElem_mem hr)
  have hij : xs[r] < xs[r+1] :=
    (List.pairwise_iff_getElem.mp hsort) r (r+1) hri hr (by omega)
  apply successive_holes_parity hb (xs[r]) (xs[r+1]) him hjm hij
  intro k hk hbet
  have hkm : k ∈ xs := (Finset.mem_sort _).mpr hk
  obtain ⟨s,hs,hks⟩ := List.mem_iff_getElem.mp hkm
  by_cases hsr : s ≤ r
  · by_cases heq : s=r
    · subst s; rw [hks] at hbet; exact lt_irrefl _ hbet.1
    · have hlt := (List.pairwise_iff_getElem.mp hsort) s r hs hri (by omega)
      rw [hks] at hlt
      exact (not_lt_of_ge hlt.le) hbet.1
  · by_cases heq : s=r+1
    · subst s; rw [hks] at hbet; exact lt_irrefl _ hbet.2
    · have hlt := (List.pairwise_iff_getElem.mp hsort) (r+1) s hr hs (by omega)
      rw [hks] at hlt
      exact (not_lt_of_ge hlt.le) hbet.2

theorem neutral_blocks {m : ℕ} (xs : List (Fin m))
    (ha : xs.IsChain (fun i j => i.val%2 ≠ j.val%2))
    (hh : ∀ i ∈ xs.head?, i.val%2=0) :
    ∃ (pairs : List (Fin m × Fin m)) (right : Option (Fin m)),
      xs = pairs.flatMap (fun q => [q.1,q.2]) ++ right.toList ∧
      (∀ q ∈ pairs, q.1.val%2=0 ∧ q.2.val%2=1) ∧
      (∀ j ∈ right, j.val%2=0) := by
  induction xs using List.twoStepInduction with
  | nil => exact ⟨[],none,by simp⟩
  | singleton j => exact ⟨[],some j,by simpa using hh⟩
  | cons_cons j k xs ih ih' =>
    have hj : j.val%2=0 := hh j (by simp)
    have hne := (List.isChain_cons_cons.mp ha).1
    have hk : k.val%2=1 := by omega
    have htail := (List.isChain_cons_cons.mp ha).2
    have hh' : ∀ i ∈ xs.head?, i.val%2=0 := by
      intro i hi
      have hki : k.val%2 ≠ i.val%2 := (List.isChain_cons.mp htail).1 i hi
      omega
    obtain ⟨pairs,right,he,hp,hr⟩ := ih htail.tail hh'
    refine ⟨(j,k)::pairs,right,?_,?_,hr⟩
    · simp [he]
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨hj,hk⟩
      · exact hp q hq

structure HoleBlocks (m : ℕ) where
  left : Option (Fin m)
  neutral : List (Fin m × Fin m)
  right : Option (Fin m)

def HoleBlocks.flatten {m : ℕ} (d : HoleBlocks m) : List (Fin m) :=
  d.left.toList ++ d.neutral.flatMap (fun q => [q.1,q.2]) ++ d.right.toList

def HoleBlocks.Parity {m : ℕ} (d : HoleBlocks m) : Prop :=
  (∀ j ∈ d.left, j.val%2=1) ∧
  (∀ q ∈ d.neutral, q.1.val%2=0 ∧ q.2.val%2=1) ∧
  (∀ j ∈ d.right, j.val%2=0)

theorem hole_blocks_exist {m : ℕ} {U : Finset (Fin m)} {b : Selection m}
    (hb : Valid U b) :
    ∃ d : HoleBlocks m, d.flatten = U.sort (· ≤ ·) ∧ d.Parity := by
  have ha := sorted_holes_alternate hb
  generalize he : U.sort (· ≤ ·)=xs at ha ⊢
  cases xs with
  | nil => exact ⟨⟨none,[],none⟩,rfl,by simp [HoleBlocks.Parity]⟩
  | cons j xs =>
    by_cases hj : j.val%2=0
    · obtain ⟨pairs,right,heq,hp,hr⟩ := neutral_blocks (j::xs) ha (by simpa using hj)
      exact ⟨⟨none,pairs,right⟩,by simpa [HoleBlocks.flatten] using heq.symm,
        by simpa [HoleBlocks.Parity] using And.intro hp hr⟩
    · have hj1 : j.val%2=1 := by omega
      have hh : ∀ i ∈ xs.head?, i.val%2=0 := by
        intro i hi
        have hji := (List.isChain_cons.mp ha).1 i hi
        omega
      obtain ⟨pairs,right,heq,hp,hr⟩ := neutral_blocks xs ha.tail hh
      refine ⟨⟨some j,pairs,right⟩,?_,?_⟩
      · simp [HoleBlocks.flatten,heq]
      · simpa [HoleBlocks.Parity] using And.intro hj1 (And.intro hp hr)

theorem selectedWeight_hole_product {m : ℕ} (hm : Even m)
    (U : Finset (Fin m)) (b : Selection m) (hb : Valid U b) (z : Fin (m+2) → ℝ) :
    selectedWeight (fun i => z i.castSucc * z i.succ) b *
        (∏ j ∈ U, z j.succ.castSucc) =
      selectedWeight (fun i => z i.castSucc * z i.succ)
        (fun i => alternating false i.val) *
      (if b 0 then z 0 else 1) * (if b (Fin.last m) then z (Fin.last (m+1)) else 1) := by
  classical
  rw [selectedWeight_vertex_factor U b hb z,
    selectedWeight_vertex_factor ∅ _ (alternating_valid m false) z]
  have hbool : alternating false (Fin.last m).val = false := by
    simp [alternating,Nat.even_iff.mp hm]
  simp only [Fin.val_zero,alternating_zero,Bool.false_eq_true,↓reduceIte,
    hbool,Finset.notMem_empty,one_mul]
  have hp : (∏ i : Fin m, if i ∈ U then 1 else z i.succ.castSucc) *
      (∏ j ∈ U, z j.succ.castSucc) = ∏ i : Fin m, z i.succ.castSucc := by
    have hU : (∏ j ∈ U, z j.succ.castSucc) =
        ∏ i : Fin m, if i ∈ U then z i.succ.castSucc else 1 := by
      rw [← Finset.prod_filter]
      simp
    rw [hU,← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases him : i ∈ U <;> simp [him]
  calc
    _ = (if b 0 then z 0 else 1) * (if b (Fin.last m) then z (Fin.last (m+1)) else 1) *
      ((∏ i : Fin m, if i ∈ U then 1 else z i.succ.castSucc) *
        (∏ j ∈ U, z j.succ.castSucc)) := by ring
    _ = _ := by rw [hp]; ring

def adjacentProducts : List ℝ → List ℝ
  | a::b::xs => a*b :: adjacentProducts (b::xs)
  | _ => []

@[simp] lemma adjacentProducts_length (xs : List ℝ) :
    (adjacentProducts xs).length = xs.length-1 := by
  induction xs using List.twoStepInduction with
  | nil => rfl
  | singleton => rfl
  | cons_cons a b xs ih ih' => simp [adjacentProducts,ih']

lemma adjacentProducts_zip (xs : List ℝ) :
    adjacentProducts xs = List.zipWith (· * ·) xs xs.tail := by
  induction xs using List.twoStepInduction with
  | nil => rfl
  | singleton => rfl
  | cons_cons a b xs ih ih' => simpa [adjacentProducts] using congrArg (a*b :: ·) (ih' b)

noncomputable def armPotentials (c : ℝ) (xs : List ℝ) : List ℝ :=
  xs.flatMap (fun x => [x/c,c])

@[simp] lemma armPotentials_length (c : ℝ) (xs : List ℝ) :
    (armPotentials c xs).length = 2*xs.length := by
  induction xs with
  | nil => simp [armPotentials]
  | cons x xs ih => simp [armPotentials] at ih ⊢; omega

lemma adjacentProducts_arm (c : ℝ) (hc : c ≠ 0) (xs ys : List ℝ) :
    adjacentProducts (c :: (armPotentials c xs ++ ys)) =
      duplicate xs ++ adjacentProducts (c::ys) := by
  induction xs with
  | nil => simp [armPotentials]
  | cons x xs ih =>
    have hmul : c*(x/c)=x := by field_simp
    have hmul' : (x/c)*c=x := by field_simp
    simpa [armPotentials,adjacentProducts,hmul,hmul',duplicate] using
      congrArg (x::x::·) ih

noncomputable def pairedPotentials (left right : List ℝ) (lam : ℝ) : List ℝ :=
  1 :: (armPotentials 1 left ++ lam :: armPotentials lam right)

@[simp] lemma pairedPotentials_length (left right : List ℝ) (lam : ℝ) :
    (pairedPotentials left right lam).length = 2*left.length+2*right.length+2 := by
  simp [pairedPotentials]; omega

theorem pairedPotentials_activities (left right : List ℝ) (lam : ℝ) (hlam : lam ≠ 0) :
    adjacentProducts (pairedPotentials left right lam) =
      duplicate left ++ [lam] ++ duplicate right := by
  unfold pairedPotentials
  rw [adjacentProducts_arm 1 one_ne_zero]
  simp only [adjacentProducts,one_mul]
  have hr := adjacentProducts_arm lam hlam right []
  simp only [List.append_nil,adjacentProducts,List.append_nil] at hr
  rw [hr]
  simp

noncomputable def profilePotentials (p : ℕ) (B Hu Hv lam : ℝ) : List ℝ :=
  pairedPotentials (List.ofFn fun r : Fin p => max B (Hu/2^r.val))
    ((List.ofFn fun r : Fin p => max B (Hv/2^r.val)).reverse) lam

@[simp] lemma profilePotentials_length (p : ℕ) (B Hu Hv lam : ℝ) :
    (profilePotentials p B Hu Hv lam).length = 4*p+2 := by
  simp [profilePotentials]; omega

noncomputable def profilePotential (p : ℕ) (B Hu Hv lam : ℝ) (i : Fin (4*p+2)) : ℝ :=
  (profilePotentials p B Hu Hv lam).get
    (i.cast (profilePotentials_length p B Hu Hv lam).symm)

theorem profileActivity_vertex_factor (p : ℕ) (B Hu Hv lam : ℝ) (hlam : lam ≠ 0)
    (i : Fin (4*p+1)) :
    profileActivity p B Hu Hv lam i =
      profilePotential p B Hu Hv lam i.castSucc * profilePotential p B Hu Hv lam i.succ := by
  have he : adjacentProducts (profilePotentials p B Hu Hv lam) = profile p B Hu Hv lam :=
    pairedPotentials_activities _ _ _ hlam
  have hi : i.val < (adjacentProducts (profilePotentials p B Hu Hv lam)).length := by
    simp only [adjacentProducts_length,profilePotentials_length]
    omega
  have hget := congrArg (fun xs : List ℝ => xs[i.val]?) he
  have hi' : i.val < (profile p B Hu Hv lam).length := by simp; omega
  rw [List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hi',Option.some.injEq] at hget
  simp only [adjacentProducts_zip,List.getElem_zipWith] at hget
  simpa only [profileActivity,profilePotential,List.get_eq_getElem,Fin.val_cast,
    Fin.val_castSucc,Fin.val_succ,List.getElem_tail] using hget.symm

lemma duplicate_getElem (xs : List ℝ) (i : ℕ) (hi : i < (duplicate xs).length) :
    (duplicate xs)[i] = xs[i/2]'(by simp only [duplicate_length] at hi; omega) := by
  induction xs generalizing i with
  | nil => simp [duplicate] at hi
  | cons x xs ih =>
    cases i with
    | zero => simp [duplicate]
    | succ i =>
      cases i with
      | zero => simp [duplicate]
      | succ i =>
        have hi' : i < (duplicate xs).length := by simp only [duplicate_cons,List.length_cons] at hi; omega
        have hh := ih i hi'
        simpa only [duplicate_cons,List.getElem_cons_succ,Nat.succ_eq_add_one,
          show (i+1+1)/2=i/2+1 by omega] using hh

lemma profile_left (p : ℕ) (B Hu Hv lam : ℝ) (i : Fin (4*p+1))
    (hi : i.val < 2*p) :
    profileActivity p B Hu Hv lam i = max B (Hu/2^(i.val/2)) := by
  unfold profileActivity profile
  simp only [List.get_eq_getElem,Fin.cast]
  have hl : i.val < (duplicate (List.ofFn fun r : Fin p => max B (Hu/2^r.val))).length := by
    simpa using hi
  rw [List.getElem_append_left (by simpa only [List.length_append,List.length_singleton] using
    (show i.val < (duplicate (List.ofFn fun r : Fin p => max B (Hu/2^r.val))).length+1 by omega))]
  rw [List.getElem_append_left hl,duplicate_getElem]
  simp

@[simp] lemma profile_center (p : ℕ) (B Hu Hv lam : ℝ) :
    profileActivity p B Hu Hv lam ⟨2*p,by omega⟩ = lam := by
  unfold profileActivity profile
  simp only [List.get_eq_getElem,Fin.cast]
  rw [List.getElem_append_left (by simp)]
  rw [List.getElem_append_right (by simp)]
  simp

lemma profile_right (p : ℕ) (B Hu Hv lam : ℝ) (i : Fin (4*p+1))
    (hi : 2*p < i.val) :
    profileActivity p B Hu Hv lam i = max B (Hv/2^((4*p-i.val)/2)) := by
  unfold profileActivity profile
  simp only [List.get_eq_getElem,Fin.cast]
  rw [List.getElem_append_right (by simp; omega),duplicate_getElem]
  simp only [duplicate_length,List.length_ofFn,List.length_append,List.length_singleton,
    List.getElem_reverse,List.getElem_ofFn]
  congr 3
  omega

theorem profile_lower (p : ℕ) (B Hu Hv lam : ℝ) (hlam : lam ≤ B)
    (i : Fin (4*p+1)) : lam ≤ profileActivity p B Hu Hv lam i := by
  rcases lt_trichotomy i.val (2*p) with hi | hi | hi
  · rw [profile_left _ _ _ _ _ _ hi]; exact hlam.trans (le_max_left _ _)
  · have he : i=⟨2*p,by omega⟩ := Fin.ext hi
    rw [he]; simp
  · rw [profile_right _ _ _ _ _ _ hi]; exact hlam.trans (le_max_left _ _)

lemma profile_noncentral_lower (p : ℕ) (B Hu Hv lam : ℝ)
    (i : Fin (4*p+1)) (hi : i.val ≠ 2*p) : B ≤ profileActivity p B Hu Hv lam i := by
  rcases lt_or_gt_of_ne hi with hi | hi
  · rw [profile_left _ _ _ _ _ _ hi]; exact le_max_left _ _
  · rw [profile_right _ _ _ _ _ _ hi]; exact le_max_left _ _

lemma legValue_antitone (B H : ℝ) (hH : 0 ≤ H) :
    Antitone (fun r : ℕ => max B (H/(2:ℝ)^r)) := by
  intro i j hij
  apply max_le_max_left
  exact div_le_div_of_nonneg_left hH (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hij)

lemma legValue_step (B H : ℝ) (hB : 0 ≤ B) (r : ℕ) :
    max B (H/(2:ℝ)^r) ≤ 2*max B (H/(2:ℝ)^(r+1)) := by
  apply max_le
  · exact (le_max_left B (H/2^(r+1))).trans
      (by have hh := (le_max_left B (H/2^(r+1))); nlinarith)
  · have he : H/(2:ℝ)^r = 2*(H/(2:ℝ)^(r+1)) := by rw [pow_succ]; field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)

lemma profile_innermost (K : ℕ) (B H : ℝ) (hB : 1 ≤ B) (hH : H ≤ 4^K) :
    max B (H/(2:ℝ)^(2*K+1)) = B := by
  apply max_eq_left
  have hp : (2:ℝ)^(2*K+1) = 2*4^K := by
    rw [pow_succ,pow_mul]; norm_num; ring
  rw [hp]
  apply (div_le_iff₀ (by positivity)).mpr
  have h4 : (0:ℝ) ≤ 4^K := by positivity
  nlinarith

noncomputable def vertexPotential (p : ℕ) (B Hu Hv lam : ℝ) (k : ℕ) : ℝ :=
  if k ≤ 2*p then
    if Even k then 1 else max B (Hu/2^(k/2))
  else if Even k then max B (Hv/2^((4*p+1-k)/2))/lam else lam

@[simp] lemma vertexPotential_zero (p : ℕ) (B Hu Hv lam : ℝ) :
    vertexPotential p B Hu Hv lam 0 = 1 := by simp [vertexPotential]

@[simp] lemma vertexPotential_last (p : ℕ) (B Hu Hv lam : ℝ) :
    vertexPotential p B Hu Hv lam (4*p+1) = lam := by
  have hn : ¬ Even (4*p+1) := by simp [Nat.even_iff]; omega
  simp [vertexPotential,show ¬ 4*p+1 ≤ 2*p by omega,hn]

theorem profile_vertexPotential (p : ℕ) (B Hu Hv lam : ℝ) (hlam : lam ≠ 0)
    (i : Fin (4*p+1)) : profileActivity p B Hu Hv lam i =
      vertexPotential p B Hu Hv lam i.val * vertexPotential p B Hu Hv lam (i.val+1) := by
  have hi := i.isLt
  rcases lt_trichotomy i.val (2*p) with hleft | hcenter | hright
  · rw [profile_left _ _ _ _ _ _ hleft]
    have hi0 : i.val ≤ 2*p := by omega
    have hi1 : i.val+1 ≤ 2*p := by omega
    simp only [vertexPotential,ite_eq_left hi0,ite_eq_left hi1]
    by_cases he : Even i.val
    · have hn : ¬ Even (i.val+1) := by simpa [Nat.even_add_one] using he
      have hdiv : (i.val+1)/2=i.val/2 := by have := Nat.even_iff.mp he; omega
      simp [he,hn,hdiv]
    · have hn : Even (i.val+1) := by simpa [Nat.even_add_one] using he
      simp [he,hn]
  · have hic : i=⟨2*p,by omega⟩ := Fin.ext hcenter
    rw [hic]
    simp [vertexPotential,show ¬ 2*p+1 ≤ 2*p by omega]
  · rw [profile_right _ _ _ _ _ _ hright]
    have hi0 : ¬ i.val ≤ 2*p := by omega
    have hi1 : ¬ i.val+1 ≤ 2*p := by omega
    simp only [vertexPotential,ite_eq_right hi0,ite_eq_right hi1]
    by_cases he : Even i.val
    · have hn : ¬ Even (i.val+1) := by simpa [Nat.even_add_one] using he
      have hdiv : (4*p+1-i.val)/2=(4*p-i.val)/2 := by have := Nat.even_iff.mp he; omega
      simp [he,hn,hdiv,hlam]
    · have hn : Even (i.val+1) := by simpa [Nat.even_add_one] using he
      have hdiv : 4*p+1-(i.val+1)=4*p-i.val := by omega
      simp [he,hn,hdiv,hlam,mul_div_cancel₀]

noncomputable def internalStrength (p : ℕ) (B Hu Hv : ℝ) (j : Fin (4*p)) : ℝ :=
  if j.val < 2*p then max B (Hu/2^(j.val/2))
    else max B (Hv/2^((4*p-(j.val+1))/2))

lemma le_internalStrength (p : ℕ) (B Hu Hv : ℝ) (j : Fin (4*p)) :
    B ≤ internalStrength p B Hu Hv j := by
  unfold internalStrength; split_ifs <;> exact le_max_left _ _

theorem internalStrength_incident (p : ℕ) (B Hu Hv lam : ℝ)
    (hHu : 0 ≤ Hu) (hHv : 0 ≤ Hv) (hlam : lam ≤ B) (j : Fin (4*p)) :
    profileActivity p B Hu Hv lam j.castSucc ≤ internalStrength p B Hu Hv j ∧
    profileActivity p B Hu Hv lam j.succ ≤ internalStrength p B Hu Hv j := by
  by_cases hj : j.val < 2*p
  · have hs : internalStrength p B Hu Hv j=max B (Hu/2^(j.val/2)) := by simp [internalStrength,hj]
    rw [hs]
    constructor
    · rw [profile_left _ _ _ _ _ _ hj]
      exact le_rfl
    · by_cases hj' : j.val+1 < 2*p
      · rw [profile_left _ _ _ _ _ _ hj']
        exact legValue_antitone B Hu hHu (by simp only [Fin.val_succ]; omega)
      · have hc : j.succ=⟨2*p,by omega⟩ := Fin.ext (by simp only [Fin.val_succ]; omega)
        rw [hc,profile_center]
        exact hlam.trans (le_max_left _ _)
  · have hs : internalStrength p B Hu Hv j=max B (Hv/2^((4*p-(j.val+1))/2)) := by
      simp [internalStrength,hj]
    rw [hs]
    constructor
    · by_cases hj' : 2*p < j.val
      · rw [profile_right _ _ _ _ _ _ hj']
        exact legValue_antitone B Hv hHv (by simp only [Fin.val_castSucc]; omega)
      · have hc : j.castSucc=⟨2*p,by omega⟩ := Fin.ext (by simp only [Fin.val_castSucc]; omega)
        rw [hc,profile_center]
        exact hlam.trans (le_max_left _ _)
    · rw [profile_right _ _ _ _ _ _ (by simp only [Fin.val_succ]; omega)]
      exact le_rfl

theorem internalStrength_left_leg (p : ℕ) (B Hu Hv lam : ℝ) (hHu : 0 ≤ Hu)
    (j : Fin (4*p)) (hj : j.val < 2*p) (i : Fin (4*p+1)) (hi : i.val ≤ j.val) :
    internalStrength p B Hu Hv j ≤ profileActivity p B Hu Hv lam i := by
  rw [profile_left _ _ _ _ _ _ (by omega)]
  simp only [internalStrength,ite_eq_left hj]
  exact legValue_antitone B Hu hHu (by omega)

theorem internalStrength_right_leg (p : ℕ) (B Hu Hv lam : ℝ) (hHv : 0 ≤ Hv)
    (j : Fin (4*p)) (hj : ¬ j.val < 2*p) (i : Fin (4*p+1)) (hi : j.val+1 ≤ i.val) :
    internalStrength p B Hu Hv j ≤ profileActivity p B Hu Hv lam i := by
  rw [profile_right _ _ _ _ _ _ (by omega)]
  simp only [internalStrength,ite_eq_right hj]
  exact legValue_antitone B Hv hHv (by omega)

lemma internalStrength_left_antitone (p : ℕ) (B Hu Hv : ℝ) (hHu : 0 ≤ Hu)
    (j k : Fin (4*p)) (hjk : j.val ≤ k.val) (hk : k.val < 2*p) :
    internalStrength p B Hu Hv k ≤ internalStrength p B Hu Hv j := by
  have hj : j.val < 2*p := by omega
  simp only [internalStrength,ite_eq_left hj,ite_eq_left hk]
  exact legValue_antitone B Hu hHu (by omega)

lemma internalStrength_right_monotone (p : ℕ) (B Hu Hv : ℝ) (hHv : 0 ≤ Hv)
    (j k : Fin (4*p)) (hjk : j.val ≤ k.val) (hj : ¬ j.val < 2*p) :
    internalStrength p B Hu Hv j ≤ internalStrength p B Hu Hv k := by
  have hk : ¬ k.val < 2*p := by omega
  simp only [internalStrength,ite_eq_right hj,ite_eq_right hk]
  exact legValue_antitone B Hv hHv (by omega)

lemma vertexPotential_pos (p : ℕ) (B Hu Hv lam : ℝ) (hB : 0 < B) (hlam : 0 < lam)
    (i : ℕ) : 0 < vertexPotential p B Hu Hv lam i := by
  unfold vertexPotential
  split_ifs
  · norm_num
  · exact hB.trans_le (le_max_left _ _)
  · exact div_pos (hB.trans_le (le_max_left _ _)) hlam
  · exact hlam

lemma consumed_left_potential (p : ℕ) (B Hu Hv lam : ℝ) (j : Fin (4*p))
    (hj : j.val%2=1) :
    vertexPotential p B Hu Hv lam (j.val+1) =
      if j.val < 2*p then 1 else internalStrength p B Hu Hv j/lam := by
  have he : Even (j.val+1) := Nat.even_iff.mpr (by omega)
  have hi : j.val+1 ≤ 2*p ↔ j.val < 2*p := by omega
  simp only [vertexPotential,he,↓reduceIte,hi]
  by_cases hs : j.val < 2*p
  · simp [hs]
  · have hd : (4*p-j.val)/2=(4*p-(j.val+1))/2 := by
      have := j.isLt; omega
    simp [hs,internalStrength,hd]

lemma consumed_right_potential (p : ℕ) (B Hu Hv lam : ℝ) (j : Fin (4*p))
    (hj : j.val%2=0) :
    vertexPotential p B Hu Hv lam (j.val+1) =
      if j.val < 2*p then internalStrength p B Hu Hv j else lam := by
  have he : ¬ Even (j.val+1) := by rw [Nat.even_iff]; omega
  have hi : j.val+1 ≤ 2*p ↔ j.val < 2*p := by omega
  have hd : (j.val+1)/2=j.val/2 := by omega
  simp only [vertexPotential,he,↓reduceIte,hi,hd]
  by_cases hs : j.val < 2*p
  · simp [hs,internalStrength]
  · simp [hs]

end MatchingFPRAS.Subdivision

end OAI
