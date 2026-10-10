import Mathlib

namespace OAI

section
open scoped BigOperators


/-! Occurrence-preserving bounds for the canonical p−1 auxiliary tree in
Section5. Equal labels under different parents remain separate list entries. -/
namespace ExactQuantumFactoring.AuxiliaryTree
open scoped BigOperators

def children (M : ℕ) : List ℕ :=
  ((M.primeFactors.filter (fun p => 2<p)).sort (·≤·)).map (·-1)

lemma mem_children {M d : ℕ} : d ∈ children M ↔
    ∃ p, p.Prime ∧ p ∣ M ∧ M≠0 ∧ 2<p ∧ d=p-1 := by
  simp only [children,List.mem_map,Finset.mem_sort,Finset.mem_filter,Nat.mem_primeFactors]
  constructor
  · rintro ⟨p,⟨⟨hp,hpm,hM⟩,hp2⟩,hd⟩
    exact ⟨p,hp,hpm,hM,hp2,hd.symm⟩
  · rintro ⟨p,hp,hpm,hM,hp2,rfl⟩
    exact ⟨p,⟨⟨hp,hpm,hM⟩,hp2⟩,rfl⟩

lemma child_bounds {M d : ℕ} (hd : d ∈ children M) : 2≤d ∧ d<M := by
  obtain ⟨p,hp,hpm,hM,hp2,rfl⟩ := mem_children.mp hd
  have hpM := Nat.le_of_dvd (Nat.pos_of_ne_zero hM) hpm
  omega

lemma child_even {M d : ℕ} (hd : d ∈ children M) : Even d := by
  obtain ⟨p,hp,_,_,hp2,rfl⟩ := mem_children.mp hd
  have ho := hp.odd_of_ne_two (by omega)
  exact (Nat.even_sub (by omega : 1≤p)).mpr (by simpa using ho)

lemma grandchild_half {M d e : ℕ} (hd : d ∈ children M) (he : e ∈ children d) :
    2*e<M := by
  obtain ⟨p,hp,hpd,hd0,hp2,rfl⟩ := mem_children.mp he
  have hopen := hp.odd_of_ne_two (by omega)
  have hcop : Nat.Coprime 2 p := (Nat.coprime_two_left).mpr hopen
  have hdiv := hcop.mul_dvd_of_dvd_of_dvd (even_iff_two_dvd.mp (child_even hd)) hpd
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hdiv
  have hdm := (child_bounds hd).2
  omega

lemma children_prod_le {M : ℕ} (hM : 0<M) : (children M).prod≤M := by
  unfold children
  rw [← List.prod_toFinset _ (Finset.sort_nodup _ _),Finset.sort_toFinset]
  calc
    (∏ p ∈ M.primeFactors.filter (fun p => 2<p), (p-1)) ≤
      ∏ p ∈ M.primeFactors.filter (fun p => 2<p), p :=
      Finset.prod_le_prod (fun _ _ => Nat.sub_le _ _)
    _ ≤ ∏ p ∈ M.primeFactors, p := Finset.prod_le_prod_of_subset_of_one_le
      (Finset.filter_subset _ _)
      (fun p hp _ => (Nat.prime_of_mem_primeFactors hp).one_lt.le)
    _ ≤ M := Nat.le_of_dvd hM (Nat.prod_primeFactors_dvd M)

/-- A level is a list, not a set: multiplicities of occurrences are retained. -/
def level (M : ℕ) : ℕ → List ℕ
  | 0 => [M]
  | k+1 => (children M).flatMap (fun d => level d k)

lemma level_bounds {M d k : ℕ} (hM : 2≤M) (hd : d ∈ level M k) : 2≤d ∧ d≤M := by
  induction k generalizing M with
  | zero =>
    have he : d=M := by simpa [level] using hd
    subst d
    exact ⟨hM,le_rfl⟩
  | succ k ih =>
    obtain ⟨e,he,hd⟩ := List.mem_flatMap.mp hd
    have hb := child_bounds he
    have hh := ih hb.1 hd
    exact ⟨hh.1,hh.2.trans hb.2.le⟩

lemma level_two_step {M d k : ℕ} (hd : d ∈ level M (2*k)) : 2^k*d≤M := by
  induction k generalizing M with
  | zero =>
    have he : d=M := by simpa [level] using hd
    simpa using he.le
  | succ k ih =>
    have heq : 2*(k+1)=2*k+1+1 := by omega
    rw [heq,level] at hd
    obtain ⟨e,he,hd⟩ := List.mem_flatMap.mp hd
    rw [level] at hd
    obtain ⟨f,hf,hd⟩ := List.mem_flatMap.mp hd
    have hx := ih hd
    have hh := grandchild_half he hf
    rw [pow_succ]
    nlinarith

lemma level_empty {M n : ℕ} (hM : 2≤M) (hbound : M<2^n) : level M (2*n)=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro d hd
  have hx := level_two_step hd
  have hy := (level_bounds hM hd).1
  have hp : 0<2^n := by positivity
  nlinarith

lemma prod_flatMap (f : ℕ→List ℕ) (xs : List ℕ) :
    (xs.flatMap f).prod=(xs.map (fun x => (f x).prod)).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

lemma level_prod_le {M k : ℕ} (hM : 2≤M) : (level M k).prod≤M := by
  induction k generalizing M with
  | zero => simp [level]
  | succ k ih =>
    rw [level,prod_flatMap]
    calc
      ((children M).map (fun d => (level d k).prod)).prod ≤
        ((children M).map id).prod := List.prod_map_le_prod_map₀ _ _
          (fun _ _ => Nat.zero_le _) (fun d hd => ih (child_bounds hd).1)
      _ = (children M).prod := by simp
      _ ≤ M := children_prod_le (by omega)

lemma pow_length_le_prod (xs : List ℕ) (hxs : ∀ x ∈ xs, 2≤x) : 2^xs.length≤xs.prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have hi := ih (fun y hy => hxs y (by simp [hy]))
    simp only [List.length_cons,List.prod_cons,pow_succ]
    exact (Nat.mul_le_mul hi hx).trans_eq (Nat.mul_comm _ _)

lemma level_length_lt {M n k : ℕ} (hM : 2≤M) (hbound : M<2^n) :
    (level M k).length<n := by
  apply (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp
  exact (pow_length_le_prod _ (fun _ hd => (level_bounds hM hd).1)).trans_lt
    ((level_prod_le hM).trans_lt hbound)

def splitWeight (M : ℕ) : ℕ := M.primeFactorsList.length

lemma splitWeight_bound {M n : ℕ} (hM : 0<M) (hbound : M<2^n) : splitWeight M<n := by
  apply (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp
  have hh := pow_length_le_prod M.primeFactorsList
    (fun p hp => (Nat.prime_of_mem_primeFactorsList hp).two_le)
  rw [Nat.prod_primeFactorsList hM.ne'] at hh
  exact hh.trans_lt hbound

lemma level_weight_lt {M n k : ℕ} (hM : 2≤M) (hbound : M<2^n) :
    ((level M k).map splitWeight).sum<n := by
  let ps := (level M k).flatMap Nat.primeFactorsList
  have he : ps.prod=(level M k).prod := by
    rw [prod_flatMap]
    congr 1
    conv_rhs => rw [← List.map_id (level M k)]
    apply List.map_congr_left
    intro d hd
    exact Nat.prod_primeFactorsList (by have := (level_bounds hM hd).1; omega)
  have hlen : ps.length=((level M k).map splitWeight).sum := by
    change (List.flatMap Nat.primeFactorsList (level M k)).length = _
    rw [List.length_flatMap]
    rfl
  have hp : 2^ps.length≤ps.prod := pow_length_le_prod ps (by
    intro p hp
    obtain ⟨d,_,hp⟩ := List.mem_flatMap.mp hp
    exact (Nat.prime_of_mem_primeFactorsList hp).two_le)
  rw [he,hlen] at hp
  exact (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp
    (hp.trans_lt ((level_prod_le hM).trans_lt hbound))

/-- The source's whole-tree task cap, expressed without real logarithms. -/
def taskBound (M n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2*n+2), ((level M k).map splitWeight).sum

lemma taskBound_le {M n : ℕ} (hM : 2≤M) (hbound : M<2^n) :
    taskBound M n ≤ (2*n+2)*n := by
  unfold taskBound
  calc
    _ ≤ ∑ _k ∈ Finset.range (2*n+2), n := Finset.sum_le_sum
      (fun k _ => (level_weight_lt (k:=k) hM hbound).le)
    _ = _ := by simp

lemma transitions_bound {n : ℕ} (hn : 2≤n) : (2*n+2)*n*(n^5+1)≤6*n^7 := by
  have hnpos : 0<n := by omega
  have hp : 1≤n^5 := Nat.one_le_pow _ _ hnpos
  have h₁ : 2*n+2≤3*n := by omega
  have h₂ : n^5+1≤2*n^5 := by omega
  calc
    _ ≤ (3*n)*n*(2*n^5) := Nat.mul_le_mul (Nat.mul_le_mul_right n h₁) h₂
    _ = 6*n^7 := by ring

lemma transitions_lt_slots {n : ℕ} (hn : 128≤n) : (2*n+2)*n*(n^5+1)<n^10 := by
  have hp : 6<n^3 := by
    have hh := Nat.pow_le_pow_left hn 3
    norm_num at hh
    omega
  have hnpos : 0<n^7 := pow_pos (by omega) _
  calc
    _ ≤ 6*n^7 := transitions_bound (by omega)
    _ < n^3*n^7 := Nat.mul_lt_mul_of_pos_right hp hnpos
    _ = n^10 := by ring

end ExactQuantumFactoring.AuxiliaryTree


end

end OAI
