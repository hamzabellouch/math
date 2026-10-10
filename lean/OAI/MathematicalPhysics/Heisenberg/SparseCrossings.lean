import OAI.MathematicalPhysics.Heisenberg.SpatialClocks

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical BigOperators

namespace Heisenberg.SparseWitness

section
variable {V : Type*} [PseudoMetricSpace V]

lemma first_crossing (p : ℕ → V) (m : ℕ) (hstep : ∀ i < m, dist (p i) (p (i+1)) ≤ 8)
    (r : ℝ) (hr : 0 < r) (hend : r ≤ dist (p 0) (p m)) :
    ∃ k ≤ m, r ≤ dist (p 0) (p k) ∧ dist (p 0) (p k) ≤ r+8 := by
  have hex : ∃ k : ℕ, k ≤ m ∧ r ≤ dist (p 0) (p k) := ⟨m,le_rfl,hend⟩
  let k := Nat.find hex
  have hk := Nat.find_spec hex
  change k ≤ m ∧ r ≤ dist (p 0) (p k) at hk
  have hk0 : 0 < k := by
    by_contra hn
    have he : k = 0 := by omega
    rw [he,dist_self] at hk
    linarith
  have hpre : dist (p 0) (p (k-1)) < r := by
    by_contra hn
    have hmin := Nat.find_min' hex (show k-1 ≤ m ∧ r ≤ dist (p 0) (p (k-1)) from
      ⟨by omega,by linarith⟩)
    change k ≤ k-1 at hmin
    omega
  refine ⟨k,hk.1,hk.2,?_⟩
  have hs := hstep (k-1) (by omega)
  have he : k-1+1 = k := by omega
  rw [he] at hs
  have ht := dist_triangle (p 0) (p (k-1)) (p k)
  linarith

theorem crossing_witness (h : ℕ → ℝ) (hp : ∀ n, 0 < h n)
    (hg : ∀ n, 8*h n+64 ≤ h (n+1)) (n : ℕ)
    (p : ℕ → V) (m : ℕ) (hstep : ∀ i < m, dist (p i) (p (i+1)) ≤ 8)
    (hend : h n ≤ dist (p 0) (p m)) :
    ∃ t : Tree V n, Admissible h t ∧ root t = p 0 ∧
      (∀ a ∈ leaves t, ∃ i ≤ m, p i = a) ∧
      (∀ a ∈ leaves t, dist (p 0) a ≤ h n+8) := by
  induction n generalizing p m with
  | zero =>
    refine ⟨p 0,True.intro,rfl,?_,?_⟩
    · intro a ha
      change a ∈ ({p 0} : Finset V) at ha
      have he := Finset.mem_singleton.mp ha
      exact ⟨0,Nat.zero_le _,he.symm⟩
    · intro a ha
      change a ∈ ({p 0} : Finset V) at ha
      rw [Finset.mem_singleton.mp ha,dist_self]
      linarith [hp 0]
  | succ n ih =>
    obtain ⟨k,hkm,hklo,hkhi⟩ := first_crossing p m hstep (h (n+1)/2)
      (by linarith [hp (n+1)]) (by linarith [hp (n+1)])
    obtain ⟨l,hl,hlroot,hlpath,hlball⟩ := ih p m hstep (by linarith [hg n,hp n])
    let q : ℕ → V := fun j => p (j+k)
    have hqstep : ∀ j < m-k, dist (q j) (q (j+1)) ≤ 8 := by
      intro j hj
      simpa [q,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hstep (j+k) (by omega)
    have hqend : h n ≤ dist (q 0) (q (m-k)) := by
      have he : m-k+k = m := by omega
      simp only [q,zero_add,he]
      have htri := dist_triangle (p 0) (p k) (p m)
      linarith [hg n,hp n]
    obtain ⟨r,hr,hrroot,hrpath,hrball⟩ := ih q (m-k) hqstep hqend
    have hrroot' : root r = p k := by simpa [q] using hrroot
    have hsep : ∀ a ∈ leaves l, ∀ b ∈ leaves r, h (n+1)/4 ≤ dist a b := by
      intro a ha b hb
      have hla := hlball a ha
      have hrb := hrball b hb
      simp only [q,zero_add] at hrb
      have ht₁ := dist_triangle (p 0) a (p k)
      have ht₂ := dist_triangle a b (p k)
      rw [dist_comm b (p k)] at ht₂
      linarith [hg n]
    refine ⟨(l,r),⟨hl,hr,?_,hsep⟩,hlroot,?_,?_⟩
    · rw [hlroot,hrroot']
      linarith [hp (n+1)]
    · intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact hlpath a ha
      · obtain ⟨j,hj,hja⟩ := hrpath a ha
        exact ⟨j+k,by omega,hja⟩
    · intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · have hh := hlball a ha
        linarith [hg n,hp n]
      · have hh := hrball a ha
        simp only [q,zero_add] at hh
        have htri := dist_triangle (p 0) (p k) a
        linarith [hg n,hp n]

lemma geometric_scale_gap (b : ℝ) (hb : 100 ≤ b) (n : ℕ) :
    8*(16*b^n)+64 ≤ 16*b^(n+1) := by
  rw [pow_succ]
  have hn : 1 ≤ b^n := one_le_pow₀ (by linarith)
  nlinarith

end

section
variable {V : Type*}

def candidates (B : ℕ → V → Finset V) : (n : ℕ) → V → Finset (Tree V n)
  | 0, z => {z}
  | n+1, z => (B (n+1) z).biUnion (fun y => (candidates B n z).product (candidates B n y))

lemma mem_candidates_root (B : ℕ → V → Finset V) {n : ℕ} {z : V} {t : Tree V n}
    (ht : t ∈ candidates B n z) : root t = z := by
  induction n with
  | zero => exact Finset.mem_singleton.mp ht
  | succ n ih =>
    obtain ⟨y,_,h⟩ := Finset.mem_biUnion.mp ht
    exact ih (Finset.mem_product.mp h).1

variable [PseudoMetricSpace V]
lemma admissible_mem_candidates (h : ℕ → ℝ) (B : ℕ → V → Finset V)
    (hB : ∀ n z y, dist z y ≤ h (n+1)+8 → y ∈ B (n+1) z)
    {n : ℕ} (t : Tree V n) (ht : Admissible h t) : t ∈ candidates B n (root t) := by
  induction n with
  | zero => exact Finset.mem_singleton_self _
  | succ n ih =>
    apply Finset.mem_biUnion.mpr
    refine ⟨root t.2,hB n (root t.1) (root t.2) ht.2.2.1,?_⟩
    exact Finset.mem_product.mpr ⟨ih t.1 ht.1,ih t.2 ht.2.1⟩

omit [PseudoMetricSpace V] in
lemma card_candidates_le (B : ℕ → V → Finset V) (M A : ℕ → ℕ)
    (hB : ∀ n z, (B (n+1) z).card ≤ M (n+1)) (hA0 : 1 ≤ A 0)
    (hA : ∀ n, M (n+1)*A n^2 ≤ A (n+1)) (n : ℕ) (z : V) :
    (candidates B n z).card ≤ A n := by
  induction n generalizing z with
  | zero =>
    change ({(show V from z)} : Finset V).card ≤ _
    simpa only [Finset.card_singleton] using hA0
  | succ n ih =>
    simp only [candidates]
    apply Finset.card_biUnion_le.trans
    calc
      _ ≤ ∑ _y ∈ B (n+1) z, A n^2 := by
        apply Finset.sum_le_sum
        intro y _
        exact (Finset.card_product (candidates B n z) (candidates B n y)).le.trans
          (by simpa only [pow_two] using Nat.mul_le_mul (ih z) (ih y))
      _ ≤ M (n+1)*A n^2 := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        exact Nat.mul_le_mul_right _ (hB n z)
      _ ≤ A (n+1) := hA n

def assignmentBound (a c : ℕ) : ℕ → ℕ
  | 0 => 1
  | n+1 => (a*c^(n+1))*assignmentBound a c n^2

lemma assignmentBound_formula (a c n : ℕ) :
    assignmentBound a c n * a*c^(n+2) = (a*c^2)^(2^n) := by
  induction n with
  | zero => simp [assignmentBound]
  | succ n ih =>
    calc
      _ = (assignmentBound a c n*a*c^(n+2))^2 := by
        simp only [assignmentBound,pow_succ]
        ring
      _ = ((a*c^2)^(2^n))^2 := by rw [ih]
      _ = (a*c^2)^(2^(n+1)) := by rw [← pow_mul,pow_succ 2 n]

lemma assignmentBound_le (a c : ℕ) (ha : 1 ≤ a) (hc : 1 ≤ c) (n : ℕ) :
    assignmentBound a c n ≤ (a*c^2)^(2^n) := by
  rw [← assignmentBound_formula]
  have hp : 1 ≤ c^(n+2) := one_le_pow₀ hc
  calc
    _ ≤ assignmentBound a c n*a := by simpa using Nat.mul_le_mul_left (assignmentBound a c n) ha
    _ ≤ assignmentBound a c n*a*c^(n+2) := by
      simpa using Nat.mul_le_mul_left (assignmentBound a c n*a) hp

omit [PseudoMetricSpace V] in

theorem geometric_candidates_count (B : ℕ → V → Finset V) (a c : ℕ)
    (ha : 1 ≤ a) (hc : 1 ≤ c)
    (hB : ∀ n z, (B (n+1) z).card ≤ a*c^(n+1)) (n : ℕ) (z : V) :
    (candidates B n z).card ≤ (a*c^2)^(2^n) := by
  apply (card_candidates_le B (fun j => a*c^j) (assignmentBound a c) hB
    le_rfl (fun _ => le_rfl) n z).trans
  exact assignmentBound_le a c ha hc n

end

variable {V Ω : Type*} [PseudoMetricSpace V] [Fintype Ω]

lemma Sparse.mono_constant {α L L' : ℝ} {F : Finset V}
    (hF : Sparse α L F) (hL : L ≤ L') : Sparse α L' F := by
  intro z r hr
  exact (hF z r hr).trans (mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg (by linarith) _))

def Crosses (Z : Set V) (z : V) (r : ℝ) : Prop :=
  ∃ (p : ℕ → V) (m : ℕ), p 0 = z ∧ (∀ i ≤ m, p i ∈ Z) ∧
    (∀ i < m, dist (p i) (p (i+1)) ≤ 8) ∧ r ≤ dist (p 0) (p m)

lemma finite_union_mass {W : Type*} (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω)
    (F : Finset W) (E : W → Ω → Prop) (A : Ω → Prop)
    (hA : ∀ ω, A ω → ∃ t ∈ F, E t ω) :
    (∑ ω, if A ω then μ ω else 0) ≤ ∑ t ∈ F, ∑ ω, if E t ω then μ ω else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases ha : A ω
  · rw [ite_eq_left ha]
    obtain ⟨t,ht,he⟩ := hA ω ha
    have h := Finset.single_le_sum (f:=fun t => if E t ω then μ ω else 0)
      (fun i _ => by split_ifs <;> simp [hμ]) ht
    simpa only [ite_eq_left he] using h
  · rw [ite_eq_right ha]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> simp [hμ])

theorem crossing_mass_bound (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (Z : Ω → Set V)
    (h : ℕ → ℝ) (hp : ∀ n, 0 < h n) (hg : ∀ n, 8*h n+64 ≤ h (n+1))
    (α L : ℝ) (hα : 0 ≤ α) (hL : 1 ≤ L)
    (hscale : ∀ n, (2:ℝ)^(n+1) ≤ (1+h (n+1)/8)^α)
    (B : ℕ → V → Finset V)
    (hB : ∀ n z y, dist z y ≤ h (n+1)+8 → y ∈ B (n+1) z)
    (a c : ℕ) (ha : 1 ≤ a) (hc : 1 ≤ c)
    (hcard : ∀ n z, (B (n+1) z).card ≤ a*c^(n+1))
    (q : ℝ) (hq : 0 ≤ q)
    (htest : ∀ F : Finset V, Sparse α L F →
      (∑ ω, if (F:Set V) ⊆ Z ω then μ ω else 0) ≤ q^F.card)
    (n : ℕ) (z : V) :
    (∑ ω, if Crosses (Z ω) z (h n) then μ ω else 0) ≤
      ((a*c^2:ℕ)*q)^(2^n) := by
  let F := (candidates B n z).filter (Admissible h)
  have hcover : ∀ ω, Crosses (Z ω) z (h n) →
      ∃ t ∈ F, (leaves t : Set V) ⊆ Z ω := by
    intro ω hω
    obtain ⟨p,m,hp0,hpz,hps,hpe⟩ := hω
    obtain ⟨t,ht,htroot,htpath,_⟩ := crossing_witness h hp hg n p m hps hpe
    refine ⟨t,?_,?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨?_,ht⟩
      rw [← hp0,← htroot]
      exact admissible_mem_candidates h B hB t ht
    · intro v hv
      obtain ⟨i,hi,rfl⟩ := htpath v hv
      exact hpz i hi
  calc
    _ ≤ ∑ t ∈ F, ∑ ω, if (leaves t:Set V) ⊆ Z ω then μ ω else 0 :=
      finite_union_mass μ hμ F _ _ hcover
    _ ≤ ∑ _t ∈ F, q^(2^n) := by
      apply Finset.sum_le_sum
      intro t ht
      have had := (Finset.mem_filter.mp ht).2
      have hsp := (admissible_sparse h (fun i => hp (i+1)) α hα hscale t had).mono_constant hL
      simpa only [card_leaves h (fun i => hp (i+1)) t had] using htest (leaves t) hsp
    _ = (F.card:ℝ)*q^(2^n) := by simp
    _ ≤ ((a*c^2:ℕ):ℝ)^(2^n)*q^(2^n) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hq _)
      exact_mod_cast ((Finset.card_filter_le _ _).trans (geometric_candidates_count B a c ha hc hcard n z))
    _ = _ := (mul_pow ..).symm

end Heisenberg.SparseWitness

end

end OAI
