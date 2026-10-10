import OAI.MathematicalPhysics.Heisenberg.HistoryMarginals

namespace OAI

noncomputable section

open Filter Topology
open scoped RealInnerProductSpace Classical
open scoped Classical
open Filter
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical

namespace Heisenberg.Bernoulli
variable {I Q : Type*} [Fintype I]

theorem marked_union_bound (p κ : I → ℝ) (hp : ∀ i,0 ≤ p i ∧ p i ≤ 1)
    (hκ : ∀ i,1 ≤ κ i) (W : (I → Bool) → ℝ) (hW : ∀ c,0 ≤ W c)
    (hins : ∀ c i,W (Function.update c i true) ≤ κ i*W (Function.update c i false))
    (q : Finset Q) (marks : Q → Finset I) (r : ℕ) (hm : ∀ x ∈ q,(marks x).card = r)
    (δ : ℝ) (_hδ : 0 ≤ δ) (hrate : ∀ i,κ i*p i ≤ δ)
    (event : (I → Bool) → Prop)
    (hcover : ∀ c,event c → ∃ x ∈ q,∀ i ∈ marks x,c i = true) :
    (∑ c,if event c then weight p c*W c else 0) ≤
      (q.card:ℝ)*δ^r*(∑ c,weight p c*W c) := by
  have hb (c : I → Bool) : (if event c then (1:ℝ) else 0) ≤ ∑ x ∈ q,test (marks x) c := by
    by_cases hc : event c
    · obtain ⟨x,hx,hm⟩ := hcover c hc
      rw [ite_eq_left hc]
      have he : test (marks x) c = 1 := ite_eq_left hm
      rw [←he]
      exact Finset.single_le_sum (fun x _ => test_nonneg _ c) hx
    · rw [ite_eq_right hc]
      exact Finset.sum_nonneg (fun x _ => test_nonneg _ c)
  have hZ : 0 ≤ ∑ c,weight p c*W c :=
    Finset.sum_nonneg (fun c _ => mul_nonneg (weight_nonneg p hp c) (hW c))
  calc
    _ = ∑ c,weight p c*W c*(if event c then (1:ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro c _
      split_ifs <;> simp
    _ ≤ ∑ c,weight p c*W c*(∑ x ∈ q,test (marks x) c) :=
      Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (hb c) (mul_nonneg (weight_nonneg p hp c) (hW c)))
    _ = ∑ x ∈ q,∑ c,weight p c*(W c*test (marks x) c) := by
      simp only [Finset.mul_sum,mul_assoc]
      rw [Finset.sum_comm]
    _ ≤ ∑ x ∈ q,δ^r*(∑ c,weight p c*W c) := by
      apply Finset.sum_le_sum
      intro x hx
      apply (factorial_bound_rates p κ hp hκ W hW hins (marks x)).trans
      apply mul_le_mul_of_nonneg_right _ hZ
      calc
        _ ≤ ∏ _i ∈ marks x,δ := Finset.prod_le_prod₀ (fun i _ => mul_nonneg (by linarith [hκ i]) (hp i).1) (fun i _ => hrate i)
        _ = δ^r := by rw [Finset.prod_const,hm x hx]
    _ = _ := by simp [mul_assoc]

end Heisenberg.Bernoulli

namespace Heisenberg.Clocks

section
variable {X E I : Type*} [Fintype E]

def weakTimes (r N : ℕ) : Finset (Fin r → Fin N) := Finset.univ.filter Monotone

lemma weakTimes_card (r N : ℕ) : (weakTimes r N).card ≤ (N+r).choose r := by
  rw [weakTimes,←Fintype.card_subtype]
  exact card_weakTimes_le N r

def functionWords (choices : X → Finset E) (next : X → E → X) (r : ℕ) (x : X) :
    Finset (Fin r → E) := Finset.univ.filter (fun w => List.ofFn w ∈ edgeWords choices next r x)

lemma card_functionWords (choices : X → Finset E) (next : X → E → X) (B : ℕ)
    (hB : ∀ x,(choices x).card ≤ B) (r : ℕ) (x : X) :
    (functionWords choices next r x).card ≤ B^r := by
  apply le_trans _ (card_edgeWords choices next B hB r x)
  apply Finset.card_le_card_of_injOn (fun w => List.ofFn w)
  · intro w hw; exact (Finset.mem_filter.mp hw).2
  · intro a _ b _ he
    exact List.ofFn_inj.mp he

def witnesses (choices : X → Finset E) (next : X → E → X) (r N : ℕ) (x : X)
    (index : Fin N → E → Bool → I) :
    Finset ((Fin r → Fin N) × (Fin r → E) × (Fin r → Bool)) :=
  ((weakTimes r N).product ((functionWords choices next r x).product Finset.univ)).filter
    (fun q => Function.Injective (fun k => index (q.1 k) (q.2.1 k) (q.2.2 k)))

def witnessMarks {r N : ℕ} (index : Fin N → E → Bool → I)
    (q : (Fin r → Fin N) × (Fin r → E) × (Fin r → Bool)) : Finset I :=
      Finset.univ.image (fun k => index (q.1 k) (q.2.1 k) (q.2.2 k))

lemma witnessMarks_card (choices : X → Finset E) (next : X → E → X) (r N : ℕ) (x : X)
    (index : Fin N → E → Bool → I) (q) (hq : q ∈ witnesses choices next r N x index) :
    (witnessMarks index q).card = r := by
  have hi := (Finset.mem_filter.mp hq).2
  rw [witnessMarks,Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_fin]

lemma witnesses_card (choices : X → Finset E) (next : X → E → X) (B : ℕ)
    (hB : ∀ x,(choices x).card ≤ B) (r N : ℕ) (x : X) (index : Fin N → E → Bool → I) :
    (witnesses choices next r N x index).card ≤ (N+r).choose r * (2*B)^r := by
  calc
    _ ≤ ((weakTimes r N).product ((functionWords choices next r x).product Finset.univ)).card :=
      Finset.card_filter_le _ _
    _ = (weakTimes r N).card * ((functionWords choices next r x).card * 2^r) := by
      simp
    _ ≤ (N+r).choose r * (B^r * 2^r) :=
      Nat.mul_le_mul (weakTimes_card r N) (Nat.mul_le_mul_right _ (card_functionWords choices next B hB r x))
    _ = _ := by rw [←Nat.mul_pow,Nat.mul_comm B 2]

theorem witness_probability [Fintype I]
    (choices : X → Finset E) (next : X → E → X) (B : ℕ)
    (hB : ∀ x,(choices x).card ≤ B) (r N : ℕ) (x : X) (index : Fin N → E → Bool → I)
    (p κ : I → ℝ) (hp : ∀ i,0 ≤ p i ∧ p i ≤ 1) (hκ : ∀ i,1 ≤ κ i)
    (W : (I → Bool) → ℝ) (hW : ∀ c,0 ≤ W c)
    (hins : ∀ c i,W (Function.update c i true) ≤ κ i*W (Function.update c i false))
    (δ : ℝ) (hδ : 0 ≤ δ) (hrate : ∀ i,κ i*p i ≤ δ)
    (event : (I → Bool) → Prop)
    (hcover : ∀ c,event c → ∃ q ∈ witnesses choices next r N x index,
      ∀ k : Fin r,c (index (q.1 k) (q.2.1 k) (q.2.2 k)) = true) :
    (∑ c,if event c then Bernoulli.weight p c*W c else 0) ≤
      ((N+r).choose r:ℝ)*(2*(B:ℝ)*δ)^r * (∑ c,Bernoulli.weight p c*W c) := by
  have hc : ∀ c,event c → ∃ q ∈ witnesses choices next r N x index,
      ∀ i ∈ witnessMarks index q,c i=true := by
    intro c he
    obtain ⟨q,hq,hh⟩ := hcover c he
    refine ⟨q,hq,?_⟩
    intro i hi
    obtain ⟨k,_hk,rfl⟩ := Finset.mem_image.mp hi
    exact hh k
  have hb := Bernoulli.marked_union_bound p κ hp hκ W hW hins
    (witnesses choices next r N x index) (witnessMarks index) r
    (fun q hq => witnessMarks_card choices next r N x index q hq) δ hδ hrate event hc
  have hZ : 0 ≤ ∑ c,Bernoulli.weight p c*W c := Finset.sum_nonneg
    (fun c _ => mul_nonneg (Bernoulli.weight_nonneg p hp c) (hW c))
  apply hb.trans
  have hn : ((witnesses choices next r N x index).card:ℝ) ≤
      ((N+r).choose r:ℝ)*(2*(B:ℝ))^r := by
    exact_mod_cast witnesses_card choices next B hB r N x index
  calc
    _ ≤ (((N+r).choose r:ℝ)*(2*(B:ℝ))^r)*δ^r*(∑ c,Bernoulli.weight p c*W c) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn (pow_nonneg hδ _)) hZ
    _ = _ := by rw [mul_assoc _ _ (δ^r),←mul_pow]

end

variable {X E I : Type*}

def moveList (x : ℕ → X) (m : ℕ) : ℕ → List ℕ
  | 0 => []
  | k+1 => if x (m+1)=x m then moveList x (m+1) k
      else m :: moveList x (m+1) k

lemma moveList_bounds (x : ℕ → X) (m n : ℕ) {j : ℕ} (hj : j ∈ moveList x m n) :
    m ≤ j ∧ j < m+n := by
  induction n generalizing m with
  | zero => simp [moveList] at hj
  | succ n ih =>
    simp only [moveList] at hj
    split_ifs at hj with he
    · obtain ⟨h₁,h₂⟩ := ih (m+1) hj
      omega
    · rcases List.mem_cons.mp hj with rfl | hj
      · omega
      · obtain ⟨h₁,h₂⟩ := ih (m+1) hj
        omega

lemma moveList_moved (x : ℕ → X) (m n : ℕ) {j : ℕ} (hj : j ∈ moveList x m n) :
    x (j+1) ≠ x j := by
  induction n generalizing m with
  | zero => simp [moveList] at hj
  | succ n ih =>
    simp only [moveList] at hj
    split_ifs at hj with he
    · exact ih (m+1) hj
    · rcases List.mem_cons.mp hj with rfl | hj
      · exact he
      · exact ih (m+1) hj

lemma moveList_pairwise (x : ℕ → X) (m n : ℕ) :
    (moveList x m n).Pairwise (· < ·) := by
  induction n generalizing m with
  | zero => simp [moveList]
  | succ n ih =>
    simp only [moveList]
    split_ifs
    · exact ih _
    · exact List.pairwise_cons.mpr ⟨fun j hj => by
        have h := (moveList_bounds x (m+1) n hj).1
        omega, ih _⟩

lemma moveList_follows (choices : X → Finset E) (next : X → E → X)
    (x : ℕ → X) (e : ℕ → E) (m n : ℕ)
    (hmove : ∀ j,m ≤ j → j < m+n → x (j+1) ≠ x j →
      e j ∈ choices (x j) ∧ x (j+1)=next (x j) (e j)) :
    Follows choices next (x m) ((moveList x m n).map e) := by
  induction n generalizing m with
  | zero => trivial
  | succ n ih =>
    simp only [moveList]
    split_ifs with he
    · rw [←he]
      exact ih (m+1) (fun j h₁ h₂ => hmove j (by omega) (by omega))
    · have hm := hmove m le_rfl (by omega) he
      change e m ∈ choices (x m) ∧ _
      refine ⟨hm.1,?_⟩
      rw [←hm.2]
      exact ih (m+1) (fun j h₁ h₂ => hmove j (by omega) (by omega))

lemma follows_take (choices : X → Finset E) (next : X → E → X)
    (x : X) (l : List E) (hl : Follows choices next x l) (r : ℕ) :
    Follows choices next x (l.take r) := by
  induction r generalizing x l with
  | zero => trivial
  | succ r ih =>
    cases l with
    | nil => trivial
    | cons e l => exact ⟨hl.1,ih _ _ hl.2⟩

lemma dist_le_moves [PseudoMetricSpace X] (x : ℕ → X) (m n : ℕ)
    (hstep : ∀ j,m ≤ j → j < m+n → dist (x j) (x (j+1)) ≤ 1) :
    dist (x m) (x (m+n)) ≤ (moveList x m n).length := by
  induction n generalizing m with
  | zero => simp [moveList]
  | succ n ih =>
    have ht := ih (m+1) (fun j h₁ h₂ => hstep j (by omega) (by omega))
    have hh : m+(n+1)=(m+1)+n := by omega
    rw [moveList]
    split_ifs with he
    · rw [←he,hh]
      exact ht
    · rw [List.length_cons,Nat.cast_add,Nat.cast_one,hh]
      exact (dist_triangle _ (x (m+1)) _).trans (by linarith [hstep m le_rfl (by omega)])

theorem trajectory_witness [Fintype E] (choices : X → Finset E) (next : X → E → X)
    (x : ℕ → X) (edge : ℕ → E) (r n N : ℕ)
    (time : ℕ → Fin N) (src : ℕ → Bool) (index : Fin N → E → Bool → I)
    (c : I → Bool) (hlen : r ≤ (moveList x 0 n).length)
    (htime : Monotone time)
    (hinj : Set.InjOn (fun j => index (time j) (edge j) (src j)) (Set.Iio n))
    (hmove : ∀ j,j<n → x (j+1)≠x j →
      edge j ∈ choices (x j) ∧ x (j+1)=next (x j) (edge j) ∧
      c (index (time j) (edge j) (src j))=true) :
    ∃ q ∈ witnesses choices next r N (x 0) index,
      ∀ k : Fin r,c (index (q.1 k) (q.2.1 k) (q.2.2 k))=true := by
  let l := (moveList x 0 n).take r
  have hl : l.length=r := by simp [l,List.length_take,Nat.min_eq_left hlen]
  let j : Fin r → ℕ := fun k => l.get (Fin.cast hl.symm k)
  have hjmem (k : Fin r) : j k ∈ moveList x 0 n :=
    List.mem_of_mem_take (List.get_mem l _)
  have hjlt (k : Fin r) : j k<n := by simpa using (moveList_bounds x 0 n (hjmem k)).2
  have hjmove (k : Fin r) := hmove (j k) (hjlt k) (moveList_moved x 0 n (hjmem k))
  have hjmono : StrictMono j := by
    intro a b hab
    have hh : l.Pairwise (· < ·) := (moveList_pairwise x 0 n).take
    exact List.pairwise_iff_get.mp hh _ _ (by simpa using hab)
  have hof : List.ofFn j = l := by
    rw [←List.ofFn_congr hl (List.get l)]
    exact List.ofFn_get l
  let q : (Fin r → Fin N) × (Fin r → E) × (Fin r → Bool) :=
    (fun k => time (j k),fun k => edge (j k),fun k => src (j k))
  refine ⟨q,?_,fun k => (hjmove k).2.2⟩
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,htime.comp hjmono.monotone⟩
    · apply Finset.mem_product.mpr
      refine ⟨?_,Finset.mem_univ _⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      have hf := moveList_follows choices next x edge 0 n
        (fun j _ hj hm => ⟨(hmove j (by simpa using hj) hm).1,(hmove j (by simpa using hj) hm).2.1⟩)
      have ht := follows_take choices next (x 0) _ hf r
      have he : List.ofFn (fun k : Fin r => edge (j k)) = l.map edge := by
        change List.ofFn (edge ∘ j) = _
        rw [←List.map_ofFn,hof]
      rw [he]
      convert follows_mem choices next (x 0) (l.map edge) (by simpa [l,List.map_take] using ht) using 1
      simp [hl]
  · intro a b he
    apply hjmono.injective
    exact hinj (hjlt a) (hjlt b) he

end Heisenberg.Clocks

end

end OAI
