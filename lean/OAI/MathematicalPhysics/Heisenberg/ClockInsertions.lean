import OAI.MathematicalPhysics.Heisenberg.ClockWitnesses

namespace OAI

noncomputable section

open Filter Topology
open scoped RealInnerProductSpace Classical
open scoped Classical
open Filter
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical

namespace Heisenberg.Clocks
open Heisenberg.Exposure
variable {V X E I : Type*} [PseudoMetricSpace X] [Fintype E] [Fintype I]

theorem mixed_trajectory_probability
    (choices : X → Finset E) (next : X → E → X) (B : ℕ)
    (hB : ∀ x,(choices x).card ≤ B)
    (τ : ℕ → Equiv.Perm V) (site : V → X) (v : V)
    (edge : ℕ → E) (n N r : ℕ) (time : ℕ → Fin N)
    (index : Fin N → E → Bool → I) (src : (I → Bool) → ℕ → Bool)
    (htime : Monotone time)
    (hinj : ∀ c,Set.InjOn (fun j => index (time j) (edge j) (src c j)) (Set.Iio n))
    (hstep : ∀ j,j<n → ∀ a,dist (site (τ j a)) (site a) ≤ 1)
    (hmove : ∀ j,j<n → ∀ a,site (τ j a)≠site a →
      edge j ∈ choices (site a) ∧ site (τ j a)=next (site a) (edge j))
    (p κ : I → ℝ) (hp : ∀ i,0 ≤ p i ∧ p i ≤ 1) (hκ : ∀ i,1 ≤ κ i)
    (W : (I → Bool) → ℝ) (hW : ∀ c,0 ≤ W c)
    (hins : ∀ c i,W (Function.update c i true) ≤ κ i*W (Function.update c i false))
    (δ : ℝ) (hδ : 0 ≤ δ) (hrate : ∀ i,κ i*p i ≤ δ) :
    (∑ c,if (r:ℝ) ≤ dist (site v)
      (site (trajectory τ (fun j => c (index (time j) (edge j) (src c j))) n v))
      then Bernoulli.weight p c*W c else 0) ≤
      ((N+r).choose r:ℝ)*(2*(B:ℝ)*δ)^r * (∑ c,Bernoulli.weight p c*W c) := by
  apply witness_probability choices next B hB r N (site v) index p κ hp hκ W hW hins δ hδ hrate
  intro c hc
  let coin : ℕ → Bool := fun j => c (index (time j) (edge j) (src c j))
  let x : ℕ → X := fun j => site (trajectory τ coin j v)
  have hx0 : x 0=site v := rfl
  have hxstep : ∀ j,0≤j → j<0+n → dist (x j) (x (j+1)) ≤ 1 := by
    intro j _ hj
    dsimp [x]
    rw [trajectory_succ]
    split_ifs
    · rw [dist_comm]
      exact hstep j (by omega) _
    · simp
  have hd := dist_le_moves x 0 n hxstep
  have hlen : r ≤ (moveList x 0 n).length := by
    have hr : (r:ℝ) ≤ ((moveList x 0 n).length:ℝ) := by
      have hc' : (r:ℝ) ≤ dist (x 0) (x n) := hc
      exact hc'.trans (by simpa only [zero_add] using hd)
    exact_mod_cast hr
  have hm : ∀ j,j<n → x (j+1)≠x j →
      edge j ∈ choices (x j) ∧ x (j+1)=next (x j) (edge j) ∧
      c (index (time j) (edge j) (src c j))=true := by
    intro j hj hne
    have hcoin : coin j=true := by
      by_contra hh
      have hf : coin j=false := Bool.eq_false_iff.mpr hh
      have he : x (j+1)=x j := by simp only [x,trajectory_succ,hf,Bool.false_eq_true,ite_false]
      exact hne he
    have he : x (j+1)=site (τ j (trajectory τ coin j v)) := by
      simp only [x,trajectory_succ,hcoin,ite_true]
    have ha : site (τ j (trajectory τ coin j v))≠site (trajectory τ coin j v) := by
      simpa only [←he] using hne
    obtain ⟨hmem,hnext⟩ := hmove j hj _ ha
    exact ⟨hmem,he.trans hnext,hcoin⟩
  simpa only [hx0] using trajectory_witness choices next x edge r n N time (src c) index c
    hlen htime (hinj c) hm

end Heisenberg.Clocks

namespace Heisenberg.Bernoulli
variable {I Q : Type*} [Fintype I]
theorem marked_union_bound_on (p κ : I → ℝ) (hp : ∀ i,0 ≤ p i ∧ p i ≤ 1)
    (hκ : ∀ i,1 ≤ κ i) (W : (I → Bool) → ℝ) (hW : ∀ c,0 ≤ W c)
    (hins : ∀ c i,W (Function.update c i true) ≤ κ i*W (Function.update c i false))
    (q : Finset Q) (marks : Q → Finset I) (r : ℕ) (hm : ∀ x ∈ q,(marks x).card = r)
    (δ : ℝ) (_hδ : 0 ≤ δ) (hrate : ∀ x ∈ q,∀ i ∈ marks x,κ i*p i ≤ δ)
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
        _ ≤ ∏ _i ∈ marks x,δ := Finset.prod_le_prod₀ (fun i _ => mul_nonneg (by linarith [hκ i]) (hp i).1) (fun i hi => hrate x hx i hi)
        _ = δ^r := by rw [Finset.prod_const,hm x hx]
    _ = _ := by simp [mul_assoc]

end Heisenberg.Bernoulli

namespace Heisenberg.Clocks
variable {X E I : Type*} [Fintype E]
theorem witness_probability_spatial [Fintype I]
    (choices : X → Finset E) (next : X → E → X) (B : ℕ)
    (hB : ∀ x,(choices x).card ≤ B) (r N : ℕ) (x : X) (index : Fin N → E → Bool → I)
    (p κ : I → ℝ) (hp : ∀ i,0 ≤ p i ∧ p i ≤ 1) (hκ : ∀ i,1 ≤ κ i)
    (W : (I → Bool) → ℝ) (hW : ∀ c,0 ≤ W c)
    (hins : ∀ c i,W (Function.update c i true) ≤ κ i*W (Function.update c i false))
    (δ : ℝ) (hδ : 0 ≤ δ) (hrate : ∀ t e b,κ (index t e b)*p (index t e b) ≤ δ)
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
  have hb := Bernoulli.marked_union_bound_on p κ hp hκ W hW hins
    (witnesses choices next r N x index) (witnessMarks index) r
    (fun q hq => witnessMarks_card choices next r N x index q hq) δ hδ (by
      intro q _ i hi
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
      exact hrate _ _ _) event hc
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

theorem adaptive_trajectory_witness (choices : X → Finset E) (next : X → E → X)
    (x : ℕ → X) (edge : ℕ → E) (r n N : ℕ)
    (time : ℕ → Fin N) (src : ℕ → Bool) (index : Fin N → E → Bool → I)
    (c : I → Bool) (hlen : r ≤ (moveList x 0 n).length)
    (htime : Monotone time)
    (hinj : Set.InjOn (fun j => index (time j) (edge j) (src j)) {j | j<n ∧ x (j+1)≠x j})
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
    exact hinj ⟨hjlt a,moveList_moved x 0 n (hjmem a)⟩ ⟨hjlt b,moveList_moved x 0 n (hjmem b)⟩ he

theorem adaptive_trajectory_probability [Fintype I] [PseudoMetricSpace X]
    (choices : X → Finset E) (next : X → E → X) (B : ℕ)
    (hB : ∀ x,(choices x).card ≤ B) (v : X)
    (x : (I → Bool) → ℕ → X) (hx0 : ∀ c,x c 0=v)
    (edge : ℕ → E) (n N r : ℕ) (time : ℕ → Fin N)
    (index : Fin N → E → Bool → I) (src : (I → Bool) → ℕ → Bool)
    (htime : Monotone time)
    (hinj : ∀ c,Set.InjOn (fun j => index (time j) (edge j) (src c j))
      {j | j<n ∧ x c (j+1)≠x c j})
    (hstep : ∀ c j,j<n → dist (x c j) (x c (j+1)) ≤ 1)
    (hmove : ∀ c j,j<n → x c (j+1)≠x c j →
      edge j ∈ choices (x c j) ∧ x c (j+1)=next (x c j) (edge j) ∧
      c (index (time j) (edge j) (src c j))=true)
    (p κ : I → ℝ) (hp : ∀ i,0 ≤ p i ∧ p i ≤ 1) (hκ : ∀ i,1 ≤ κ i)
    (W : (I → Bool) → ℝ) (hW : ∀ c,0 ≤ W c)
    (hins : ∀ c i,W (Function.update c i true) ≤ κ i*W (Function.update c i false))
    (δ : ℝ) (hδ : 0 ≤ δ) (hrate : ∀ t e b,κ (index t e b)*p (index t e b) ≤ δ) :
    (∑ c,if (r:ℝ) ≤ dist v (x c n) then Bernoulli.weight p c*W c else 0) ≤
      ((N+r).choose r:ℝ)*(2*(B:ℝ)*δ)^r * (∑ c,Bernoulli.weight p c*W c) := by
  apply witness_probability_spatial choices next B hB r N v index p κ hp hκ W hW hins δ hδ hrate
  intro c hc
  have hd := dist_le_moves (x c) 0 n (fun j _ hj => hstep c j (by simpa using hj))
  have hd' : dist v (x c n) ≤ ((moveList (x c) 0 n).length:ℝ) := by simpa [hx0 c] using hd
  have hlen : r ≤ (moveList (x c) 0 n).length := by
    have hh : (r:ℝ) ≤ ((moveList (x c) 0 n).length:ℝ) := hc.trans hd'
    exact_mod_cast hh
  simpa only [hx0 c] using adaptive_trajectory_witness choices next (x c) edge r n N time (src c) index c
    hlen htime (hinj c) (hmove c)

end Heisenberg.Clocks

namespace Heisenberg.Bernoulli
variable {I : Type*} [Fintype I]

def doubleRates (p : I → ℝ) : I ⊕ I → ℝ := Sum.elim p p

def original (c : I ⊕ I → Bool) : I → Bool := c ∘ Sum.inl

def fresh (c : I ⊕ I → Bool) : I → Bool := c ∘ Sum.inr

lemma weight_total (p : I → ℝ) : ∑ c, weight p c=1 := by
  classical
  unfold weight
  rw [←Fintype.prod_sum (fun i (b : Bool) => if b then p i else 1-p i)]
  simp

lemma double_weight (p : I → ℝ) (c : I ⊕ I → Bool) :
    weight (doubleRates p) c=weight p (original c)*weight p (fresh c) := by
  classical
  simp only [weight,Fintype.prod_sum_type,doubleRates,original,fresh,Function.comp_apply,Sum.elim_inl,Sum.elim_inr]
  congr 1

lemma double_sum (p : I → ℝ) (F : (I → Bool) → (I → Bool) → ℝ) :
    (∑ c : I ⊕ I → Bool,weight (doubleRates p) c*F (original c) (fresh c)) =
      ∑ b : I → Bool,∑ f : I → Bool,weight p b*weight p f*F b f := by
  rw [←(Equiv.sumArrowEquivProdArrow I I Bool).symm.sum_comp]
  simp only [double_weight,Fintype.sum_prod_type]
  rfl

lemma double_partition (p : I → ℝ) (W : (I → Bool) → ℝ) :
    (∑ c : I ⊕ I → Bool,weight (doubleRates p) c*W (original c)) =
      ∑ b : I → Bool,weight p b*W b := by
  rw [double_sum p (fun b _ => W b)]
  simp_rw [mul_right_comm _ _ (W _),←Finset.mul_sum,weight_total,mul_one]

omit [Fintype I] in
lemma original_update_left (c : I ⊕ I → Bool) (i : I) (b : Bool) :
    original (Function.update c (Sum.inl i) b)=Function.update (original c) i b := by
  classical
  funext j
  by_cases hj : j=i
  · subst j; simp [original]
  · simp [original,hj]

omit [Fintype I] in
lemma original_update_right (c : I ⊕ I → Bool) (i : I) (b : Bool) :
    original (Function.update c (Sum.inr i) b)=original c := by
  classical
  funext j
  simp [original]

omit [Fintype I] in

theorem double_insertion {κ : ℝ} (W : (I → Bool) → ℝ)
    (h : ∀ c i,W (Function.update c i true)≤κ*W (Function.update c i false)) :
    ∀ (c : I ⊕ I → Bool) i,
      W (original (Function.update c i true)) ≤
        (Sum.elim (fun _ => κ) (fun _ => (1:ℝ)) i)*W (original (Function.update c i false)) := by
  intro c i
  cases i with
  | inl i => simpa only [original_update_left,Sum.elim_inl] using h (original c) i
  | inr i => simp only [original_update_right,Sum.elim_inr,one_mul,le_refl]

end Heisenberg.Bernoulli

end

end OAI
