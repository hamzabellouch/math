import OAI.MathematicalPhysics.Heisenberg.ClockInsertions

namespace OAI

noncomputable section

open Filter Topology
open scoped RealInnerProductSpace Classical
open scoped Classical
open Filter
open scoped BigOperators Classical

namespace Heisenberg.Clocks
open Heisenberg.Exposure Heisenberg.Bernoulli
variable {V X E I : Type*} [PseudoMetricSpace X] [Fintype E] [Fintype I]

def mixedCoins (M : (I → Bool) → I → Prop) (c : I ⊕ I → Bool) (r : ℕ → I) : ℕ → Bool :=
  fun j=>if M (original c) (r j) then original c (r j) else fresh c (r j)

def mixedSource (M : (I → Bool) → I → Prop) (c : I ⊕ I → Bool) (r : ℕ → I) : ℕ → Bool :=
  fun j=>decide (M (original c) (r j))

omit [PseudoMetricSpace X] [Fintype E] [Fintype I] in
lemma mixedCoins_index (M : (I → Bool) → I → Prop) (c : I ⊕ I → Bool) (r : ℕ → I) (j : ℕ) :
    mixedCoins M c r j=c (if mixedSource M c r j then Sum.inl (r j) else Sum.inr (r j)) := by
  simp only [mixedCoins,mixedSource,decide_eq_true_eq]
  split_ifs <;> rfl

theorem joint_trajectory_localization
    (choices : X → Finset E) (next : X → E → X) (B : ℕ)
    (hB : ∀ x,(choices x).card≤B)
    (τ : ℕ → Equiv.Perm V) (site : V → X) (v : V)
    (r : ℕ → I) (n N R : ℕ) (hr : Set.InjOn r (Set.Iio n))
    (edge : ℕ → E) (time : ℕ → Fin N) (index : Fin N → E → Bool → I ⊕ I)
    (htime : Monotone time)
    (hstep : ∀ j,j<n → ∀ a,dist (site (τ j a)) (site a)≤1)
    (hmove : ∀ j,j<n → ∀ a,site (τ j a)≠site a →
      edge j∈choices (site a) ∧ site (τ j a)=next (site a) (edge j))
    (hindex : ∀ j,j<n → ∀ a,site (τ j a)≠site a → ∀ b,
      index (time j) (edge j) b=(if b then Sum.inl (r j) else Sum.inr (r j)))
    (M : (I → Bool) → I → Prop) (p : I → ℝ) (hp : ∀ i,0≤p i ∧ p i≤1)
    {κ δ : ℝ} (hκ : 1≤κ) (hδ : 0≤δ)
    (W : (I → Bool) → ℝ) (hW : ∀ c,0≤W c)
    (hins : ∀ c i,W (Function.update c i true)≤κ*W (Function.update c i false))
    (hrate : ∀ t e b,
      (Sum.elim (fun _=>κ) (fun _=>(1:ℝ)) (index t e b)) * doubleRates p (index t e b)≤δ) :
    (∑ c : I ⊕ I → Bool,if (R:ℝ)≤dist (site v)
      (site (trajectory τ (mixedCoins M c r) n v)) then
      weight (doubleRates p) c*W (original c) else 0) ≤
      ((N+R).choose R:ℝ)*(2*(B:ℝ)*δ)^R*(∑ c,weight p c*W c) := by
  let x : (I ⊕ I → Bool) → ℕ → X := fun c j=>site (trajectory τ (mixedCoins M c r) j v)
  have hd (c : I ⊕ I → Bool) (j : ℕ) (_hj : j<n) (hne : x c (j+1)≠x c j) :
      mixedCoins M c r j=true ∧
      x c (j+1)=site (τ j (trajectory τ (mixedCoins M c r) j v)) ∧
      site (τ j (trajectory τ (mixedCoins M c r) j v))≠x c j := by
    have hc : mixedCoins M c r j=true := by
      by_contra hh
      simp only [x,trajectory_succ,ite_eq_right hh] at hne
      exact hne rfl
    refine ⟨hc,?_,?_⟩
    · simp only [x,trajectory_succ,hc,ite_true]
    · simpa only [x,trajectory_succ,hc,ite_true] using hne
  have hi (c : I ⊕ I → Bool) (j : ℕ) (hj : j<n) (hne : x c (j+1)≠x c j) :
      index (time j) (edge j) (mixedSource M c r j)=
        (if mixedSource M c r j then Sum.inl (r j) else Sum.inr (r j)) :=
    hindex j hj _ (hd c j hj hne).2.2 _
  have hb (c : I ⊕ I → Bool) : Set.InjOn
      (fun j=>index (time j) (edge j) (mixedSource M c r j))
      {j | j<n ∧ x c (j+1)≠x c j} := by
    intro j hj k hk he
    dsimp only at he
    rw [hi c j hj.1 hj.2,hi c k hk.1 hk.2] at he
    apply hr hj.1 hk.1
    have he' := congrArg (Sum.elim id id) he
    split_ifs at he' <;> exact he'
  have hm (c : I ⊕ I → Bool) (j : ℕ) (hj : j<n) (hne : x c (j+1)≠x c j) :
      edge j∈choices (x c j) ∧ x c (j+1)=next (x c j) (edge j) ∧
      c (index (time j) (edge j) (mixedSource M c r j))=true := by
    have hh:=hd c j hj hne
    obtain ⟨h1,h2⟩:=hmove j hj _ hh.2.2
    refine ⟨h1,hh.2.1.trans h2,?_⟩
    rw [hi c j hj hne,←mixedCoins_index M c r j]
    exact hh.1
  have hs (c : I ⊕ I → Bool) (j : ℕ) (hj : j<n) : dist (x c j) (x c (j+1))≤1 := by
    dsimp only [x]
    rw [trajectory_succ]
    split_ifs
    · rw [dist_comm]; exact hstep j hj _
    · simp
  have hh:=adaptive_trajectory_probability choices next B hB (site v) x (fun _=>rfl)
    edge n N R time index (fun c=>mixedSource M c r) htime hb hs hm
    (doubleRates p) (Sum.elim (fun _=>κ) (fun _=>(1:ℝ)))
    (by intro i; cases i <;> exact hp _) (by intro i; cases i <;> simp [hκ])
    (fun c=>W (original c)) (fun c=>hW _)
    (by
      intro c i
      convert double_insertion W hins c i using 1 <;>
        congr 2 <;> funext j <;> simp only [original,Function.comp_apply,Function.update_apply] <;> split_ifs <;> rfl) δ hδ hrate
  have hz : (∑ c : I ⊕ I → Bool,weight (doubleRates p) c*W (original c)) =
      ∑ c : I → Bool,weight p c*W c := by
    convert double_partition p W using 1
  convert hh using 1
  · congr 1
    ext c
    simp
  · rw [←hz]
    congr 2
    ext c
    simp

end Heisenberg.Clocks

open scoped BigOperators Classical
namespace Heisenberg.Serial

section
open Heisenberg.Exposure Heisenberg.Bernoulli Heisenberg.Clocks Heisenberg.MeshPair
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

def sampledPrefix (τ : ℕ → Equiv.Perm V) (p : I → ℝ) (r : ℕ → I)
    (M : (I → Bool) → I → Prop) (n : ℕ) (D : (I → Bool) → Fin (n+1) → Set V)
    (base : I → Bool) : Matrix V V ℝ :=
  product n (fun i=>∑ b : Bool,(if b then p (r i) else 1-p (r i)) •
    killedBetween (D base i.castSucc) (D base i.succ)
      (if (if M base (r i) then base (r i) else b) then τ i else 1)) * projection (D base 0)

theorem sampledPrefix_event (τ : ℕ → Equiv.Perm V) (p : I → ℝ)
    (hp : ∀ i,0≤p i ∧ p i≤1) (r : ℕ → I) (n : ℕ)
    (hr : Set.InjOn r (Set.Iio n)) (M : (I → Bool) → I → Prop)
    (D : (I → Bool) → Fin (n+1) → Set V)
    (W : (I → Bool) → ℝ) (hW : ∀ c,0≤W c) (v : V) (A : Set V) :
    (∑ base : I → Bool,weight p base*W base*
      (∑ i,if i∈A then sampledPrefix τ p r M n D base i v else 0)) ≤
    ∑ c : I ⊕ I → Bool,if trajectory τ (mixedCoins M c r) n v∈A then
      weight (doubleRates p) c*W (original c) else 0 := by
  have hir : Function.Injective (fun i : Fin n=>r i) := by
    intro i j h
    exact Fin.ext (hr i.isLt j.isLt h)
  have hw (i : I) : (∑ b : Bool,if b then p i else 1-p i)=1 := by simp
  have hw0 (i : I) (b : Bool) : 0≤(if b then p i else 1-p i) := by
    cases b <;> simp <;> linarith [(hp i).1,(hp i).2]
  have hbase (base : I → Bool) := prefix_endpoint_bound n
    (fun i b=>if b then p i else 1-p i) hw hw0 (fun i=>r i) hir (D base)
    (fun i b=>if (if M base (r i) then base (r i) else b) then τ i else 1) v A
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun base _=>
    mul_le_mul_of_nonneg_left (hbase base)
      (mul_nonneg (weight_nonneg p hp base) (hW base)))
  change (∑ base : I → Bool,weight p base*W base*
      (∑ i,if i∈A then sampledPrefix τ p r M n D base i v else 0)) ≤ _ at h
  apply h.trans_eq
  simp only [Finset.mul_sum]
  rw [←(Equiv.sumArrowEquivProdArrow I I Bool).symm.sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro base _
  apply Finset.sum_congr rfl
  intro c _
  have he : follow n (fun i=>if (if M base (r i) then base (r i) else c (r i)) then τ i else 1) v=
      trajectory τ (fun j=>if M base (r j) then base (r j) else c (r j)) n v :=
    follow_trajectory τ (fun j=>if M base (r j) then base (r j) else c (r j)) n v
  change weight p base*W base*(if follow n _ v∈A then productWeight _ c else 0) = _
  rw [he]
  have ho : original ((Equiv.sumArrowEquivProdArrow I I Bool).symm (base,c))=base := rfl
  have hf : fresh ((Equiv.sumArrowEquivProdArrow I I Bool).symm (base,c))=c := rfl
  have hc : mixedCoins M ((Equiv.sumArrowEquivProdArrow I I Bool).symm (base,c)) r=
      (fun j=>if M base (r j) then base (r j) else c (r j)) := by
    funext j
    simp only [mixedCoins,ho,hf]
  rw [hc,double_weight,ho,hf]
  split_ifs <;> simp only [productWeight,weight,mul_zero]
  ring

end

open Heisenberg.Exposure Heisenberg.Bernoulli Heisenberg.Clocks Heisenberg.MeshPair
variable {V X E I : Type*} [Fintype V] [DecidableEq V] [PseudoMetricSpace X] [Fintype E] [Fintype I]

theorem sampledPrefix_localization
    (choices : X → Finset E) (next : X → E → X) (B : ℕ)
    (hB : ∀ x,(choices x).card≤B)
    (τ : ℕ → Equiv.Perm V) (site : V → X) (v : V)
    (r : ℕ → I) (n N R : ℕ) (hr : Set.InjOn r (Set.Iio n))
    (edge : ℕ → E) (time : ℕ → Fin N) (index : Fin N → E → Bool → I ⊕ I)
    (htime : Monotone time)
    (hstep : ∀ j,j<n → ∀ a,dist (site (τ j a)) (site a)≤1)
    (hmove : ∀ j,j<n → ∀ a,site (τ j a)≠site a →
      edge j∈choices (site a) ∧ site (τ j a)=next (site a) (edge j))
    (hindex : ∀ j,j<n → ∀ a,site (τ j a)≠site a → ∀ b,
      index (time j) (edge j) b=(if b then Sum.inl (r j) else Sum.inr (r j)))
    (M : (I → Bool) → I → Prop) (p : I → ℝ) (hp : ∀ i,0≤p i ∧ p i≤1)
    {κ δ : ℝ} (hκ : 1≤κ) (hδ : 0≤δ)
    (W : (I → Bool) → ℝ) (hW : ∀ c,0≤W c)
    (hins : ∀ c i,W (Function.update c i true)≤κ*W (Function.update c i false))
    (D : (I → Bool) → Fin (n+1) → Set V)
    (hrate : ∀ t e b,
      (Sum.elim (fun _=>κ) (fun _=>(1:ℝ)) (index t e b)) * doubleRates p (index t e b)≤δ) :
    (∑ base : I → Bool, weight p base*W base*
      (∑ j,if (R:ℝ)<dist (site j) (site v) then sampledPrefix τ p r M n D base j v else 0)) ≤
      ((N+R).choose R:ℝ)*(2*(B:ℝ)*δ)^R*(∑ c,weight p c*W c) := by
  have he := sampledPrefix_event τ p hp r n hr M D W hW v {j | (R:ℝ)<dist (site j) (site v)}
  have hl := joint_trajectory_localization choices next B hB τ site v r n N R hr edge time index
    htime hstep hmove hindex M p hp hκ hδ W hW hins hrate
  apply he.trans
  apply le_trans _ hl
  apply Finset.sum_le_sum
  intro c _
  change (if (R:ℝ)<dist (site (trajectory τ (mixedCoins M c r) n v)) (site v) then _ else 0)≤_
  by_cases hc : (R:ℝ)<dist (site (trajectory τ (mixedCoins M c r) n v)) (site v)
  · have hc' : (R:ℝ)≤dist (site v) (site (trajectory τ (mixedCoins M c r) n v)) := by
      rw [dist_comm]; exact hc.le
    rw [ite_eq_left hc,ite_eq_left hc']
  · rw [ite_eq_right hc]
    split_ifs
    · exact mul_nonneg (weight_nonneg (doubleRates p) (by intro i; cases i <;> exact hp _) c) (hW _)
    · rfl

end Heisenberg.Serial

open scoped Classical

open scoped Classical BigOperators
namespace Heisenberg.SparseWitness

variable (V : Type*)
def Tree : ℕ → Type _
  | 0 => V
  | n+1 => Tree n × Tree n
variable {V}

def root : {n : ℕ} → Tree V n → V
  | 0, t => t
  | _+1, t => root t.1

def leaves [DecidableEq V] : {n : ℕ} → Tree V n → Finset V
  | 0, t => {t}
  | _+1, t => leaves t.1 ∪ leaves t.2

lemma root_mem [DecidableEq V] {n : ℕ} (t : Tree V n) : root t ∈ leaves t := by
  induction n with
  | zero => exact Finset.mem_singleton_self _
  | succ n ih => exact Finset.mem_union_left _ (ih t.1)

variable [PseudoMetricSpace V]

def Admissible (h : ℕ → ℝ) : {n : ℕ} → Tree V n → Prop
  | 0, _ => True
  | n+1, t => Admissible h t.1 ∧ Admissible h t.2 ∧
      dist (root t.1) (root t.2) ≤ h (n+1) + 8 ∧
      ∀ a ∈ leaves t.1, ∀ b ∈ leaves t.2, h (n+1)/4 ≤ dist a b

lemma leaves_disjoint (h : ℕ → ℝ) (hp : ∀ n, 0 < h (n+1))
    {n : ℕ} (t : Tree V (n+1)) (ht : Admissible h t) :
    Disjoint (leaves t.1) (leaves t.2) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  have hh := ht.2.2.2 a ha a hb
  simp only [dist_self] at hh
  linarith [hp n]

lemma card_leaves (h : ℕ → ℝ) (hp : ∀ n, 0 < h (n+1))
    {n : ℕ} (t : Tree V n) (ht : Admissible h t) : (leaves t).card = 2^n := by
  induction n with
  | zero =>
    change ({(show V from t)} : Finset V).card = 1
    exact Finset.card_singleton _
  | succ n ih =>
    rw [leaves,Finset.card_union_of_disjoint (leaves_disjoint h hp t ht),
      ih t.1 ht.1,ih t.2 ht.2.1,pow_succ]
    omega

lemma small_diameter_count (h : ℕ → ℝ) (hm : Monotone h)
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n+1) (t : Tree V n) (ht : Admissible h t)
    (A : Set V) (hA : ∀ a ∈ A, ∀ b ∈ A, dist a b < h k/4) :
    ((leaves t).filter (fun a => a ∈ A)).card ≤ 2^(k-1) := by
  induction n with
  | zero =>
    have hk1 : k = 1 := by omega
    subst k
    change ({a ∈ ({(show V from t)} : Finset V) | a ∈ A}).card ≤ 1
    exact (Finset.card_filter_le _ _).trans (le_of_eq (Finset.card_singleton _))
  | succ n ih =>
    by_cases hk' : k = n+2
    · subst k
      calc
        _ ≤ (leaves t).card := Finset.card_filter_le _ _
        _ ≤ 2^(n+1) := by
          have hc : ∀ {j} (s : Tree V j), (leaves s).card ≤ 2^j := by
            intro j
            induction j with
            | zero =>
              intro s
              change ({(show V from s)} : Finset V).card ≤ 1
              exact le_of_eq (Finset.card_singleton _)
            | succ j hj =>
              intro s
              exact (Finset.card_union_le _ _).trans (by
                rw [pow_succ]
                linarith [hj s.1,hj s.2])
          exact hc t
        _ = 2^(n+2-1) := by congr 1
    · have hkn' : k ≤ n+1 := by omega
      let L := (leaves t.1).filter (fun a => a ∈ A)
      let R := (leaves t.2).filter (fun a => a ∈ A)
      have hone : L = ∅ ∨ R = ∅ := by
        by_cases hL : L = ∅
        · exact Or.inl hL
        · right
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro b hb
          obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr hL
          obtain ⟨hal,haA⟩ := Finset.mem_filter.mp ha
          obtain ⟨hbr,hbA⟩ := Finset.mem_filter.mp hb
          have hs := ht.2.2.2 a hal b hbr
          have hlt := hA a haA b hbA
          have hm' := hm (show k ≤ n+1 by omega)
          linarith
      rw [leaves,Finset.filter_union]
      change (L ∪ R).card ≤ _
      rcases hone with hL | hR
      · rw [hL,Finset.empty_union]
        exact ih hkn' t.2 ht.2.1
      · rw [hR,Finset.union_empty]
        exact ih hkn' t.1 ht.1

lemma ball_count (h : ℕ → ℝ) (hm : Monotone h)
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n+1) (t : Tree V n) (ht : Admissible h t)
    (z : V) (r : ℝ) (hr : r < h k/8) :
    ((leaves t).filter (fun a => dist a z ≤ r)).card ≤ 2^(k-1) := by
  apply small_diameter_count h hm hk hkn t ht {a | dist a z ≤ r}
  intro a ha b hb
  calc
    dist a b ≤ dist a z + dist b z := dist_triangle_right a b z
    _ < h k/4 := by dsimp at ha hb; linarith

lemma ball_meets_one_child (h : ℕ → ℝ) {n : ℕ} (t : Tree V (n+1))
    (ht : Admissible h t) (z : V) (r : ℝ) (hr : r < h (n+1)/8) :
    ((leaves t).filter (fun a => dist a z ≤ r)) =
      ((leaves t.1).filter (fun a => dist a z ≤ r)) ∨
    ((leaves t).filter (fun a => dist a z ≤ r)) =
      ((leaves t.2).filter (fun a => dist a z ≤ r)) := by
  let L := (leaves t.1).filter (fun a => dist a z ≤ r)
  let R := (leaves t.2).filter (fun a => dist a z ≤ r)
  rw [leaves,Finset.filter_union]
  change L ∪ R = L ∨ L ∪ R = R
  by_cases hL : L = ∅
  · exact Or.inr (by rw [hL,Finset.empty_union])
  · left
    have hR : R = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro b hb
      obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr hL
      obtain ⟨ha,har⟩ := Finset.mem_filter.mp ha
      obtain ⟨hb,hbr⟩ := Finset.mem_filter.mp hb
      have hs := ht.2.2.2 a ha b hb
      have hd := dist_triangle_right a b z
      linarith
    rw [hR,Finset.union_empty]

def Sparse (α L : ℝ) (F : Finset V) : Prop :=
  ∀ z r, 0 ≤ r → (((F.filter (fun a => dist a z ≤ r)).card : ℕ) : ℝ) ≤ L*(1+r)^α

theorem admissible_sparse (h : ℕ → ℝ) (hp : ∀ n, 0 < h (n+1))
    (α : ℝ) (hα : 0 ≤ α)
    (hg : ∀ n, (2:ℝ)^(n+1) ≤ (1+h (n+1)/8)^α)
    {n : ℕ} (t : Tree V n) (ht : Admissible h t) : Sparse α 1 (leaves t) := by
  intro z r hr
  simp only [one_mul]
  induction n with
  | zero =>
    have hc : ((leaves t).filter (fun a => dist a z ≤ r)).card ≤ 1 := by
      exact (Finset.card_filter_le _ _).trans (le_of_eq (card_leaves h hp t ht))
    calc
      _ ≤ (1:ℝ) := by exact_mod_cast hc
      _ ≤ (1+r)^α := Real.one_le_rpow (by linarith) hα
  | succ n ih =>
    by_cases hh : r < h (n+1)/8
    · rcases ball_meets_one_child h t ht z r hh with he | he
      · rw [he]; exact ih t.1 ht.1
      · rw [he]; exact ih t.2 ht.2.1
    · calc
        _ ≤ ((leaves t).card:ℝ) := by
          exact_mod_cast (Finset.card_filter_le (leaves t) (fun a => dist a z ≤ r))
        _ = (2:ℝ)^(n+1) := by rw [card_leaves h hp t ht]; norm_cast
        _ ≤ (1+h (n+1)/8)^α := hg n
        _ ≤ (1+r)^α := Real.rpow_le_rpow (by linarith [hp n]) (by linarith) hα

lemma geometric_scale_growth (b α : ℝ) (hb : 1 ≤ b) (hα : 0 ≤ α)
    (hba : 2 ≤ b^α) (n : ℕ) :
    (2:ℝ)^(n+1) ≤ (1+(16*b^(n+1))/8)^α := by
  calc
    _ ≤ (b^α)^(n+1) := pow_le_pow_left₀ (by positivity) hba _
    _ = (b^(n+1))^α := by rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith),
      mul_comm,Real.rpow_mul (by linarith),Real.rpow_natCast]
    _ ≤ (1+(16*b^(n+1))/8)^α := by
      apply Real.rpow_le_rpow (by positivity) _ hα
      have : 0 ≤ b^(n+1) := by positivity
      linarith

end Heisenberg.SparseWitness

end

end OAI
