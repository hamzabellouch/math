import OAI.MathematicalPhysics.Heisenberg.QuietSweeps

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical
open scoped Classical
open Filter
open scoped Classical
open scoped Classical
open Filter Topology
open scoped RealInnerProductSpace Classical

namespace Heisenberg.Exposure
open Heisenberg.MeshPair
variable {T V : Type*} [Fintype T] [Fintype V] [DecidableEq V]

omit [Fintype T] in
lemma exposedStep_substochastic (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ) (hp : ∀ i,0≤p i ∧ p i≤1) (t : T) :
    Heisenberg.MatrixContraction.DoublySubstochastic (exposedStep s a b base P I p t) :=
  residualBetween_substochastic _ _ _ _ _ _ _ (hp t).1 (hp t).2

omit [Fintype T] in
lemma exposedSweep_contraction (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ) (hp : ∀ i,0≤p i ∧ p i≤1)
    (r : ℕ → T) (n : ℕ) (v : EuclideanSpace ℝ V) :
    ‖exposedSweep s a b base P I p r n v‖≤‖v‖ := by
  induction n with
  | zero => rfl
  | succ n ih => exact (euclideanMap_contraction _ (exposedStep_substochastic s a b base P I p hp _) _).trans ih

omit [Fintype T] in

theorem exposedSweep_energy (s : Equiv.Perm T) (a b : T → V) (r : ℕ → T) (n : ℕ)
    (hr : ∀ i,i<n → r (i+1)=s (r i)) (hab : ∀ i,i<n → a (r i)≠b (r i))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ t in 𝓝 (0:ℝ),∀ (base : T → Bool) (P : Set (T×V)) (I : Set V) (v : EuclideanSpace ℝ V),
      (∀ i,i<n → base (r i)=false) →
      (∀ j,j∉holeCut s (fun i => Equiv.swap (a i) (b i)) base P (r 0)∩I → v.ofLp j=0) →
      |‖exposedSweep s a b base P I (fun _ => t/2) r n v‖^2-‖v‖^2+
        t*quietEnergy (holeCut s (fun i => Equiv.swap (a i) (b i)) base P (r 0)) (a ∘ r) (b ∘ r) n v|
        ≤ ε * |t| * ‖v‖^2 := by
  filter_upwards [quietSweep_energy (a ∘ r) (b ∘ r) n hab hε] with t ht
  intro base P I v hb hv
  rw [exposedSweep_quiet s a b base P I r n t hr hb hab v]
  exact ht _ _ v hv

omit [Fintype T] [Fintype V] [DecidableEq V] in
lemma quietEnergy_le_card (H : Set V) (a b : ℕ → V) (n : ℕ) (v : EuclideanSpace ℝ V)
    (hv : ∀ j,0≤v.ofLp j ∧ v.ofLp j≤1) : quietEnergy H a b n v≤n := by
  apply le_trans (Finset.sum_le_sum (fun i _ => ?_)) (by simp : (∑ _i∈Finset.range n,(1:ℝ))=n).le
  split_ifs
  · nlinarith [(hv (a i)).1,(hv (a i)).2,(hv (b i)).1,(hv (b i)).2,
      mul_nonneg (hv (a i)).1 (hv (b i)).1]
  · norm_num

omit [Fintype T] in

theorem exposedSweep_loss (s : Equiv.Perm T) (a b : T → V) (r : ℕ → T) (n : ℕ)
    (hr : ∀ i,i<n → r (i+1)=s (r i)) (hab : ∀ i,i<n → a (r i)≠b (r i))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ t in 𝓝 (0:ℝ),0≤t → t≤2 →
      ∀ (base : T → Bool) (P : Set (T×V)) (I : Set V) (v : EuclideanSpace ℝ V),
      (∀ j,0≤v.ofLp j ∧ v.ofLp j≤1) →
      (∀ j,j∉holeCut s (fun i => Equiv.swap (a i) (b i)) base P (r 0)∩I → v.ofLp j=0) →
      t*quietEnergy (holeCut s (fun i => Equiv.swap (a i) (b i)) base P (r 0)) (a ∘ r) (b ∘ r) n v ≤
        ‖v‖^2-‖exposedSweep s a b base P I (fun _ => t/2) r n v‖^2+
        ε*t*‖v‖^2+(if ∃ i,i<n ∧ base (r i)=true then t*n else 0) := by
  filter_upwards [exposedSweep_energy s a b r n hr hab hε] with t ht
  intro ht0 ht2 base P I v hv hvI
  have hc := exposedSweep_contraction s a b base P I (fun _ => t/2)
    (fun _ => ⟨by positivity,by linarith⟩) r n v
  have hl : 0≤‖v‖^2-‖exposedSweep s a b base P I (fun _ => t/2) r n v‖^2 := by
    nlinarith [norm_nonneg v,norm_nonneg (exposedSweep s a b base P I (fun _ => t/2) r n v)]
  by_cases hb : ∃ i,i<n ∧ base (r i)=true
  · rw [ite_eq_left hb]
    have he := mul_le_mul_of_nonneg_left (quietEnergy_le_card (holeCut s (fun i => Equiv.swap (a i) (b i)) base P (r 0)) (a ∘ r) (b ∘ r) n v hv) ht0
    have hz : 0≤ε*t*‖v‖^2 := by positivity
    linarith
  · rw [ite_eq_right hb]
    have hquiet : ∀ i,i<n → base (r i)=false := by
      intro i hi
      cases he : base (r i)
      · rfl
      · exact (hb ⟨i,hi,he⟩).elim
    have he := (abs_le.mp (ht base P I v hquiet hvI)).2
    rw [abs_of_nonneg ht0] at he
    linarith

end Heisenberg.Exposure

open scoped BigOperators Classical
namespace Heisenberg.Bernoulli
variable {I : Type*} [Fintype I]

def weight (p : I → ℝ) (c : I → Bool) : ℝ := ∏ i, if c i then p i else 1-p i

def join (i : I) (b : Bool) (d : {j // j ≠ i} → Bool) : I → Bool :=
  (Equiv.funSplitAt i Bool).symm (b,d)

omit [Fintype I] in
@[simp] lemma join_at (i : I) (b : Bool) (d : {j // j ≠ i} → Bool) :
    join i b d i = b := by simp [join,Equiv.funSplitAt]

omit [Fintype I] in
@[simp] lemma join_ne (i : I) (b : Bool) (d : {j // j ≠ i} → Bool) (j : {j // j ≠ i}) :
    join i b d j = d j := by simp [join,Equiv.funSplitAt,j.property]

omit [Fintype I] in
lemma join_update (i : I) (b b' : Bool) (d : {j // j ≠ i} → Bool) :
    Function.update (join i b d) i b' = join i b' d := by
  funext j
  by_cases h : j = i
  · subst j; simp
  · simpa only [Function.update_of_ne h] using (join_ne i b d ⟨j,h⟩).trans (join_ne i b' d ⟨j,h⟩).symm

lemma weight_join (p : I → ℝ) (i : I) (b : Bool) (d : {j // j ≠ i} → Bool) :
    weight p (join i b d) = (if b then p i else 1-p i) * weight (fun j : {j // j ≠ i} => p j) d := by
  unfold weight
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  simp only [join_at,join_ne]

lemma sum_split (p : I → ℝ) (F : (I → Bool) → ℝ) (i : I) :
    (∑ c, weight p c * F c) =
      ∑ d : {j // j ≠ i} → Bool, weight (fun j : {j // j ≠ i} => p j) d *
        ((1-p i)*F (join i false d) + p i*F (join i true d)) := by
  rw [← (Equiv.funSplitAt i Bool).symm.sum_comp]
  change (∑ q : Bool × ({j // j ≠ i} → Bool), weight p (join i q.1 q.2) * F (join i q.1 q.2)) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, weight_join, Bool.false_eq_true, ↓reduceIte]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  ring

lemma scalar_bound {κ p W₀ W₁ : ℝ} (hκ : 1 ≤ κ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hW₁ : 0 ≤ W₁) (hW : W₁ ≤ κ*W₀) :
    W₁ ≤ κ*((1-p)*W₀+p*W₁) := by
  have h1 := mul_le_mul_of_nonneg_left hW (sub_nonneg.mpr hp1)
  have h2 := mul_le_mul_of_nonneg_left (show W₁ ≤ κ*W₁ by nlinarith) hp
  nlinarith

lemma weight_nonneg (p : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (c : I → Bool) :
    0 ≤ weight p c := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith [(hp i).1,(hp i).2]

lemma one_coin (p : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) {κ : ℝ} (hκ : 1 ≤ κ)
    (W G : (I → Bool) → ℝ) (i : I)
    (hW : ∀ c, 0 ≤ W c) (hG : ∀ c, 0 ≤ G c)
    (hins : ∀ c, W (Function.update c i true) ≤ κ*W (Function.update c i false))
    (hGi : ∀ c, G (Function.update c i true) = G (Function.update c i false)) :
    (∑ c, weight p c * ((if c i then W c else 0)*G c)) ≤
      κ*p i * ∑ c, weight p c*(W c*G c) := by
  rw [sum_split, sum_split, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d _
  have hi := hins (join i false d)
  have hg := hGi (join i false d)
  simp only [join_update] at hi hg
  simp only [join_at,Bool.false_eq_true,↓reduceIte,zero_mul,mul_zero,zero_add]
  rw [hg]
  have hb := scalar_bound hκ (hp i).1 (hp i).2 (hW _) hi
  have hn := mul_le_mul_of_nonneg_left hb (mul_nonneg (hp i).1 (hG (join i false d)))
  have hf := mul_le_mul_of_nonneg_left hn
    (weight_nonneg (fun j : {j // j ≠ i} => p j) (fun j => hp j) d)
  nlinarith

def test (s : Finset I) (c : I → Bool) : ℝ := if ∀ i ∈ s, c i = true then 1 else 0

lemma test_nonneg (s : Finset I) (c : I → Bool) : 0 ≤ test s c := by
  unfold test; split_ifs <;> norm_num

lemma test_update {s : Finset I} {i : I} (hi : i ∉ s) (c : I → Bool) (b : Bool) :
    test s (Function.update c i b) = test s c := by
  unfold test
  congr 1
  apply propext
  constructor <;> intro h j hj
  · have hjn : j ≠ i := by intro he; subst j; exact hi hj
    simpa only [Function.update_of_ne hjn] using h j hj
  · rw [Function.update_of_ne (show j ≠ i by intro he; subst j; exact hi hj)]
    exact h j hj

lemma test_insert (s : Finset I) (i : I) (c : I → Bool) :
    test (insert i s) c = (if c i then 1 else 0)*test s c := by
  simp only [test,Finset.forall_mem_insert]
  split_ifs <;> simp_all

theorem factorial_bound (p : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) {κ : ℝ} (hκ : 1 ≤ κ)
    (W : (I → Bool) → ℝ) (hW : ∀ c, 0 ≤ W c)
    (hins : ∀ c i, W (Function.update c i true) ≤ κ*W (Function.update c i false))
    (s : Finset I) :
    (∑ c, weight p c*(W c*test s c)) ≤ (∏ i ∈ s, κ*p i) * ∑ c, weight p c*W c := by
  induction s using Finset.induction_on with
  | empty => simp [test]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    have hc := one_coin p hp hκ W (test s) i hW (test_nonneg s)
      (fun c => hins c i) (fun c => by rw [test_update hi,test_update hi])
    have he : (∑ c, weight p c*(W c*test (insert i s) c)) =
        ∑ c, weight p c*((if c i then W c else 0)*test s c) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [test_insert]
      cases c i <;> simp
    rw [he]
    exact hc.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ih (mul_nonneg (by linarith) (hp i).1))

theorem factorial_bound_rates (p κ : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hκ : ∀ i,1 ≤ κ i) (W : (I → Bool) → ℝ) (hW : ∀ c, 0 ≤ W c)
    (hins : ∀ c i, W (Function.update c i true) ≤ κ i*W (Function.update c i false))
    (s : Finset I) :
    (∑ c, weight p c*(W c*test s c)) ≤ (∏ i ∈ s, κ i*p i) * ∑ c, weight p c*W c := by
  induction s using Finset.induction_on with
  | empty => simp [test]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    have hc := one_coin p hp (hκ i) W (test s) i hW (test_nonneg s)
      (fun c => hins c i) (fun c => by rw [test_update hi,test_update hi])
    have he : (∑ c, weight p c*(W c*test (insert i s) c)) =
        ∑ c, weight p c*((if c i then W c else 0)*test s c) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [test_insert]
      cases c i <;> simp
    rw [he]
    exact hc.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ih
        (mul_nonneg (by linarith [hκ i]) (hp i).1))

theorem polynomial_bound (p κ : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hκ : ∀ i,1 ≤ κ i) (W : (I → Bool) → ℝ) (hW : ∀ c, 0 ≤ W c)
    (hins : ∀ c i, W (Function.update c i true) ≤ κ i*W (Function.update c i false))
    (a : Finset I → ℝ) (ha : ∀ s,0 ≤ a s) :
    (∑ c, weight p c * W c * (∑ s, a s*test s c)) ≤
      (∑ s, a s*(∏ i ∈ s, κ i*p i)) * ∑ c,weight p c*W c := by
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm,Finset.sum_comm (f := fun x => fun i => (a i * ∏ j ∈ i, κ j * p j) * (weight p x * W x))]
  apply Finset.sum_le_sum
  intro s _
  have hh := mul_le_mul_of_nonneg_left (factorial_bound_rates p κ hp hκ W hW hins s) (ha s)
  simpa only [Finset.mul_sum,Finset.sum_mul,mul_assoc,mul_left_comm] using hh

lemma test_eq_prod (s : Finset I) (c : I → Bool) :
    test s c = ∏ i ∈ s, if c i then (1:ℝ) else 0 := by
  induction s using Finset.induction_on with
  | empty => simp [test]
  | @insert i s hi ih => rw [test_insert,Finset.prod_insert hi,ih]

lemma weight_test_sum (p : I → ℝ) (s : Finset I) :
    (∑ c,weight p c*test s c) = ∏ i ∈ s,p i := by
  have he (c : I → Bool) : weight p c*test s c =
      ∏ i, if c i then p i else if i ∈ s then 0 else 1-p i := by
    rw [test_eq_prod]
    have ht : (∏ i ∈ s, if c i then (1:ℝ) else 0) = ∏ i,if i ∈ s then (if c i then (1:ℝ) else 0) else 1 := by
      simp only [Finset.prod_ite_mem,Finset.univ_inter]
    rw [ht,weight,←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ s <;> cases c i <;> simp [hi]
  simp_rw [he]
  rw [←Fintype.prod_sum (fun i (b : Bool) => if b then p i else if i ∈ s then 0 else 1-p i)]
  simp only [Fintype.sum_bool,Bool.false_eq_true,↓reduceIte]
  have he : (fun i => p i + if i ∈ s then (0:ℝ) else 1-p i) = fun i => if i ∈ s then p i else 1 := by
    funext i
    split_ifs <;> ring
  rw [he]
  simp only [Finset.prod_ite_mem,Finset.univ_inter]

end Heisenberg.Bernoulli
end

end OAI
