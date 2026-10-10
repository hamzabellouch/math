import OAI.MathematicalPhysics.Heisenberg.ExposedEnergy

namespace OAI

noncomputable section

open Matrix
open Filter
open scoped Classical
open Filter Topology
open scoped RealInnerProductSpace Classical
open scoped BigOperators Classical

namespace Heisenberg.Cycle
open Equiv
variable {V : Type*} [Fintype V]

lemma weight_left_swap_le (π : Perm V) (P : Set V) (a b : V) :
    (2:ℝ)^missingCount (swap a b * π) P ≤ 2*(2:ℝ)^missingCount π P := by
  have he : swap a b * π = π * swap (π.symm a) (π.symm b) := by
    apply Equiv.ext
    intro x
    by_cases ha : x = π.symm a
    · subst x; simp
    by_cases hb : x = π.symm b
    · subst x; simp
    have ha' : π x ≠ a := fun h => ha (π.injective (h.trans (π.apply_symm_apply a).symm))
    have hb' : π x ≠ b := fun h => hb (π.injective (h.trans (π.apply_symm_apply b).symm))
    simp [Perm.mul_apply,swap_apply_of_ne_of_ne ha hb,swap_apply_of_ne_of_ne ha' hb']
  rw [he]
  exact weight_swap_le π P _ _
end Heisenberg.Cycle

namespace Heisenberg.Exposure

section
open Heisenberg.Cycle Heisenberg.LayeredExchange Heisenberg.Bernoulli
variable {T V : Type*} [Fintype T] [Fintype V]

omit [Fintype T] [Fintype V] in
lemma layerHistory_insert (s : Equiv.Perm T) (a b : T → V) (c : T → Bool) (t : T) :
    layerHistory s (fun j => Equiv.swap (a j) (b j)) (Function.update c t true) =
      Equiv.swap (s t,a t) (s t,b t) *
        layerHistory s (fun j => Equiv.swap (a j) (b j)) (Function.update c t false) := by
  let σ := fun j => if Function.update c t false j then Equiv.swap (a j) (b j) else 1
  have he : (fun j => if Function.update c t true j then Equiv.swap (a j) (b j) else 1) =
      Function.update σ t (Equiv.swap (a t) (b t)*σ t) := by
    funext j
    by_cases h : j=t
    · subst j
      simp [σ]
    · simp [Function.update_of_ne h,σ]
  change wiring s _ = _ * wiring s σ
  rw [he,wiring_update_swap]

def layerWeight (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V)) (c : T → Bool) : ℝ :=
  2^missingCount (layerHistory s (fun j => Equiv.swap (a j) (b j)) c) P

omit [Fintype T] [Fintype V] in
lemma layerWeight_nonneg (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V)) (c : T → Bool) :
    0 ≤ layerWeight s a b P c := by unfold layerWeight; positivity

omit [Fintype T] [Fintype V] in
lemma layerWeight_one_le (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V)) (c : T → Bool) :
    1 ≤ layerWeight s a b P c := one_le_pow₀ (by norm_num)

lemma layerWeight_insertion (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V))
    (c : T → Bool) (t : T) :
    layerWeight s a b P (Function.update c t true) ≤
      2*layerWeight s a b P (Function.update c t false) := by
  unfold layerWeight
  have h := weight_left_swap_le (layerHistory s (fun j => Equiv.swap (a j) (b j)) (Function.update c t false)) P (s t,a t) (s t,b t)
  convert h using 1
  congr 2
  exact (layerHistory_insert s a b c t).trans (by
    congr 1
    apply Equiv.ext
    intro x
    simp only [Equiv.swap_apply_def]
    split_ifs <;> rfl)

def layerPartition (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V)) (p : T → ℝ) : ℝ :=
  ∑ c,weight p c*layerWeight s a b P c

def layerMass (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V)) (p : T → ℝ) (c : T → Bool) : ℝ :=
  weight p c*layerWeight s a b P c / layerPartition s a b P p

lemma coin_weight_sum (p : T → ℝ) : (∑ c,weight p c)=1 := by
  simpa [Bernoulli.test] using weight_test_sum p ∅

omit [Fintype V] in
lemma layerPartition_one_le (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V))
    (p : T → ℝ) (hp : ∀ t,0≤p t ∧ p t≤1) : 1≤layerPartition s a b P p := by
  rw [←coin_weight_sum p]
  exact Finset.sum_le_sum fun c _ => le_mul_of_one_le_right (weight_nonneg p hp c) (layerWeight_one_le s a b P c)

omit [Fintype V] in
lemma layerMass_nonneg (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V))
    (p : T → ℝ) (hp : ∀ t,0≤p t ∧ p t≤1) (c : T → Bool) : 0≤layerMass s a b P p c := by
  exact div_nonneg (mul_nonneg (weight_nonneg p hp c) (layerWeight_nonneg s a b P c))
    (le_trans (by norm_num) (layerPartition_one_le s a b P p hp))

omit [Fintype V] in
lemma layerMass_sum (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V))
    (p : T → ℝ) (hp : ∀ t,0≤p t ∧ p t≤1) : (∑ c,layerMass s a b P p c)=1 := by
  simp only [layerMass,←Finset.sum_div]
  change layerPartition s a b P p / layerPartition s a b P p = 1
  exact div_self (ne_of_gt (lt_of_lt_of_le (by norm_num) (layerPartition_one_le s a b P p hp)))

theorem layer_factorial_bound (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V))
    (p : T → ℝ) (hp : ∀ t,0≤p t ∧ p t≤1) (F : Finset T) :
    (∑ c,if ∀ i ∈ F,c i=true then layerMass s a b P p c else 0) ≤ ∏ i ∈ F,2*p i := by
  have hz : 0<layerPartition s a b P p :=
    lt_of_lt_of_le (by norm_num) (layerPartition_one_le s a b P p hp)
  have h := factorial_bound p hp (κ:=2) (by norm_num) (layerWeight s a b P)
    (layerWeight_nonneg s a b P) (layerWeight_insertion s a b P) F
  have he : (∑ c,if ∀ i ∈ F,c i=true then layerMass s a b P p c else 0) =
      (∑ c,weight p c*(layerWeight s a b P c*Bernoulli.test F c))/layerPartition s a b P p := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro c _
    unfold Bernoulli.test layerMass
    split_ifs <;> simp
  rw [he]
  exact (div_le_iff₀ hz).mpr h

theorem layer_nonquiet_bound (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V))
    (p : T → ℝ) (hp : ∀ t,0≤p t ∧ p t≤1) (F : Finset T) :
    (∑ c,if ∃ i ∈ F,c i=true then layerMass s a b P p c else 0) ≤ ∑ i ∈ F,2*p i := by
  have h : ∀ c,(if ∃ i ∈ F,c i=true then layerMass s a b P p c else 0) ≤
      ∑ i ∈ F,if c i=true then layerMass s a b P p c else 0 := by
    intro c
    by_cases hc : ∃ i ∈ F,c i=true
    · obtain ⟨i,hi,hci⟩ := hc
      rw [ite_eq_left ⟨i,hi,hci⟩]
      calc
        _ = if c i=true then layerMass s a b P p c else 0 := by rw [ite_eq_left hci]
        _ ≤ _ := Finset.single_le_sum (f := fun j => if c j=true then layerMass s a b P p c else 0) (fun j _ => by split_ifs; exact layerMass_nonneg s a b P p hp c; exact le_rfl) hi
    · rw [ite_eq_right hc]
      exact Finset.sum_nonneg (fun j _ => by split_ifs; exact layerMass_nonneg s a b P p hp c; exact le_rfl)
  calc
    _ ≤ ∑ c,∑ i ∈ F,if c i=true then layerMass s a b P p c else 0 := Finset.sum_le_sum (fun c _ => h c)
    _ = ∑ i ∈ F,∑ c,if c i=true then layerMass s a b P p c else 0 := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun i _ => by simpa using layer_factorial_bound s a b P p hp {i})

end

open Heisenberg.MeshPair Heisenberg.Bernoulli
variable {T V : Type*} [Fintype T] [Fintype V]

omit [Fintype T] in
lemma bounded_euclidean_sq (v : EuclideanSpace ℝ V)
    (hv : ∀ j,0≤v.ofLp j ∧ v.ofLp j≤1) : ‖v‖^2≤Fintype.card V := by
  rw [EuclideanSpace.norm_sq_eq]
  apply le_trans (Finset.sum_le_sum (fun j _ => ?_)) (by simp : (∑ _j : V,(1:ℝ))=Fintype.card V).le
  rw [Real.norm_eq_abs,sq_abs]
  nlinarith [(hv j).1,(hv j).2]

theorem tilted_nonquiet_error (s : Equiv.Perm T) (a b : T → V)
    (P : Set (T×V)) (p : T → ℝ) (hp : ∀ i,0≤p i ∧ p i≤1)
    (r : ℕ → T) (n : ℕ) {t : ℝ} (ht : 0≤t)
    (hrate : ∀ i,i<n → p (r i)=t/2) :
    (∑ base,layerMass s a b P p base *
      (if ∃ i,i<n ∧ base (r i)=true then t*n else 0)) ≤ t^2*n^2 := by
  let F := (Finset.range n).image r
  have he (base : T → Bool) : (∃ i,i<n ∧ base (r i)=true) ↔ ∃ j∈F,base j=true := by
    simp only [F,Finset.mem_image,Finset.mem_range]
    constructor
    · rintro ⟨i,hi,hb⟩; exact ⟨r i,⟨i,hi,rfl⟩,hb⟩
    · rintro ⟨j,⟨i,hi,rfl⟩,hb⟩; exact ⟨i,hi,hb⟩
  have hF : F.card≤n := (Finset.card_image_le).trans (by simp)
  have hFr : ∑ j∈F,2*p j = t*F.card := by
    calc
      _ = ∑ _j∈F,t := Finset.sum_congr rfl (by
        intro j hj
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
        rw [hrate i (Finset.mem_range.mp hi)]
        ring)
      _ = _ := by simp [mul_comm]
  have hq := layer_nonquiet_bound s a b P p hp F
  rw [hFr] at hq
  have hqn : (∑ base,if ∃ j∈F,base j=true then layerMass s a b P p base else 0)≤t*n := by
    exact hq.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hF) ht)
  have hh := mul_le_mul_of_nonneg_right hqn (show 0≤t*(n:ℝ) by positivity)
  rw [Finset.sum_mul] at hh
  calc
    _ = ∑ base,(if ∃ j∈F,base j=true then layerMass s a b P p base else 0)*(t*n) := by
      apply Finset.sum_congr rfl
      intro base _
      simp only [he base]
      split_ifs <;> ring
    _ ≤ t*n*(t*n) := hh
    _ = _ := by ring

omit [Fintype T] in
lemma exposedSweep_coins (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p q : T → ℝ) (r : ℕ → T) (n : ℕ)
    (hpq : ∀ i,i<n → p (r i)=q (r i)) (v : EuclideanSpace ℝ V) :
    exposedSweep s a b base P I p r n v=exposedSweep s a b base P I q r n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [exposedSweep,exposedSweep,ih (fun i hi => hpq i (by omega))]
    simp only [exposedStep,hpq n (by omega)]

theorem tilted_sweep_energy (s : Equiv.Perm T) (a b : T → V) (r : ℕ → T) (n : ℕ)
    (hr : ∀ i,i<n → r (i+1)=s (r i)) (hab : ∀ i,i<n → a (r i)≠b (r i))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ t in 𝓝 (0:ℝ),0≤t → t≤2 →
      ∀ (p : T → ℝ) (_hp : ∀ i,0≤p i ∧ p i≤1) (_hrate : ∀ i,i<n → p (r i)=t/2)
        (P : Set (T×V)) (I : Set V) (v : (T → Bool) → EuclideanSpace ℝ V),
      (∀ base j,0≤(v base).ofLp j ∧ (v base).ofLp j≤1) →
      (∀ base j,j∉holeCut s (fun i => Equiv.swap (a i) (b i)) base P (r 0)∩I →
        (v base).ofLp j=0) →
      (∑ base,layerMass s a b P p base *
        (t*quietEnergy (holeCut s (fun i => Equiv.swap (a i) (b i)) base P (r 0))
          (a ∘ r) (b ∘ r) n (v base))) ≤
        (∑ base,layerMass s a b P p base *
          (‖v base‖^2-‖exposedSweep s a b base P I p r n (v base)‖^2))+
        ε*t*Fintype.card V+t^2*n^2 := by
  filter_upwards [exposedSweep_loss s a b r n hr hab hε] with t ht
  intro ht0 ht2 p hp hrate P I v hv hvI
  have hs := layerMass_sum s a b P p hp
  have hc (base : T → Bool) := exposedSweep_coins s a b base P I p (fun _=>t/2) r n hrate (v base)
  have hl (base : T → Bool) := ht ht0 ht2 base P I (v base) (hv base) (hvI base)
  simp only [←hc] at hl
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun base _ =>
    mul_le_mul_of_nonneg_left (hl base)
      (layerMass_nonneg s a b P p hp base))
  have he : (∑ base,layerMass s a b P p base*(ε*t*‖v base‖^2))≤
      ε*t*Fintype.card V := by
    calc
      _ ≤ ∑ base,layerMass s a b P p base*(ε*t*Fintype.card V) :=
        Finset.sum_le_sum (fun base _ => mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (bounded_euclidean_sq (v base) (hv base))
            (by positivity)) (layerMass_nonneg s a b P p hp base))
      _ = _ := by rw [←Finset.sum_mul,hs,one_mul]
  have hn := tilted_nonquiet_error s a b P p hp r n ht0 hrate
  simp only [mul_add,Finset.sum_add_distrib] at h
  linarith

end Heisenberg.Exposure

open scoped Classical
namespace Heisenberg.Geometry
abbrev Site (d : ℕ) := Fin d → ℤ

def Step {d : ℕ} (x y : Site d) : Prop :=
  ∃ j, (y j = x j + 1 ∨ x j = y j + 1) ∧ ∀ k, k ≠ j → y k = x k

def Box {d : ℕ} (r : ℤ) : Set (Site d) := {x | ∀ j, |x j| ≤ r}
def Shell {d : ℕ} (r : ℤ) : Set (Site d) := {x | x ∈ Box r ∧ ∃ j, |x j| = r}

def Reach {d : ℕ} (U : Set (Site d)) (x y : Site d) : Prop :=
  Relation.ReflTransGen (fun a b => Step a b ∧ a ∈ U ∧ b ∈ U) x y

lemma step_symm {d : ℕ} {x y : Site d} (h : Step x y) : Step y x := by
  obtain ⟨j, h, hj⟩ := h
  exact ⟨j, h.symm, fun k hk => (hj k hk).symm⟩

lemma reach_refl {d : ℕ} (U : Set (Site d)) (x : Site d) : Reach U x x :=
  Relation.ReflTransGen.refl

lemma reach_trans {d : ℕ} {U : Set (Site d)} {x y z : Site d}
    (hxy : Reach U x y) (hyz : Reach U y z) : Reach U x z := hxy.trans hyz

lemma reach_symm {d : ℕ} {U : Set (Site d)} {x y : Site d}
    (hxy : Reach U x y) : Reach U y x := by
  induction hxy with
  | refl => exact reach_refl U x
  | @tail b c hab hbc ih =>
    exact (Relation.ReflTransGen.single ⟨step_symm hbc.1, hbc.2.2, hbc.2.1⟩).trans ih

lemma reach_mono {d : ℕ} {U W : Set (Site d)} {x y : Site d}
    (hUW : U ⊆ W) (hxy : Reach U x y) : Reach W x y :=
  Relation.ReflTransGen.mono (fun _ _ h => ⟨h.1, hUW h.2.1, hUW h.2.2⟩) x y hxy

lemma step_update_succ {d : ℕ} (x : Site d) (j : Fin d) (a : ℤ) :
    Step (Function.update x j a) (Function.update x j (a + 1)) := by
  refine ⟨j, Or.inl ?_, ?_⟩
  · simp
  · intro k hk
    simp [Function.update_of_ne hk]

lemma reach_axis_nat {d : ℕ} (U : Set (Site d)) (x : Site d) (j : Fin d)
    (a : ℤ) (n : ℕ) (hU : ∀ k : ℕ, k ≤ n → Function.update x j (a + k) ∈ U) :
    Reach U (Function.update x j a) (Function.update x j (a + n)) := by
  induction n with
  | zero => simpa using reach_refl U (Function.update x j a)
  | succ n ih =>
    apply reach_trans (ih (fun k hk => hU k (by omega)))
    apply Relation.ReflTransGen.single
    refine ⟨?_, hU n (by omega), hU (n + 1) le_rfl⟩
    simpa [Nat.cast_add, Nat.cast_one, add_assoc] using step_update_succ x j (a + n)

lemma reach_axis {d : ℕ} (U : Set (Site d)) (x : Site d) (j : Fin d)
    (a b : ℤ) (hU : ∀ t, min a b ≤ t → t ≤ max a b → Function.update x j t ∈ U) :
    Reach U (Function.update x j a) (Function.update x j b) := by
  wlog hab : a ≤ b generalizing a b
  · exact reach_symm (this b a (by simpa [min_comm, max_comm] using hU) (by omega))
  have he : a + ((b - a).toNat : ℤ) = b := by omega
  rw [← he]
  apply reach_axis_nat
  intro k hk
  apply hU
  · simp only [min_eq_left hab]; omega
  · simp only [max_eq_right hab]; omega

end Heisenberg.Geometry

end

end OAI
