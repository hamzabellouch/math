import Mathlib
import OAI.Combinatorics.SharpRamsey.Reciprocal.ReciprocalCurrent

namespace OAI

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.Selection
open scoped BigOperators Classical
open Finset
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B]
lemma Law.prod_rectangle_event (p : Law A) (q : Law B) (S : Finset A) (T : Finset B) :
    (p.prod q).event (S ×ˢ T) = p.event S*q.event T := by
  simp only [Law.event, Law.prod, sum_product, sum_mul, mul_sum]
  exact sum_comm

lemma Law.event_filter_le_add (p : Law A) (P Q : A → Prop) :
    p.event (univ.filter P) ≤ p.event (univ.filter (fun a => P a ∧ ¬Q a)) +
      p.event (univ.filter (fun a => P a ∧ Q a)) := by
  simp only [Law.event, sum_filter, ← sum_add_distrib]
  apply sum_le_sum
  intro a _
  by_cases hp : P a <;> by_cases hq : Q a <;> simp [hp,hq]

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

def firstCore (p : Law (A × B)) (v : B → V) (ρ : ℝ) (a : A) : Submodule K V :=
  (p.condSnd a).core v ρ

def secondCore (p : Law (A × B)) (w : A → Module.Dual K V) (ρ : ℝ) (y : B) :
    Submodule K (Module.Dual K V) := (p.condFst y).core w ρ

def coreContained (p q : Law (A × B)) (v : B → V) (w : A → Module.Dual K V)
    (ρ : ℝ) (a : A) (y : B) : Prop :=
  secondCore q w ρ y ≤ (firstCore (K := K) p v ρ a).dualAnnihilator

def coreCollision (p q : Law (A × B)) (v : B → V) (w : A → Module.Dual K V)
    (ρ : ℝ) (goodA : A → Prop) (goodB : B → Prop) (z : (A × B) × (A × B)) : Prop :=
  goodA z.1.1 ∧ goodB z.2.2 ∧ w z.1.1 (v z.2.2) = 0 ∧
    coreContained p q v w ρ z.1.1 z.2.2 ∧
    v z.1.2 ∈ firstCore (K := K) p v ρ z.1.1 ∧ w z.2.1 ∈ secondCore q w ρ z.2.2

lemma core_capture_product (p q : Law (A × B)) (v : B → V)
    (w : A → Module.Dual K V) {ρ c : ℝ} (hρ : 0 ≤ ρ) (hc : 0 ≤ c)
    (hd : c ≤ 1-(Module.finrank K V:ℝ)*ρ) (a : A) (y : B) :
    c^2 ≤ ((p.condSnd a).prod (q.condFst y)).event
      (univ.filter (fun bc : B × A => v bc.1 ∈ firstCore (K := K) p v ρ a ∧
        w bc.2 ∈ secondCore q w ρ y)) := by
  have h₁ := (p.condSnd a).core_capture (K := K) v hρ
  have h₂ := (q.condFst y).core_capture (K := K) w hρ
  rw [Subspace.dual_finrank_eq] at h₂
  have he : (univ.filter (fun bc : B × A => v bc.1 ∈ firstCore (K := K) p v ρ a ∧
      w bc.2 ∈ secondCore q w ρ y)) =
      (univ.filter (fun b => v b ∈ firstCore (K := K) p v ρ a)) ×ˢ
      (univ.filter (fun a => w a ∈ secondCore q w ρ y)) := by ext bc; simp
  rw [he, Law.prod_rectangle_event, pow_two]
  exact mul_le_mul (hd.trans h₁) (hd.trans h₂) hc
    ((p.condSnd a).event_nonneg _)

lemma core_collision_capture (p q : Law (A × B)) (v : B → V)
    (w : A → Module.Dual K V) {ρ c : ℝ} (hρ : 0 ≤ ρ) (hc : 0 ≤ c)
    (hd : c ≤ 1-(Module.finrank K V:ℝ)*ρ) (goodA : A → Prop) (goodB : B → Prop) :
    c^2*(p.fst.prod q.snd).event (univ.filter (fun ay : A × B =>
      goodA ay.1 ∧ goodB ay.2 ∧ w ay.1 (v ay.2) = 0 ∧ coreContained p q v w ρ ay.1 ay.2)) ≤
    (p.prod q).event (univ.filter (coreCollision p q v w ρ goodA goodB)) := by
  rw [show (p.prod q).event (univ.filter (coreCollision p q v w ρ goodA goodB)) =
    (p.prod q).event (univ.filter (fun z => coreCollision p q v w ρ goodA goodB (z.1,z.2))) by rfl,
    p.product_event_disintegration q (fun ab cy => coreCollision p q v w ρ goodA goodB (ab,cy))]
  simp only [Law.event, sum_filter, mul_sum]
  apply sum_le_sum
  intro ay _
  rw [←mul_sum]
  by_cases h : goodA ay.1 ∧ goodB ay.2 ∧ w ay.1 (v ay.2) = 0 ∧ coreContained p q v w ρ ay.1 ay.2
  · rw [ite_eq_left h]
    have he : (∑ bc : B × A, if coreCollision p q v w ρ goodA goodB ((ay.1,bc.1), (bc.2,ay.2))
        then ((p.condSnd ay.1).prod (q.condFst ay.2)).mass bc else 0) =
        ((p.condSnd ay.1).prod (q.condFst ay.2)).event (univ.filter (fun bc : B × A =>
          v bc.1 ∈ firstCore (K := K) p v ρ ay.1 ∧ w bc.2 ∈ secondCore q w ρ ay.2)) := by
      simp [Law.event, sum_filter, coreCollision, h.1,h.2.1,h.2.2.1,h.2.2.2]
    rw [he, mul_comm (c^2)]
    exact mul_le_mul_of_nonneg_left (core_capture_product p q v w hρ hc hd ay.1 ay.2)
      ((p.fst.prod q.snd).nonneg ay)
  · rw [ite_eq_right h, mul_zero]
    exact mul_nonneg ((p.fst.prod q.snd).nonneg ay) (sum_nonneg (fun bc _ => by
      split_ifs; exact ((p.condSnd ay.1).prod (q.condFst ay.2)).nonneg bc; rfl))
omit [FiniteDimensional K V] in

lemma exceptional_core_mass (p q : Law (A × B)) (v : B → V)
    (w : A → Module.Dual K V) {ρ : ℝ} (hρ : 0 < ρ)
    (goodA : A → Prop) (goodB : B → Prop) :
    ρ^2*(p.fst.prod q.snd).event (univ.filter (fun ay : A × B =>
      (goodA ay.1 ∧ goodB ay.2 ∧ w ay.1 (v ay.2) = 0) ∧
        ¬coreContained p q v w ρ ay.1 ay.2)) ≤
    (p.prod q).event (univ.filter (fun z : (A × B) × (A × B) =>
      w z.1.1 (v z.2.2) = 0 ∧ w z.2.1 (v z.1.2) ≠ 0)) := by
  calc
    _ ≤ ∑ ay : A × B, (p.fst.prod q.snd).mass ay *
      ((p.condSnd ay.1).prod (q.condFst ay.2)).event
        (univ.filter (fun bc : B × A =>
          w ay.1 (v ay.2) = 0 ∧ w bc.2 (v bc.1) ≠ 0)) := by
      change ρ^2*(∑ ay with (goodA ay.1 ∧ goodB ay.2 ∧ w ay.1 (v ay.2) = 0) ∧
        ¬coreContained p q v w ρ ay.1 ay.2, (p.fst.prod q.snd).mass ay) ≤ _
      rw [sum_filter,mul_sum]
      apply sum_le_sum
      intro ay _
      by_cases h : (goodA ay.1 ∧ goodB ay.2 ∧ w ay.1 (v ay.2) = 0) ∧
          ¬coreContained p q v w ρ ay.1 ay.2
      · rw [ite_eq_left h, mul_comm (ρ^2)]
        apply mul_le_mul_of_nonneg_left _ ((p.fst.prod q.snd).nonneg ay)
        simp only [h.1.2.2, true_and]
        apply le_of_not_gt
        intro he
        exact h.2 ((p.condSnd ay.1).cores_orthogonal (q.condFst ay.2) v w hρ he.le)
      · rw [ite_eq_right h,mul_zero]
        exact mul_nonneg ((p.fst.prod q.snd).nonneg ay)
          (((p.condSnd ay.1).prod (q.condFst ay.2)).event_nonneg _)
    _ = _ := by
      convert (p.product_event_disintegration q
        (fun ab cy => w ab.1 (v cy.2) = 0 ∧ w cy.1 (v ab.2) ≠ 0)).symm using 1 <;> congr!

theorem reciprocal_incidence_collision (p : Law ((A × B) × (A × B)))
    (v : B → V) (w : A → Module.Dual K V)
    {ρ c : ℝ} (hρ : 0 < ρ) (hc : 0 < c)
    (hd : c ≤ 1-(Module.finrank K V:ℝ)*ρ)
    (goodA : A → Prop) (goodB : B → Prop)
    (hconsistent : ∀ z, p.mass z ≠ 0 →
      w z.1.1 (v z.2.2) = 0 → w z.2.1 (v z.1.2) = 0) :
    (p.fst.fst.prod p.snd.snd).event (univ.filter (fun ay : A × B =>
      goodA ay.1 ∧ goodB ay.2 ∧ w ay.1 (v ay.2) = 0)) ≤
    2*mutualInfo p/ρ^2 +
      2*(mutualInfo p+p.event (univ.filter (coreCollision p.fst p.snd v w ρ goodA goodB)))/c^2 := by
  have hconf : p.event (univ.filter (fun z : (A × B) × (A × B) =>
      w z.1.1 (v z.2.2) = 0 ∧ w z.2.1 (v z.1.2) ≠ 0)) = 0 := by
    apply sum_eq_zero
    intro z hz
    by_contra hn
    have hz' := (mem_filter.mp hz).2
    exact hz'.2 (hconsistent z hn hz'.1)
  have herr := mutualInfo_event_transfer p (univ.filter (fun z : (A × B) × (A × B) =>
      w z.1.1 (v z.2.2) = 0 ∧ w z.2.1 (v z.1.2) ≠ 0))
  rw [hconf,add_zero] at herr
  have he := (exceptional_core_mass p.fst p.snd v w hρ goodA goodB).trans herr
  have hex : (p.fst.fst.prod p.snd.snd).event (univ.filter (fun ay : A × B =>
      (goodA ay.1 ∧ goodB ay.2 ∧ w ay.1 (v ay.2) = 0) ∧
        ¬coreContained p.fst p.snd v w ρ ay.1 ay.2)) ≤ 2*mutualInfo p/ρ^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hρ)).mpr
    simpa only [mul_comm] using he
  have hcap := (core_collision_capture p.fst p.snd v w hρ.le hc.le hd goodA goodB).trans
    (mutualInfo_event_transfer p (univ.filter (coreCollision p.fst p.snd v w ρ goodA goodB)))
  have hcm : (p.fst.fst.prod p.snd.snd).event (univ.filter (fun ay : A × B =>
      goodA ay.1 ∧ goodB ay.2 ∧ w ay.1 (v ay.2) = 0 ∧
        coreContained p.fst p.snd v w ρ ay.1 ay.2)) ≤
      2*(mutualInfo p+p.event (univ.filter (coreCollision p.fst p.snd v w ρ goodA goodB)))/c^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
    simpa only [mul_comm] using hcap
  have hs := (p.fst.fst.prod p.snd.snd).event_filter_le_add
    (fun ay : A × B => goodA ay.1 ∧ goodB ay.2 ∧ w ay.1 (v ay.2) = 0)
    (fun ay => coreContained p.fst p.snd v w ρ ay.1 ay.2)
  have hcm' : (p.fst.fst.prod p.snd.snd).event (univ.filter (fun ay : A × B =>
      (goodA ay.1 ∧ goodB ay.2 ∧ w ay.1 (v ay.2) = 0) ∧
      coreContained p.fst p.snd v w ρ ay.1 ay.2)) ≤
      2*(mutualInfo p+p.event (univ.filter (coreCollision p.fst p.snd v w ρ goodA goodB)))/c^2 := by
    simpa only [and_assoc] using hcm
  have HF := hs.trans (by
    convert add_le_add hex hcm' using 1
    congr!)
  convert HF using 1
  congr!

end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

lemma not_contained_of_rank_sum (W : Submodule K V) (U : Submodule K (Module.Dual K V))
    {r s : ℕ} (hW : r ≤ Module.finrank K W) (hU : s ≤ Module.finrank K U)
    (hsum : Module.finrank K V < r+s) : ¬U ≤ W.dualAnnihilator := by
  intro h
  have hle := Submodule.finrank_mono h
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  omega

lemma complementary_of_rank_sum (W : Submodule K V) (U : Submodule K (Module.Dual K V))
    {r s : ℕ} (hW : r ≤ Module.finrank K W) (hU : s ≤ Module.finrank K U)
    (hsum : Module.finrank K V = r+s) (h : U ≤ W.dualAnnihilator) :
    Module.finrank K W = r ∧ U = W.dualAnnihilator := by
  have hle := Submodule.finrank_mono h
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  refine ⟨by omega, Submodule.eq_of_le_of_finrank_eq h ?_⟩
  omega

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
open scoped BigOperators Classical
open Finset
noncomputable section
variable {A B Ω : Type*} [Fintype A] [Fintype B] [Fintype Ω]
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [Fintype Ω] [FiniteDimensional K V] in
lemma firstCore_own (p : Law (A × B)) (v : B → V) (w : A → Module.Dual K V)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hflag : ∀ ab, p.mass ab ≠ 0 → w ab.1 (v ab.2) = 0)
    (a : A) (ha : p.fst.mass a ≠ 0) :
    w a ∈ (firstCore (K := K) p v ρ a).dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator]
  apply (p.condSnd a).core_le_test v ρ (w a)
  have he : (p.condSnd a).event (univ.filter (fun b => w a (v b) ≠ 0)) = 0 := by
    apply sum_eq_zero
    intro b hb
    rw [p.condSnd_mass a ha]
    rw [show p.mass (a,b) = 0 from not_not.mp (fun hn => (mem_filter.mp hb).2 (hflag (a,b) hn))]
    exact zero_div _
  simpa only [he] using hρ

omit [Fintype Ω] [FiniteDimensional K V] in
lemma secondCore_own (p : Law (A × B)) (v : B → V) (w : A → Module.Dual K V)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hflag : ∀ ab, p.mass ab ≠ 0 → w ab.1 (v ab.2) = 0)
    (y : B) (hy : p.snd.mass y ≠ 0) :
    v y ∈ (secondCore p w ρ y).dualCoannihilator := by
  rw [Submodule.mem_dualCoannihilator]
  apply (p.condFst y).core_le_test w ρ (Module.Dual.eval K V (v y))
  have he : (p.condFst y).event (univ.filter (fun a => (Module.Dual.eval K V (v y)) (w a) ≠ 0)) = 0 := by
    apply sum_eq_zero
    intro a ha
    rw [p.condFst_mass y hy]
    rw [show p.mass (a,y) = 0 from not_not.mp (fun hn => (mem_filter.mp ha).2 (hflag (a,y) hn))]
    exact zero_div _
  simpa only [he] using hρ

def orthogonalRectangle (v : B → V) (w : A → Module.Dual K V) (W : Submodule K V) : Finset (A × B) :=
  univ.filter (fun ab => v ab.2 ∈ W ∧ w ab.1 ∈ W.dualAnnihilator)

omit [Fintype Ω] in
lemma coreCollision_rectangle (p q : Law (A × B)) (v : B → V) (w : A → Module.Dual K V)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (goodA : A → Prop) (goodB : B → Prop)
    (hpflag : ∀ ab, p.mass ab ≠ 0 → w ab.1 (v ab.2) = 0)
    (hqflag : ∀ ab, q.mass ab ≠ 0 → w ab.1 (v ab.2) = 0)
    {r s : ℕ} (hsum : Module.finrank K V = r+s)
    (hW : ∀ a, goodA a → r ≤ Module.finrank K (firstCore (K := K) p v ρ a))
    (hU : ∀ y, goodB y → s ≤ Module.finrank K (secondCore q w ρ y))
    (ab cy : A × B) (hp : p.mass ab ≠ 0) (hq : q.mass cy ≠ 0)
    (hcol : coreCollision p q v w ρ goodA goodB (ab,cy)) :
    ab ∈ orthogonalRectangle v w (firstCore (K := K) p v ρ ab.1) ∧
    cy ∈ orthogonalRectangle v w (firstCore (K := K) p v ρ ab.1) := by
  obtain ⟨hga,hgy,_,hcont,hb,hc⟩ := hcol
  have hcomp := (complementary_of_rank_sum _ _ (hW _ hga) (hU _ hgy) hsum hcont).2
  have hpa : p.fst.mass ab.1 ≠ 0 := (lt_of_lt_of_le (lt_of_le_of_ne (p.nonneg _) (Ne.symm hp)) (p.le_fst _ _)).ne'
  have hqy : q.snd.mass cy.2 ≠ 0 := (lt_of_lt_of_le (lt_of_le_of_ne (q.nonneg _) (Ne.symm hq)) (q.le_snd _ _)).ne'
  have hy := secondCore_own q v w hρ hqflag cy.2 hqy
  rw [hcomp, Subspace.dualAnnihilator_dualCoannihilator_eq] at hy
  exact ⟨mem_filter.mpr ⟨mem_univ _, hb, firstCore_own p v w hρ hpflag ab.1 hpa⟩,
    mem_filter.mpr ⟨mem_univ _,hy,hcomp ▸ hc⟩⟩

end
end SharpLogRamsey.Selection
namespace SharpLogRamsey.Selection
open scoped BigOperators Classical
open Finset
noncomputable section
variable {A B Ω : Type*} [Fintype A] [Fintype B] [Fintype Ω]

lemma Law.event_map (p : Law Ω) (f : Ω → A) (E : Finset A) :
    (p.map f).event E = p.event (univ.filter (fun x => f x ∈ E)) := by
  have h := p.sum_map f (fun a => if a ∈ E then 1 else 0)
  simpa only [mul_ite, mul_one, mul_zero, ← sum_filter, filter_mem_eq_inter, univ_inter,
    Law.event] using h

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in

lemma slot_flag {n : ℕ} (p : Law Ω) (f : Ω → Fin n → A × B)
    (v : B → V) (w : A → Module.Dual K V)
    (hflag : ∀ x, p.mass x ≠ 0 → ∀ i, w (f x i).1 (v (f x i).2) = 0)
    (i : Fin n) (ab : A × B) (hab : (p.map (fun x => f x i)).mass ab ≠ 0) :
    w ab.1 (v ab.2) = 0 := by
  obtain ⟨x,hx,rfl⟩ := p.map_support (fun x => f x i) ab hab
  exact hflag x hx i

theorem reciprocal_charge_sum {n : ℕ} (p : Law Ω) (f : Ω → Fin n → A × B)
    (v : B → V) (w : A → Module.Dual K V) {ρ M : ℝ} (hρ : 0 ≤ ρ)
    (goodA : Fin n → A → Prop) (goodB : Fin n → B → Prop)
    (hflag : ∀ x, p.mass x ≠ 0 → ∀ i, w (f x i).1 (v (f x i).2) = 0)
    {r s : ℕ} (hsum : Module.finrank K V = r+s)
    (hW : ∀ i a, goodA i a → r ≤ Module.finrank K
      (firstCore (K := K) (p.map (fun x => f x i)) v ρ a))
    (hU : ∀ j y, goodB j y → s ≤ Module.finrank K
      (secondCore (p.map (fun x => f x j)) w ρ y))
    (hocc : ∀ x, p.mass x ≠ 0 → ∀ W : Submodule K V,
      ((univ.filter (fun j : Fin n => f x j ∈ orthogonalRectangle v w W)).card:ℝ) ≤ M) :
    ∑ i, ∑ j with i < j,
      p.event (univ.filter (fun x => coreCollision (p.map (fun z => f z i))
        (p.map (fun z => f z j)) v w ρ (goodA i) (goodB j) (f x i,f x j))) ≤ n*M := by
  let C (i j : Fin n) (x : Ω) := coreCollision (p.map (fun z => f z i))
    (p.map (fun z => f z j)) v w ρ (goodA i) (goodB j) (f x i,f x j)
  have hpoint (x : Ω) (hx : p.mass x ≠ 0) (i : Fin n) :
      ∑ j with i < j, (if C i j x then (1:ℝ) else 0) ≤ M := by
    have hc : (univ.filter (fun j : Fin n => i < j ∧ C i j x)) ⊆
        univ.filter (fun j => f x j ∈ orthogonalRectangle v w
          (firstCore (K := K) (p.map (fun z => f z i)) v ρ (f x i).1)) := by
      intro j hj
      have hpi : (p.map (fun z => f z i)).mass (f x i) ≠ 0 :=
        (lt_of_lt_of_le (lt_of_le_of_ne (p.nonneg x) (Ne.symm hx)) (p.le_map _ x)).ne'
      have hpj : (p.map (fun z => f z j)).mass (f x j) ≠ 0 :=
        (lt_of_lt_of_le (lt_of_le_of_ne (p.nonneg x) (Ne.symm hx)) (p.le_map _ x)).ne'
      exact mem_filter.mpr ⟨mem_univ _, (coreCollision_rectangle _ _ v w hρ _ _
        (slot_flag p f v w hflag i) (slot_flag p f v w hflag j) hsum (hW i) (hU j)
        (f x i) (f x j) hpi hpj (mem_filter.mp hj).2.2).2⟩
    have hh := (Nat.cast_le.mpr (card_le_card hc) :
      ((univ.filter (fun j : Fin n => i < j ∧ C i j x)).card:ℝ) ≤ _)
    have hs : (∑ j with i < j, (if C i j x then (1:ℝ) else 0)) =
        ((univ.filter (fun j : Fin n => i < j ∧ C i j x)).card:ℝ) := by
      simp only [← sum_filter, filter_filter, sum_const, nsmul_eq_mul, mul_one]
    rw [hs]
    exact hh.trans (hocc x hx _)
  have hs : (∑ i, ∑ j with i < j, p.event (univ.filter (C i j))) =
      ∑ x, p.mass x * (∑ i, ∑ j with i < j, (if C i j x then (1:ℝ) else 0)) := by
    have he (i j : Fin n) : p.event (univ.filter (C i j)) =
        ∑ x, p.mass x*(if C i j x then (1:ℝ) else 0) := by
      simp only [Law.event, sum_filter, mul_ite, mul_one, mul_zero]
    simp_rw [he]
    calc
      _ = ∑ i, ∑ x, ∑ j with i < j, p.mass x*(if C i j x then (1:ℝ) else 0) := by
        apply sum_congr rfl
        intro i hi
        exact sum_comm
      _ = ∑ x, ∑ i, ∑ j with i < j, p.mass x*(if C i j x then (1:ℝ) else 0) := sum_comm
      _ = _ := by simp_rw [← mul_sum]
  change (∑ i, ∑ j with i < j, p.event (univ.filter (C i j))) ≤ _
  rw [hs]
  calc
    _ ≤ ∑ x, p.mass x * (n*M) := by
      apply sum_le_sum
      intro x hx
      by_cases hp : p.mass x = 0
      · simp [hp]
      apply mul_le_mul_of_nonneg_left _ (p.nonneg x)
      calc
        _ ≤ ∑ _i : Fin n, M := sum_le_sum (fun i _ => hpoint x hp i)
        _ = _ := by simp
    _ = _ := by rw [← sum_mul, p.total, one_mul]

end
end SharpLogRamsey.Selection

end

end OAI
