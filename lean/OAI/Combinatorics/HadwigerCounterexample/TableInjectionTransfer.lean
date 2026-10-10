import OAI.Combinatorics.HadwigerCounterexample.InjectionWitnesses

namespace OAI

/-! # Table Injection Transfer -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
variable {A B : Type}

def named (P : A×A → Prop) (C : ℝ) :=
  ∃ k : ℕ,(k:ℝ) ≤ C ∧ ∃ S : Fin k → A → Prop,∀ y,∃ i,∀ x,P (x,y)↔S i x

theorem named_at [Fintype B] {P : A×A → Prop} {C : ℝ}
    (S : B → A → Prop) (h : (Fintype.card B:ℝ) ≤ C)
    (he : ∀ y,∃ i,∀ x,P (x,y) ↔ S i x) :
    named P C := by
  classical
  let e := Fintype.equivFin B
  refine ⟨Fintype.card B,h,fun i => S (e.symm i),fun y => ?_⟩
  obtain ⟨i,hi⟩ := he y
  exact ⟨e i,by simpa using hi⟩

theorem named_true {A : Type} {C : ℝ} (h : 1 ≤ C) :
    named (fun _ : A×A => True) C :=
  ⟨1,(by simpa using h),fun _ _ => True,fun _ => ⟨0,fun _ => Iff.rfl⟩⟩

theorem pair_each [Fintype A] (w : Wgt A) (P : A×A→Prop) :
    pr (pairW w w) P = avg w (fun y => pr w (fun x => P (x,y))) := by
  unfold pr
  rw [pairW_avg]; exact avg_avg w w _

set_option maxHeartbeats 600000 in
private theorem named_fans {P : UnitType p n N × UnitType p n N → Prop}
    {C U L l : ℝ} (hP : named P C) (hu : 0<U) (hl : 0≤L) (hℓ : 0<l)
    (w : Wgt (UnitType p n N)) (b : Fpins p n N) (K k : ℕ)
    (hb : ∀ x,planRank (b x)≤K)
    (hw : IsLaw w) (m : Mixer p n) (hm : bySide p w m L) (i j : Bool) (z : Place p)
    (hN : 2*num (Full p n)-N≤ -1)
    (hf : rhUp L (2*U)*2 * bp (num (Row p n)+k-N) ≤ l) :
    pr (pairW w w) (fun x => P x ∧ fans b z i j x.1 x.2) ≤
      3*l* pr (pairW w w) P + U+ C*(fireBill p k K L/(pushCost l K)^k) := by
  classical
  obtain ⟨t,hC,S,hS⟩ := hP
  let v := onW w
  let f := fans b z i j
  let event (y : UnitType p n N) :=
    ∃ a : Fin t,U≤pr w (S a) ∧ 3*l≤pr (v (S a)) (fun x => f x y)
  let R := fireBill p k K L/(pushCost l K)^k
  have hR : 0 ≤ R := by
    refine div_nonneg ?_ (pow_nonneg (div_pos hℓ (bp_pos _)).le _)
    exact mul_nonneg (by positivity) (bp_pos _).le
  have he : pr w event ≤ C * R := by
    let Q (a : Fin t) := fun y => U ≤ pr w (S a) ∧ 3*l≤pr (v (S a)) (fun x => f x y)
    have h a : pr w (Q a) ≤ R := by
      by_cases ht : U≤pr w (S a)
      · have hv := on_law hw.nz (lt_of_lt_of_le hu ht)
        have hk := bySide_on m hw.nz hm (S a) (show 0<2*U by positivity) (by linarith)
        simp only [Q,ht,true_and]
        exact cannon K k hb z i j (v (S a)) w hv hw hℓ m (by unfold rhUp; positivity)
          hl hk hm hN hf
      simp only [Q,ht,false_and,pr_false]; exact hR
    refine (pr_exists_le hw.nz Q).trans ?_
    refine (Finset.sum_le_sum fun i _ => h i).trans ?_
    rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hC hR
  have hU (y : UnitType p n N) :
      pr w (fun x => P (x,y) ∧ f x y) ≤ 3*l*pr w (fun x => P (x,y)) + U + ind (event y) := by
    obtain ⟨a,ha⟩ := hS y
    simp_rw [ha]
    have h1 := pr_nonneg (p:=S a) hw.nz
    have hr := mul_nonneg (show 0≤3*l by linarith) h1
    by_cases h : U≤pr w (S a)
    · by_cases ht : 3*l ≤ pr (v (S a)) (fun x => f x y)
      · rw [ind_one (show event y from ⟨a,h,ht⟩)]
        exact ((pr_le_tot hw.nz).trans hw.total.le).trans (by linarith only [hr,hu])
      rw [pr_of_on hw.nz]
      have hj := mul_le_mul_of_nonneg_left (le_of_not_ge ht) h1
      have hi := ind_nonneg (event y)
      refine hj.trans ?_
      linarith only [hi,hu]
    have hh := (pr_mono hw.nz (p:=fun x => S a x∧ f x y) (q:=S a) fun x h => h.1).trans
      (le_of_not_ge h)
    refine hh.trans ?_
    linarith only [hr,ind_nonneg (event y)]
  rw [pair_each,pair_each]
  apply (avg_mono hw.nz hU).trans
  rw [avg_add,avg_add,avg_mul',hw.avg_const]
  exact add_le_add_right he _

def acceptsInj (p : Shape) {n N} (b : Fpins p n N) (x : UnitType p n N×UnitType p n N) :=
  tableInj (b x.1) (b x.2) (actual p x.1 x.2)

set_option maxHeartbeats 800000 in
theorem secure_one {P : UnitType p n N × UnitType p n N → Prop}
    {C U L l : ℝ} (hP : named P C) (hu : 0<U) (hl : 0≤L) (hℓ : 0<l)
    (w : Wgt (UnitType p n N)) (b : Fpins p n N) (K k : ℕ)
    (hb : ∀ x,planRank (b x)≤K)
    (hw : IsLaw w) (m : Mixer p n) (hm : bySide p w m L)
    (hx : ∀ x,w x≠0 → ∀ i,frameLaw m (onSide x i))
    (hN : 2*num (Full p n)-N≤ -1)
    (hf : rhUp L (2*U)*2 * bp (num (Row p n)+k-N) ≤ l) :
    pr (pairW w w) (fun x => P x ∧ ¬ acceptsInj p b x) ≤
      (4*num (Place p))*(3*l* pr (pairW w w) P + U+ C*(fireBill p k K L/(pushCost l K)^k)) := by
  classical
  let J := Place p × Bool × Bool
  let Q := fun (u : Place p × Bool × Bool) (x : UnitType p n N × _) =>
    P x ∧ fans b u.1 u.2.1 u.2.2 x.1 x.2
  let v := pairW w w
  have hh x (h : v x≠0) (hf : P x ∧ ¬ acceptsInj p b x) : ∃ i,Q i x := by
    obtain ⟨z,i,j,hf₀⟩ := fans_of_not_inj b _ _ m (hx x.1 (left_ne_zero_of_mul h)) hf.2
    exact ⟨(z,i,j),⟨hf.1,hf₀⟩⟩
  have hv := (pairW_law hw hw).nz
  refine ((pr_on_mono hv hh).trans (pr_exists_le hv Q)).trans ?_
  refine (Finset.sum_le_sum fun i _ => named_fans hP hu hl hℓ w b K k hb hw m hm i.2.1 i.2.2 i.1
    hN hf).trans_eq ?_
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_prod,num,Fintype.card_bool]
  push_cast
  ring

theorem perm_pair_prob [Fintype A] (w : Wgt A) (P : A × A→ Prop) :
    pr (pairW w w) (P ∘ Prod.swap)=pr (pairW w w) P := by
  rw [pair_each]
  unfold pr; rw [pairW_avg]; rfl

def secureAt (p : Shape) {n N} (b : Fpins p n N) (x : UnitType p n N×UnitType p n N) :=
  acceptsInj p b x ∧ acceptsInj p b x.swap

theorem secure_bound {P : UnitType p n N × UnitType p n N → Prop}
    {C U L l : ℝ} (hP : named P C) (hq : named (P ∘ Prod.swap) C)
    (hu : 0<U) (hl : 0≤L) (hℓ : 0<l)
    (w : Wgt (UnitType p n N)) (b : Fpins p n N) (K k : ℕ)
    (hb : ∀ x,planRank (b x)≤K)
    (hw : IsLaw w) (m : Mixer p n) (hm : bySide p w m L)
    (hx : ∀ x,w x≠0 → ∀ i,frameLaw m (onSide x i))
    (hN : 2*num (Full p n)-N≤ -1)
    (hf : rhUp L (2*U)*2 * bp (num (Row p n)+k-N) ≤ l) :
    pr (pairW w w) (fun x => P x ∧ ¬ secureAt p b x) ≤
      8*num (Place p)*(3*l*pr (pairW w w) P+U+C*(fireBill p k K L/(pushCost l K)^k)) := by
  classical
  let Q := acceptsInj p b
  let v := pairW w w
  have he := secure_one hP hu hl hℓ w b K k hb hw m hm hx hN hf
  have ht :
      pr v (fun x => P x∧¬ Q x.swap)≤
      4*num (Place p)*(3*l*pr v P+U+C*(fireBill p k K L/(pushCost l K)^k)) := by
    rw [←perm_pair_prob w (fun x => P x∧¬Q x.swap),←perm_pair_prob w P]
    have h : (fun x => P x∧¬Q x.swap) ∘ Prod.swap = fun x => P x.swap∧¬ Q x := by
      funext x; rw [Function.comp_apply,Prod.swap_swap]
    rw [h]; exact secure_one hq hu hl hℓ w b K k hb hw m hm hx hN hf
  have hx x : P x ∧ ¬secureAt p b x → (P x∧¬Q x)∨ (P x ∧¬Q x.swap) := by
    intro h
    have hh : P x∧¬ (Q x∧Q x.swap) := h
    tauto
  have hv := (pairW_law hw hw).nz
  refine ((pr_mono hv hx).trans ((pr_or_le hv).trans (add_le_add he ht))).trans_eq ?_
  unfold v
  ring

end HadwigerCounterexample

end

end OAI
