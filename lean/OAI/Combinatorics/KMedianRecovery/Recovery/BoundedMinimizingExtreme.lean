import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Region

namespace OAI

namespace MetricKMedianRecovery.PolytopeCertificate

section
open Matrix
open scoped Topology BigOperators
variable {R V : Type*} [Fintype R] [Fintype V]

omit [Fintype R] in

theorem bounded_minimizing_extreme (A : Matrix R V ℝ) (b : R → ℝ) (c : V → ℝ) (B : ℝ)
    (hn : (region A b).Nonempty)
    (hbound : ∀ x ∈ region A b, ∀ j, -B ≤ x j ∧ x j ≤ B) :
    ∃ x, x ∈ (region A b).extremePoints ℝ ∧
      ∀ y ∈ region A b, (∑ j, c j*x j) ≤ ∑ j, c j*y j := by
  let L : (V → ℝ) → ℝ := fun x => ∑ j, c j*x j
  have hL : Continuous L := by fun_prop
  have hc : IsCompact (region A b) :=
    isCompact_Icc.of_isClosed_subset (region_closed A b) (by
      intro x hx
      exact ⟨fun j => (hbound x hx j).1,fun j => (hbound x hx j).2⟩)
  obtain ⟨x0,hx0,hmin⟩ := hc.exists_isMinOn hn hL.continuousOn
  let S : Set (V → ℝ) := region A b ∩ {x | L x=L x0}
  have hS : IsCompact S := hc.inter_right (isClosed_eq hL continuous_const)
  have hSn : S.Nonempty := ⟨x0,hx0,rfl⟩
  have he : IsExtreme ℝ (region A b) S := by
    refine ⟨fun _ hx => hx.1,?_⟩
    intro x hx y hy z hz hseg
    refine ⟨hx,?_⟩
    rcases hseg with ⟨a,b,ha,hb,hab,rfl⟩
    have heq : L (a • x+b • y)=a*L x+b*L y := by
      simp only [L,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib]
      rw [Finset.mul_sum,Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
    have hval : a*L x+b*L y=L x0 := heq.symm.trans hz.2
    have hmx : L x0 ≤ L x := hmin hx
    have hmy : L x0 ≤ L y := hmin hy
    change L x=L x0
    apply le_antisymm ?_ hmx
    by_contra! hh
    have hpos := mul_pos ha (sub_pos.mpr hh)
    have hnon := mul_nonneg hb.le (sub_nonneg.mpr hmy)
    have hab0 : (a+b)*L x0=L x0 := by rw [hab,one_mul]
    nlinarith
  obtain ⟨x,hx⟩ := hS.extremePoints_nonempty hSn
  refine ⟨x,he.extremePoints_subset_extremePoints hx,?_⟩
  intro y hy
  change L x ≤ L y
  rw [hx.1.2]
  exact hmin hy

theorem integer_min_certificate [DecidableEq V] (A : Matrix R V ℤ) (b : R → ℤ)
    (c : V → ℝ) (B : ℝ) (H : ℤ) (hH : 0 ≤ H)
    (hA : ∀ r j, |A r j| ≤ H) (hb : ∀ r, |b r| ≤ H)
    (hn : (region (fun r j => (A r j:ℝ)) (fun r => (b r:ℝ))).Nonempty)
    (hbound : ∀ x ∈ region (fun r j => (A r j:ℝ)) (fun r => (b r:ℝ)),
      ∀ j, -B ≤ x j ∧ x j ≤ B) :
    ∃ p : V → ℤ, ∃ q : ℤ, q≠0 ∧
      |q| ≤ (Fintype.card V).factorial * ((Fintype.card R:ℤ)*H^2)^(Fintype.card V) ∧
      (∀ j, |p j| ≤ (Fintype.card V).factorial * ((Fintype.card R:ℤ)*H^2)^(Fintype.card V)) ∧
      (fun j => (p j:ℝ)/(q:ℝ)) ∈ region (fun r j => (A r j:ℝ)) (fun r => (b r:ℝ)) ∧
      ∀ y ∈ region (fun r j => (A r j:ℝ)) (fun r => (b r:ℝ)),
        (∑ j, c j*((p j:ℝ)/(q:ℝ))) ≤ ∑ j, c j*y j := by
  obtain ⟨x,hx,hm⟩ := bounded_minimizing_extreme (fun r j => (A r j:ℝ))
    (fun r => (b r:ℝ)) c B hn hbound
  obtain ⟨p,q,hq,hqb,hpb,heq⟩ := integer_point_certificate A b H hH hA hb x
    (fun u hu => active_kernel_zero _ _ x hx u hu)
  refine ⟨p,q,hq,hqb,hpb,heq.symm ▸ hx.1,?_⟩
  intro y hy
  have heqj (j : V) : (p j:ℝ)/(q:ℝ)=x j := congrFun heq j
  simpa only [heqj] using hm y hy

end

open Matrix
open scoped BigOperators
variable {R V : Type*} [Fintype R] [Fintype V] [DecidableEq V]

abbrev SlackRow (R V : Type*) := R ⊕ (Bool × Option V)

def slackMatrix (A : Matrix R V ℤ) : Matrix (SlackRow R V) (Option V) ℤ
  | .inl _r,none => -1
  | .inl r,some j => A r j
  | .inr (s,j),k => if k=j then if s then 1 else -1 else 0

def slackBounds (b : R → ℤ) (B H : ℤ) : SlackRow R V → ℤ
  | .inl r => b r
  | .inr (s,none) => if s then H else 0
  | .inr (_,some _) => B

omit [Fintype R] in
lemma slack_region_iff (A : Matrix R V ℤ) (b : R → ℤ) (B H : ℤ) (y : Option V → ℝ) :
    y ∈ region (fun r j => (slackMatrix A r j:ℝ)) (fun r => (slackBounds b B H r:ℝ)) ↔
      (0 ≤ y none ∧ y none ≤ (H:ℝ)) ∧
      (∀ j, -(B:ℝ) ≤ y (some j) ∧ y (some j) ≤ (B:ℝ)) ∧
      (∀ r, (∑ j, (A r j:ℝ)*y (some j)) ≤ (b r:ℝ)+y none) := by
  have he (r : R) : (∑ j, (slackMatrix A (.inl r) j:ℝ)*y j) =
      -y none+∑ j, (A r j:ℝ)*y (some j) := by
    simp [Fintype.sum_option,slackMatrix]
  have hb (s : Bool) (j : Option V) :
      (∑ k, (slackMatrix A (.inr (s,j)) k:ℝ)*y k) = if s then y j else -y j := by
    cases s <;> simp [slackMatrix]
  constructor
  · intro h
    have h0 := h (.inr (false,none))
    have hH := h (.inr (true,none))
    rw [hb] at h0 hH
    refine ⟨?_,?_,?_⟩
    · simpa only [Bool.false_eq_true,Bool.true_eq,ite_false,ite_true,slackBounds,
        Int.cast_zero,neg_nonpos] using And.intro h0 hH
    · intro j
      have hl := h (.inr (false,some j))
      have hu := h (.inr (true,some j))
      simp only [hb,slackBounds,Bool.false_eq_true,ite_false,ite_true] at hl hu
      exact ⟨by linarith,hu⟩
    · intro r
      have hh := h (.inl r)
      rw [he] at hh
      change -y none+(∑ j, (A r j:ℝ)*y (some j)) ≤ (b r:ℝ) at hh
      linarith
  · rintro ⟨ht,hx,ha⟩ r
    cases r with
    | inl r =>
      rw [he]
      change _ ≤ (b r:ℝ)
      linarith [ha r]
    | inr p =>
      rcases p with ⟨s,j⟩
      rw [hb]
      cases j with
      | none =>
        cases s
        · simpa only [Bool.false_eq_true,ite_false,slackBounds,Int.cast_zero,neg_nonpos] using ht.1
        · exact ht.2
      | some j =>
        cases s
        · change -y (some j) ≤ (B:ℝ)
          linarith [(hx j).1]
        · exact (hx j).2

lemma positive_fraction_gap (p q : ℤ) (Q : ℝ) (hq : q≠0)
    (hb : |(q:ℝ)| ≤ Q) (hpq : 0 < (p:ℝ)/(q:ℝ)) :
    1/Q ≤ (p:ℝ)/(q:ℝ) := by
  have hqr : (q:ℝ)≠0 := by exact_mod_cast hq
  have hq0 : 0 < |(q:ℝ)| := abs_pos.mpr hqr
  have hp : p≠0 := by
    intro he
    simp [he] at hpq
  have hp1 : (1:ℤ) ≤ |p| := by have hh := abs_pos.mpr hp; omega
  have hp1r : (1:ℝ) ≤ |(p:ℝ)| := by exact_mod_cast hp1
  calc
    _ ≤ 1/|(q:ℝ)| := one_div_le_one_div_of_le hq0 hb
    _ ≤ |(p:ℝ)|/|(q:ℝ)| := div_le_div_of_nonneg_right hp1r hq0.le
    _ = (p:ℝ)/(q:ℝ) := by rw [←abs_div,abs_of_pos hpq]

theorem approximate_implies_feasible (A : Matrix R V ℤ) (b : R → ℤ) (B H : ℤ)
    (hB : 0 ≤ B) (hH : 1 ≤ H) (hA : ∀ r j, |A r j|≤H) (hb : ∀ r, |b r|≤H)
    (eps : ℝ) (heps0 : 0≤eps) (hepsH : eps≤(H:ℝ))
    (heps : eps < 1 / ((Fintype.card (Option V)).factorial *
      ((Fintype.card (SlackRow R V):ℤ)*(max H B)^2)^(Fintype.card (Option V)) : ℤ))
    (x : V → ℝ) (hx : ∀ j, -(B:ℝ)≤x j ∧ x j≤(B:ℝ))
    (ha : ∀ r, (∑ j, (A r j:ℝ)*x j)≤(b r:ℝ)+eps) :
    ∃ y ∈ region (fun r j => (A r j:ℝ)) (fun r => (b r:ℝ)),
      ∀ j, -(B:ℝ)≤y j ∧ y j≤(B:ℝ) := by
  classical
  let C := slackMatrix A
  let d := slackBounds (V:=V) b B H
  let K := max H B
  have hK : 0≤K := le_trans (by omega) (le_max_left H B)
  have hKH : H≤K := le_max_left _ _
  have hKB : B≤K := le_max_right _ _
  have hC : ∀ r j, |C r j|≤K := by
    intro r j
    cases r with
    | inl r =>
      cases j with
      | none => change |-1|≤K; simp only [abs_neg,abs_one]; omega
      | some j => exact (hA r j).trans hKH
    | inr p =>
      rcases p with ⟨s,k⟩
      change |if j=k then if s then 1 else -1 else 0|≤K
      split_ifs <;> simp only [abs_one,abs_neg,abs_zero] <;> omega
  have hd : ∀ r, |d r|≤K := by
    intro r
    cases r with
    | inl r => exact (hb r).trans hKH
    | inr p =>
      rcases p with ⟨s,j⟩
      cases j with
      | none => cases s <;> simp_all [d,slackBounds,abs_of_nonneg (show 0≤H by omega)]
      | some j => simpa only [d,slackBounds,abs_of_nonneg hB] using hKB
  let c : Option V → ℝ := fun j => if j=none then 1 else 0
  have hc (y : Option V → ℝ) : (∑ j, c j*y j)=y none := by simp [c]
  have hn : (region (fun r j => (C r j:ℝ)) (fun r => (d r:ℝ))).Nonempty := by
    refine ⟨Option.elim' (H:ℝ) (fun _ => 0),(slack_region_iff A b B H _).mpr ?_⟩
    refine ⟨?_,?_,?_⟩
    · change 0≤(H:ℝ) ∧ (H:ℝ)≤(H:ℝ)
      exact ⟨by exact_mod_cast (show 0≤H by omega),le_rfl⟩
    · intro j
      simp only [Option.elim'_some]
      exact ⟨neg_nonpos.mpr (by exact_mod_cast hB),by exact_mod_cast hB⟩
    · intro r
      simp only [Option.elim'_some,Option.elim'_none,mul_zero,Finset.sum_const_zero]
      have hh := (abs_le.mp (hb r)).1
      exact_mod_cast (show 0≤b r+H by omega)
  have hbounded : ∀ y ∈ region (fun r j => (C r j:ℝ)) (fun r => (d r:ℝ)),
      ∀ j, -(K:ℝ)≤y j ∧ y j≤(K:ℝ) := by
    intro y hy j
    have hh := (slack_region_iff A b B H y).mp hy
    have hKr : 0≤(K:ℝ) := by exact_mod_cast hK
    have hKHr : (H:ℝ)≤(K:ℝ) := by exact_mod_cast hKH
    have hKBr : (B:ℝ)≤(K:ℝ) := by exact_mod_cast hKB
    cases j with
    | none => exact ⟨by linarith [hh.1.1],hh.1.2.trans hKHr⟩
    | some j => exact ⟨by linarith [(hh.2.1 j).1],(hh.2.1 j).2.trans hKBr⟩
  obtain ⟨p,q,hq,hqb,_hpb,hpq,hmin⟩ := integer_min_certificate C d c (K:ℝ) K
    hK hC hd hn hbounded
  have hh := (slack_region_iff A b B H _).mp hpq
  by_cases he : (p none:ℝ)/(q:ℝ)=0
  · refine ⟨fun j => (p (some j):ℝ)/(q:ℝ),?_,hh.2.1⟩
    intro r
    simpa only [he,add_zero] using hh.2.2 r
  · have hpqpos : 0<(p none:ℝ)/(q:ℝ) := lt_of_le_of_ne hh.1.1 (Ne.symm he)
    have hqbR : |(q:ℝ)| ≤ ((Fintype.card (Option V)).factorial *
        ((Fintype.card (SlackRow R V):ℤ)*K^2)^(Fintype.card (Option V)) : ℤ) := by
      exact_mod_cast hqb
    have hgap := positive_fraction_gap (p none) q _ hq hqbR hpqpos
    have happrox : Option.elim' eps x ∈
        region (fun r j => (C r j:ℝ)) (fun r => (d r:ℝ)) :=
      (slack_region_iff A b B H _).mpr ⟨⟨heps0,hepsH⟩,hx,ha⟩
    have hval := hmin (Option.elim' eps x) happrox
    rw [hc,hc] at hval
    change (p none:ℝ)/(q:ℝ) ≤ eps at hval
    exact (not_lt_of_ge (hgap.trans hval) heps).elim

end MetricKMedianRecovery.PolytopeCertificate

end OAI
