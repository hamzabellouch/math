import Mathlib
import OAI.Probability.UnimodularPercolation.Exploration.TailBounds

namespace OAI

/-! Large Contacts for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section UnorderedContactConcentration
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem cluster_contact_tail (G : BondGraph V E) (Q : Finset E)
    (d : ℕ) (hd : ∀ z, (Q.filter fun e => z ∈ G e).card ≤ d)
    (x v : V) (p : unitInterval) (m : ℕ) (hdm : 0 < d*m) (a : ℝ) (ha : 0 < a) :
    bernoulliPolynomial Q (fun ω => if ¬Conn G (ω:Set E) x v ∧
      min (finiteRootComponent G ω x).card (finiteRootComponent G ω v).card ≤ m ∧
      2*a ≤ (p:ℝ)*(contactBonds G Q (finiteRootComponent G ω x)
        (finiteRootComponent G ω v)).card then 1 else 0) p ≤
      8*Real.exp (-2*a^2/(d*m:ℕ)) := by
  let f (x v : V) (ω : Finset E) : ℝ :=
    if ¬Conn G (ω:Set E) x v ∧ (incidentBonds G Q (finiteRootComponent G ω v)).card ≤ d*m ∧
      2*a ≤ (p:ℝ)*(contactBonds G Q (finiteRootComponent G ω x)
        (finiteRootComponent G ω v)).card then 1 else 0
  calc
    _ ≤ bernoulliPolynomial Q (fun ω => f x v ω+f v x ω) p := by
      apply bernoulliPolynomial_mono _ _ _ p p.2
      intro ω _
      by_cases h : ¬Conn G (ω:Set E) x v ∧
          min (finiteRootComponent G ω x).card (finiteRootComponent G ω v).card ≤ m ∧
          2*a ≤ (p:ℝ)*(contactBonds G Q (finiteRootComponent G ω x)
            (finiteRootComponent G ω v)).card
      · simp only [ite_eq_left h]
        rcases le_total (finiteRootComponent G ω v).card (finiteRootComponent G ω x).card with hc | hc
        · have hsmall : (finiteRootComponent G ω v).card ≤ m := by simpa only [min_eq_right hc] using h.2.1
          have hh : ¬Conn G (ω:Set E) x v ∧ (incidentBonds G Q (finiteRootComponent G ω v)).card ≤ d*m ∧
              2*a ≤ (p:ℝ)*(contactBonds G Q (finiteRootComponent G ω x) (finiteRootComponent G ω v)).card :=
            ⟨h.1,(incidentBonds_card_le G Q _ d hd).trans (Nat.mul_le_mul_left d hsmall),h.2.2⟩
          simp only [f,ite_eq_left hh]; split_ifs <;> norm_num
        · have hsmall : (finiteRootComponent G ω x).card ≤ m := by simpa only [min_eq_left hc] using h.2.1
          have hh : ¬Conn G (ω:Set E) v x ∧ (incidentBonds G Q (finiteRootComponent G ω x)).card ≤ d*m ∧
              2*a ≤ (p:ℝ)*(contactBonds G Q (finiteRootComponent G ω v) (finiteRootComponent G ω x)).card := by
            refine ⟨fun hc' => h.1 (conn_symm G _ hc'),
              (incidentBonds_card_le G Q _ d hd).trans (Nat.mul_le_mul_left d hsmall),?_⟩
            rw [contactBonds_comm G Q (finiteRootComponent G ω v)]
            exact h.2.2
          simp only [f,ite_eq_left hh]; split_ifs <;> norm_num
      · simp only [ite_eq_right h,f]; split_ifs <;> norm_num
    _ = bernoulliPolynomial Q (f x v) p+bernoulliPolynomial Q (f v x) p :=
      bernoulliPolynomial_add ..
    _ ≤ 4*Real.exp (-2*a^2/(d*m:ℕ))+4*Real.exp (-2*a^2/(d*m:ℕ)) :=
      add_le_add (ordered_cluster_contact_tail G Q x v p (d*m) hdm a ha)
        (ordered_cluster_contact_tail G Q v x p (d*m) hdm a ha)
    _ = _ := by ring

end UnorderedContactConcentration
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TwoLargeFiniteClusters
attribute [local instance] Classical.propDecidable Classical.decEq

theorem cluster_exterior_weighted_bound (G : BondGraph V E) (Q : Finset E)
    (x : V) (p : unitInterval) (F : Finset V → ℝ) (hF : ∀ W, 0 ≤ F W)
    (f : Finset V → Finset E → ℝ) (K : ℝ)
    (hf : ∀ W : Finset V, bernoulliPolynomial (exteriorBonds G Q (W:Set V)) (f W) p ≤ K) :
    bernoulliPolynomial Q (fun ω => F (finiteRootComponent G ω x)*f (finiteRootComponent G ω x)
      (exteriorBonds G ω (finiteRootComponent G ω x:Set V))) p ≤
      K*bernoulliPolynomial Q (fun ω => F (finiteRootComponent G ω x)) p := by
  have hh := cluster_exterior_expectation_bound G Q x p
    (fun W η => F W*f W η-K*F W) 0 (fun W => by
      rw [bernoulliPolynomial_sub,bernoulliPolynomial_const_mul,bernoulliPolynomial_const]
      exact sub_nonpos.mpr (by simpa only [mul_comm K] using mul_le_mul_of_nonneg_left (hf W) (hF W)))
  rw [bernoulliPolynomial_sub,bernoulliPolynomial_const_mul] at hh
  exact sub_nonpos.mp hh

theorem finiteClusterTail_domain_mono (G : BondGraph V E) {Q R : Finset E} (hRQ : R ⊆ Q)
    (x : V) (n : ℕ) (p : unitInterval) : finiteClusterTail G R x n p ≤ finiteClusterTail G Q x n p := by
  unfold finiteClusterTail
  rw [←bernoulliPolynomial_restrict R Q hRQ]
  apply bernoulliPolynomial_mono _ _ _ p p.2
  intro ω _
  exact finiteClusterTailIndicator_mono G x n Finset.inter_subset_left

 

theorem two_large_clusters_tail (G : BondGraph V E) (Q : Finset E)
    (x v : V) (n m : ℕ) (p : unitInterval) :
    bernoulliPolynomial Q (fun ω => if ¬Conn G (ω:Set E) x v ∧
      n ≤ (finiteRootComponent G ω x).card ∧ m ≤ (finiteRootComponent G ω v).card
        then 1 else 0) p ≤ finiteClusterTail G Q v m p*finiteClusterTail G Q x n p := by
  let F (W : Finset V) : ℝ := if n ≤ W.card then 1 else 0
  let f (W : Finset V) (η : Finset E) : ℝ := if v ∈ W then 0 else finiteClusterTailIndicator G v m η
  have hF : ∀ W, 0 ≤ F W := fun W => by dsimp [F]; split_ifs <;> norm_num
  have hf (W : Finset V) : bernoulliPolynomial (exteriorBonds G Q (W:Set V)) (f W) p ≤
      finiteClusterTail G Q v m p := by
    by_cases hv : v ∈ W
    · simp only [f,ite_eq_left hv,bernoulliPolynomial_zero]
      exact finiteClusterTail_nonneg G Q v m p
    · simp only [f,ite_eq_right hv]
      exact finiteClusterTail_domain_mono G (Finset.filter_subset _ _) v m p
  have hp := cluster_exterior_weighted_bound G Q x p F hF f (finiteClusterTail G Q v m p) hf
  have heq : bernoulliPolynomial Q (fun ω => F (finiteRootComponent G ω x)*f (finiteRootComponent G ω x)
      (exteriorBonds G ω (finiteRootComponent G ω x:Set V))) p =
      bernoulliPolynomial Q (fun ω => if ¬Conn G (ω:Set E) x v ∧
      n ≤ (finiteRootComponent G ω x).card ∧ m ≤ (finiteRootComponent G ω v).card then 1 else 0) p := by
    apply bernoulliPolynomial_congr
    intro ω _
    have hv : v ∈ finiteRootComponent G ω x ↔ Conn G (ω:Set E) x v := by
      change v ∈ (finiteRootComponent G ω x:Set V) ↔ _
      rw [coe_finiteRootComponent]
      rfl
    by_cases hc : Conn G (ω:Set E) x v
    · simp only [F,f,ite_eq_left (hv.mpr hc),mul_zero,not_true_eq_false,hc,false_and,ite_false]
    · simp only [F,f,ite_eq_right (fun h => hc (hv.mp h)),finiteClusterTailIndicator,
        finiteRootComponent_exterior G ω x v hc]
      split_ifs <;> norm_num <;> grind
  rw [heq] at hp
  exact hp

end TwoLargeFiniteClusters
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section EndpointClusterTails
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finiteClusterTail_of_endpoint_moment [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (q : unitInterval) (α C : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hfin : ∀ y, ∀ᵐ ω ∂law q, (cluster G ω y).Finite)
    (hI : ∀ y, Integrable (fun ω => ((cluster G ω y).ncard:ℝ)^α) (law q))
    (hC : ∀ y, (∫ ω, ((cluster G ω y).ncard:ℝ)^α ∂law q) ≤ C)
    (Q : Finset E) (x : V) (p : unitInterval) (hpq : p ≤ q) (n : ℕ) (hn : 1 ≤ n) :
    finiteClusterTail G Q x n p ≤ 2*C*(n:ℝ)^(-α) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let h : unitInterval := ⟨1/(n:ℝ),⟨by positivity,by apply (div_le_one hn0).mpr; exact_mod_cast hn⟩⟩
  have hh : 0 < (h:ℝ) := by dsimp [h]; positivity
  have hhpow : (h:ℝ)^α = (n:ℝ)^(-α) := by
    dsimp [h]
    rw [one_div,Real.inv_rpow hn0.le,Real.rpow_neg hn0.le]
  have hhn : 1 ≤ (h:ℝ)*n := by dsimp [h]; rw [one_div,inv_mul_cancel₀ hn0.ne']
  have hm := cluster_power_mono_integral G hloc x p q hpq α hα (hfin x) (hI x)
  have hb := markedConnection_le_cluster_power G Q x h p α hα hα1
    (cluster_finite_ae_mono G x p q hpq (hfin x)) hm.1
  have hM : markedConnectionPolynomial G Q x h p ≤ C*(n:ℝ)^(-α) := by
    apply hb.trans
    rw [hhpow]
    simpa only [mul_comm C] using
      mul_le_mul_of_nonneg_left (hm.2.trans (hC x)) (Real.rpow_nonneg (Nat.cast_nonneg n) (-α))
  have hb' := (finiteClusterTail_le_markedConnection G Q x n p h hhn).trans
    (mul_le_mul_of_nonneg_left hM (by norm_num : (0:ℝ) ≤ 2))
  simpa only [mul_assoc] using hb'

theorem two_large_clusters_of_endpoint_moment [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (q : unitInterval) (α C : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hC0 : 0 ≤ C)
    (hfin : ∀ y, ∀ᵐ ω ∂law q, (cluster G ω y).Finite)
    (hI : ∀ y, Integrable (fun ω => ((cluster G ω y).ncard:ℝ)^α) (law q))
    (hC : ∀ y, (∫ ω, ((cluster G ω y).ncard:ℝ)^α ∂law q) ≤ C)
    (Q : Finset E) (x v : V) (p : unitInterval) (hpq : p ≤ q) (n : ℕ) (hn : 1 ≤ n) :
    bernoulliPolynomial Q (fun ω => if ¬Conn G (ω:Set E) x v ∧
      n ≤ (finiteRootComponent G ω x).card ∧ n ≤ (finiteRootComponent G ω v).card
        then 1 else 0) p ≤ 4*C^2*(n:ℝ)^(-2*α) := by
  have ht (y : V) := finiteClusterTail_of_endpoint_moment G hloc q α C hα hα1 hfin hI hC Q y p hpq n hn
  have hc : 0 ≤ 2*C*(n:ℝ)^(-α) := by positivity
  calc
    _ ≤ finiteClusterTail G Q v n p*finiteClusterTail G Q x n p := two_large_clusters_tail ..
    _ ≤ (2*C*(n:ℝ)^(-α))*(2*C*(n:ℝ)^(-α)) :=
      mul_le_mul (ht v) (ht x) (finiteClusterTail_nonneg G Q x n p) hc
    _ = 4*C^2*(n:ℝ)^(-2*α) := by
      have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      rw [show (2*C*(n:ℝ)^(-α))*(2*C*(n:ℝ)^(-α)) =
        4*C^2*((n:ℝ)^(-α)*(n:ℝ)^(-α)) by ring,←Real.rpow_add hn0]
      congr 2
      ring

end EndpointClusterTails
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ContactBinFirstMoment
attribute [local instance] Classical.propDecidable Classical.decEq

theorem contactBonds_card_le (G : BondGraph V E) (Q : Finset E)
    (d : ℕ) (hd : ∀ z, (Q.filter fun e => z ∈ G e).card ≤ d) (A B : Finset V) :
    (contactBonds G Q A B).card ≤ d*min A.card B.card := by
  have hh (A B : Finset V) : (contactBonds G Q A B).card ≤ d*A.card := by
    apply (Finset.card_le_card (t := incidentBonds G Q A) _).trans (incidentBonds_card_le G Q A d hd)
    intro e he
    obtain ⟨he,a,ha,b,_,hab⟩ := Finset.mem_filter.mp he
    exact (mem_incidentBonds G Q A e).mpr ⟨he,a,ha,by rw [hab]; simp⟩
  rcases le_total A.card B.card with h | h
  · rw [min_eq_left h]; exact hh A B
  · rw [min_eq_right h,contactBonds_comm G Q A B]; exact hh B A

noncomputable def clusterContactBin (G : BondGraph V E) (Q : Finset E)
    (x v : V) (n m : ℕ) (ω : Finset E) : ℝ :=
  if ¬Conn G (ω:Set E) x v ∧
    n ≤ min (finiteRootComponent G ω x).card (finiteRootComponent G ω v).card ∧
    min (finiteRootComponent G ω x).card (finiteRootComponent G ω v).card ≤ m
  then (contactBonds G Q (finiteRootComponent G ω x) (finiteRootComponent G ω v)).card else 0

 

theorem clusterContactBin_bound (G : BondGraph V E) (Q : Finset E)
    (d : ℕ) (hd : ∀ z, (Q.filter fun e => z ∈ G e).card ≤ d)
    (x v : V) (p : unitInterval) (hp : 0 < (p:ℝ)) (n m : ℕ) (hdm : 0 < d*m)
    (a : ℝ) (ha : 0 < a) :
    bernoulliPolynomial Q (clusterContactBin G Q x v n m) p ≤
      (2*a/(p:ℝ))*(finiteClusterTail G Q v n p*finiteClusterTail G Q x n p)+
      (d*m:ℕ)*(8*Real.exp (-2*a^2/(d*m:ℕ))) := by
  let D (ω : Finset E) : Prop := ¬Conn G (ω:Set E) x v ∧
    n ≤ (finiteRootComponent G ω x).card ∧ n ≤ (finiteRootComponent G ω v).card
  let T (ω : Finset E) : Prop := ¬Conn G (ω:Set E) x v ∧
    min (finiteRootComponent G ω x).card (finiteRootComponent G ω v).card ≤ m ∧
    2*a ≤ (p:ℝ)*(contactBonds G Q (finiteRootComponent G ω x) (finiteRootComponent G ω v)).card
  calc
    _ ≤ bernoulliPolynomial Q (fun ω => (2*a/(p:ℝ))*(if D ω then 1 else 0)+
        (d*m:ℕ)*(if T ω then 1 else 0)) p := by
      apply bernoulliPolynomial_mono _ _ _ p p.2
      intro ω _
      unfold clusterContactBin
      by_cases h : ¬Conn G (ω:Set E) x v ∧
          n ≤ min (finiteRootComponent G ω x).card (finiteRootComponent G ω v).card ∧
          min (finiteRootComponent G ω x).card (finiteRootComponent G ω v).card ≤ m
      · have hD : D ω := ⟨h.1,(le_min_iff.mp h.2.1).1,(le_min_iff.mp h.2.1).2⟩
        simp only [ite_eq_left h,ite_eq_left hD,mul_one]
        by_cases ht : T ω
        · rw [ite_eq_left ht,mul_one]
          have hk : (contactBonds G Q (finiteRootComponent G ω x) (finiteRootComponent G ω v)).card ≤ d*m :=
            (contactBonds_card_le G Q d hd _ _).trans (Nat.mul_le_mul_left d h.2.2)
          have hk' : ((contactBonds G Q (finiteRootComponent G ω x) (finiteRootComponent G ω v)).card:ℝ) ≤ (d*m:ℕ) := by exact_mod_cast hk
          have hapos : 0 ≤ 2*a/(p:ℝ) := by positivity
          linarith
        · rw [ite_eq_right ht,mul_zero,add_zero]
          apply (le_div_iff₀ hp).mpr
          have hn : ¬ 2*a ≤ (p:ℝ)*(contactBonds G Q (finiteRootComponent G ω x) (finiteRootComponent G ω v)).card :=
            fun hh => ht ⟨h.1,h.2.2,hh⟩
          simpa only [mul_comm] using (not_le.mp hn).le
      · simp only [ite_eq_right h]
        split_ifs <;> positivity
    _ = (2*a/(p:ℝ))*bernoulliPolynomial Q (fun ω => if D ω then 1 else 0) p+
        (d*m:ℕ)*bernoulliPolynomial Q (fun ω => if T ω then 1 else 0) p := by
      rw [bernoulliPolynomial_add,bernoulliPolynomial_const_mul,bernoulliPolynomial_const_mul]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (two_large_clusters_tail G Q x v n n p) (by positivity))
      (mul_le_mul_of_nonneg_left (cluster_contact_tail G Q d hd x v p m hdm a ha) (Nat.cast_nonneg _))

end ContactBinFirstMoment
end Percolation

 
namespace Percolation
section StretchedContactDecay

theorem exists_stretched_exp_volume_bound (d ε r : ℝ) (hd : 0 < d) (hε : 0 < ε) (hr : r ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 0 < z → z*Real.exp (-(z^ε)/d) ≤ C*z^r := by
  let s := (1-r)/ε
  have hs : 0 ≤ s := by dsimp [s]; positivity
  obtain ⟨K,hK,hKb⟩ := exists_exp_neg_le_rpow s hs
  refine ⟨K*d^s,by positivity,?_⟩
  intro z hz
  have he := mul_le_mul_of_nonneg_left (hKb (z^ε/d) (by positivity)) hz.le
  have hex : ε*(-s) = r-1 := by dsimp [s]; field_simp; ring
  have hid : (z^ε/d)^(-s) = z^(r-1)*d^s := by
    rw [Real.div_rpow (Real.rpow_nonneg hz.le ε) hd.le,←Real.rpow_mul hz.le,hex,
      Real.rpow_neg hd.le,div_inv_eq_mul]
  have hzpow : z*z^(r-1) = z^r := by
    conv_lhs => lhs; rw [←Real.rpow_one z]
    rw [←Real.rpow_add hz]
    congr 1
    ring
  calc
    _ ≤ z*(K*(z^ε/d)^(-s)) := by simpa only [neg_div] using he
    _ = (K*d^s)*(z*z^(r-1)) := by rw [hid]; ring
    _ = _ := by rw [hzpow]

theorem contact_tail_exponent (d z ε : ℝ) (hd : 0 < d) (hz : 0 < z) :
    -2*(z^((1:ℝ)/2+ε))^2/(d*(2*z)) = -(z^(2*ε))/d := by
  have hpow : (z^((1:ℝ)/2+ε))^2 = z*z^(2*ε) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
    norm_num only [Nat.cast_ofNat]
    rw [show ((1:ℝ)/2+ε)*2 = 1+2*ε by ring,Real.rpow_add hz,Real.rpow_one]
  rw [hpow]
  field_simp

end StretchedContactDecay
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section UniformContactBins
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem clusterContactBin_power_bound [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (q : unitInterval)
    (α ε C p₀ : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hε : 0 < ε)
    (hr : (1:ℝ)/2+ε-2*α < 0) (hC0 : 0 < C) (hp₀ : 0 < p₀)
    (hfin : ∀ y, ∀ᵐ ω ∂law q, (cluster G ω y).Finite)
    (hI : ∀ y, Integrable (fun ω => ((cluster G ω y).ncard:ℝ)^α) (law q))
    (hC : ∀ y, (∫ ω, ((cluster G ω y).ncard:ℝ)^α ∂law q) ≤ C)
    (d : ℕ) (hd : 0 < d) :
    ∃ A : ℝ, 0 < A ∧ ∀ (Q : Finset E), (∀ z, (Q.filter fun e => z ∈ G e).card ≤ d) →
      ∀ (x v : V) (p : unitInterval), p₀ ≤ (p:ℝ) → p ≤ q → ∀ n : ℕ, 1 ≤ n →
      bernoulliPolynomial Q (clusterContactBin G Q x v n (2*n)) p ≤
        A*(n:ℝ)^((1:ℝ)/2+ε-2*α) := by
  let r : ℝ := (1:ℝ)/2+ε-2*α
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr hd
  obtain ⟨K,hK,hKb⟩ := exists_stretched_exp_volume_bound (d:ℝ) (2*ε) r hd' (by positivity) (by dsimp [r]; linarith)
  refine ⟨8*C^2/p₀+16*(d:ℝ)*K,by positivity,?_⟩
  intro Q hdeg x v p hpp hpq n hn
  have hn' : 0 < n := by omega
  have hnr : (0:ℝ) < n := Nat.cast_pos.mpr hn'
  have hp : 0 < (p:ℝ) := hp₀.trans_le hpp
  let a : ℝ := (n:ℝ)^((1:ℝ)/2+ε)
  have ha : 0 < a := Real.rpow_pos_of_pos hnr _
  have hb := clusterContactBin_bound G Q d hdeg x v p hp n (2*n) (by positivity) a ha
  have ht (y : V) := finiteClusterTail_of_endpoint_moment G hloc q α C hα hα1 hfin hI hC Q y p hpq n hn
  have hprod : finiteClusterTail G Q v n p*finiteClusterTail G Q x n p ≤ 4*C^2*(n:ℝ)^(-2*α) := by
    calc
      _ ≤ (2*C*(n:ℝ)^(-α))*(2*C*(n:ℝ)^(-α)) :=
        mul_le_mul (ht v) (ht x) (finiteClusterTail_nonneg G Q x n p) (by positivity)
      _ = _ := by
        rw [show (2*C*(n:ℝ)^(-α))*(2*C*(n:ℝ)^(-α)) = 4*C^2*((n:ℝ)^(-α)*(n:ℝ)^(-α)) by ring,
          ←Real.rpow_add hnr]
        congr 2
        ring
  have hfirst : (2*a/(p:ℝ))*(finiteClusterTail G Q v n p*finiteClusterTail G Q x n p) ≤
      (8*C^2/p₀)*(n:ℝ)^r := by
    calc
      _ ≤ (2*a/p₀)*(4*C^2*(n:ℝ)^(-2*α)) :=
        mul_le_mul (div_le_div_of_nonneg_left (by positivity) hp₀ hpp) hprod
          (mul_nonneg (finiteClusterTail_nonneg G Q v n p) (finiteClusterTail_nonneg G Q x n p)) (by positivity)
      _ = (8*C^2/p₀)*((n:ℝ)^((1:ℝ)/2+ε)*(n:ℝ)^(-2*α)) := by dsimp [a]; ring
      _ = _ := by rw [←Real.rpow_add hnr]; congr 2; dsimp [r]; ring
  have hex : -2*a^2/(d*(2*n):ℕ) = -((n:ℝ)^(2*ε))/(d:ℝ) := by
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    exact contact_tail_exponent d n ε hd' hnr
  have hsecond : (d*(2*n):ℕ)*(8*Real.exp (-2*a^2/(d*(2*n):ℕ))) ≤
      (16*(d:ℝ)*K)*(n:ℝ)^r := by
    rw [hex]
    calc
      _ = (16*(d:ℝ))*((n:ℝ)*Real.exp (-((n:ℝ)^(2*ε))/(d:ℝ))) := by
        push_cast
        ring
      _ ≤ (16*(d:ℝ))*(K*(n:ℝ)^r) := mul_le_mul_of_nonneg_left (hKb n hnr) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ _ := hb
    _ ≤ (8*C^2/p₀)*(n:ℝ)^r+(16*(d:ℝ)*K)*(n:ℝ)^r := add_le_add hfirst hsecond
    _ = _ := by dsimp [r]; ring

end UniformContactBins
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section InfiniteContacts
attribute [local instance] Classical.propDecidable Classical.decEq

 
def closedContactSet (G : BondGraph V E) (A B : Set V) : Set E :=
  {e | ∃ a ∈ A, ∃ b ∈ B, G e = s(a,b)}

noncomputable def clusterContactCount (G : BondGraph V E) (ω : Set E) (x v : V) : ℕ :=
  (closedContactSet G (cluster G ω x) (cluster G ω v)).ncard

noncomputable def fullContactBin (G : BondGraph V E) (x v : V) (n m : ℕ) (ω : Set E) : ℝ :=
  if ¬Conn G ω x v ∧ n ≤ min (cluster G ω x).ncard (cluster G ω v).ncard ∧
    min (cluster G ω x).ncard (cluster G ω v).ncard ≤ m
  then clusterContactCount G ω x v else 0

theorem contactSet_subset_incident (G : BondGraph V E) (hloc : LocallyFinite G)
    (A : Finset V) (B : Set V) : closedContactSet G (A:Set V) B ⊆ (incidentSupport G hloc A:Set E) := by
  rintro e ⟨a,ha,b,_,hab⟩
  exact (mem_incidentSupport G hloc A e).mpr ⟨a,ha,by rw [hab]; simp⟩

theorem coe_contactBonds_eq (G : BondGraph V E) (hloc : LocallyFinite G)
    (Q : Finset E) (A B : Finset V) (hQ : incidentSupport G hloc A ⊆ Q) :
    (contactBonds G Q A B : Set E) = closedContactSet G A B := by
  ext e
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨hQ (contactSet_subset_incident G hloc A B h),h⟩

theorem contactSet_ncard_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ z, {e | z ∈ G e}.ncard ≤ d)
    (A B : Set V) (hA : A.Finite) (hB : B.Finite) :
    (closedContactSet G A B).ncard ≤ d*min A.ncard B.ncard := by
  let Q := incidentSupport G hloc (hA.toFinset ∪ hB.toFinset)
  have hdeg (z : V) : (Q.filter fun e => z ∈ G e).card ≤ d := by
    calc
      _ = ((Q.filter fun e => z ∈ G e):Set E).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ {e | z ∈ G e}.ncard := Set.ncard_le_ncard (fun e he => (Finset.mem_filter.mp he).2) (hloc z)
      _ ≤ d := hd z
  have hQ : incidentSupport G hloc hA.toFinset ⊆ Q :=
    incidentSupport_mono G hloc Finset.subset_union_left
  have he := coe_contactBonds_eq G hloc Q hA.toFinset hB.toFinset hQ
  simp only [Set.Finite.coe_toFinset] at he
  rw [←he,Set.ncard_coe_finset]
  simpa only [←Set.ncard_eq_toFinset_card] using contactBonds_card_le G Q d hdeg hA.toFinset hB.toFinset

theorem fullContactBin_nonneg (G : BondGraph V E) (x v : V) (n m : ℕ) (ω : Set E) :
    0 ≤ fullContactBin G x v n m ω := by unfold fullContactBin; split_ifs <;> positivity

theorem fullContactBin_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ z, {e | z ∈ G e}.ncard ≤ d) (x v : V) (n m : ℕ) (hn : 0 < n) (ω : Set E) :
    fullContactBin G x v n m ω ≤ (d*m:ℕ) := by
  unfold fullContactBin
  split_ifs with h
  · have hx : (cluster G ω x).Finite := Set.finite_of_ncard_ne_zero (by omega)
    have hv : (cluster G ω v).Finite := Set.finite_of_ncard_ne_zero (by omega)
    exact_mod_cast (contactSet_ncard_le G hloc d hd _ _ hx hv).trans (Nat.mul_le_mul_left d h.2.2)
  · positivity

end InfiniteContacts
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section ContactMeasurability
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_clusterContactCount [Countable V] [Countable E]
    (G : BondGraph V E) (x v : V) : Measurable (fun ω : Set E => clusterContactCount G ω x v) := by
  apply measurable_ncard.comp
  apply measurable_setOfPred.comp
  apply Measurable.of_eval
  intro e
  apply measurableSet_setOfPred.mp
  change MeasurableSet {ω : Set E | ∃ a, Conn G ω x a ∧ ∃ b, Conn G ω v b ∧ G e = s(a,b)}
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro a
  have he : {ω : Set E | Conn G ω x a ∧ ∃ b, Conn G ω v b ∧ G e = s(a,b)} =
      {ω | Conn G ω x a} ∩ ⋃ b, {ω | Conn G ω v b ∧ G e = s(a,b)} := by ext ω; simp
  rw [he]
  apply (measurableSet_conn G x a).inter
  apply MeasurableSet.iUnion
  intro b
  by_cases h : G e = s(a,b)
  · simpa only [h,and_true] using measurableSet_conn G v b
  · simp only [h,and_false,Set.ofPred_false]; exact MeasurableSet.empty

theorem measurable_fullContactBin [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x v : V) (n m : ℕ) :
    Measurable (fullContactBin G x v n m) := by
  have hs : Measurable (fun ω : Set E => min (cluster G ω x).ncard (cluster G ω v).ncard) :=
    (measurable_cluster_ncard G hloc x).min (measurable_cluster_ncard G hloc v)
  exact ((measurable_of_countable (fun k : ℕ => (k:ℝ))).comp (measurable_clusterContactCount G x v)).ite
    (((measurableSet_conn G x v).compl).inter ((measurableSet_le measurable_const hs).inter
      (measurableSet_le hs measurable_const))) measurable_const

theorem coe_domainBits (Q : Finset E) (ω : Set E) :
    (domainBits Q ω:Set E) = ω ∩ (Q:Set E) := by ext e; simp only [mem_domainBits,Set.mem_inter_iff,Finset.mem_coe,and_comm]

theorem domainBits_local (Q : Finset E) (ω : Set E) :
    domainBits Q (ω ∩ (Q:Set E)) = domainBits Q ω := by
  ext e
  simp only [mem_domainBits,Set.mem_inter_iff,Finset.mem_coe]
  tauto

theorem domainBits_of_subset (Q ω : Finset E) (hω : ω ⊆ Q) : domainBits Q (ω:Set E) = ω := by
  ext e
  simp only [mem_domainBits,Finset.mem_coe]
  exact ⟨fun h => h.2,fun h => ⟨hω h,h⟩⟩

theorem integral_domainBits (Q : Finset E) (p : unitInterval) (f : Finset E → ℝ) :
    (∫ ω, f (domainBits Q ω) ∂law p) = bernoulliPolynomial Q f p := by
  rw [integral_eq_bernoulliPolynomial Q p _ (fun ω => by rw [domainBits_local])]
  apply bernoulliPolynomial_congr
  intro ω hω
  rw [domainBits_of_subset Q ω hω]

end ContactMeasurability
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section InfiniteContactLimit
attribute [local instance] Classical.propDecidable Classical.decEq

theorem fullContactBin_eq_finite (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x v : V) (hx : (cluster G ω x).Finite) (hv : (cluster G ω v).Finite)
    (Q : Finset E) (hQx : incidentSupport G hloc hx.toFinset ⊆ Q)
    (hQv : incidentSupport G hloc hv.toFinset ⊆ Q) (n m : ℕ) :
    clusterContactBin G Q x v n m (domainBits Q ω) = fullContactBin G x v n m ω := by
  have hcluster (y : V) (hy : (cluster G ω y).Finite) (hQ : incidentSupport G hloc hy.toFinset ⊆ Q) :
      cluster G (domainBits Q ω:Set E) y = cluster G ω y := by
    rw [coe_domainBits]
    have hh := (cluster_restrict_incident_eq_iff G hloc hy.toFinset Q hQ ω y).mpr
      (Set.Finite.coe_toFinset hy).symm
    simpa only [Set.Finite.coe_toFinset] using hh
  have hcx := hcluster x hx hQx
  have hcv := hcluster v hv hQv
  have hFx : finiteRootComponent G (domainBits Q ω) x = hx.toFinset := by
    apply Finset.coe_injective
    rw [coe_finiteRootComponent,hcx,Set.Finite.coe_toFinset]
  have hFv : finiteRootComponent G (domainBits Q ω) v = hv.toFinset := by
    apply Finset.coe_injective
    rw [coe_finiteRootComponent,hcv,Set.Finite.coe_toFinset]
  have hconn : Conn G (domainBits Q ω:Set E) x v ↔ Conn G ω x v := by
    change v ∈ cluster G (domainBits Q ω:Set E) x ↔ v ∈ cluster G ω x
    rw [hcx]
  have hc : (contactBonds G Q hx.toFinset hv.toFinset).card = clusterContactCount G ω x v := by
    rw [←Set.ncard_coe_finset,coe_contactBonds_eq G hloc Q _ _ hQx]
    simp only [Set.Finite.coe_toFinset,clusterContactCount]
  simp only [clusterContactBin,fullContactBin,hconn,hFx,hFv,←Set.ncard_eq_toFinset_card,hc]

theorem clusterContactBin_norm_le (G : BondGraph V E) (Q : Finset E)
    (d : ℕ) (hd : ∀ z, (Q.filter fun e => z ∈ G e).card ≤ d)
    (x v : V) (n m : ℕ) (ω : Finset E) : ‖clusterContactBin G Q x v n m ω‖ ≤ (d*m:ℕ) := by
  unfold clusterContactBin
  split_ifs with h
  · rw [Real.norm_natCast]
    exact_mod_cast (contactBonds_card_le G Q d hd _ _).trans (Nat.mul_le_mul_left d h.2.2)
  · simp only [norm_zero]; positivity

theorem fullContactBin_integral_le_of_finite [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (d : ℕ)
    (hd : ∀ z, {e | z ∈ G e}.ncard ≤ d) (x v : V) (p : unitInterval)
    (hx : ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (hv : ∀ᵐ ω ∂law p, (cluster G ω v).Finite) (n m : ℕ) (B : ℝ)
    (hB : ∀ Q : Finset E, bernoulliPolynomial Q (clusterContactBin G Q x v n m) p ≤ B) :
    (∫ ω, fullContactBin G x v n m ω ∂law p) ≤ B := by
  let : Encodable E := Encodable.ofCountable E
  let Q := vertexExhaustion (V := E)
  let f := fun j ω => clusterContactBin G (Q j) x v n m (domainBits (Q j) ω)
  have hfl (j : ℕ) (ω : Set E) : f j ω = f j (ω ∩ (Q j:Set E)) := by
    dsimp [f]; rw [domainBits_local]
  have hfi (j : ℕ) : Integrable (f j) (law p) := integrable_finite_local (Q j) p (f j) (hfl j)
  have hdeg (j : ℕ) (z : V) : ((Q j).filter fun e => z ∈ G e).card ≤ d := by
    calc
      _ = (((Q j).filter fun e => z ∈ G e):Set E).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ {e | z ∈ G e}.ncard := Set.ncard_le_ncard (fun e he => (Finset.mem_filter.mp he).2) (hloc z)
      _ ≤ d := hd z
  have ht : ∀ᵐ ω ∂law p, Tendsto (fun j => f j ω) atTop (nhds (fullContactBin G x v n m ω)) := by
    filter_upwards [hx,hv] with ω hωx hωv
    obtain ⟨jx,hjx⟩ := subset_vertexExhaustion (incidentSupport G hloc hωx.toFinset)
    obtain ⟨jv,hjv⟩ := subset_vertexExhaustion (incidentSupport G hloc hωv.toFinset)
    have he : (fun j => f j ω) =ᶠ[atTop] (fun _ => fullContactBin G x v n m ω) := by
      filter_upwards [eventually_ge_atTop (max jx jv)] with j hj
      exact fullContactBin_eq_finite G hloc ω x v hωx hωv (Q j)
        (hjx.trans (vertexExhaustion_mono (le_max_left jx jv |>.trans hj)))
        (hjv.trans (vertexExhaustion_mono (le_max_right jx jv |>.trans hj))) n m
    exact tendsto_const_nhds.congr' he.symm
  have hdom := tendsto_integral_of_dominated_convergence (fun _ : Set E => (d*m:ℕ))
    (fun j => (hfi j).aestronglyMeasurable) (integrable_const _)
    (fun j => Eventually.of_forall (fun ω => clusterContactBin_norm_le G (Q j) d (hdeg j) x v n m _)) ht
  apply le_of_tendsto hdom
  exact Eventually.of_forall (fun j => by rw [show (∫ ω, f j ω ∂law p) =
    bernoulliPolynomial (Q j) (clusterContactBin G (Q j) x v n m) p from by dsimp [f]; exact integral_domainBits (Q j) p (clusterContactBin G (Q j) x v n m)]; exact hB (Q j))

end InfiniteContactLimit
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FullContactPower
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem fullContactBin_power_bound [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (q : unitInterval)
    (α ε C p₀ : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hε : 0 < ε)
    (hr : (1:ℝ)/2+ε-2*α < 0) (hC0 : 0 < C) (hp₀ : 0 < p₀)
    (hfin : ∀ y, ∀ᵐ ω ∂law q, (cluster G ω y).Finite)
    (hI : ∀ y, Integrable (fun ω => ((cluster G ω y).ncard:ℝ)^α) (law q))
    (hC : ∀ y, (∫ ω, ((cluster G ω y).ncard:ℝ)^α ∂law q) ≤ C)
    (d : ℕ) (hd : 0 < d) (hdeg : ∀ z, {e | z ∈ G e}.ncard ≤ d) :
    ∃ A : ℝ, 0 < A ∧ ∀ (x v : V) (p : unitInterval), p₀ ≤ (p:ℝ) → p ≤ q →
      ∀ n : ℕ, 1 ≤ n → (∫ ω, fullContactBin G x v n (2*n) ω ∂law p) ≤
        A*(n:ℝ)^((1:ℝ)/2+ε-2*α) := by
  obtain ⟨A,hA,hAb⟩ := clusterContactBin_power_bound G hloc q α ε C p₀ hα hα1 hε hr hC0 hp₀ hfin hI hC d hd
  refine ⟨A,hA,?_⟩
  intro x v p hpp hpq n hn
  apply fullContactBin_integral_le_of_finite G hloc d hdeg x v p
    (cluster_finite_ae_mono G x p q hpq (hfin x)) (cluster_finite_ae_mono G v p q hpq (hfin v))
  intro Q
  apply hAb Q _ x v p hpp hpq n hn
  intro z
  calc
    _ = ((Q.filter fun e => z ∈ G e):Set E).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ {e | z ∈ G e}.ncard := Set.ncard_le_ncard (fun e he => (Finset.mem_filter.mp he).2) (hloc z)
    _ ≤ d := hdeg z

theorem integrable_fullContactBin [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (d : ℕ)
    (hd : ∀ z, {e | z ∈ G e}.ncard ≤ d) (x v : V) (n m : ℕ) (hn : 0 < n) (p : unitInterval) :
    Integrable (fullContactBin G x v n m) (law p) := by
  apply Integrable.mono' (integrable_const ((d*m:ℕ):ℝ)) (measurable_fullContactBin G hloc x v n m).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (fullContactBin_nonneg G x v n m ω)]
    exact fullContactBin_le G hloc d hd x v n m hn ω)

end FullContactPower
end Percolation

 
namespace Percolation
open MeasureTheory
section NonnegativeDyadicIntegration

 

theorem integral_le_tsum_majorants {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (F : ℕ → Ω → ℝ) (hfm : AEStronglyMeasurable f μ)
    (hf0 : ∀ ω, 0 ≤ f ω) (hF0 : ∀ j ω, 0 ≤ F j ω) (hFi : ∀ j, Integrable (F j) μ)
    (hs : Summable (fun j => ∫ ω, F j ω ∂μ))
    (hb : ∀ ω, ENNReal.ofReal (f ω) ≤ ∑' j, ENNReal.ofReal (F j ω)) :
    Integrable f μ ∧ (∫ ω, f ω ∂μ) ≤ ∑' j, ∫ ω, F j ω ∂μ := by
  have he : (∫⁻ ω, ∑' j, ENNReal.ofReal (F j ω) ∂μ) =
      ENNReal.ofReal (∑' j, ∫ ω, F j ω ∂μ) := by
    rw [lintegral_tsum (fun j => (hFi j).aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
    simp_rw [←ofReal_integral_eq_lintegral_ofReal (hFi _) (Filter.Eventually.of_forall (hF0 _))]
    exact (ENNReal.ofReal_tsum_of_nonneg (fun j => integral_nonneg (hF0 j)) hs).symm
  have hle := (lintegral_mono hb).trans_eq he
  have hi : Integrable f μ := ⟨hfm,(hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf0)).mpr
    (hle.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi,?_⟩
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hf0)] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (tsum_nonneg (fun j => integral_nonneg (hF0 j)))).mp hle

theorem dyadic_rpow_identity (L : ℕ) (hL : 0 < L) (r : ℝ) (j : ℕ) :
    ((2^j*L:ℕ):ℝ)^r = (L:ℝ)^r*((2:ℝ)^r)^j := by
  rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Real.mul_rpow (by positivity) (by positivity),
    ←Real.rpow_natCast,←Real.rpow_mul (by norm_num),mul_comm (j:ℝ) r,Real.rpow_mul (by norm_num),Real.rpow_natCast,mul_comm]

theorem dyadic_rpow_summable (L : ℕ) (hL : 0 < L) (r : ℝ) (hr : r < 0) :
    Summable (fun j : ℕ => ((2^j*L:ℕ):ℝ)^r) := by
  simp only [dyadic_rpow_identity L hL r]
  exact (summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hr)).mul_left _

theorem dyadic_rpow_sum (L : ℕ) (hL : 0 < L) (r : ℝ) (hr : r < 0) :
    (∑' j : ℕ, ((2^j*L:ℕ):ℝ)^r) = (L:ℝ)^r*(1-(2:ℝ)^r)⁻¹ := by
  simp only [dyadic_rpow_identity L hL r,tsum_mul_left]
  rw [tsum_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) _) (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hr)]

end NonnegativeDyadicIntegration
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FullLargeContacts
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def fullLargeContact (G : BondGraph V E) (x v : V) (L : ℕ) (ω : Set E) : ℝ :=
  if ¬Conn G ω x v ∧ L ≤ min (cluster G ω x).ncard (cluster G ω v).ncard
  then clusterContactCount G ω x v else 0

theorem fullLargeContact_nonneg (G : BondGraph V E) (x v : V) (L : ℕ) (ω : Set E) :
    0 ≤ fullLargeContact G x v L ω := by unfold fullLargeContact; split_ifs <;> positivity

theorem measurable_fullLargeContact [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x v : V) (L : ℕ) :
    Measurable (fullLargeContact G x v L) := by
  have hs : Measurable (fun ω : Set E => min (cluster G ω x).ncard (cluster G ω v).ncard) :=
    (measurable_cluster_ncard G hloc x).min (measurable_cluster_ncard G hloc v)
  exact ((measurable_of_countable (fun k : ℕ => (k:ℝ))).comp (measurable_clusterContactCount G x v)).ite
    (((measurableSet_conn G x v).compl).inter (measurableSet_le measurable_const hs)) measurable_const

theorem fullLargeContact_le_dyadic (G : BondGraph V E) (x v : V) (L : ℕ) (hL : 0 < L) (ω : Set E) :
    ENNReal.ofReal (fullLargeContact G x v L ω) ≤
      ∑' j : ℕ, ENNReal.ofReal (fullContactBin G x v (2^j*L) (2*(2^j*L)) ω) := by
  by_cases h : ¬Conn G ω x v ∧ L ≤ min (cluster G ω x).ncard (cluster G ω v).ncard
  · let k := min (cluster G ω x).ncard (cluster G ω v).ncard
    let j := Nat.log 2 (k/L)
    have hq : k/L ≠ 0 := by
      have : 1 ≤ k/L := (Nat.le_div_iff_mul_le hL).mpr (by rw [one_mul]; exact h.2)
      omega
    have hl := (Nat.le_div_iff_mul_le hL).mp (Nat.pow_log_le_self 2 hq)
    have hu := (Nat.div_lt_iff_lt_mul hL).mp (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) (k/L))
    have hbin : fullContactBin G x v (2^j*L) (2*(2^j*L)) ω = fullLargeContact G x v L ω := by
      rw [fullLargeContact,ite_eq_left h,fullContactBin,ite_eq_left]
      refine ⟨h.1,hl,?_⟩
      calc
        _ = k := rfl
        _ ≤ 2^(Nat.log 2 (k/L)+1)*L := hu.le
        _ = _ := by dsimp [j]; rw [pow_succ]; ring
    exact (le_of_eq (congrArg ENNReal.ofReal hbin.symm)).trans
      (ENNReal.le_tsum (f := fun scale =>
        ENNReal.ofReal (fullContactBin G x v (2^scale*L) (2*(2^scale*L)) ω)) j)
  · simp only [fullLargeContact,ite_eq_right h,ENNReal.ofReal_zero]; exact bot_le

 

theorem fullLargeContact_bound_of_bins [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (d : ℕ)
    (hd : ∀ z, {e | z ∈ G e}.ncard ≤ d) (x v : V) (p : unitInterval)
    (A r : ℝ) (_hA : 0 ≤ A) (hr : r < 0)
    (hB : ∀ n : ℕ, 1 ≤ n → (∫ ω, fullContactBin G x v n (2*n) ω ∂law p) ≤ A*(n:ℝ)^r)
    (L : ℕ) (hL : 0 < L) :
    Integrable (fullLargeContact G x v L) (law p) ∧
      (∫ ω, fullLargeContact G x v L ω ∂law p) ≤ A*(1-(2:ℝ)^r)⁻¹*(L:ℝ)^r := by
  let F := fun j => fullContactBin G x v (2^j*L) (2*(2^j*L))
  have hbp (j : ℕ) : 0 < 2^j*L := Nat.mul_pos (pow_pos (by norm_num) _) hL
  have hFi (j : ℕ) : Integrable (F j) (law p) := integrable_fullContactBin G hloc d hd x v _ _ (hbp j) p
  have hsumB := (dyadic_rpow_summable L hL r hr).mul_left A
  have hsum : Summable (fun j => ∫ ω, F j ω ∂law p) :=
    hsumB.of_nonneg_of_le (fun j => integral_nonneg (fullContactBin_nonneg G x v _ _))
      (fun j => hB _ (hbp j))
  obtain ⟨hi,hb⟩ := integral_le_tsum_majorants (law p) (fullLargeContact G x v L) F
    (measurable_fullLargeContact G hloc x v L).aestronglyMeasurable
    (fullLargeContact_nonneg G x v L) (fun j => fullContactBin_nonneg G x v _ _) hFi hsum
    (fullLargeContact_le_dyadic G x v L hL)
  refine ⟨hi,hb.trans ?_⟩
  calc
    _ ≤ ∑' j : ℕ, A*((2^j*L:ℕ):ℝ)^r := hsum.tsum_le_tsum (fun j => hB _ (hbp j)) hsumB
    _ = _ := by rw [tsum_mul_left,dyadic_rpow_sum L hL r hr]; ring

end FullLargeContacts
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section UniformLargeContacts
attribute [local instance] Classical.propDecidable Classical.decEq

theorem incident_ncard_le_degree (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) :
    {e | x ∈ G e}.ncard ≤ degree G x := by
  have he : ((hloc x).toFinset.filter fun e => x ∈ G e) = (hloc x).toFinset := by
    ext e
    simp only [Finset.mem_filter,Set.Finite.mem_toFinset,Set.mem_ofPred_eq,and_self]
  simpa only [he,←Set.ncard_eq_toFinset_card] using incident_filter_card_le_degree G hloc (hloc x).toFinset x

theorem fullLargeContact_power_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G) (q : unitInterval)
    (α ε C p₀ : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hε : 0 < ε)
    (hr : (1:ℝ)/2+ε-2*α < 0) (hC0 : 0 < C) (hp₀ : 0 < p₀)
    (hfin : ∀ y, ∀ᵐ ω ∂law q, (cluster G ω y).Finite)
    (hI : ∀ y, Integrable (fun ω => ((cluster G ω y).ncard:ℝ)^α) (law q))
    (hC : ∀ y, (∫ ω, ((cluster G ω y).ncard:ℝ)^α ∂law q) ≤ C) :
    ∃ A : ℝ, 0 < A ∧ ∀ (x v : V) (p : unitInterval), p₀ ≤ (p:ℝ) → p ≤ q →
      ∀ L : ℕ, 1 ≤ L → Integrable (fullLargeContact G x v L) (law p) ∧
        (∫ ω, fullLargeContact G x v L ω ∂law p) ≤ A*(L:ℝ)^((1:ℝ)/2+ε-2*α) := by
  obtain ⟨d,hd,hdeg⟩ := exists_degree_bound G hqt
  have hdn (x : V) := (incident_ncard_le_degree G hloc x).trans (hdeg x)
  obtain ⟨A,hA,hAb⟩ := fullContactBin_power_bound G hloc q α ε C p₀ hα hα1 hε hr hC0 hp₀ hfin hI hC d hd hdn
  refine ⟨A*(1-(2:ℝ)^((1:ℝ)/2+ε-2*α))⁻¹,?_ ,?_⟩
  · exact mul_pos hA (inv_pos.mpr (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hr)))
  · intro x v p hpp hpq L hL
    exact fullLargeContact_bound_of_bins G hloc d hdn x v p A _ hA.le hr (hAb x v p hpp hpq) L hL

 

theorem critical_large_contact_bound
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
    (α ε : ℝ) (hα : 0 < α) (hα1 : α < 1/2) (hε : 0 < ε)
    (hr : (1:ℝ)/2+ε-2*α < 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ (x v : V) (p : unitInterval), (pc G:ℝ)/2 ≤ (p:ℝ) → p ≤ pc G →
      ∀ L : ℕ, 1 ≤ L → Integrable (fullLargeContact G x v L) (law p) ∧
        (∫ ω, fullLargeContact G x v L ω ∂law p) ≤ A*(L:ℝ)^((1:ℝ)/2+ε-2*α) := by
  have hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i) := by
    intro x
    obtain ⟨i,a,ha,hax⟩ := hcov x
    obtain ⟨b,hab⟩ := hΓ ha
    exact ⟨i,a,b,hab,hax⟩
  have hfinite : ∀ x, ∀ᵐ ω ∂law (pc G), (cluster G ω x).Finite := by
    intro x
    obtain ⟨i,a,b,hab,rfl⟩ := hcover x
    exact cluster_finite_ae_covariant G (pc G) hab (root i) (hfin i)
  obtain ⟨C,hC,hb⟩ := uniform_cluster_power_of_root G hloc (pc G) root hcover α
    (critical_root_power_integrable G hloc hconn hqt hh root weight Γ hΓ htr hcov hw hw1 hp₀ hp₁ hfin α hα hα1)
  exact fullLargeContact_power_bound G hloc hqt (pc G) α ε C ((pc G:ℝ)/2) hα.le (by linarith)
    hε hr hC (by positivity) hfinite (fun x => (hb x).1) (fun x => (hb x).2)

end UniformLargeContacts
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ExtendedTransport
attribute [local instance] Classical.propDecidable Classical.decEq

theorem enn_sum_iSup_nat {α : Type*} (s : Finset α) (f : ℕ → α → ℝ≥0∞)
    (hm : ∀ a, Monotone (fun n => f n a)) :
    (∑ a ∈ s, ⨆ n, f n a) = ⨆ n, ∑ a ∈ s, f n a := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha,ih]
    exact ENNReal.iSup_add_iSup_of_monotone (hm a) (fun n m h =>
      Finset.sum_le_sum fun a _ => hm a h)

theorem enn_tsum_iSup_nat {α : Type*} (f : ℕ → α → ℝ≥0∞)
    (hm : ∀ a, Monotone (fun n => f n a)) :
    (∑' a, ⨆ n, f n a) = ⨆ n, ∑' a, f n a := by
  simp_rw [ENNReal.tsum_eq_iSup_sum,enn_sum_iSup_nat _ f hm]
  exact iSup_comm

 

theorem RootTransport.ennreal (G : BondGraph V E) (hconn : Connected G)
    (hloc : LocallyFinite G) {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (m : V → V → ℝ≥0∞)
    (hi : ∀ a ∈ Γ, ∀ x y, m (a x) (a y) = m x y) :
    (∑ i, ENNReal.ofReal (weight i) * ∑' y, m (root i) y) =
      (∑ i, ENNReal.ofReal (weight i) * ∑' x, m x (root i)) := by
  let cut (n : ℕ) (x y : V) : ℝ≥0∞ :=
    if transportCut G n x y then min (m x y) n else 0
  have hc0 (n : ℕ) (x y : V) : cut n x y ≠ ⊤ := by
    dsimp [cut]
    split_ifs
    · exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_right _ _)
    · exact ENNReal.zero_ne_top
  have hcm (x y : V) : Monotone (fun n => cut n x y) := by
    intro n k hnk
    dsimp [cut]
    split_ifs with hn hk
    · exact min_le_min_left _ (by exact_mod_cast hnk)
    · exact False.elim (hk (transportCut_mono G hnk hn))
    · exact zero_le
    · exact le_refl _
  have hcs (x y : V) : (⨆ n, cut n x y) = m x y := by
    apply le_antisymm
    · refine iSup_le fun n => ?_
      dsimp [cut]
      split_ifs
      · exact min_le_left _ _
      · exact zero_le
    · obtain ⟨N,hN⟩ := exists_transportCut G hconn y {x}
      have hxy := hN x (Finset.mem_singleton_self x)
      have he : (⨆ k : ℕ, min (m x y) (k:ℝ≥0∞)) = m x y := by
        rw [←inf_iSup_eq,ENNReal.iSup_natCast,inf_top_eq]
      rw [←he]
      refine iSup_le fun k => le_iSup_of_le (max N k) ?_
      dsimp [cut]
      rw [ite_eq_left (transportCut_mono G (le_max_left N k) hxy)]
      exact min_le_min_left _ (by exact_mod_cast le_max_right N k)
  have hrow (n : ℕ) (x : V) : Summable (fun y => (cut n x y).toReal) := by
    apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x n).toFinset)
    intro y hy
    have hh : ¬transportCut G n x y := fun h => hy ((Set.Finite.mem_toFinset _).mpr h.1)
    simp only [cut,ite_eq_right hh,ENNReal.toReal_zero]
  have hcol (n : ℕ) (y : V) : Summable (fun x => (cut n x y).toReal) := by
    apply summable_of_ne_finset_zero (s := (finite_reachBall hloc y n).toFinset)
    intro x hx
    have hh : ¬transportCut G n x y := fun h => hx ((Set.Finite.mem_toFinset _).mpr h.2)
    simp only [cut,ite_eq_right hh,ENNReal.toReal_zero]
  have he (n : ℕ) :
      (∑ i, ENNReal.ofReal (weight i) * ∑' y, cut n (root i) y) =
        (∑ i, ENNReal.ofReal (weight i) * ∑' x, cut n x (root i)) := by
    have ht := htr.real root weight Γ (fun x y => (cut n x y).toReal)
      (fun a ha x y => by
        obtain ⟨b,hb⟩ := hΓ ha
        simp only [cut,transportCut_aut G hb,hi a ha]) (hrow n) (hcol n)
    apply_fun ENNReal.ofReal at ht
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hw i)
      (tsum_nonneg fun _ => ENNReal.toReal_nonneg)),
      ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hw i)
      (tsum_nonneg fun _ => ENNReal.toReal_nonneg))] at ht
    simp_rw [ENNReal.ofReal_mul (hw _),
      ENNReal.ofReal_tsum_of_nonneg (fun _ => ENNReal.toReal_nonneg) (hrow n _),
      ENNReal.ofReal_tsum_of_nonneg (fun _ => ENNReal.toReal_nonneg) (hcol n _),
      ENNReal.ofReal_toReal (hc0 n _ _)] at ht
    exact ht
  have hlim (f : ι → V → ℝ≥0∞) (g : ℕ → ι → V → ℝ≥0∞)
      (hmono : ∀ i y, Monotone (fun n => g n i y)) (hs : ∀ i y, (⨆ n, g n i y) = f i y) :
      (∑ i, ENNReal.ofReal (weight i) * ∑' y, f i y) =
        ⨆ n, ∑ i, ENNReal.ofReal (weight i) * ∑' y, g n i y := by
    simp_rw [←hs,enn_tsum_iSup_nat _ (hmono _),ENNReal.mul_iSup]
    exact enn_sum_iSup_nat _ _ (fun i n k h => mul_le_mul_right (ENNReal.tsum_le_tsum
      (fun y => hmono i y h)) _)
  rw [hlim (fun i y => m (root i) y) (fun n i y => cut n (root i) y)
    (fun i y => hcm (root i) y) (fun i y => hcs (root i) y),
    hlim (fun i x => m x (root i)) (fun n i x => cut n x (root i))
    (fun i x => hcm x (root i)) (fun i x => hcs x (root i))]
  exact iSup_congr he

end ExtendedTransport
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ClusterAveraging
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def clusterAveragingKernel (G : BondGraph V E) (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if Conn G ω x y then ((cluster G ω x).ncard:ℝ≥0∞)⁻¹ else 0

theorem measurable_clusterAveragingKernel [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x y : V) :
    Measurable (fun ω => clusterAveragingKernel G ω x y) := by
  exact (((measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp
    (measurable_cluster_ncard G hloc x)).inv).ite (measurableSet_conn G x y) measurable_const

theorem clusterAveragingKernel_symm (G : BondGraph V E) (ω : Set E) (x y : V) :
    clusterAveragingKernel G ω x y = clusterAveragingKernel G ω y x := by
  by_cases h : Conn G ω x y
  · simp only [clusterAveragingKernel,ite_eq_left h,ite_eq_left (conn_symm G ω h),cluster_eq_of_conn G ω h]
  · have h' : ¬Conn G ω y x := fun hh => h (conn_symm G ω hh)
    simp only [clusterAveragingKernel,ite_eq_right h,ite_eq_right h']

theorem cluster_ncard_pos (G : BondGraph V E) (ω : Set E) (x : V)
    (hf : (cluster G ω x).Finite) : 0 < (cluster G ω x).ncard :=
  (Set.ncard_pos hf).mpr ⟨x,mem_cluster_self G ω x⟩

theorem clusterAveragingKernel_row (G : BondGraph V E) (ω : Set E) (x : V)
    (hf : (cluster G ω x).Finite) : (∑' y, clusterAveragingKernel G ω x y) = 1 := by
  have he : (fun y => clusterAveragingKernel G ω x y) =
      (fun y => (if Conn G ω x y then (1:ℝ≥0∞) else 0)*((cluster G ω x).ncard:ℝ≥0∞)⁻¹) := by
    funext y
    unfold clusterAveragingKernel
    split_ifs <;> simp
  rw [he,ENNReal.tsum_mul_right]
  change clusterMass G ω x * ((cluster G ω x).ncard:ℝ≥0∞)⁻¹ = 1
  rw [clusterMass_eq_ncard G ω x hf]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast (cluster_ncard_pos G ω x hf).ne') (ENNReal.natCast_ne_top _)

theorem clusterAveragingKernel_column (G : BondGraph V E) (ω : Set E) (y : V)
    (hf : (cluster G ω y).Finite) : (∑' x, clusterAveragingKernel G ω x y) = 1 := by
  simp_rw [clusterAveragingKernel_symm G ω]
  exact clusterAveragingKernel_row G ω y hf

theorem clusterAveragingKernel_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x y : V) :
    clusterAveragingKernel G (b ⁻¹' ω) x y = clusterAveragingKernel G ω (a x) (a y) := by
  simp only [clusterAveragingKernel,conn_aut_iff G hab,cluster_ncard_covariant G hab]

 

theorem root_cluster_average [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (p : unitInterval)
    (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (f : Set E → V → ℝ≥0∞) (hf : ∀ x, Measurable (fun ω => f ω x))
    (hi : ∀ a ∈ Γ, ∀ b, IsAut G a b → ∀ ω x, f (b ⁻¹' ω) x = f ω (a x)) :
    (∑ i, ENNReal.ofReal (weight i) * ∫⁻ ω, ∑' y,
      clusterAveragingKernel G ω (root i) y * f ω y ∂law p) =
    (∑ i, ENNReal.ofReal (weight i) * ∫⁻ ω, f ω (root i) ∂law p) := by
  let m (x y : V) : ℝ≥0∞ := ∫⁻ ω, clusterAveragingKernel G ω x y * f ω y ∂law p
  have hm (x y : V) : Measurable (fun ω => clusterAveragingKernel G ω x y * f ω y) :=
    (measurable_clusterAveragingKernel G hloc x y).mul (hf y)
  have hinv : ∀ a ∈ Γ, ∀ x y, m (a x) (a y) = m x y := by
    intro a ha x y
    obtain ⟨b,hb⟩ := hΓ ha
    have ht := lintegral_map (μ := law p) (hm x y) (measurable_set_preimage b)
    rw [law_map_preimage_equiv] at ht
    dsimp only [m]
    rw [ht]
    apply lintegral_congr
    intro ω
    rw [clusterAveragingKernel_aut G hb,hi a ha b hb]
  have ht := htr.ennreal G hconn hloc root weight Γ hΓ hw m hinv
  have hr (x : V) : (∑' y, m x y) = ∫⁻ ω, ∑' y, clusterAveragingKernel G ω x y*f ω y ∂law p := by
    exact (lintegral_tsum (fun y => (hm x y).aemeasurable)).symm
  have hc (y : V) : (∑' x, m x y) = ∫⁻ ω, f ω y ∂law p := by
    rw [show (∑' x, m x y) = ∫⁻ ω, ∑' x, clusterAveragingKernel G ω x y*f ω y ∂law p from
      (lintegral_tsum (fun x => (hm x y).aemeasurable)).symm]
    apply lintegral_congr_ae
    filter_upwards [hfin y] with ω hω
    rw [ENNReal.tsum_mul_right,clusterAveragingKernel_column G ω y hω,one_mul]
  simpa only [hr,hc] using ht

end ClusterAveraging
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section PositiveClusterPairs
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def clusterPairKernel (G : BondGraph V E) (ω : Set E)
    (J : V → V → ℝ≥0∞) (x y : V) : ℝ≥0∞ :=
  ∑' a, ∑' b, if Conn G ω x a ∧ Conn G ω y b then J a b else 0

 

noncomputable def clusterPairDensity (G : BondGraph V E) (ω : Set E)
    (F : V → V → ℝ≥0∞) (x : V) : ℝ≥0∞ :=
  ((cluster G ω x).ncard:ℝ≥0∞)⁻¹ *
    ∑' y, ((cluster G ω y).ncard:ℝ≥0∞)⁻¹ * (if ¬Conn G ω x y then F x y else 0)

noncomputable def clusterPairFunctional (G : BondGraph V E) (p : unitInterval)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (F : Set E → V → V → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ i, ENNReal.ofReal (weight i) * ∫⁻ ω, clusterPairDensity G ω (F ω) (root i) ∂law p

theorem cluster_weighted_resum (G : BondGraph V E) (ω : Set E)
    (hfin : ∀ x, (cluster G ω x).Finite) (f : V → V → ℝ≥0∞)
    (hc : ∀ x y, Conn G ω x y → f x y = f y y) :
    (∑' x, ((cluster G ω x).ncard:ℝ≥0∞)⁻¹ *
      ∑' y, if Conn G ω x y then f x y else 0) = ∑' y, f y y := by
  have he (x y : V) : ((cluster G ω x).ncard:ℝ≥0∞)⁻¹ *
      (if Conn G ω x y then f x y else 0) = clusterAveragingKernel G ω x y*f y y := by
    by_cases h : Conn G ω x y
    · simp only [ite_eq_left h,clusterAveragingKernel,hc x y h]
    · simp only [ite_eq_right h,clusterAveragingKernel,mul_zero,zero_mul]
  simp_rw [←ENNReal.tsum_mul_left,he]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro y
  rw [ENNReal.tsum_mul_right,clusterAveragingKernel_column G ω y (hfin y),one_mul]

theorem clusterPairDensity_reroot_pointwise (G : BondGraph V E) (ω : Set E)
    (hfin : ∀ x, (cluster G ω x).Finite) (J F : V → V → ℝ≥0∞)
    (hF : ∀ x y a b, Conn G ω x a → Conn G ω y b → F x y = F a b) (x : V) :
    clusterPairDensity G ω (fun a b => clusterPairKernel G ω J a b * F a b) x =
      ∑' a, clusterAveragingKernel G ω x a *
        ∑' b, J a b * (if ¬Conn G ω a b then F a b else 0) := by
  let K (a b : V) : ℝ≥0∞ := if ¬Conn G ω a b then F a b else 0
  have hK (a b c d : V) (hac : Conn G ω a c) (hbd : Conn G ω b d) : K a b = K c d := by
    have he : Conn G ω a b ↔ Conn G ω c d := by
      constructor
      · intro h; exact conn_trans G ω (conn_symm G ω hac) (conn_trans G ω h hbd)
      · intro h; exact conn_trans G ω hac (conn_trans G ω h (conn_symm G ω hbd))
    simp only [K,he,hF a b c d hac hbd]
  have hterm (y : V) : ((cluster G ω y).ncard:ℝ≥0∞)⁻¹ *
      (if ¬Conn G ω x y then clusterPairKernel G ω J x y*F x y else 0) =
      ∑' a, if Conn G ω x a then ((cluster G ω y).ncard:ℝ≥0∞)⁻¹ *
        ∑' b, if Conn G ω y b then J a b*K x y else 0 else 0 := by
    have hcond : (if ¬Conn G ω x y then clusterPairKernel G ω J x y*F x y else 0) =
        clusterPairKernel G ω J x y*K x y := by dsimp [K]; split_ifs <;> simp
    rw [hcond,clusterPairKernel,←ENNReal.tsum_mul_right,←ENNReal.tsum_mul_left]
    apply tsum_congr
    intro a
    by_cases hxa : Conn G ω x a
    · rw [ite_eq_left hxa,←ENNReal.tsum_mul_right]
      congr 1
      apply tsum_congr
      intro b
      by_cases hyb : Conn G ω y b <;> simp only [hxa,hyb,and_self,and_false,
        ite_true,ite_false,zero_mul]
    · simp only [hxa,false_and,ite_false,tsum_zero,zero_mul,mul_zero]
  unfold clusterPairDensity
  simp_rw [hterm]
  rw [ENNReal.tsum_comm,←ENNReal.tsum_mul_left]
  apply tsum_congr
  intro a
  by_cases hxa : Conn G ω x a
  · simp only [ite_eq_left hxa,clusterAveragingKernel]
    congr 1
    rw [cluster_weighted_resum G ω hfin (fun y b => J a b*K x y)
      (fun y b hyb => congrArg (fun t => J a b*t) (hK x y x b (conn_refl G ω x) hyb))]
    apply tsum_congr
    intro b
    rw [hK x b a b hxa (conn_refl G ω b)]
  · simp only [ite_eq_right hxa,tsum_zero,mul_zero,clusterAveragingKernel,zero_mul]

end PositiveClusterPairs
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ClusterPairRerooting
attribute [local instance] Classical.propDecidable Classical.decEq

theorem clusterPairFunctional_reroot [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (p : unitInterval)
    (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (J : V → V → ℝ≥0∞) (hJ : ∀ a ∈ Γ, ∀ x y, J (a x) (a y) = J x y)
    (F : Set E → V → V → ℝ≥0∞) (hm : ∀ x y, Measurable (fun ω => F ω x y))
    (hF : ∀ ω x y a b, Conn G ω x a → Conn G ω y b → F ω x y = F ω a b)
    (hi : ∀ a ∈ Γ, ∀ b, IsAut G a b → ∀ ω x y, F (b ⁻¹' ω) x y = F ω (a x) (a y)) :
    clusterPairFunctional G p root weight (fun ω x y => clusterPairKernel G ω J x y * F ω x y) =
      ∑ i, ENNReal.ofReal (weight i) * ∫⁻ ω, ∑' y,
        J (root i) y * (if ¬Conn G ω (root i) y then F ω (root i) y else 0) ∂law p := by
  let f (ω : Set E) (x : V) : ℝ≥0∞ :=
    ∑' y, J x y * (if ¬Conn G ω x y then F ω x y else 0)
  have hf (x : V) : Measurable (fun ω => f ω x) := by
    apply Measurable.tsum
    intro y
    exact measurable_const.mul ((hm x y).ite (measurableSet_conn G x y).compl measurable_const)
  have hfe : ∀ a ∈ Γ, ∀ b, IsAut G a b → ∀ ω x, f (b ⁻¹' ω) x = f ω (a x) := by
    intro a ha b hab ω x
    dsimp [f]
    rw [←a.tsum_eq (fun y => J (a x) y * (if ¬Conn G ω (a x) y then F ω (a x) y else 0))]
    apply tsum_congr
    intro y
    rw [hJ a ha,conn_aut_iff G hab,hi a ha b hab]
  have ht := root_cluster_average G hconn hloc root weight Γ hΓ htr hw p hfin f hf hfe
  rw [clusterPairFunctional]
  calc
    _ = ∑ i, ENNReal.ofReal (weight i) * ∫⁻ ω, ∑' y,
        clusterAveragingKernel G ω (root i) y*f ω y ∂law p := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      apply lintegral_congr_ae
      filter_upwards [ae_all_iff.mpr hfin] with ω hω
      exact clusterPairDensity_reroot_pointwise G ω hω J (F ω) (hF ω) (root i)
    _ = _ := ht

end ClusterPairRerooting
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section PairReversal
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def clusterPairMass (G : BondGraph V E) (ω : Set E)
    (F : V → V → ℝ≥0∞) (x y : V) : ℝ≥0∞ :=
  ((cluster G ω x).ncard:ℝ≥0∞)⁻¹ * ((cluster G ω y).ncard:ℝ≥0∞)⁻¹ *
    (if ¬Conn G ω x y then F x y else 0)

theorem clusterPairDensity_eq_tsum (G : BondGraph V E) (ω : Set E)
    (F : V → V → ℝ≥0∞) (x : V) :
    clusterPairDensity G ω F x = ∑' y, clusterPairMass G ω F x y := by
  simp only [clusterPairDensity,clusterPairMass,←ENNReal.tsum_mul_left,mul_assoc]

theorem clusterPairMass_swap (G : BondGraph V E) (ω : Set E)
    (F : V → V → ℝ≥0∞) (x y : V) :
    clusterPairMass G ω F x y = clusterPairMass G ω (fun a b => F b a) y x := by
  have he : Conn G ω x y ↔ Conn G ω y x := ⟨conn_symm G ω,conn_symm G ω⟩
  simp only [clusterPairMass,he,mul_comm]

theorem measurable_clusterPairMass [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G)
    (F : Set E → V → V → ℝ≥0∞) (hf : ∀ x y, Measurable (fun ω => F ω x y)) (x y : V) :
    Measurable (fun ω => clusterPairMass G ω (F ω) x y) := by
  have hs (x : V) : Measurable (fun ω => ((cluster G ω x).ncard:ℝ≥0∞)⁻¹) :=
    (((measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp (measurable_cluster_ncard G hloc x))).inv
  exact ((hs x).mul (hs y)).mul ((hf x y).ite (measurableSet_conn G x y).compl measurable_const)

theorem clusterPairFunctional_swap [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (p : unitInterval)
    (F : Set E → V → V → ℝ≥0∞) (hf : ∀ x y, Measurable (fun ω => F ω x y))
    (hi : ∀ a ∈ Γ, ∀ b, IsAut G a b → ∀ ω x y, F (b ⁻¹' ω) x y = F ω (a x) (a y)) :
    clusterPairFunctional G p root weight F =
      clusterPairFunctional G p root weight (fun ω x y => F ω y x) := by
  let m (x y : V) : ℝ≥0∞ := ∫⁻ ω, clusterPairMass G ω (F ω) x y ∂law p
  have hm := measurable_clusterPairMass G hloc F hf
  have hinv : ∀ a ∈ Γ, ∀ x y, m (a x) (a y) = m x y := by
    intro a ha x y
    obtain ⟨b,hb⟩ := hΓ ha
    have ht := lintegral_map (μ := law p) (hm x y) (measurable_set_preimage b)
    rw [law_map_preimage_equiv] at ht
    dsimp only [m]
    rw [ht]
    apply lintegral_congr
    intro ω
    simp only [clusterPairMass,cluster_ncard_covariant G hb,conn_aut_iff G hb,hi a ha b hb]
  have ht := htr.ennreal G hconn hloc root weight Γ hΓ hw m hinv
  have hr (x : V) : (∑' y, m x y) = ∫⁻ ω, clusterPairDensity G ω (F ω) x ∂law p := by
    simp_rw [clusterPairDensity_eq_tsum]
    exact (lintegral_tsum (fun y => (hm x y).aemeasurable)).symm
  have hc (y : V) : (∑' x, m x y) =
      ∫⁻ ω, clusterPairDensity G ω (fun a b => F ω b a) y ∂law p := by
    simp_rw [clusterPairDensity_eq_tsum,←clusterPairMass_swap G _ (F _)]
    exact (lintegral_tsum (fun x => (hm x y).aemeasurable)).symm
  simpa only [hr,hc,clusterPairFunctional] using ht

end PairReversal
end Percolation

end OAI
