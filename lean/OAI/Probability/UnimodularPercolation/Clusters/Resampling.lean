import Mathlib
import OAI.Probability.UnimodularPercolation.Kernel.ScaleBudget

namespace OAI

/-! Resampling for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section ContractingIteration

 

theorem exists_efficient_of_contracting_successor {S : Type*}
    (g H : S → ℝ) (C : ℝ) (hC : 0 ≤ C) (hC1 : C < 1)
    (hstep : ∀ x, ∃ y, g y ≤ C*g x ∧ 2*H x ≤ H y)
    (x₀ : S) (hH₀ : 0 < H x₀) (η R : ℝ) (hη : 0 < η) :
    ∃ x, g x < η ∧ R < H x := by
  classical
  choose f hf using hstep
  let x : ℕ → S := fun n => f^[n] x₀
  have hx (n : ℕ) : x (n+1) = f (x n) := Function.iterate_succ_apply' f n x₀
  have hbounds (n : ℕ) : g (x n) ≤ C^n*g x₀ ∧ (2:ℝ)^n*H x₀ ≤ H (x n) := by
    induction n with
    | zero => simp only [x,Function.iterate_zero,id_eq,pow_zero,one_mul,le_refl,and_self]
    | succ n ih =>
      rw [hx]
      obtain ⟨hg,hH⟩ := hf (x n)
      constructor
      · calc
          _ ≤ C*g (x n) := hg
          _ ≤ C*(C^n*g x₀) := mul_le_mul_of_nonneg_left ih.1 hC
          _ = _ := by rw [pow_succ]; ring
      · calc
          _ = 2*((2:ℝ)^n*H x₀) := by rw [pow_succ]; ring
          _ ≤ 2*H (x n) := mul_le_mul_of_nonneg_left ih.2 (by norm_num)
          _ ≤ _ := hH
  have hg : Tendsto (fun n : ℕ => C^n*g x₀) atTop (nhds 0) := by
    simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one hC hC1).mul_const (g x₀)
  have hH : Tendsto (fun n : ℕ => (2:ℝ)^n*H x₀) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2)).atTop_mul_const hH₀
  obtain ⟨n,hg',hH'⟩ := ((tendsto_order.mp hg).2 η hη |>.and
    (hH.eventually (eventually_gt_atTop R))).exists
  exact ⟨x n,(hbounds n).1.trans_lt hg',hH'.trans_le (hbounds n).2⟩

end ContractingIteration

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section EfficientEndpointProfiles
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem efficient_endpoint_profiles_of_divergent_moment
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (p : unitInterval) (hp : 0 < (p:ℝ)) (hp1 : (p:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law p, (cluster G ω (root i)).Finite)
    (α β ε : ℝ) (hα : 0 < α) (hαβ : α < β)
    (hε : 0 < ε) (hε1 : ε < 1/2) (hsmall : β+(1/2+ε) < 1)
    (hdiv : ∃ i, ¬ Integrable (fun ω => ((cluster G ω (root i)).ncard:ℝ)^α) (law p)) :
    ∃ i, ∀ η : ℝ, 0 < η → ∀ R : ℝ,
      ∃ q : EndpointProfile G hloc p (root i) (1/2+ε),
        2 ≤ q.cap ∧ 1 < q.H ∧ R < q.H ∧ q.U+q.m < η*q.H := by
  have hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i) := by
    intro x
    obtain ⟨i,e,he,hx⟩ := hcov x
    obtain ⟨b,hb⟩ := hΓ he
    exact ⟨i,e,b,hb,hx⟩
  obtain ⟨i,hscales⟩ := orbit_scales_of_divergent_moment G hloc root weight Γ hΓ htr hw hw1 hcover p α β hα hαβ hdiv
  obtain ⟨ξ,hξ,hξ1,hC,hC1⟩ := exists_amplification_contraction β (1/2+ε) (by linarith) (by linarith) hsmall
  have hsξ : 0 < 1/2+ε+ξ := by linarith
  obtain ⟨M₀,hM₀⟩ := eventually_atTop.1 (eventually_inverseCodeMass_budget (1/2+ε) ξ (by linarith) hξ)
  obtain ⟨q₀,hq₀,hH₀⟩ := starting_endpoint_profile G hloc hqt hh p hp hp1 root weight Γ hΓ htr
    (fun i => (hw i).le) hw1 i (hw i) (hfin i) ε hε hε1 M₀
  obtain ⟨d,_,hdeg⟩ := exists_degree_bound G hqt
  let c : ℝ := ∑ j, 1/weight j
  have hc : 0 ≤ c := Finset.sum_nonneg (fun j _ => (one_div_pos.mpr (hw j)).le)
  have hmin (j : ι) : 1 ≤ c*weight j := by
    apply (div_le_iff₀ (hw j)).mp
    exact Finset.single_le_sum (fun l _ => (one_div_pos.mpr (hw l)).le) (Finset.mem_univ j)
  let S := {q : EndpointProfile G hloc p (root i) (1/2+ε) // M₀ ≤ q.cap ∧ 1 < q.H}
  let g : S → ℝ := fun q => q.val.cost ξ/q.val.H
  let H : S → ℝ := fun q => q.val.H
  have hstep : ∀ q : S, ∃ q' : S, g q' ≤ amplificationContraction β (1/2+ε) ξ*g q ∧ 2*H q ≤ H q' := by
    intro q
    have hcap := hM₀ q.val.cap q.property.1
    have hH : 0 < q.val.H := lt_trans zero_lt_one q.property.2
    obtain ⟨r,k,hr,hk,hU,hm,hH',hH''⟩ := q.val.amplify_at_scales hconn hqt root weight Γ hΓ htr hcov hw hw1
      c hc hmin i p hp1 d hdeg ε ξ β hε hε1 hξ hξ1 hscales hcap.1 hcap.2.1 hcap.2.2 hH M₀
    have hrH : 1 < r.H := by linarith [q.property.2]
    refine ⟨⟨r,hr,hrH⟩,?_,hH''⟩
    exact q.val.cost_contraction r β ξ k hcap.1 hsξ hH hξ1 hk hC hU hm hH'
  refine ⟨i,?_⟩
  intro η hη R
  let D : ℝ := 1+1/(1/2+ε+ξ)
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨q,hg,hR⟩ := exists_efficient_of_contracting_successor g H (amplificationContraction β (1/2+ε) ξ)
    hC hC1 hstep ⟨q₀,hq₀,hH₀⟩ (lt_trans zero_lt_one hH₀) (η/D) R (div_pos hη hD)
  have hcap := (hM₀ q.val.cap q.property.1).1
  refine ⟨q.val,hcap,q.property.2,hR,?_⟩
  have hH : 0 < q.val.H := lt_trans zero_lt_one q.property.2
  have hcost := q.val.total_cost_le hcap ξ hsξ
  have hratio : (q.val.U+q.val.m)/q.val.H ≤ D*g q := by
    have h := div_le_div_of_nonneg_right hcost hH.le
    simpa only [D,g,mul_div_assoc] using h
  apply (div_lt_iff₀ hH).mp
  apply hratio.trans_lt
  have hg' := (lt_div_iff₀ hD).mp hg
  simpa only [mul_comm] using hg'

end EfficientEndpointProfiles

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ShortBoundaryPivotal
attribute [local instance] Classical.propDecidable Classical.decEq

 

def ShortClosedBoundary (G : BondGraph V E) (ω : Set E) (x z : V) (M : ℕ) (e : E) : Prop :=
  e ∉ ω ∧ ¬Conn G ω x z ∧ ∃ a b : V, ∃ l : List E,
    G e = s(a,b) ∧ Along G x l a ∧ (∀ f ∈ l, f ∈ ω) ∧ l.length < M ∧ Conn G ω b z

theorem bridgeIndex_le_short_trail (G : BondGraph V E) (ω : Set E) (x z : V)
    (hC : (cluster G ω x).Finite) (e : E) (he : OpenMarkedPivotal G ω {z} x e)
    (a b : V) (hab : G e = s(a,b)) (l : List E) (hl : Along G x l a)
    (ho : ∀ f ∈ l, f ∈ ω) : bridgeIndex G ω x z e ≤ l.length+1 := by
  unfold bridgeIndex
  have hsub : (separatingBonds G ω x z).filter (fun f => pivotalRank G ω x f ≤ pivotalRank G ω x e) ⊆
      (e::l).toFinset := by
    intro f hf
    obtain ⟨hf,hfe⟩ := Finset.mem_filter.mp hf
    have hfp := (mem_separatingBonds G ω x z f).mp hf
    by_cases h : f = e
    · subst f; simp
    by_contra hnot
    have hn : f ∉ l := fun hfl => hnot (List.mem_toFinset.mpr (List.mem_cons_of_mem _ hfl))
    have hlt : pivotalRank G ω x f < pivotalRank G ω x e := by
      apply lt_of_le_of_ne hfe
      intro heq
      exact h (pivotalRank_injective_of_cluster_finite G ω {z} x hC hfp he heq)
    have hout := (pivotalRank_lt_iff_of_cluster_finite G ω {z} x hC hfp he).mp hlt
    have hb : ¬ Conn G (ω \ {f}) x b := ((mem_internalEdges_of_ends G _ e a b hab).mp hout).2
    apply hb
    have hxa : Conn G (ω \ {f}) x a := hl.conn (fun g hg => ⟨ho g hg,fun hgf => hn ((Set.mem_singleton_iff.mp hgf) ▸ hg)⟩)
    exact hxa.tail ⟨e,⟨he.1,fun hEq => h hEq.symm⟩,hab⟩
  exact (Finset.card_le_card hsub).trans (by simpa only [List.length_cons] using List.toFinset_card_le (e::l))

theorem ShortClosedBoundary.open_pivotal (G : BondGraph V E) (ω : Set E) (x z : V)
    (M : ℕ) (e : E) (h : ShortClosedBoundary G ω x z M e) :
    OpenMarkedPivotal G (insert e ω) {z} x e := by
  obtain ⟨he,hxz,a,b,l,hab,hl,ho,_,hbz⟩ := h
  refine ⟨Set.mem_insert e ω,⟨z,rfl,?_⟩,?_⟩
  · have hxa := hl.conn ho
    exact (conn_mono G (Set.subset_insert e ω) hxa).trans
      ((Relation.ReflTransGen.single ⟨e,Set.mem_insert e ω,hab⟩).trans
        (conn_mono G (Set.subset_insert e ω) hbz))
  · rintro ⟨y,hy,hxy⟩
    have hy' : y = z := Set.mem_singleton_iff.mp hy
    subst y
    apply hxz
    apply conn_mono G _ hxy
    intro f hf
    rcases hf.1 with hfe | hfω
    · exact (hf.2 (Set.mem_singleton_iff.mpr hfe)).elim
    · exact hfω

theorem ShortClosedBoundary.bridgeIndex_le (G : BondGraph V E) (ω : Set E) (x z : V)
    (hω : ω.Finite) (M : ℕ) (e : E) (h : ShortClosedBoundary G ω x z M e) :
    bridgeIndex G (insert e ω) x z e ≤ M := by
  have hpiv := ShortClosedBoundary.open_pivotal G ω x z M e h
  obtain ⟨_,_,a,b,l,hab,hl,ho,hlen,_⟩ := h
  have hc := cluster_finite_of_finite_edges G (hω.insert e) x
  have hb := bridgeIndex_le_short_trail G (insert e ω) x z hc e hpiv
    a b hab l hl (fun f hf => Set.mem_insert_of_mem e (ho f hf))
  exact hb.trans (by omega)

end ShortBoundaryPivotal

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ShortBoundaryCounting
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def firstOpenBridgeCount (G : BondGraph V E) (Q : Finset E)
    (x z : V) (M : ℕ) (ω : Finset E) : ℕ :=
  (Q.filter (fun e => OpenMarkedPivotal G ω {z} x e ∧ bridgeIndex G ω x z e ≤ M)).card

noncomputable def shortClosedBoundaryCount (G : BondGraph V E) (Q : Finset E)
    (x z : V) (M : ℕ) (ω : Finset E) : ℕ :=
  (Q.filter (ShortClosedBoundary G ω x z M)).card

theorem firstOpenBridgeCount_le (G : BondGraph V E) (Q : Finset E)
    (x z : V) (M : ℕ) (ω : Finset E) :
    firstOpenBridgeCount G Q x z M ω ≤ if Conn G ω x z then M else 0 := by
  by_cases hc : Conn G ω x z
  · rw [ite_eq_left hc]
    unfold firstOpenBridgeCount
    let S := Q.filter (fun e => OpenMarkedPivotal G ω {z} x e ∧ bridgeIndex G ω x z e ≤ M)
    have hm : Set.MapsTo (bridgeIndex G ω x z) (S : Set E) (Finset.Icc 1 M) := by
      intro e he
      have he' := (Finset.mem_filter.mp he).2
      exact Finset.mem_Icc.mpr ⟨bridgeIndex_pos G ω x z he'.1,he'.2⟩
    have hi : Set.InjOn (bridgeIndex G ω x z) (S : Set E) := by
      intro e he f hf h
      exact bridgeIndex_injective G ω x z (cluster_finite_of_finite_edges G ω.finite_toSet x)
        (Finset.mem_filter.mp he).2.1 (Finset.mem_filter.mp hf).2.1 h
    simpa only [Nat.card_Icc,Nat.add_sub_cancel] using
      (Finset.card_le_card_of_injOn (bridgeIndex G ω x z) hm hi)
  · rw [ite_eq_right hc]
    unfold firstOpenBridgeCount
    have he : Q.filter (fun e => OpenMarkedPivotal G ω {z} x e ∧ bridgeIndex G ω x z e ≤ M) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨y,hy,hxy⟩ := (Finset.mem_filter.mp he).2.1.2.1
      exact hc ((Set.mem_singleton_iff.mp hy) ▸ hxy)
    rw [he,Finset.card_empty]

theorem bernoulliPolynomial_bit_balance (Q : Finset E) (e : E) (he : e ∈ Q)
    (f : Finset E → ℝ) (p : ℝ) :
    p*bernoulliPolynomial Q (fun ω => if e ∉ ω then f ω else 0) p =
      (1-p)*bernoulliPolynomial Q (fun ω => if e ∈ ω then f (ω.erase e) else 0) p := by
  conv_lhs => rw [←Finset.insert_erase he]
  conv_rhs => rw [←Finset.insert_erase he]
  rw [bernoulliPolynomial_insert _ e (Finset.notMem_erase e Q),
    bernoulliPolynomial_insert _ e (Finset.notMem_erase e Q)]
  have hc : bernoulliPolynomial (Q.erase e) (fun ω => if e ∉ ω then f ω else 0) p =
      bernoulliPolynomial (Q.erase e) f p := by
    apply bernoulliPolynomial_congr
    intro ω hω
    simp only [show e ∉ ω from fun h => Finset.notMem_erase e Q (hω h),not_false_eq_true,ite_true]
  have hco : bernoulliPolynomial (Q.erase e) (fun ω => if e ∉ insert e ω then f (insert e ω) else 0) p = 0 := by
    simp only [Finset.mem_insert_self,not_true_eq_false,ite_false,bernoulliPolynomial_zero]
  have ho : bernoulliPolynomial (Q.erase e) (fun ω => if e ∈ ω then f (ω.erase e) else 0) p = 0 := by
    calc
      _ = bernoulliPolynomial (Q.erase e) (fun _ => 0) p := by
        apply bernoulliPolynomial_congr
        intro ω hω
        simp only [show e ∉ ω from fun h => Finset.notMem_erase e Q (hω h),ite_false]
      _ = 0 := bernoulliPolynomial_zero _ _
  have hoo : bernoulliPolynomial (Q.erase e)
      (fun ω => if e ∈ insert e ω then f ((insert e ω).erase e) else 0) p =
      bernoulliPolynomial (Q.erase e) f p := by
    apply bernoulliPolynomial_congr
    intro ω hω
    simp only [Finset.mem_insert_self,ite_true,Finset.erase_insert
      (show e ∉ ω from fun h => Finset.notMem_erase e Q (hω h))]
  rw [hc,hco,ho,hoo]
  ring

end ShortBoundaryCounting

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ShortBoundaryExpectation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem bernoulliPolynomial_closed_count_balance (Q : Finset E)
    (P : Finset E → E → Prop) (hP : ∀ ω e, P ω e → e ∉ ω) (p : ℝ) :
    p*bernoulliPolynomial Q (fun ω => ((Q.filter (P ω)).card:ℝ)) p =
      (1-p)*bernoulliPolynomial Q
        (fun ω => ((Q.filter (fun e => e ∈ ω ∧ P (ω.erase e) e)).card:ℝ)) p := by
  have hbal (e : E) (he : e ∈ Q) :
      p*bernoulliPolynomial Q (fun ω => if P ω e then 1 else 0) p =
        (1-p)*bernoulliPolynomial Q (fun ω => if e ∈ ω ∧ P (ω.erase e) e then 1 else 0) p := by
    have h := bernoulliPolynomial_bit_balance Q e he (fun ω => if P ω e then 1 else 0) p
    have hL : bernoulliPolynomial Q (fun ω => if e ∉ ω then (if P ω e then 1 else 0) else 0) p =
        bernoulliPolynomial Q (fun ω => if P ω e then 1 else 0) p := by
      apply bernoulliPolynomial_congr
      intro ω _
      by_cases hp : P ω e
      · simp only [hp,hP ω e hp,not_false_eq_true,ite_true]
      · simp only [hp,ite_false,ite_self]
    have hR : bernoulliPolynomial Q (fun ω => if e ∈ ω then (if P (ω.erase e) e then 1 else 0) else 0) p =
        bernoulliPolynomial Q (fun ω => if e ∈ ω ∧ P (ω.erase e) e then 1 else 0) p := by
      apply bernoulliPolynomial_congr
      intro ω _
      by_cases hm : e ∈ ω <;> simp only [hm,true_and,false_and,ite_true,ite_false]
    rw [hL,hR] at h
    exact h
  simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
    bernoulliPolynomial_sum,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun e he => hbal e he)

theorem shortClosedBoundary_erase_first (G : BondGraph V E) (ω : Finset E)
    (x z : V) (M : ℕ) (e : E) (he : e ∈ ω)
    (h : ShortClosedBoundary G (ω.erase e) x z M e) :
    OpenMarkedPivotal G ω {z} x e ∧ bridgeIndex G ω x z e ≤ M := by
  have h₁ := ShortClosedBoundary.open_pivotal G (ω.erase e) x z M e h
  have h₂ := ShortClosedBoundary.bridgeIndex_le G (ω.erase e) x z (ω.erase e).finite_toSet M e h
  rw [←Finset.coe_insert,Finset.insert_erase he] at h₁ h₂
  exact ⟨h₁,h₂⟩

theorem shortRecoveredBoundaryCount_le (G : BondGraph V E) (Q ω : Finset E)
    (x z : V) (M : ℕ) :
    (Q.filter (fun e => e ∈ ω ∧ ShortClosedBoundary G (ω.erase e) x z M e)).card ≤
      if Conn G ω x z then M else 0 := by
  apply le_trans _ (firstOpenBridgeCount_le G Q x z M ω)
  apply Finset.card_le_card
  intro e he
  obtain ⟨heQ,heω,hb⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨heQ,shortClosedBoundary_erase_first G ω x z M e heω hb⟩

 

theorem finite_short_boundary_expectation (G : BondGraph V E) (Q : Finset E)
    (x z : V) (M : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    bernoulliPolynomial Q (fun ω => (shortClosedBoundaryCount G Q x z M ω:ℝ)) p ≤
      ((1-p)/p)*M*bernoulliPolynomial Q (fun ω => if Conn G ω x z then 1 else 0) p := by
  have hbal := bernoulliPolynomial_closed_count_balance Q
    (fun ω e => ShortClosedBoundary G ω x z M e) (fun ω e h => h.1) p
  have hmono := bernoulliPolynomial_mono Q
    (fun ω => ((Q.filter (fun e => e ∈ ω ∧ ShortClosedBoundary G (ω.erase e) x z M e)).card:ℝ))
    (fun ω => (M:ℝ)*(if Conn G ω x z then 1 else 0)) p ⟨hp.le,hp1⟩ (by
      intro ω _
      have h := shortRecoveredBoundaryCount_le G Q ω x z M
      by_cases hc : Conn G ω x z
      · simp only [hc,ite_true,mul_one] at *
        exact_mod_cast h
      · simp only [hc,ite_false,mul_zero] at *
        exact_mod_cast h)
  rw [bernoulliPolynomial_const_mul] at hmono
  have hbound := mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr hp1)
  rw [←hbal] at hbound
  change p*bernoulliPolynomial Q (fun ω => (shortClosedBoundaryCount G Q x z M ω:ℝ)) p ≤ _ at hbound
  have hdiv := (le_div_iff₀ hp).mpr (show
      bernoulliPolynomial Q (fun ω => (shortClosedBoundaryCount G Q x z M ω:ℝ)) p*p ≤ _ by
        simpa only [mul_comm p] using hbound)
  simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hdiv

end ShortBoundaryExpectation

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ClusterResampling
attribute [local instance] Classical.propDecidable Classical.decEq

theorem bernoulliPolynomial_commute {F : Type*} (Q : Finset E) (R : Finset F)
    (f : Finset E → Finset F → ℝ) (p q : ℝ) :
    bernoulliPolynomial Q (fun a => bernoulliPolynomial R (f a) q) p =
      bernoulliPolynomial R (fun b => bernoulliPolynomial Q (fun a => f a b) p) q := by
  simp only [bernoulliPolynomial,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem exteriorBonds_union_blocks (G : BondGraph V E) (Q : Finset E)
    (W : Set V) (a b : Finset E) (ha : a ⊆ Q \ exteriorBonds G Q W)
    (hb : b ⊆ exteriorBonds G Q W) : exteriorBonds G (a ∪ b) W = b := by
  ext e
  simp only [exteriorBonds,Finset.mem_filter,Finset.mem_union]
  constructor
  · rintro ⟨he,heW⟩
    rcases he with he | he
    · obtain ⟨heQ,heR⟩ := Finset.mem_sdiff.mp (ha he)
      exact (heR (Finset.mem_filter.mpr ⟨heQ,heW⟩)).elim
    · exact he
  · intro he
    exact ⟨Or.inr he,(Finset.mem_filter.mp (hb he)).2⟩

 
theorem cluster_cell_exterior_factor (G : BondGraph V E) (Q : Finset E)
    (x : V) (W : Set V) (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial Q (fun ω =>
      (if cluster G ω x = W then (1:ℝ) else 0)*f (exteriorBonds G ω W)) p =
      bernoulliPolynomial (Q \ exteriorBonds G Q W)
        (fun a => if cluster G a x = W then (1:ℝ) else 0) p *
      bernoulliPolynomial (exteriorBonds G Q W) f p := by
  let R := exteriorBonds G Q W
  let A := Q \ R
  have hQ : A ∪ R = Q := Finset.sdiff_union_of_subset (Finset.filter_subset _ _)
  conv_lhs => rw [←hQ,bernoulliPolynomial_union A R Finset.sdiff_disjoint]
  trans bernoulliPolynomial A (fun a =>
    (if cluster G a x = W then (1:ℝ) else 0)*bernoulliPolynomial R f p) p
  · apply bernoulliPolynomial_congr
    intro a ha
    rw [←bernoulliPolynomial_const_mul]
    apply bernoulliPolynomial_congr
    intro b hb
    have hc := cluster_union_external_eq_iff G (a:Set E) b x W
      (fun e he => (Finset.mem_filter.mp (hb he)).2)
    rw [exteriorBonds_union_blocks G Q W a b ha hb]
    simp only [Finset.coe_union,hc]
  · exact bernoulliPolynomial_mul_const A _ _ p

theorem cluster_cell_incident_probability (G : BondGraph V E) (Q : Finset E)
    (x : V) (W : Set V) (p : ℝ) :
    bernoulliPolynomial Q (fun ω => if cluster G ω x = W then (1:ℝ) else 0) p =
      bernoulliPolynomial (Q \ exteriorBonds G Q W)
        (fun a => if cluster G a x = W then (1:ℝ) else 0) p := by
  have h := cluster_cell_exterior_factor G Q x W (fun _ => 1) p
  simpa only [mul_one,bernoulliPolynomial_const] using h

noncomputable def resampleClusterAt (G : BondGraph V E) (Q : Finset E)
    (W : Set V) (ω η : Finset E) : Finset E :=
  exteriorBonds G ω W ∪ (η ∩ (Q \ exteriorBonds G Q W))

 

theorem cluster_resample_cell_independent (G : BondGraph V E) (Q : Finset E)
    (x : V) (W : Set V) (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial Q (fun ω => bernoulliPolynomial Q (fun η =>
      (if cluster G ω x = W then (1:ℝ) else 0)*f (resampleClusterAt G Q W ω η)) p) p =
      bernoulliPolynomial Q (fun ω => if cluster G ω x = W then (1:ℝ) else 0) p *
      bernoulliPolynomial Q f p := by
  let R := exteriorBonds G Q W
  let A := Q \ R
  let c := bernoulliPolynomial A (fun a => if cluster G a x = W then (1:ℝ) else 0) p
  rw [bernoulliPolynomial_commute]
  trans bernoulliPolynomial Q (fun η => c * bernoulliPolynomial R
    (fun b => f (b ∪ (η ∩ A))) p) p
  · apply bernoulliPolynomial_congr
    intro η _
    exact cluster_cell_exterior_factor G Q x W (fun b => f (b ∪ (η ∩ A))) p
  · rw [bernoulliPolynomial_const_mul,bernoulliPolynomial_restrict A Q Finset.sdiff_subset
      (fun a => bernoulliPolynomial R (fun b => f (b ∪ a)) p) p,
      bernoulliPolynomial_commute]
    have hQ : R ∪ A = Q := Finset.union_sdiff_of_subset (Finset.filter_subset _ _)
    rw [←bernoulliPolynomial_union R A Finset.disjoint_sdiff,hQ,
      cluster_cell_incident_probability G Q x W p]

end ClusterResampling
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ResampledBoundary
attribute [local instance] Classical.propDecidable Classical.decEq

theorem resampleClusterAt_subset (G : BondGraph V E) (Q : Finset E)
    (W : Set V) (ω η : Finset E) (hω : ω ⊆ Q) :
    resampleClusterAt G Q W ω η ⊆ Q := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · exact hω (Finset.mem_filter.mp he).1
  · exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp he).2).1

theorem resampleClusterAt_external (G : BondGraph V E) (Q : Finset E)
    (W : Set V) (ω η : Finset E) {e : E} (he : e ∈ resampleClusterAt G Q W ω η)
    (heW : e ∈ internalEdges G Wᶜ) : e ∈ ω := by
  rcases Finset.mem_union.mp he with he | he
  · exact (Finset.mem_filter.mp he).1
  · obtain ⟨_,heA⟩ := Finset.mem_inter.mp he
    obtain ⟨heQ,heR⟩ := Finset.mem_sdiff.mp heA
    exact (heR (Finset.mem_filter.mpr ⟨heQ,heW⟩)).elim

 

theorem resampled_path_boundary (G : BondGraph V E) (Q ω η : Finset E)
    (hω : ω ⊆ Q) (x z y : V) (M : ℕ)
    (hy : Conn G ω z y) (hx : ¬Conn G ω x z)
    (l : List E) (hl : Along G x l y) (hlen : l.length ≤ M)
    (ho : ∀ e ∈ l, e ∈ resampleClusterAt G Q (cluster G ω z) ω η) :
    ∃ e ∈ Q, ShortClosedBoundary G ω x z M e := by
  let W := cluster G ω z
  have hxW : x ∉ W := fun h => hx (conn_symm G ω h)
  rcases hl.first_outside (internalEdges G Wᶜ) with hall | ⟨a,b,e,l₁,l₂,heq,h₁,hab,_,hfirst,hen⟩
  · have hc : Conn G ((Set.univ:Set E) ∩ internalEdges G Wᶜ) x y :=
      hl.conn (fun e he => ⟨Set.mem_univ e,hall e he⟩)
    exact ((conn_internal_endpoint G Wᶜ hxW hc) hy).elim
  · subst l
    have heopen := ho e (List.mem_append_right _ (by simp))
    have heQ := resampleClusterAt_subset G Q W ω η hω heopen
    have hprefix : ∀ f ∈ l₁, f ∈ ω := by
      intro f hf
      exact resampleClusterAt_external G Q W ω η
        (ho f (List.mem_append_left _ hf)) (hfirst f hf)
    have hxa : Conn G ((ω:Set E) ∩ internalEdges G Wᶜ) x a :=
      h₁.conn (fun f hf => ⟨hprefix f hf,hfirst f hf⟩)
    have haW : a ∉ W := conn_internal_endpoint G Wᶜ hxW hxa
    have hbW : b ∈ W := by
      by_contra hbW
      exact hen ((mem_internalEdges_of_ends G Wᶜ e a b hab).mpr ⟨haW,hbW⟩)
    have heclosed : e ∉ ω := by
      intro heω
      apply haW
      exact (show Conn G ω z b from hbW).tail ⟨e,heω,hab.trans (Sym2.eq_swap ..)⟩
    refine ⟨e,heQ,heclosed,hx,a,b,l₁,hab,h₁,hprefix,?_,conn_symm G ω hbW⟩
    simp only [List.length_append,List.length_cons] at hlen
    omega

noncomputable def resampleRootCluster (G : BondGraph V E) (Q : Finset E)
    (z : V) (ω η : Finset E) : Finset E :=
  resampleClusterAt G Q (cluster G ω z) ω η

 
theorem resampled_hit_le_boundaryCount (G : BondGraph V E) (Q ω η : Finset E)
    (hω : ω ⊆ Q) (x z y : V) (M : ℕ)
    (hpath : ∃ l : List E, Along G x l y ∧ l.length ≤ M ∧
      ∀ e ∈ l, e ∈ resampleRootCluster G Q z ω η) :
    (if Conn G ω z y then (1:ℝ) else 0) ≤
      (if Conn G ω x z then (1:ℝ) else 0) + shortClosedBoundaryCount G Q x z M ω := by
  by_cases hy : Conn G ω z y
  · rw [ite_eq_left hy]
    by_cases hx : Conn G ω x z
    · rw [ite_eq_left hx]
      exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    · rw [ite_eq_right hx,zero_add]
      obtain ⟨l,hl,hlen,ho⟩ := hpath
      obtain ⟨e,heQ,he⟩ := resampled_path_boundary G Q ω η hω x z y M hy hx l hl hlen ho
      have hpos : 0 < shortClosedBoundaryCount G Q x z M ω :=
        Finset.card_pos.mpr ⟨e,Finset.mem_filter.mpr ⟨heQ,he⟩⟩
      exact_mod_cast hpos
  · rw [ite_eq_right hy]
    positivity

end ResampledBoundary
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RootResamplingLaw
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem rootCluster_resampling_law (G : BondGraph V E) (Q : Finset E)
    (x : V) (f : Finset V → Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial Q (fun ω => bernoulliPolynomial Q
      (fun η => f (finiteRootComponent G ω x) (resampleRootCluster G Q x ω η)) p) p =
      bernoulliPolynomial Q (fun ω => bernoulliPolynomial Q
        (f (finiteRootComponent G ω x)) p) p := by
  let F := insert x (searchVertices G Q)
  let c := fun (W : Finset V) (ω : Finset E) => if cluster G ω x = (W:Set V) then (1:ℝ) else 0
  have hpart (ω η : Finset E) (hω : ω ⊆ Q) :
      f (finiteRootComponent G ω x) (resampleRootCluster G Q x ω η) =
        ∑ W ∈ F.powerset, c W ω * f W (resampleClusterAt G Q W ω η) := by
    have h := sum_component_partition G Q F x ω hω (by rfl)
      (fun W => f W (resampleClusterAt G Q W ω η))
    simpa only [c,ite_mul,one_mul,zero_mul,coe_finiteRootComponent,
      resampleRootCluster] using h.symm
  trans ∑ W ∈ F.powerset,
    bernoulliPolynomial Q (c W) p * bernoulliPolynomial Q (f W) p
  · trans bernoulliPolynomial Q (fun ω => bernoulliPolynomial Q (fun η =>
      ∑ W ∈ F.powerset, c W ω * f W (resampleClusterAt G Q W ω η)) p) p
    · apply bernoulliPolynomial_congr
      intro ω hω
      apply bernoulliPolynomial_congr
      intro η _
      exact hpart ω η hω
    · simp only [bernoulliPolynomial_sum]
      apply Finset.sum_congr rfl
      intro W _
      exact cluster_resample_cell_independent G Q x W (f W) p
  · trans bernoulliPolynomial Q (fun ω => ∑ W ∈ F.powerset,
      c W ω * bernoulliPolynomial Q (f W) p) p
    · rw [bernoulliPolynomial_sum]
      apply Finset.sum_congr rfl
      intro W _
      exact (bernoulliPolynomial_mul_const Q (c W) _ p).symm
    · apply bernoulliPolynomial_congr
      intro ω hω
      have h := sum_component_partition G Q F x ω hω (by rfl)
        (fun W => bernoulliPolynomial Q (f W) p)
      simpa only [c,ite_mul,one_mul,zero_mul] using h

end RootResamplingLaw
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteMaximalSusceptibility
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteSusceptibility (G : BondGraph V E) (Q : Finset E)
    (F : Finset V) (p : ℝ) (x : V) : ℝ :=
  ∑ z ∈ F, bernoulliPolynomial Q (fun ω => if Conn G ω x z then (1:ℝ) else 0) p

theorem finiteSusceptibility_nonneg (G : BondGraph V E) (Q : Finset E)
    (F : Finset V) (p : ℝ) (x : V) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ finiteSusceptibility G Q F p x := by
  apply Finset.sum_nonneg
  intro z _
  exact bernoulliPolynomial_nonneg Q _ p hp (fun _ _ => by positivity)

theorem rootCluster_resampled_selector (G : BondGraph V E) (Q : Finset E)
    (w : V) (Z : Finset E → V) (p : ℝ) :
    bernoulliPolynomial Q (fun ω => bernoulliPolynomial Q (fun η =>
      if Conn G ω w (Z (resampleRootCluster G Q w ω η)) then (1:ℝ) else 0) p) p =
      bernoulliPolynomial Q (fun η => bernoulliPolynomial Q (fun ω =>
        if Conn G ω w (Z η) then (1:ℝ) else 0) p) p := by
  have hm (ω : Finset E) (y : V) :
      y ∈ finiteRootComponent G ω w ↔ Conn G ω w y := by
    change y ∈ (finiteRootComponent G ω w : Set V) ↔ _
    rw [coe_finiteRootComponent]
    rfl
  have h := rootCluster_resampling_law G Q w (fun W η => if Z η ∈ W then (1:ℝ) else 0) p
  simp only [hm] at h
  exact h.trans (bernoulliPolynomial_commute Q Q _ p p)

theorem finite_selector_connection_bound (G : BondGraph V E) (Q : Finset E)
    (x w : V) (M : ℕ) (Z : Finset E → V)
    (hZ : ∀ η ⊆ Q, ∃ l : List E, Along G x l (Z η) ∧ l.length ≤ M ∧ ∀ e ∈ l, e ∈ η)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    bernoulliPolynomial Q (fun η => bernoulliPolynomial Q (fun ω =>
      if Conn G ω w (Z η) then (1:ℝ) else 0) p) p ≤
      (1+(1-p)/p*M)*bernoulliPolynomial Q (fun ω => if Conn G ω x w then (1:ℝ) else 0) p := by
  rw [←rootCluster_resampled_selector G Q w Z p]
  have hmono := bernoulliPolynomial_mono Q
    (fun ω => bernoulliPolynomial Q (fun η =>
      if Conn G ω w (Z (resampleRootCluster G Q w ω η)) then (1:ℝ) else 0) p)
    (fun ω => (if Conn G ω x w then (1:ℝ) else 0)+shortClosedBoundaryCount G Q x w M ω)
    p ⟨hp.le,hp1⟩ (by
      intro ω hω
      calc
        _ ≤ bernoulliPolynomial Q (fun _ =>
          (if Conn G ω x w then (1:ℝ) else 0)+shortClosedBoundaryCount G Q x w M ω) p := by
            apply bernoulliPolynomial_mono Q _ _ p ⟨hp.le,hp1⟩
            intro η _
            exact resampled_hit_le_boundaryCount G Q ω η hω x w _ M
              (hZ _ (resampleClusterAt_subset G Q _ ω η hω))
        _ = _ := bernoulliPolynomial_const Q _ p)
  rw [bernoulliPolynomial_add] at hmono
  have hb := finite_short_boundary_expectation G Q x w M p hp hp1
  calc
    _ ≤ _ := hmono
    _ ≤ bernoulliPolynomial Q (fun ω => if Conn G ω x w then (1:ℝ) else 0) p +
      ((1-p)/p)*M*bernoulliPolynomial Q (fun ω => if Conn G ω x w then (1:ℝ) else 0) p :=
        add_le_add le_rfl hb
    _ = _ := by ring

 

theorem finite_selected_susceptibility_bound (G : BondGraph V E) (Q : Finset E)
    (F : Finset V) (x : V) (M : ℕ) (Z : Finset E → V)
    (hZ : ∀ η ⊆ Q, ∃ l : List E, Along G x l (Z η) ∧ l.length ≤ M ∧ ∀ e ∈ l, e ∈ η)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    bernoulliPolynomial Q (fun η => finiteSusceptibility G Q F p (Z η)) p ≤
      (1+(1-p)/p*M)*finiteSusceptibility G Q F p x := by
  unfold finiteSusceptibility
  rw [bernoulliPolynomial_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w _
  have h := finite_selector_connection_bound G Q x w M Z hZ p hp hp1
  calc
    _ = bernoulliPolynomial Q (fun η => bernoulliPolynomial Q (fun ω =>
        if Conn G ω w (Z η) then (1:ℝ) else 0) p) p := by
      apply bernoulliPolynomial_congr
      intro η _
      apply bernoulliPolynomial_congr
      intro ω _
      apply if_congr _ rfl rfl
      exact ⟨conn_symm G ω,conn_symm G ω⟩
    _ ≤ _ := h

end FiniteMaximalSusceptibility
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter Topology
section RestrictedConnectionLimit
attribute [local instance] Classical.propDecidable Classical.decEq

theorem tendsto_bernoulliPolynomial {ι : Type*} {l : Filter ι}
    (Q : Finset E) (f : ι → Finset E → ℝ) (g : Finset E → ℝ) (p : ℝ)
    (h : ∀ a ⊆ Q, Tendsto (fun i => f i a) l (𝓝 (g a))) :
    Tendsto (fun i => bernoulliPolynomial Q (f i) p) l
      (𝓝 (bernoulliPolynomial Q g p)) := by
  unfold bernoulliPolynomial
  exact tendsto_finsetSum _ (fun a ha =>
    ((h a (Finset.mem_powerset.mp ha)).mul_const _).mul_const _)

theorem conn_finite_exhaustion (G : BondGraph V E) (S : Set E)
    (Q : ℕ → Finset E) (hQ : Monotone Q) (hcover : ∀ e ∈ S, ∃ n, e ∈ Q n)
    {ω : Set E} {x y : V} (h : Conn G (ω ∩ S) x y) :
    ∃ n, Conn G (ω ∩ (Q n : Set E)) x y := by
  induction h with
  | refl => exact ⟨0,conn_refl _ _ _⟩
  | @tail a b hxa hab ih =>
    obtain ⟨n,hn⟩ := ih
    obtain ⟨e,he,hab⟩ := hab
    obtain ⟨m,hm⟩ := hcover e he.2
    refine ⟨max n m,?_⟩
    exact (conn_mono G (Set.inter_subset_inter_right _
      (show (Q n:Set E) ⊆ (Q (max n m):Set E) from hQ (le_max_left n m))) hn).tail
      ⟨e,⟨he.1,hQ (le_max_right n m) hm⟩,hab⟩

theorem finite_connection_polynomial_tendsto (G : BondGraph V E) (S : Set E)
    (Q : ℕ → Finset E) (hQ : Monotone Q) (hsub : ∀ n, (Q n:Set E) ⊆ S)
    (hcover : ∀ e ∈ S, ∃ n, e ∈ Q n) (p : unitInterval) (x y : V) :
    Tendsto (fun n => bernoulliPolynomial (Q n) (fun ω => if Conn G ω x y then (1:ℝ) else 0) p)
      atTop (𝓝 ((law p).real {ω | Conn G (ω ∩ S) x y})) := by
  have he (n : ℕ) : bernoulliPolynomial (Q n) (fun ω => if Conn G ω x y then (1:ℝ) else 0) p =
      (law p).real {ω | Conn G (ω ∩ (Q n:Set E)) x y} :=
    finiteEventPolynomial_restrict (Q n) {ω | Conn G ω x y} p
  simp_rw [he]
  have hm : Monotone (fun n => {ω : Set E | Conn G (ω ∩ (Q n:Set E)) x y}) := by
    intro m n h ω hc
    exact conn_mono G (Set.inter_subset_inter_right _ (show (Q m:Set E) ⊆ (Q n:Set E) from hQ h)) hc
  have hu : (⋃ n, {ω : Set E | Conn G (ω ∩ (Q n:Set E)) x y}) =
      {ω : Set E | Conn G (ω ∩ S) x y} := by
    ext ω
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
    exact ⟨fun ⟨n,hn⟩ => conn_mono G (Set.inter_subset_inter_right _ (hsub n)) hn,
      conn_finite_exhaustion G S Q hQ hcover⟩
  have ht := tendsto_measure_iUnion_atTop (μ := law p) hm
  rw [hu] at ht
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht

noncomputable def restrictedBondExhaustion [Encodable E] (S : Set E) (K : Finset E)
    (n : ℕ) : Finset E := K ∪ (vertexExhaustion (V := E) n).filter (· ∈ S)

theorem restrictedBondExhaustion_mono [Encodable E] (S : Set E) (K : Finset E) :
    Monotone (restrictedBondExhaustion S K) := by
  intro m n h
  exact Finset.union_subset_union (by rfl) (Finset.filter_subset_filter _ (vertexExhaustion_mono h))

theorem restrictedBondExhaustion_cover [Encodable E] (S : Set E) (K : Finset E)
    (e : E) (he : e ∈ S) : ∃ n, e ∈ restrictedBondExhaustion S K n := by
  obtain ⟨n,hn⟩ := subset_vertexExhaustion ({e}:Finset E)
  exact ⟨n,Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn (by simp),he⟩)⟩

theorem restrictedBondExhaustion_subset [Encodable E] (S : Set E) (K : Finset E)
    (hK : (K:Set E) ⊆ S) (n : ℕ) : (restrictedBondExhaustion S K n:Set E) ⊆ S := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · exact hK he
  · exact (Finset.mem_filter.mp he).2

end RestrictedConnectionLimit
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter Topology
section RestrictedSelectorBound
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem restricted_selector_connection_bound [Countable E] (G : BondGraph V E)
    (S : Set E) (K : Finset E) (hK : (K:Set E) ⊆ S)
    (x w : V) (M : ℕ) (Z : Finset E → V)
    (hZ : ∀ η ⊆ K, ∃ l : List E, Along G x l (Z η) ∧ l.length ≤ M ∧ ∀ e ∈ l, e ∈ η)
    (p : unitInterval) (hp : 0 < (p:ℝ)) :
    bernoulliPolynomial K (fun η => (law p).real {ω | Conn G (ω ∩ S) w (Z η)}) p ≤
      (1+(1-(p:ℝ))/p*M)*(law p).real {ω | Conn G (ω ∩ S) x w} := by
  let := Encodable.ofCountable E
  let Q := restrictedBondExhaustion S K
  have hlim (a b : V) := finite_connection_polynomial_tendsto G S Q
    (restrictedBondExhaustion_mono S K) (restrictedBondExhaustion_subset S K hK)
    (restrictedBondExhaustion_cover S K) p a b
  have hleft := tendsto_bernoulliPolynomial K
    (fun n η => bernoulliPolynomial (Q n) (fun ω => if Conn G ω w (Z η) then (1:ℝ) else 0) p)
    (fun η => (law p).real {ω | Conn G (ω ∩ S) w (Z η)}) p (fun η _ => hlim w (Z η))
  have hright := (hlim x w).const_mul (1+(1-(p:ℝ))/p*M)
  apply le_of_tendsto_of_tendsto hleft hright
  apply Eventually.of_forall
  intro n
  have hZQ : ∀ η ⊆ Q n, ∃ l : List E, Along G x l (Z (η ∩ K)) ∧
      l.length ≤ M ∧ ∀ e ∈ l, e ∈ η := by
    intro η _
    obtain ⟨l,hl,hlen,ho⟩ := hZ (η ∩ K) Finset.inter_subset_right
    exact ⟨l,hl,hlen,fun e he => (Finset.mem_inter.mp (ho e he)).1⟩
  have h := finite_selector_connection_bound G (Q n) x w M (fun η => Z (η ∩ K)) hZQ p hp p.2.2
  rw [bernoulliPolynomial_restrict K (Q n) Finset.subset_union_left
    (fun η => bernoulliPolynomial (Q n) (fun ω => if Conn G ω w (Z η) then (1:ℝ) else 0) p) p] at h
  exact h

noncomputable def restrictedSusceptibility (G : BondGraph V E) (S : Set E)
    (p : unitInterval) (x : V) : ℝ :=
  ∑' y, (law p).real {ω | Conn G (ω ∩ S) x y}

theorem restrictedTwoPoint_le (G : BondGraph V E) (S : Set E)
    (p : unitInterval) (x y : V) :
    (law p).real {ω | Conn G (ω ∩ S) x y} ≤ twoPoint G p x y := by
  exact measureReal_mono (fun _ h => conn_mono G Set.inter_subset_left h)

theorem summable_restrictedTwoPoint [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (S : Set E) (x : V) :
    Summable (fun y => (law p).real {ω | Conn G (ω ∩ S) x y}) := by
  obtain ⟨C,_,hC⟩ := subcritical_row_bound G hloc hqt p hp
  apply summable_of_sum_le (fun _ => measureReal_nonneg)
  intro F
  exact (Finset.sum_le_sum (fun y _ => restrictedTwoPoint_le G S p x y)).trans (hC x F)

end RestrictedSelectorBound
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter Topology
section SelectorSusceptibility
attribute [local instance] Classical.propDecidable Classical.decEq

theorem summable_bernoulliPolynomial {A : Type*} (K : Finset E)
    (f : Finset E → A → ℝ) (p : ℝ) (hf : ∀ η ⊆ K, Summable (f η)) :
    Summable (fun y => bernoulliPolynomial K (fun η => f η y) p) := by
  unfold bernoulliPolynomial
  apply summable_sum
  intro η hη
  exact ((hf η (Finset.mem_powerset.mp hη)).mul_right _).mul_right _

theorem bernoulliPolynomial_tsum {A : Type*} (K : Finset E)
    (f : Finset E → A → ℝ) (p : ℝ) (hf : ∀ η ⊆ K, Summable (f η)) :
    bernoulliPolynomial K (fun η => ∑' y, f η y) p =
      ∑' y, bernoulliPolynomial K (fun η => f η y) p := by
  unfold bernoulliPolynomial
  rw [Summable.tsum_finsetSum (fun η hη =>
    ((hf η (Finset.mem_powerset.mp hη)).mul_right _).mul_right _)]
  apply Finset.sum_congr rfl
  intro η _
  rw [tsum_mul_right,tsum_mul_right]

theorem restrictedTwoPoint_symm (G : BondGraph V E) (S : Set E)
    (p : unitInterval) (x y : V) :
    (law p).real {ω | Conn G (ω ∩ S) x y} =
      (law p).real {ω | Conn G (ω ∩ S) y x} := by
  congr 1
  ext ω
  exact ⟨conn_symm G _,conn_symm G _⟩

 

theorem restricted_selected_susceptibility_bound [Countable E] (G : BondGraph V E)
    (S : Set E) (K : Finset E) (hK : (K:Set E) ⊆ S)
    (x : V) (M : ℕ) (Z : Finset E → V)
    (hZ : ∀ η ⊆ K, ∃ l : List E, Along G x l (Z η) ∧ l.length ≤ M ∧ ∀ e ∈ l, e ∈ η)
    (p : unitInterval) (hp : 0 < (p:ℝ))
    (hfin : ∀ y, Summable (fun z => (law p).real {ω | Conn G (ω ∩ S) y z})) :
    bernoulliPolynomial K (fun η => restrictedSusceptibility G S p (Z η)) p ≤
      (1+(1-(p:ℝ))/p*M)*restrictedSusceptibility G S p x := by
  unfold restrictedSusceptibility
  rw [bernoulliPolynomial_tsum K _ p (fun η _ => hfin (Z η)),←tsum_mul_left]
  apply Summable.tsum_le_tsum _ (summable_bernoulliPolynomial K _ p (fun η _ => hfin (Z η)))
    ((hfin x).mul_left _)
  intro w
  have h := restricted_selector_connection_bound G S K hK x w M Z hZ p hp
  simpa only [restrictedTwoPoint_symm G S p (Z _) w] using h

 

theorem subcritical_selected_susceptibility_bound
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (S : Set E) (K : Finset E) (hK : (K:Set E) ⊆ S)
    (x : V) (M : ℕ) (Z : Finset E → V)
    (hZ : ∀ η ⊆ K, ∃ l : List E, Along G x l (Z η) ∧ l.length ≤ M ∧ ∀ e ∈ l, e ∈ η)
    (p : unitInterval) (hp : 0 < (p:ℝ)) (hpc : p < pc G) :
    bernoulliPolynomial K (fun η => restrictedSusceptibility G S p (Z η)) p ≤
      (1+(1-(p:ℝ))/p*M)*restrictedSusceptibility G S p x :=
  restricted_selected_susceptibility_bound G S K hK x M Z hZ p hp
    (summable_restrictedTwoPoint G hloc hqt p hpc S)

end SelectorSusceptibility
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section IntrinsicBall
attribute [local instance] Classical.propDecidable Classical.decEq

 
def intrinsicBall (G : BondGraph V E) (ω : Set E) (x : V) (M : ℕ) : Set V :=
  {y | ∃ l : List E, Along G x l y ∧ l.length ≤ M ∧ ∀ e ∈ l, e ∈ ω}

theorem mem_intrinsicBall_self (G : BondGraph V E) (ω : Set E) (x : V) (M : ℕ) :
    x ∈ intrinsicBall G ω x M := ⟨[],.nil x,Nat.zero_le _,by simp⟩

theorem intrinsicBall_subset_reachBall (G : BondGraph V E) (ω : Set E) (x : V) (M : ℕ) :
    intrinsicBall G ω x M ⊆ reachBall G x M := by
  rintro y ⟨l,hl,hlen,_⟩
  exact reachBall_mono G x hlen hl.mem_reachBall

theorem intrinsicBall_mono (G : BondGraph V E) {ω η : Set E} (h : ω ⊆ η) (x : V) (M : ℕ) :
    intrinsicBall G ω x M ⊆ intrinsicBall G η x M := by
  rintro y ⟨l,hl,hlen,ho⟩
  exact ⟨l,hl,hlen,fun e he => h (ho e he)⟩

theorem Along.bonds_in_incidentBall {G : BondGraph V E} (hloc : LocallyFinite G)
    {x y : V} {l : List E} (h : Along G x l y) (M : ℕ) (hlen : l.length ≤ M) :
    ∀ e ∈ l, e ∈ incidentSupport G hloc (finite_reachBall hloc x M).toFinset := by
  rcases h.first_outside (incidentSupport G hloc (finite_reachBall hloc x M).toFinset : Set E)
    with h | ⟨a,b,e,l₁,l₂,heq,h₁,he,_,_,hnot⟩
  · exact h
  · exfalso
    apply hnot
    apply (mem_incidentSupport G hloc _ e).mpr
    refine ⟨a,?_,by simp [he]⟩
    apply (finite_reachBall hloc x M).mem_toFinset.mpr
    apply reachBall_mono G x (show l₁.length ≤ M by subst l; simp only [List.length_append,List.length_cons] at hlen; omega)
    exact h₁.mem_reachBall

theorem intrinsicBall_restrict (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (M : ℕ) :
    intrinsicBall G (ω ∩ (incidentSupport G hloc (finite_reachBall hloc x M).toFinset : Set E)) x M =
      intrinsicBall G ω x M := by
  apply Set.Subset.antisymm (intrinsicBall_mono G Set.inter_subset_left x M)
  rintro y ⟨l,hl,hlen,ho⟩
  exact ⟨l,hl,hlen,fun e he => ⟨ho e he,hl.bonds_in_incidentBall hloc M hlen e he⟩⟩

theorem integral_eq_bernoulliPolynomial (Q : Finset E) (p : unitInterval) (f : Set E → ℝ)
    (hf : ∀ ω, f ω = f (ω ∩ (Q:Set E))) :
    (∫ ω, f ω ∂law p) = bernoulliPolynomial Q (fun η => f η) p := by
  rw [integral_finite_local Q p f hf]
  simp only [finiteFieldWeight,finiteFieldSet]
  rw [Finset.sum_coe_sort Q.powerset (fun η => bernoulliWeight Q η p * f η)]
  unfold bernoulliPolynomial
  apply Finset.sum_congr rfl
  intro η _
  unfold bernoulliWeight
  ring

end IntrinsicBall
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section IntrinsicMaximum
attribute [local instance] Classical.propDecidable Classical.decEq

theorem intrinsicBall_exists_max (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (M : ℕ) (f : V → ℝ) :
    ∃ z ∈ intrinsicBall G ω x M, ∀ y ∈ intrinsicBall G ω x M, f y ≤ f z :=
  Set.exists_max_image _ f ((finite_reachBall hloc x M).subset
    (intrinsicBall_subset_reachBall G ω x M)) ⟨x,mem_intrinsicBall_self G ω x M⟩

noncomputable def intrinsicMaximizer (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (M : ℕ) (f : V → ℝ) : V :=
  Classical.choose (intrinsicBall_exists_max G hloc ω x M f)

theorem intrinsicMaximizer_spec (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (M : ℕ) (f : V → ℝ) :
    intrinsicMaximizer G hloc ω x M f ∈ intrinsicBall G ω x M ∧
      ∀ y ∈ intrinsicBall G ω x M, f y ≤ f (intrinsicMaximizer G hloc ω x M f) :=
  Classical.choose_spec (intrinsicBall_exists_max G hloc ω x M f)

noncomputable def intrinsicPotentialMax (G : BondGraph V E) (ω : Set E)
    (x : V) (M : ℕ) (f : V → ℝ) : ℝ := sSup (f '' intrinsicBall G ω x M)

theorem intrinsicPotentialMax_eq (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (M : ℕ) (f : V → ℝ) :
    intrinsicPotentialMax G ω x M f = f (intrinsicMaximizer G hloc ω x M f) := by
  have h := intrinsicMaximizer_spec G hloc ω x M f
  apply IsGreatest.csSup_eq
  exact ⟨⟨_,h.1,rfl⟩,fun _ ⟨y,hy,he⟩ => he ▸ h.2 y hy⟩

theorem le_intrinsicPotentialMax (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (M : ℕ) (f : V → ℝ) (y : V) (hy : y ∈ intrinsicBall G ω x M) :
    f y ≤ intrinsicPotentialMax G ω x M f := by
  rw [intrinsicPotentialMax_eq G hloc]
  exact (intrinsicMaximizer_spec G hloc ω x M f).2 y hy

noncomputable def intrinsicBondSupport (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Set E) (x : V) (M : ℕ) : Finset E :=
  (incidentSupport G hloc (finite_reachBall hloc x M).toFinset).filter (· ∈ S)

theorem intrinsicBondSupport_coe (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Set E) (x : V) (M : ℕ) :
    (intrinsicBondSupport G hloc S x M : Set E) =
      (incidentSupport G hloc (finite_reachBall hloc x M).toFinset : Set E) ∩ S := by
  ext e
  simp [intrinsicBondSupport]

theorem intrinsicBall_domain_restrict (G : BondGraph V E) (hloc : LocallyFinite G)
    (S ω : Set E) (x : V) (M : ℕ) :
    intrinsicBall G (ω ∩ (intrinsicBondSupport G hloc S x M : Set E)) x M =
      intrinsicBall G (ω ∩ S) x M := by
  rw [intrinsicBondSupport_coe]
  have he : ω ∩ ((incidentSupport G hloc (finite_reachBall hloc x M).toFinset : Set E) ∩ S) =
      (ω ∩ S) ∩ (incidentSupport G hloc (finite_reachBall hloc x M).toFinset : Set E) := by
    ext e; simp [and_left_comm,and_comm,and_assoc]
  rw [he,intrinsicBall_restrict G hloc]

theorem intrinsicPotentialMax_domain_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (S ω : Set E) (x : V) (M : ℕ) (f : V → ℝ) :
    intrinsicPotentialMax G (ω ∩ S) x M f =
      intrinsicPotentialMax G ((ω ∩ (intrinsicBondSupport G hloc S x M : Set E)) ∩ S) x M f := by
  have hsub : (intrinsicBondSupport G hloc S x M : Set E) ⊆ S := by
    rw [intrinsicBondSupport_coe]; exact Set.inter_subset_right
  rw [Set.inter_assoc,Set.inter_eq_left.mpr hsub]
  unfold intrinsicPotentialMax
  rw [intrinsicBall_domain_restrict G hloc]

end IntrinsicMaximum
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section MaximalSusceptibility
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem maximal_restricted_susceptibility_bound
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (S : Set E) (x : V) (M : ℕ) (p : unitInterval)
    (hp : 0 < (p:ℝ)) (hpc : p < pc G) :
    (∫ ω, intrinsicPotentialMax G (ω ∩ S) x M (restrictedSusceptibility G S p) ∂law p) ≤
      (1+(1-(p:ℝ))/p*M)*restrictedSusceptibility G S p x := by
  let K := intrinsicBondSupport G hloc S x M
  let f := restrictedSusceptibility G S p
  let Z : Finset E → V := fun η => intrinsicMaximizer G hloc η x M f
  have hK : (K:Set E) ⊆ S := by
    rw [intrinsicBondSupport_coe]; exact Set.inter_subset_right
  rw [integral_eq_bernoulliPolynomial K p _ (fun ω =>
    intrinsicPotentialMax_domain_local G hloc S ω x M f)]
  have he : bernoulliPolynomial K (fun η => intrinsicPotentialMax G ((η:Set E) ∩ S) x M f) p =
      bernoulliPolynomial K (fun η => f (Z η)) p := by
    apply bernoulliPolynomial_congr K _ p
    intro η hη
    rw [Set.inter_eq_left.mpr (fun e he => hK (hη he))]
    exact intrinsicPotentialMax_eq G hloc η x M f
  rw [he]
  apply subcritical_selected_susceptibility_bound G hloc hqt S K hK x M Z _ p hp hpc
  intro η _
  exact (intrinsicMaximizer_spec G hloc η x M f).1

 

noncomputable def inducedSusceptibility (G : BondGraph V E) (D : Set V)
    (p : unitInterval) (x : V) : ℝ :=
  if x ∈ D then restrictedSusceptibility G (internalEdges G D) p x else 0

theorem intrinsicBall_internal_subset (G : BondGraph V E) (D : Set V)
    (ω : Set E) (x : V) (hx : x ∈ D) (M : ℕ) :
    intrinsicBall G (ω ∩ internalEdges G D) x M ⊆ D := by
  rintro y ⟨l,hl,_,ho⟩
  exact conn_internal_endpoint G D hx (hl.conn ho)

theorem inducedSusceptibility_max_eq (G : BondGraph V E) (D : Set V)
    (ω : Set E) (p : unitInterval) (x : V) (hx : x ∈ D) (M : ℕ) :
    intrinsicPotentialMax G (ω ∩ internalEdges G D) x M (inducedSusceptibility G D p) =
      intrinsicPotentialMax G (ω ∩ internalEdges G D) x M (restrictedSusceptibility G (internalEdges G D) p) := by
  unfold intrinsicPotentialMax
  congr 1
  apply Set.image_congr
  intro y hy
  exact ite_eq_left (intrinsicBall_internal_subset G D ω x hx M hy)

 

theorem maximal_induced_susceptibility_bound
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (D : Set V) (x : V) (hx : x ∈ D) (M : ℕ) (p : unitInterval)
    (hp : 0 < (p:ℝ)) (hpc : p < pc G) :
    (∫ ω, intrinsicPotentialMax G (ω ∩ internalEdges G D) x M (inducedSusceptibility G D p) ∂law p) ≤
      (1+(1-(p:ℝ))/p*M)*inducedSusceptibility G D p x := by
  simp_rw [inducedSusceptibility_max_eq G D _ p x hx M]
  rw [inducedSusceptibility,ite_eq_left hx]
  exact maximal_restricted_susceptibility_bound G hloc hqt (internalEdges G D) x M p hp hpc

end MaximalSusceptibility
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section RestrictedPathPotential
attribute [local instance] Classical.propDecidable Classical.decEq

theorem restrictedTwoPoint_adj_lower [Countable E] (G : BondGraph V E)
    (S : Set E) (p : unitInterval) (x y z : V) (e : E)
    (he : G e = s(x,y)) (heS : e ∈ S) :
    (p:ℝ)*(law p).real {ω | Conn G (ω ∩ S) y z} ≤
      (law p).real {ω | Conn G (ω ∩ S) x z} := by
  have h := association_finiteWitness p {ω : Set E | e ∈ ω} {ω | Conn G (ω ∩ S) y z}
    (fun _ _ hω h => hω h)
    (fun _ _ hω h => conn_mono G (Set.inter_subset_inter_left _ hω) h)
    (finiteWitness_edge e) (finiteWitness_inter _ (finiteWitness_conn G y z) S)
  have hp : (law p).real {ω : Set E | e ∈ ω} = (p:ℝ) := by
    simpa using finite_open_probability p {e}
  rw [hp] at h
  exact h.trans (measureReal_mono (fun ω hω =>
    conn_trans G _ (Relation.ReflTransGen.single ⟨e,⟨hω.1,heS⟩,he⟩) hω.2))

theorem restrictedTwoPoint_path_lower [Countable E] (G : BondGraph V E)
    (S : Set E) (p : unitInterval) {x y : V} {l : List E}
    (hl : Along G x l y) (hS : ∀ e ∈ l, e ∈ S) (z : V) :
    (p:ℝ)^l.length*(law p).real {ω | Conn G (ω ∩ S) y z} ≤
      (law p).real {ω | Conn G (ω ∩ S) x z} := by
  induction hl with
  | nil => simp
  | @cons x a y l e he ht ih =>
    have hh := mul_le_mul_of_nonneg_left (ih (fun d hd => hS d (List.mem_cons_of_mem _ hd))) p.2.1
    have ha := restrictedTwoPoint_adj_lower G S p x a z e he (hS e (by simp))
    simpa only [List.length_cons,pow_succ',mul_assoc] using hh.trans ha

theorem restrictedSusceptibility_nonneg (G : BondGraph V E) (S : Set E)
    (p : unitInterval) (x : V) : 0 ≤ restrictedSusceptibility G S p x :=
  tsum_nonneg (fun _ => measureReal_nonneg)

theorem restrictedSusceptibility_path_lower [Countable E] (G : BondGraph V E)
    (S : Set E) (p : unitInterval) {x y : V} {l : List E}
    (hl : Along G x l y) (hS : ∀ e ∈ l, e ∈ S)
    (hfin : ∀ a, Summable (fun z => (law p).real {ω | Conn G (ω ∩ S) a z})) :
    (p:ℝ)^l.length*restrictedSusceptibility G S p y ≤ restrictedSusceptibility G S p x := by
  unfold restrictedSusceptibility
  rw [←tsum_mul_left]
  exact ((hfin y).mul_left _).tsum_le_tsum (restrictedTwoPoint_path_lower G S p hl hS) (hfin x)

 

theorem restrictedSusceptibility_short_path_bound [Countable E] (G : BondGraph V E)
    (S : Set E) (p : unitInterval) (hp : 0 < (p:ℝ)) {x y : V} {l : List E}
    (hl : Along G x l y) (hS : ∀ e ∈ l, e ∈ S) (M : ℕ) (hlen : l.length ≤ M)
    (hfin : ∀ a, Summable (fun z => (law p).real {ω | Conn G (ω ∩ S) a z})) :
    restrictedSusceptibility G S p y ≤ (p:ℝ)^(-(M:ℤ))*restrictedSusceptibility G S p x := by
  have hh := restrictedSusceptibility_path_lower G S p hl hS hfin
  have hpow : (p:ℝ)^M ≤ (p:ℝ)^l.length :=
    pow_le_pow_of_le_one p.2.1 p.2.2 hlen
  have hbound := (mul_le_mul_of_nonneg_right hpow (restrictedSusceptibility_nonneg G S p y)).trans hh
  rw [zpow_neg,zpow_natCast,←div_eq_inv_mul]
  exact (le_div_iff₀ (pow_pos hp M)).mpr (by simpa only [mul_comm] using hbound)

end RestrictedPathPotential
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ShortPathsDeletedDomain
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem conn_short_of_cluster_cap (G : BondGraph V E) (ω : Set E) (x y : V)
    (hxy : Conn G ω x y) (hfin : (cluster G ω x).Finite)
    (M : ℕ) (hM : (cluster G ω x).ncard ≤ M) :
    ∃ l : List E, Along G x l y ∧ l.length ≤ M ∧ ∀ e ∈ l, e ∈ ω := by
  obtain ⟨w⟩ := (conn_iff_reachable G ω x y).mp hxy
  let q := w.toPath
  have hs : q.val.support.toFinset ⊆ hfin.toFinset := by
    intro z hz
    have hz' : z ∈ q.val.support := List.mem_toFinset.mp hz
    exact hfin.mem_toFinset.mpr ((conn_iff_reachable G ω x z).mpr ⟨q.val.takeUntil z hz'⟩)
  have hc : q.val.length+1 ≤ (cluster G ω x).ncard := by
    have hc := Finset.card_le_card hs
    rwa [List.toFinset_card_of_nodup q.property.support_nodup,
      SimpleGraph.Walk.length_support,←Set.ncard_eq_toFinset_card _ hfin] at hc
  obtain ⟨l,hl,he,ho⟩ := walk_lift_bonds G ω q.val
  have hlen : l.length = q.val.length := by
    have hh := congrArg List.length he
    simpa only [List.length_map,SimpleGraph.Walk.length_edges] using hh
  exact ⟨l,hl,by omega,ho⟩

 

theorem Along.last_entrance {G : BondGraph V E} {x y : V} {l : List E}
    (hl : Along G x l y) (D : Set V) (hy : y ∈ D) :
    (x ∈ D ∧ ∀ e ∈ l, e ∈ internalEdges G D) ∨
      ∃ a b e l₁ l₂, l = l₁ ++ e::l₂ ∧ Along G x l₁ a ∧ G e = s(a,b) ∧
        a ∉ D ∧ b ∈ D ∧ Along G b l₂ y ∧ ∀ d ∈ l₂, d ∈ internalEdges G D := by
  induction hl with
  | nil => exact Or.inl ⟨hy,by simp⟩
  | @cons x z y l e he ht ih =>
    rcases ih hy with ⟨hz,hall⟩ | ⟨a,b,d,l₁,l₂,heq,h₁,hd,ha,hb,h₂,hs⟩
    · by_cases hx : x ∈ D
      · left
        refine ⟨hx,?_⟩
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact (mem_internalEdges_of_ends G D d x z he).mpr ⟨hx,hz⟩
        · exact hall d hd
      · right
        exact ⟨x,z,e,[],l,rfl,.nil x,he,hx,hz,ht,hall⟩
    · right
      exact ⟨a,b,d,e::l₁,l₂,by simp [heq],.cons e he h₁,hd,ha,hb,h₂,hs⟩

end ShortPathsDeletedDomain
end Percolation

end OAI
