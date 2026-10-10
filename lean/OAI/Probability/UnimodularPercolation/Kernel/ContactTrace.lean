import Mathlib
import OAI.Probability.UnimodularPercolation.Clusters.LargeContacts

namespace OAI

/-! Contact Trace for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section IndexedEdgeKernel
attribute [local instance] Classical.propDecidable Classical.decEq

theorem enn_ncard_eq_tsum {α : Type*} (A : Set α) (hA : A.Finite) :
    (A.ncard:ℝ≥0∞) = ∑' a, if a ∈ A then (1:ℝ≥0∞) else 0 := by
  rw [tsum_eq_sum (s := hA.toFinset) (fun a ha => by
    simp only [Set.Finite.mem_toFinset] at ha
    exact ite_eq_right ha)]
  simp only [Set.ncard_eq_toFinset_card A hA]
  rw [Finset.sum_congr rfl (fun a ha => ite_eq_left ((Set.Finite.mem_toFinset _).mp ha))]
  simp

 

noncomputable def indexedEdgeKernel (G : BondGraph V E) (x y : V) : ℝ≥0∞ :=
  ∑' e, if G e = s(x,y) then 1 else 0

theorem indexedEdgeKernel_eq_ncard (G : BondGraph V E) (hloc : LocallyFinite G) (x y : V) :
    indexedEdgeKernel G x y = ({e | G e = s(x,y)}.ncard:ℝ≥0∞) := by
  have hf : ({e | G e = s(x,y)} : Set E).Finite := (hloc x).subset (fun e he => by change x ∈ G e; change G e = s(x,y) at he; rw [he]; simp)
  unfold indexedEdgeKernel
  convert (enn_ncard_eq_tsum _ hf).symm using 1
  apply tsum_congr
  intro e
  by_cases h : G e = s(x,y) <;> simp only [Set.mem_ofPred_eq,h,ite_true,ite_false]

theorem indexedEdgeKernel_symm (G : BondGraph V E) (x y : V) :
    indexedEdgeKernel G x y = indexedEdgeKernel G y x := by rw [indexedEdgeKernel,indexedEdgeKernel,Sym2.eq_swap]

theorem indexedEdgeKernel_row (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) :
    (∑' y, indexedEdgeKernel G x y) = (degree G x:ℝ≥0∞) := by
  change (∑' y, ∑' e, if G e = s(x,y) then (1:ℝ≥0∞) else 0) = _
  rw [ENNReal.tsum_comm,←ENNReal.tsum_prod]
  have hn := (enn_ncard_eq_tsum _ (finite_steps G hloc x)).symm
  have he : (∑' (p : E × V), if G p.1 = s(x,p.2) then (1:ℝ≥0∞) else 0) =
      (({ey : E × V | G ey.1 = s(x,ey.2)} : Set (E × V)).ncard:ℝ≥0∞) := by
    convert hn using 1
    apply tsum_congr
    intro ey
    by_cases h : G ey.1 = s(x,ey.2) <;> simp only [Set.mem_ofPred_eq,h,ite_true,ite_false]
  rw [he]
  change (({ey : E × V | G ey.1 = s(x,ey.2)} : Set (E × V)).ncard:ℝ≥0∞) = (Nat.card (Step G x):ℝ≥0∞)
  rw [←Nat.card_coe_set_eq]; rfl

theorem indexedEdgeKernel_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x y : V) :
    indexedEdgeKernel G (a x) (a y) = indexedEdgeKernel G x y := by
  unfold indexedEdgeKernel
  rw [←b.tsum_eq (fun e => if G e = s(a x,a y) then (1:ℝ≥0∞) else 0)]
  apply tsum_congr
  intro e
  have he : G (b e) = s(a x,a y) ↔ G e = s(x,y) := by
    rw [hab e,←Sym2.map_mk]
    exact (Sym2.map.injective a.injective).eq_iff
  simp only [he]

end IndexedEdgeKernel
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ContactKernelCounting
attribute [local instance] Classical.propDecidable Classical.decEq

theorem contact_endpoints_unique (G : BondGraph V E) (ω : Set E) (x y : V)
    (hd : ¬Conn G ω x y) {e : E} {a b c d : V}
    (ha : Conn G ω x a) (_hb : Conn G ω y b)
    (_hc : Conn G ω x c) (he : Conn G ω y d)
    (hab : G e = s(a,b)) (hcd : G e = s(c,d)) : a = c ∧ b = d := by
  rcases Sym2.eq_iff.mp (hab.symm.trans hcd) with h | h
  · exact h
  · exfalso
    apply hd
    exact conn_trans G ω ha (by simpa only [h.1] using conn_symm G ω he)

theorem closedContactSet_finite (G : BondGraph V E) (hloc : LocallyFinite G)
    (A B : Set V) (hA : A.Finite) : (closedContactSet G A B).Finite := by
  have hs := contactSet_subset_incident G hloc hA.toFinset B
  rw [Set.Finite.coe_toFinset] at hs
  exact (incidentSupport G hloc hA.toFinset).finite_toSet.subset hs

theorem clusterPairKernel_edge (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x y : V) (hd : ¬Conn G ω x y) (hx : (cluster G ω x).Finite) :
    clusterPairKernel G ω (indexedEdgeKernel G) x y = (clusterContactCount G ω x y:ℝ≥0∞) := by
  have hed (e : E) :
      (∑' a, ∑' b, if Conn G ω x a ∧ Conn G ω y b ∧ G e = s(a,b) then (1:ℝ≥0∞) else 0) =
      if e ∈ closedContactSet G (cluster G ω x) (cluster G ω y) then 1 else 0 := by
    by_cases h : e ∈ closedContactSet G (cluster G ω x) (cluster G ω y)
    · obtain ⟨a,ha,b,hb,hab⟩ := h
      change Conn G ω x a at ha
      change Conn G ω y b at hb
      have hh : e ∈ closedContactSet G (cluster G ω x) (cluster G ω y) := ⟨a,ha,b,hb,hab⟩
      rw [ite_eq_left hh,tsum_eq_single a]
      · rw [tsum_eq_single b]
        · exact ite_eq_left ⟨ha,hb,hab⟩
        · intro d hdb
          apply ite_eq_right
          intro hc
          exact hdb (contact_endpoints_unique G ω x y hd hc.1 hc.2.1 ha hb hc.2.2 hab).2
      · intro c hca
        apply ENNReal.tsum_eq_zero.mpr
        intro d
        apply ite_eq_right
        intro hc
        exact hca (contact_endpoints_unique G ω x y hd hc.1 hc.2.1 ha hb hc.2.2 hab).1
    · rw [ite_eq_right h]
      apply ENNReal.tsum_eq_zero.mpr
      intro a
      apply ENNReal.tsum_eq_zero.mpr
      intro b
      apply ite_eq_right
      intro hab
      exact h ⟨a,hab.1,b,hab.2.1,hab.2.2⟩
  have he (a b : V) : (if Conn G ω x a ∧ Conn G ω y b then indexedEdgeKernel G a b else 0) =
      ∑' e, if Conn G ω x a ∧ Conn G ω y b ∧ G e = s(a,b) then (1:ℝ≥0∞) else 0 := by
    by_cases ha : Conn G ω x a <;> by_cases hb : Conn G ω y b <;>
      simp only [ha,hb,and_self,true_and,false_and,ite_true,ite_false,indexedEdgeKernel,tsum_zero]
  rw [clusterPairKernel]
  simp_rw [he]
  calc
    _ = ∑' e, ∑' a, ∑' b, if Conn G ω x a ∧ Conn G ω y b ∧ G e = s(a,b) then (1:ℝ≥0∞) else 0 := by
      calc
        _ = ∑' a, ∑' e, ∑' b, if Conn G ω x a ∧ Conn G ω y b ∧ G e = s(a,b) then (1:ℝ≥0∞) else 0 := by
          apply tsum_congr; intro a; exact ENNReal.tsum_comm
        _ = _ := ENNReal.tsum_comm
    _ = ∑' e, if e ∈ closedContactSet G (cluster G ω x) (cluster G ω y) then (1:ℝ≥0∞) else 0 := tsum_congr hed
    _ = _ := (enn_ncard_eq_tsum _ (closedContactSet_finite G hloc _ _ hx)).symm

end ContactKernelCounting
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ContactCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

theorem closedContactSet_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (A B : Set V) :
    b '' closedContactSet G A B = closedContactSet G (a '' A) (a '' B) := by
  ext e
  constructor
  · rintro ⟨f,⟨x,hx,y,hy,hf⟩,rfl⟩
    exact ⟨a x,Set.mem_image_of_mem a hx,a y,Set.mem_image_of_mem a hy,by rw [hab f,hf,Sym2.map_mk]⟩
  · rintro ⟨z,⟨x,hx,rfl⟩,w,⟨y,hy,rfl⟩,he⟩
    refine ⟨b.symm e,⟨x,hx,y,hy,?_⟩,b.apply_symm_apply e⟩
    apply Sym2.map.injective a.injective
    rw [←hab,Sym2.map_mk]
    simpa only [Equiv.apply_symm_apply] using he

theorem clusterContactCount_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x y : V) :
    clusterContactCount G (b ⁻¹' ω) x y = clusterContactCount G ω (a x) (a y) := by
  unfold clusterContactCount
  rw [←cluster_aut G hab ω x,←cluster_aut G hab ω y,←closedContactSet_aut G hab,
    Set.ncard_image_of_injective _ b.injective]

theorem fullLargeContact_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x y : V) (L : ℕ) :
    fullLargeContact G x y L (b ⁻¹' ω) = fullLargeContact G (a x) (a y) L ω := by
  simp only [fullLargeContact,conn_aut_iff G hab,cluster_ncard_covariant G hab,clusterContactCount_aut G hab]

theorem fullLargeContact_cluster_constant (G : BondGraph V E) (ω : Set E)
    (L : ℕ) (x y a b : V) (hxa : Conn G ω x a) (hyb : Conn G ω y b) :
    fullLargeContact G x y L ω = fullLargeContact G a b L ω := by
  have hc : Conn G ω x y ↔ Conn G ω a b := by
    constructor
    · intro h; exact conn_trans G ω (conn_symm G ω hxa) (conn_trans G ω h hyb)
    · intro h; exact conn_trans G ω hxa (conn_trans G ω h (conn_symm G ω hyb))
  simp only [fullLargeContact,clusterContactCount,cluster_eq_of_conn G ω hxa,
    cluster_eq_of_conn G ω hyb,hc]

theorem fullLargeContact_distinct (G : BondGraph V E) (ω : Set E) (x y : V) (L : ℕ) :
    (if ¬Conn G ω x y then ENNReal.ofReal (fullLargeContact G x y L ω) else 0) =
      ENNReal.ofReal (fullLargeContact G x y L ω) := by
  by_cases h : Conn G ω x y
  · simp only [fullLargeContact,h,not_true_eq_false,false_and,ite_false,ENNReal.ofReal_zero]
  · exact ite_eq_left h

end ContactCovariance
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ContactSquareTrace
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def contactSquareLarge (G : BondGraph V E) (L : ℕ)
    (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if L ≤ min (cluster G ω x).ncard (cluster G ω y).ncard then
    (clusterContactCount G ω x y:ℝ≥0∞)^2 else 0

theorem contactSquareLarge_reroot [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (p : unitInterval)
    (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite) (L : ℕ) :
    clusterPairFunctional G p root weight (contactSquareLarge G L) =
      ∑ i, ENNReal.ofReal (weight i) * ∫⁻ ω, ∑' y,
        indexedEdgeKernel G (root i) y * ENNReal.ofReal (fullLargeContact G (root i) y L ω) ∂law p := by
  have hj : ∀ a ∈ Γ, ∀ x y, indexedEdgeKernel G (a x) (a y) = indexedEdgeKernel G x y := by
    intro a ha x y
    obtain ⟨b,hab⟩ := hΓ ha
    exact indexedEdgeKernel_aut G hab x y
  have ht := clusterPairFunctional_reroot G hconn hloc root weight Γ hΓ htr hw p hfin
    (indexedEdgeKernel G) hj (fun ω x y => ENNReal.ofReal (fullLargeContact G x y L ω))
    (fun x y => (measurable_fullLargeContact G hloc x y L).ennreal_ofReal)
    (fun ω x y a b hxa hyb => congrArg ENNReal.ofReal (fullLargeContact_cluster_constant G ω L x y a b hxa hyb))
    (fun a _ b hab ω x y => congrArg ENNReal.ofReal (fullLargeContact_aut G hab ω x y L))
  simp_rw [fullLargeContact_distinct] at ht
  rw [←ht]
  unfold clusterPairFunctional
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hfin (root i)] with ω hω
  unfold clusterPairDensity
  congr 1
  apply tsum_congr
  intro y
  congr 1
  by_cases hd : Conn G ω (root i) y
  · simp only [hd,not_true_eq_false,ite_false]
  · rw [ite_eq_left hd,ite_eq_left hd]
    dsimp only
    rw [clusterPairKernel_edge G hloc ω (root i) y hd hω]
    unfold contactSquareLarge fullLargeContact
    by_cases hs : L ≤ min (cluster G ω (root i)).ncard (cluster G ω y).ncard
    · simp only [hd,hs,not_false_eq_true,true_and,ite_true,ENNReal.ofReal_natCast,pow_two]
    · simp only [hs,and_false,ite_false,ENNReal.ofReal_zero,mul_zero]

theorem contactSquareLarge_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1) (p : unitInterval)
    (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite) (L d : ℕ)
    (hd : ∀ x, degree G x ≤ d) (B : ℝ) (_hB : 0 ≤ B)
    (hI : ∀ x y, Integrable (fullLargeContact G x y L) (law p))
    (hb : ∀ x y, (∫ ω, fullLargeContact G x y L ω ∂law p) ≤ B) :
    clusterPairFunctional G p root weight (contactSquareLarge G L) ≤ ENNReal.ofReal ((d:ℝ)*B) := by
  have hi (x y : V) : (∫⁻ ω, ENNReal.ofReal (fullLargeContact G x y L ω) ∂law p) ≤ ENNReal.ofReal B := by
    rw [←ofReal_integral_eq_lintegral_ofReal (hI x y) (Filter.Eventually.of_forall (fullLargeContact_nonneg G x y L))]
    exact ENNReal.ofReal_le_ofReal (hb x y)
  have hr (x : V) : (∫⁻ ω, ∑' y, indexedEdgeKernel G x y * ENNReal.ofReal (fullLargeContact G x y L ω) ∂law p) ≤
      ENNReal.ofReal ((d:ℝ)*B) := by
    have hm (y : V) : Measurable (fun ω => indexedEdgeKernel G x y * ENNReal.ofReal (fullLargeContact G x y L ω)) :=
      (measurable_const : Measurable (fun _ : Set E => indexedEdgeKernel G x y)).mul (measurable_fullLargeContact G hloc x y L).ennreal_ofReal
    rw [lintegral_tsum (fun y => (hm y).aemeasurable)]
    simp_rw [lintegral_const_mul _ (measurable_fullLargeContact G hloc x _ L).ennreal_ofReal]
    calc
      _ ≤ ∑' y, indexedEdgeKernel G x y * ENNReal.ofReal B := ENNReal.tsum_le_tsum (fun y => mul_le_mul_right (hi x y) _)
      _ = (degree G x:ℝ≥0∞)*ENNReal.ofReal B := by rw [ENNReal.tsum_mul_right,indexedEdgeKernel_row G hloc x]
      _ ≤ (d:ℝ≥0∞)*ENNReal.ofReal B := mul_le_mul_left (by exact_mod_cast hd x) _
      _ = _ := by rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_natCast]
  rw [contactSquareLarge_reroot G hconn hloc root weight Γ hΓ htr hw p hfin L]
  calc
    _ ≤ ∑ i, ENNReal.ofReal (weight i)*ENNReal.ofReal ((d:ℝ)*B) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_right (hr (root i)) _)
    _ = _ := by rw [←Finset.sum_mul,←ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i),hw1,ENNReal.ofReal_one,one_mul]

end ContactSquareTrace
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section CriticalContactSquare
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem critical_contact_square_bound_nat
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
    ∃ C : ℝ, 0 < C ∧ ∀ (p : unitInterval), (pc G:ℝ)/2 ≤ (p:ℝ) → p ≤ pc G →
      ∀ L : ℕ, 1 ≤ L → clusterPairFunctional G p root weight (contactSquareLarge G L) ≤
        ENNReal.ofReal (C*(L:ℝ)^((1:ℝ)/2+ε-2*α)) := by
  obtain ⟨A,hA,hb⟩ := critical_large_contact_bound G hloc hconn hqt hh root weight Γ hΓ htr
    hcov hw hw1 hp₀ hp₁ hfin α ε hα hα1 hε hr
  obtain ⟨d,hd,hdeg⟩ := exists_degree_bound G hqt
  refine ⟨(d:ℝ)*A,mul_pos (by exact_mod_cast hd) hA,?_⟩
  intro p hp hpq L hL
  have hf : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite := by
    intro x
    obtain ⟨i,a,ha,rfl⟩ := hcov x
    obtain ⟨b,hab⟩ := hΓ ha
    exact cluster_finite_ae_mono G (a (root i)) p (pc G) hpq
      (cluster_finite_ae_covariant G (pc G) hab (root i) (hfin i))
  have h := contactSquareLarge_bound G hconn hloc root weight Γ hΓ htr (fun i => (hw i).le) hw1 p hf
    L d hdeg (A*(L:ℝ)^((1:ℝ)/2+ε-2*α)) (mul_nonneg hA.le (Real.rpow_nonneg (by positivity) _))
    (fun x y => (hb x y p hp hpq L hL).1) (fun x y => (hb x y p hp hpq L hL).2)
  simpa only [mul_assoc] using h

end CriticalContactSquare
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section DistinctClusterBK
attribute [local instance] Classical.propDecidable Classical.decEq

theorem distinct_cluster_disjoint_occurrence (G : BondGraph V E) (ω : Set E)
    (x y a b : V) (hxa : Conn G ω x a) (hyb : Conn G ω y b) (hd : ¬Conn G ω x y) :
    ω ∈ DisjointOccurrence {η | Conn G η x a} {η | Conn G η y b} := by
  obtain ⟨s,hs,hsa⟩ := finiteWitness_conn G x a _ (conn_restrict_cluster G ω x (mem_cluster_self G ω x) hxa)
  obtain ⟨t,ht,htb⟩ := finiteWitness_conn G y b _ (conn_restrict_cluster_compl G ω x hd hyb)
  refine ⟨s,t,fun e he => (hs he).1,fun e he => (ht he).1,?_,hsa,htb⟩
  apply Finset.disjoint_left.mpr
  intro e he ht'
  obtain ⟨⟨z,w⟩,hr⟩ := Quot.exists_rep (G e)
  have hz : z ∈ G e := by rw [←hr]; exact Sym2.mem_mk_left z w
  exact (ht ht').2 z hz ((hs he).2 z hz)

theorem distinct_cluster_two_point_bound [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x y a b : V) :
    law p {ω | Conn G ω x a ∧ Conn G ω y b ∧ ¬Conn G ω x y} ≤
      law p {ω | Conn G ω x a} * law p {ω | Conn G ω y b} := by
  calc
    _ ≤ law p (DisjointOccurrence {ω | Conn G ω x a} {ω | Conn G ω y b}) :=
      measure_mono (fun ω h => distinct_cluster_disjoint_occurrence G ω x y a b h.1 h.2.1 h.2.2)
    _ ≤ _ := bk_ennreal p _ _ (fun _ _ h hc => conn_mono G h hc)
      (fun _ _ h hc => conn_mono G h hc) (finiteWitness_conn G x a) (finiteWitness_conn G y b)

theorem measurable_clusterPairKernel [Countable V] [Countable E]
    (G : BondGraph V E) (J : V → V → ℝ≥0∞) (x y : V) :
    Measurable (fun ω => clusterPairKernel G ω J x y) := by
  apply Measurable.tsum
  intro a
  apply Measurable.tsum
  intro b
  exact measurable_const.ite ((measurableSet_conn G x a).inter (measurableSet_conn G y b)) measurable_const

theorem clusterPairKernel_cluster_constant (G : BondGraph V E) (ω : Set E)
    (J : V → V → ℝ≥0∞) (x y a b : V) (hxa : Conn G ω x a) (hyb : Conn G ω y b) :
    clusterPairKernel G ω J x y = clusterPairKernel G ω J a b := by
  have hx (z : V) : Conn G ω x z ↔ Conn G ω a z :=
    ⟨fun h => conn_trans G ω (conn_symm G ω hxa) h,fun h => conn_trans G ω hxa h⟩
  have hy (z : V) : Conn G ω y z ↔ Conn G ω b z :=
    ⟨fun h => conn_trans G ω (conn_symm G ω hyb) h,fun h => conn_trans G ω hyb h⟩
  simp only [clusterPairKernel,hx,hy]

theorem clusterPairKernel_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (J : V → V → ℝ≥0∞) (hJ : ∀ x y, J (a x) (a y) = J x y)
    (ω : Set E) (x y : V) :
    clusterPairKernel G (b ⁻¹' ω) J x y = clusterPairKernel G ω J (a x) (a y) := by
  unfold clusterPairKernel
  rw [←a.tsum_eq (fun x' => ∑' y', if Conn G ω (a x) x' ∧ Conn G ω (a y) y' then J x' y' else 0)]
  apply tsum_congr
  intro x'
  rw [←a.tsum_eq (fun y' => if Conn G ω (a x) (a x') ∧ Conn G ω (a y) y' then J (a x') y' else 0)]
  simp only [hJ,conn_aut_iff G hab]

end DistinctClusterBK
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section PairSquareDiagram
attribute [local instance] Classical.propDecidable Classical.decEq

theorem clusterPairKernel_distinct_integral [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (J : V → V → ℝ≥0∞) (x y : V) :
    (∫⁻ ω, if ¬Conn G ω x y then clusterPairKernel G ω J x y else 0 ∂law p) =
      ∑' a, ∑' b, J a b * law p {ω | Conn G ω x a ∧ Conn G ω y b ∧ ¬Conn G ω x y} := by
  have he (ω : Set E) : (if ¬Conn G ω x y then clusterPairKernel G ω J x y else 0) =
      ∑' a, ∑' b, J a b * (if Conn G ω x a ∧ Conn G ω y b ∧ ¬Conn G ω x y then (1:ℝ≥0∞) else 0) := by
    by_cases hd : Conn G ω x y
    · simp only [hd,not_true_eq_false,and_false,ite_false,mul_zero,tsum_zero]
    · rw [ite_eq_left hd,clusterPairKernel]
      apply tsum_congr; intro a
      apply tsum_congr; intro b
      by_cases h : Conn G ω x a ∧ Conn G ω y b
      · simp only [h.1,h.2,hd,not_false_eq_true,and_self,ite_true,mul_one]
      · have hn : ¬ (Conn G ω x a ∧ Conn G ω y b ∧ ¬Conn G ω x y) := fun h' => h ⟨h'.1,h'.2.1⟩
        simp only [ite_eq_right h,ite_eq_right hn,mul_zero]
  have hm (a b : V) : Measurable (fun ω => if Conn G ω x a ∧ Conn G ω y b ∧ ¬Conn G ω x y then (1:ℝ≥0∞) else 0) :=
    measurable_const.ite ((measurableSet_conn G x a).inter ((measurableSet_conn G y b).inter (measurableSet_conn G x y).compl)) measurable_const
  have hm' (a b : V) : Measurable (fun ω : Set E => J a b * (if Conn G ω x a ∧ Conn G ω y b ∧ ¬Conn G ω x y then (1:ℝ≥0∞) else 0)) :=
    (measurable_const : Measurable (fun _ : Set E => J a b)).mul (hm a b)
  simp_rw [he]
  rw [lintegral_tsum (fun a => (Measurable.tsum (fun b => hm' a b)).aemeasurable)]
  apply tsum_congr; intro a
  rw [lintegral_tsum (fun b => (hm' a b).aemeasurable)]
  apply tsum_congr; intro b
  rw [lintegral_const_mul _ (hm a b)]
  congr 1
  convert
    (lintegral_indicator_one (μ := law p) ((measurableSet_conn G x a).inter ((measurableSet_conn G y b).inter (measurableSet_conn G x y).compl))) using 1
  · apply lintegral_congr
    intro ω
    simp only [Set.indicator,Set.mem_inter_iff,Set.mem_compl_iff,Set.mem_ofPred_eq,Pi.one_apply]
  · congr 1

theorem clusterPairKernel_distinct_bound [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (J : V → V → ℝ≥0∞) (x y : V) :
    (∫⁻ ω, if ¬Conn G ω x y then clusterPairKernel G ω J x y else 0 ∂law p) ≤
      ∑' a, ∑' b, J a b * (law p {ω | Conn G ω x a} * law p {ω | Conn G ω y b}) := by
  rw [clusterPairKernel_distinct_integral]
  exact ENNReal.tsum_le_tsum (fun a => ENNReal.tsum_le_tsum (fun b =>
    mul_le_mul_right (distinct_cluster_two_point_bound G p x y a b) _))

 

theorem clusterPairFunctional_square_diagram [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (p : unitInterval)
    (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (J : V → V → ℝ≥0∞) (hJ : ∀ a ∈ Γ, ∀ x y, J (a x) (a y) = J x y) :
    clusterPairFunctional G p root weight (fun ω x y => (clusterPairKernel G ω J x y)^2) ≤
      ∑ i, ENNReal.ofReal (weight i) * ∑' v, ∑' a, ∑' b,
        J (root i) v * (J a b * (law p {ω | Conn G ω (root i) a} * law p {ω | Conn G ω v b})) := by
  have ht := clusterPairFunctional_reroot G hconn hloc root weight Γ hΓ htr hw p hfin J hJ
    (fun ω x y => clusterPairKernel G ω J x y) (measurable_clusterPairKernel G J)
    (fun ω x y a b => clusterPairKernel_cluster_constant G ω J x y a b)
    (fun a ha b hab ω x y => clusterPairKernel_aut G hab J (hJ a ha) ω x y)
  simp only [←pow_two] at ht
  rw [ht]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_right
  have hm (v : V) : Measurable (fun ω : Set E => if ¬Conn G ω (root i) v then clusterPairKernel G ω J (root i) v else 0) :=
    (measurable_clusterPairKernel G J (root i) v).ite (measurableSet_conn G (root i) v).compl measurable_const
  have hm' (v : V) : Measurable (fun ω : Set E => J (root i) v * (if ¬Conn G ω (root i) v then clusterPairKernel G ω J (root i) v else 0)) :=
    (measurable_const : Measurable (fun _ : Set E => J (root i) v)).mul (hm v)
  rw [lintegral_tsum (fun v => (hm' v).aemeasurable)]
  apply ENNReal.tsum_le_tsum
  intro v
  rw [lintegral_const_mul _ (hm v)]
  simp_rw [ENNReal.tsum_mul_left]
  exact mul_le_mul_right (clusterPairKernel_distinct_bound G p J (root i) v) _

end PairSquareDiagram
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ContactRealCutoff
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def contactSquareLargeReal (G : BondGraph V E) (L : ℝ)
    (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if L ≤ min ((cluster G ω x).ncard:ℝ) ((cluster G ω y).ncard:ℝ) then
    (clusterContactCount G ω x y:ℝ≥0∞)^2 else 0

theorem contactSquareLargeReal_eq_ceil (G : BondGraph V E) (L : ℝ)
    (ω : Set E) (x y : V) :
    contactSquareLargeReal G L ω x y = contactSquareLarge G ⌈L⌉₊ ω x y := by
  have he : L ≤ min ((cluster G ω x).ncard:ℝ) ((cluster G ω y).ncard:ℝ) ↔
      ⌈L⌉₊ ≤ min (cluster G ω x).ncard (cluster G ω y).ncard := by
    rw [←Nat.cast_min, Nat.ceil_le]
  simp only [contactSquareLargeReal,contactSquareLarge,he]

 

theorem critical_contact_square_bound
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
    ∃ C : ℝ, 0 < C ∧ ∀ (p : unitInterval), (pc G:ℝ)/2 ≤ (p:ℝ) → p ≤ pc G →
      ∀ L : ℝ, 1 ≤ L → clusterPairFunctional G p root weight (contactSquareLargeReal G L) ≤
        ENNReal.ofReal (C*L^((1:ℝ)/2+ε-2*α)) := by
  obtain ⟨C,hC,hb⟩ := critical_contact_square_bound_nat G hloc hconn hqt hh root weight Γ hΓ htr
    hcov hw hw1 hp₀ hp₁ hfin α ε hα hα1 hε hr
  refine ⟨C,hC,?_⟩
  intro p hp hpq L hL
  have hLn : 1 ≤ ⌈L⌉₊ := by
    have hc : (1:ℝ) ≤ (⌈L⌉₊:ℝ) := hL.trans (Nat.le_ceil L)
    exact_mod_cast hc
  have hEq : contactSquareLargeReal G L = contactSquareLarge G ⌈L⌉₊ := funext fun ω => funext fun x => funext fun y => contactSquareLargeReal_eq_ceil G L ω x y
  rw [hEq]
  exact (hb p hp hpq _ hLn).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by linarith : 0 < L) (Nat.le_ceil L) hr.le) hC.le))

end ContactRealCutoff
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section NonnegativeOperatorDiagram
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def ennMatrixCoeff (A : Hilbert V →L[ℂ] Hilbert V) (x y : V) : ℝ≥0∞ :=
  ENNReal.ofReal (matrixCoeff A x y).re

theorem ennMatrixCoeff_mul {A B : Hilbert V →L[ℂ] Hilbert V}
    (hA : PositiveRealMatrix A) (hB : PositiveRealMatrix B) (x y : V) :
    ennMatrixCoeff (A*B) x y = ∑' z, ennMatrixCoeff A x z * ennMatrixCoeff B z y := by
  unfold ennMatrixCoeff
  rw [←(hA.mul_hasSum B x y).tsum_eq, ENNReal.ofReal_tsum_of_nonneg
    (fun z => mul_nonneg (hA x z).2 (hB z y).2) (hA.mul_hasSum B x y).summable]
  apply tsum_congr; intro z
  exact ENNReal.ofReal_mul (hA x z).2

theorem ennMatrixCoeff_symm {A : Hilbert V →L[ℂ] Hilbert V}
    (hA : IsSelfAdjoint A) (x y : V) : ennMatrixCoeff A x y = ennMatrixCoeff A y x := by
  unfold ennMatrixCoeff
  rw [matrixCoeff_real_symm A hA x y]

theorem HasKernel.ennMatrixCoeff [Countable E] (G : BondGraph V E) (p : unitInterval)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) (x y : V) :
    ennMatrixCoeff T x y = law p {ω | Conn G ω x y} := by
  unfold Percolation.ennMatrixCoeff matrixCoeff
  rw [hT x y]
  simp only [Complex.ofReal_re,twoPoint,ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem HasKernel.positiveRealMatrix (G : BondGraph V E) (p : unitInterval)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) : PositiveRealMatrix T := by
  intro x y
  change (T (lp.single 2 y (1:ℂ)) x).im = 0 ∧ 0 ≤ (T (lp.single 2 y (1:ℂ)) x).re
  rw [hT x y]
  exact ⟨rfl,twoPoint_nonneg G p x y⟩

theorem square_kernel_diagram (J T : Hilbert V →L[ℂ] Hilbert V)
    (hJ : PositiveRealMatrix J) (hT : PositiveRealMatrix T)
    (hsJ : IsSelfAdjoint J) (hsT : IsSelfAdjoint T) (x : V) :
    (∑' v, ∑' a, ∑' b, ennMatrixCoeff J x v * (ennMatrixCoeff J a b *
      (ennMatrixCoeff T x a * ennMatrixCoeff T v b))) = ennMatrixCoeff (J*T*J*T) x x := by
  rw [mul_assoc,mul_assoc,ennMatrixCoeff_mul hJ (hT.mul (hJ.mul hT))]
  apply tsum_congr; intro v
  rw [ennMatrixCoeff_mul hT (hJ.mul hT)]
  simp_rw [ennMatrixCoeff_mul hJ hT]
  simp_rw [←ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr; intro b
  apply tsum_congr; intro a
  rw [ennMatrixCoeff_symm hsJ b a,ennMatrixCoeff_symm hsT a x]
  ac_rfl

theorem enn_rootTrace {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A) :
    (∑ i, ENNReal.ofReal (weight i) * ennMatrixCoeff A (root i) (root i)) =
      ENNReal.ofReal (rootTrace root weight A).re := by
  unfold rootTrace ennMatrixCoeff
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hw i) (hA _ _).2)]
  apply Finset.sum_congr rfl; intro i _
  exact (ENNReal.ofReal_mul (hw i)).symm

end NonnegativeOperatorDiagram
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal ComplexOrder
section KernelSquareTrace
attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance] spectralRealOperatorScalarTower spectralRealOperatorSMulCommClass
local instance : NonUnitalContinuousFunctionalCalculus ℝ
    (Hilbert V →L[ℂ] Hilbert V) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus (A := Hilbert V →L[ℂ] Hilbert V)
local instance : ContinuousFunctionalCalculus ℝ
    (Hilbert V →L[ℂ] Hilbert V) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus (A := Hilbert V →L[ℂ] Hilbert V)

theorem rootTrace_six_le_cube {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) {Γ : Set (V ≃ V)}
    (htr : RootTransport root weight Γ) (hw : ∀ i, 0 ≤ weight i)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : KernelInvariant Γ T) (hpos : 0 ≤ T) :
    (rootTrace root weight (T^6)).re ≤ ‖T‖^3*(rootTrace root weight (T^3)).re := by
  have hp3 : 0 ≤ T^3 := CStarAlgebra.pow_nonneg T 3 hpos
  have h := rootTrace_positive_mul_le root weight htr hw (T^3) (T^3)
    (hT.pow 3) (hT.pow 3) hp3 (IsSelfAdjoint.of_nonneg hp3)
  have he : T^3*T^3 = T^6 := by rw [←pow_add]
  rw [he] at h
  have hr := (Complex.le_def.mp h).1
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hr
  exact hr.trans (mul_le_mul_of_nonneg_right (norm_pow_le' T (by norm_num : 0 < (3:ℕ)))
    (Complex.nonneg_iff.mp (rootTrace_nonneg root weight hw (T^3) hp3)).1)

 

theorem clusterPairFunctional_twoPoint_square_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (p : unitInterval)
    (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) :
    clusterPairFunctional G p root weight (fun ω x y =>
      (clusterPairKernel G ω (ennMatrixCoeff (T^2)) x y)^2) ≤
      ENNReal.ofReal (‖T‖^3*(rootTrace root weight (T^3)).re) := by
  have hp := hT.positiveRealMatrix G p T
  have hpos : 0 ≤ T := ContinuousLinearMap.nonneg_iff_isPositive.mpr (hT.isPositive G p T)
  have hsa := IsSelfAdjoint.of_nonneg hpos
  have hI : KernelInvariant Γ T := fun a ha => hT.invariant G p T a (hΓ ha)
  have hJ : ∀ a ∈ Γ, ∀ x y, ennMatrixCoeff (T^2) (a x) (a y) = ennMatrixCoeff (T^2) x y := by
    intro a ha x y
    unfold ennMatrixCoeff
    rw [(hI.pow 2) a ha]
  have hb := clusterPairFunctional_square_diagram G hconn hloc root weight Γ hΓ htr hw p hfin
    (ennMatrixCoeff (T^2)) hJ
  have hd (x : V) : (∑' v, ∑' a, ∑' b, ennMatrixCoeff (T^2) x v * (ennMatrixCoeff (T^2) a b *
      (law p {ω | Conn G ω x a} * law p {ω | Conn G ω v b}))) = ennMatrixCoeff (T^6) x x := by
    simp_rw [←hT.ennMatrixCoeff G p T]
    rw [square_kernel_diagram (T^2) T (hp.pow 2) hp (hsa.pow 2) hsa]
    congr 1
  simp_rw [hd] at hb
  rw [enn_rootTrace root weight hw (T^6) (hp.pow 6)] at hb
  exact hb.trans (ENNReal.ofReal_le_ofReal (rootTrace_six_le_cube root weight htr hw T hI hpos))

end KernelSquareTrace
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FiniteClusterKernel
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteClusterWeight (G : BondGraph V E) (f : V → ℝ)
    (x : V) (ω : Finset E) : ℝ := ∑ y ∈ finiteRootComponent G ω x, f y

theorem finiteClusterWeight_expand (G : BondGraph V E) (f : V → ℝ)
    (Q ω : Finset E) (hω : ω ⊆ Q) (x : V) :
    finiteClusterWeight G f x ω = ∑ y ∈ insert x (searchVertices G Q),
      f y * (if Conn G (ω:Set E) x y then (1:ℝ) else 0) := by
  unfold finiteClusterWeight
  calc
    _ = ∑ y ∈ finiteRootComponent G ω x, f y * (if Conn G (ω:Set E) x y then (1:ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro y hy
      have hc : Conn G (ω:Set E) x y := by
        change y ∈ (finiteRootComponent G ω x:Set V) at hy
        rwa [coe_finiteRootComponent] at hy
      rw [ite_eq_left hc,mul_one]
    _ = _ := Finset.sum_subset (finiteRootComponent_subset G Q _ x ω hω (by rfl)) (by
      intro y _ hy
      have hn : ¬Conn G (ω:Set E) x y := by
        intro h
        apply hy
        change y ∈ (finiteRootComponent G ω x:Set V)
        rwa [coe_finiteRootComponent]
      rw [ite_eq_right hn,mul_zero])

theorem finiteClusterWeight_expectation_le [Countable E]
    (G : BondGraph V E) (Q : Finset E) (f : V → ℝ) (hf : ∀ y, 0 ≤ f y)
    (x : V) (p : unitInterval) (hs : Summable (fun y => f y*twoPoint G p x y)) :
    bernoulliPolynomial Q (finiteClusterWeight G f x) p ≤ ∑' y, f y*twoPoint G p x y := by
  have he : bernoulliPolynomial Q (finiteClusterWeight G f x) p =
      bernoulliPolynomial Q (fun ω => ∑ y ∈ insert x (searchVertices G Q), f y*(if Conn G (ω:Set E) x y then (1:ℝ) else 0)) p := by
    apply bernoulliPolynomial_congr
    intro ω hω
    exact finiteClusterWeight_expand G f Q ω hω x
  rw [he,bernoulliPolynomial_sum]
  calc
    _ ≤ ∑ y ∈ insert x (searchVertices G Q), f y*twoPoint G p x y := by
      apply Finset.sum_le_sum
      intro y _
      have hpQ : bernoulliPolynomial Q (fun ω => if Conn G (ω:Set E) x y then (1:ℝ) else 0) p =
          (law p).real {ω | Conn G (ω ∩ (Q:Set E)) x y} :=
        finiteEventPolynomial_restrict Q {ω | Conn G ω x y} p
      rw [bernoulliPolynomial_const_mul,hpQ]
      apply mul_le_mul_of_nonneg_left _ (hf y)
      exact measureReal_mono (fun ω h => conn_mono G Set.inter_subset_left h)
    _ ≤ _ := hs.sum_le_tsum _ (fun y _ => mul_nonneg (hf y) (twoPoint_nonneg G p x y))

noncomputable def finitePairKernel (G : BondGraph V E) (J : V → V → ℝ)
    (ω : Finset E) (x y : V) : ℝ :=
  ∑ a ∈ finiteRootComponent G ω x, finiteClusterWeight G (J a) y ω

theorem finitePairKernel_nonneg (G : BondGraph V E) (J : V → V → ℝ)
    (hJ : ∀ a b, 0 ≤ J a b) (ω : Finset E) (x y : V) : 0 ≤ finitePairKernel G J ω x y :=
  Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hJ a b

theorem finitePairKernel_exterior (G : BondGraph V E) (J : V → V → ℝ)
    (ω : Finset E) (x y : V) (hd : ¬Conn G (ω:Set E) x y) :
    finitePairKernel G J ω x y = ∑ a ∈ finiteRootComponent G ω x,
      finiteClusterWeight G (J a) y (exteriorBonds G ω (finiteRootComponent G ω x:Set V)) := by
  unfold finitePairKernel finiteClusterWeight
  rw [finiteRootComponent_exterior G ω x y hd]

end FiniteClusterKernel
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SmallFinitePairKernel
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteSmallPairKernel (G : BondGraph V E) (J : V → V → ℝ)
    (L : ℝ) (x y : V) (ω : Finset E) : ℝ :=
  if (finiteRootComponent G ω x).card < L ∧ ¬Conn G (ω:Set E) x y then finitePairKernel G J ω x y else 0

noncomputable def finiteSmallClusterSize (G : BondGraph V E) (L : ℝ) (x : V) (ω : Finset E) : ℝ :=
  if (finiteRootComponent G ω x).card < L then (finiteRootComponent G ω x).card else 0

 
theorem finiteSmallPairKernel_bound [Countable E]
    (G : BondGraph V E) (Q : Finset E) (J : V → V → ℝ) (hJ : ∀ a b, 0 ≤ J a b)
    (x y : V) (p : unitInterval) (L M : ℝ) (hM : 0 ≤ M)
    (hs : ∀ a, Summable (fun b => J a b*twoPoint G p y b))
    (hb : ∀ a, (∑' b, J a b*twoPoint G p y b) ≤ M) :
    bernoulliPolynomial Q (finiteSmallPairKernel G J L x y) p ≤
      M*bernoulliPolynomial Q (finiteSmallClusterSize G L x) p := by
  let f (W : Finset V) (η : Finset E) : ℝ :=
    (if (W.card:ℝ) < L ∧ y ∉ W then ∑ a ∈ W, finiteClusterWeight G (J a) y η else 0) -
      M*(if (W.card:ℝ) < L then (W.card:ℝ) else 0)
  have hf (W : Finset V) : bernoulliPolynomial (exteriorBonds G Q (W:Set V)) (f W) p ≤ 0 := by
    by_cases hW : (W.card:ℝ) < L
    · by_cases hy : y ∈ W
      · simp only [f,hW,hy,not_true_eq_false,and_false,ite_false,ite_true,zero_sub,
          bernoulliPolynomial_const]
        exact neg_nonpos.mpr (mul_nonneg hM (Nat.cast_nonneg _))
      · simp only [f,hW,hy,not_false_eq_true,and_self,ite_true,bernoulliPolynomial_sub,
          bernoulliPolynomial_const,bernoulliPolynomial_sum]
        apply sub_nonpos.mpr
        calc
          _ ≤ ∑ _a ∈ W, M := Finset.sum_le_sum fun a _ =>
            (finiteClusterWeight_expectation_le G _ (J a) (hJ a) y p (hs a)).trans (hb a)
          _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
    · simp only [f,hW,false_and,ite_false,mul_zero,sub_zero,bernoulliPolynomial_zero]
      exact le_rfl
  have ht := cluster_exterior_expectation_bound G Q x p f 0 hf
  have he (ω : Finset E) : f (finiteRootComponent G ω x)
      (exteriorBonds G ω (finiteRootComponent G ω x:Set V)) =
      finiteSmallPairKernel G J L x y ω - M*finiteSmallClusterSize G L x ω := by
    have hm : y ∈ finiteRootComponent G ω x ↔ Conn G (ω:Set E) x y := by
      change y ∈ (finiteRootComponent G ω x:Set V) ↔ _
      rw [coe_finiteRootComponent]
      rfl
    unfold f finiteSmallPairKernel finiteSmallClusterSize
    simp only [hm]
    by_cases hc : (finiteRootComponent G ω x).card < L ∧ ¬Conn G (ω:Set E) x y
    · rw [ite_eq_left hc,ite_eq_left hc,finitePairKernel_exterior G J ω x y hc.2]
    · rw [ite_eq_right hc,ite_eq_right hc]
  simp_rw [he] at ht
  rw [bernoulliPolynomial_sub,bernoulliPolynomial_const_mul] at ht
  exact sub_nonpos.mp ht

end SmallFinitePairKernel
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SmallSizeFractionalMoment
attribute [local instance] Classical.propDecidable Classical.decEq

theorem small_count_le_power (s L α : ℝ) (hs : 0 ≤ s) (hL : 0 ≤ L) (hα : α ≤ 1) :
    (if s < L then s else 0) ≤ L^(1-α)*s^α := by
  by_cases h : s < L
  · rw [ite_eq_left h]
    rcases eq_or_lt_of_le hs with rfl | hs'
    · positivity
    · calc
        s = s^(1-α)*s^α := by rw [←Real.rpow_add hs']; simp only [sub_add_cancel,Real.rpow_one]
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hs h.le (by linarith)) (Real.rpow_nonneg hs α)
  · rw [ite_eq_right h]
    exact mul_nonneg (Real.rpow_nonneg hL _) (Real.rpow_nonneg hs _)

theorem finiteSmallClusterSize_moment_bound [Countable E]
    (G : BondGraph V E) (Q : Finset E) (x : V) (p : unitInterval)
    (L α : ℝ) (hL : 0 ≤ L) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hfin : ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (hI : Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law p)) :
    bernoulliPolynomial Q (finiteSmallClusterSize G L x) p ≤
      L^(1-α)*(∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law p) := by
  let f (ω : Set E) := finiteSmallClusterSize G L x (domainBits Q ω)
  have hf : Integrable f (law p) := integrable_finite_local Q p f (fun ω => by
    dsimp [f]; rw [domainBits_local])
  rw [←integral_domainBits Q p (finiteSmallClusterSize G L x),←integral_const_mul]
  apply integral_mono_ae hf (hI.const_mul _)
  filter_upwards [hfin] with ω hω
  have hc : (finiteRootComponent G (domainBits Q ω) x).card ≤ (cluster G ω x).ncard := by
    rw [←Set.ncard_coe_finset,coe_finiteRootComponent,coe_domainBits]
    exact Set.ncard_le_ncard (fun y hy => conn_mono G Set.inter_subset_left hy) hω
  have hc' : ((finiteRootComponent G (domainBits Q ω) x).card:ℝ) ≤ (cluster G ω x).ncard := by exact_mod_cast hc
  exact (small_count_le_power _ L α (Nat.cast_nonneg _) hL hα1).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hc' hα0) (Real.rpow_nonneg hL _))

theorem finiteSmallPairKernel_moment_bound [Countable E]
    (G : BondGraph V E) (Q : Finset E) (J : V → V → ℝ) (hJ : ∀ a b, 0 ≤ J a b)
    (x y : V) (p : unitInterval) (L M α : ℝ) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hfin : ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (hI : Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law p))
    (hs : ∀ a, Summable (fun b => J a b*twoPoint G p y b))
    (hb : ∀ a, (∑' b, J a b*twoPoint G p y b) ≤ M) :
    bernoulliPolynomial Q (finiteSmallPairKernel G J L x y) p ≤
      M*(L^(1-α)*(∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law p)) :=
  (finiteSmallPairKernel_bound G Q J hJ x y p L M hM hs hb).trans
    (mul_le_mul_of_nonneg_left (finiteSmallClusterSize_moment_bound G Q x p L α hL hα0 hα1 hfin hI) hM)

end SmallSizeFractionalMoment
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
open scoped ENNReal
section SmallKernelLimit
attribute [local instance] Classical.propDecidable Classical.decEq

theorem clusterPairKernel_finite (G : BondGraph V E) (J : V → V → ℝ≥0∞)
    (ω : Finset E) (x y : V) :
    clusterPairKernel G ω J x y =
      ∑ a ∈ finiteRootComponent G ω x, ∑ b ∈ finiteRootComponent G ω y, J a b := by
  have hm (x a : V) : a ∈ finiteRootComponent G ω x ↔ Conn G (ω:Set E) x a := by
    change a ∈ (finiteRootComponent G ω x:Set V) ↔ _
    rw [coe_finiteRootComponent]
    rfl
  rw [clusterPairKernel,tsum_eq_sum (s := finiteRootComponent G ω x) (fun a ha => by
    simp only [←hm x a,ha,false_and,ite_false,tsum_zero])]
  apply Finset.sum_congr rfl
  intro a ha
  rw [tsum_eq_sum (s := finiteRootComponent G ω y) (fun b hb => by
    simp only [←hm y b,hb,and_false,ite_false])]
  apply Finset.sum_congr rfl
  intro b hb
  rw [ite_eq_left ⟨(hm x a).mp ha,(hm y b).mp hb⟩]

theorem ofReal_finitePairKernel (G : BondGraph V E) (J : V → V → ℝ)
    (hJ : ∀ a b, 0 ≤ J a b) (ω : Finset E) (x y : V) :
    ENNReal.ofReal (finitePairKernel G J ω x y) =
      clusterPairKernel G ω (fun a b => ENNReal.ofReal (J a b)) x y := by
  rw [clusterPairKernel_finite]
  unfold finitePairKernel finiteClusterWeight
  rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => Finset.sum_nonneg fun b _ => hJ a b)]
  apply Finset.sum_congr rfl
  intro a _
  exact ENNReal.ofReal_sum_of_nonneg (fun b _ => hJ a b)

noncomputable def smallPairKernel (G : BondGraph V E) (J : V → V → ℝ≥0∞)
    (L : ℝ) (x y : V) (ω : Set E) : ℝ≥0∞ :=
  if ((cluster G ω x).ncard:ℝ) < L ∧ ¬Conn G ω x y then clusterPairKernel G ω J x y else 0

theorem smallPairKernel_eq_finite (G : BondGraph V E) (hloc : LocallyFinite G)
    (J : V → V → ℝ) (hJ : ∀ a b, 0 ≤ J a b) (L : ℝ)
    (ω : Set E) (x y : V) (hx : (cluster G ω x).Finite) (hy : (cluster G ω y).Finite)
    (Q : Finset E) (hQx : incidentSupport G hloc hx.toFinset ⊆ Q)
    (hQy : incidentSupport G hloc hy.toFinset ⊆ Q) :
    ENNReal.ofReal (finiteSmallPairKernel G J L x y (domainBits Q ω)) =
      smallPairKernel G (fun a b => ENNReal.ofReal (J a b)) L x y ω := by
  have hcluster (z : V) (hz : (cluster G ω z).Finite) (hQ : incidentSupport G hloc hz.toFinset ⊆ Q) :
      cluster G (domainBits Q ω:Set E) z = cluster G ω z := by
    rw [coe_domainBits]
    have hh := (cluster_restrict_incident_eq_iff G hloc hz.toFinset Q hQ ω z).mpr
      (Set.Finite.coe_toFinset hz).symm
    simpa only [Set.Finite.coe_toFinset] using hh
  have hxC := hcluster x hx hQx
  have hyC := hcluster y hy hQy
  have hxN : (finiteRootComponent G (domainBits Q ω) x).card = (cluster G ω x).ncard := by
    rw [←Set.ncard_coe_finset,coe_finiteRootComponent,hxC]
  have hxconn (a : V) : Conn G (domainBits Q ω:Set E) x a ↔ Conn G ω x a := by
    change a ∈ cluster G (domainBits Q ω:Set E) x ↔ a ∈ cluster G ω x
    rw [hxC]
  have hyconn (b : V) : Conn G (domainBits Q ω:Set E) y b ↔ Conn G ω y b := by
    change b ∈ cluster G (domainBits Q ω:Set E) y ↔ b ∈ cluster G ω y
    rw [hyC]
  unfold finiteSmallPairKernel smallPairKernel
  rw [hxN]
  simp only [hxconn]
  split_ifs
  · rw [ofReal_finitePairKernel G J hJ]
    simp only [clusterPairKernel,hxconn,hyconn]
  · exact ENNReal.ofReal_zero

end SmallKernelLimit
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
open scoped ENNReal
section SmallKernelFatou
attribute [local instance] Classical.propDecidable Classical.decEq

theorem smallPairKernel_lintegral_le_of_finite [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G)
    (J : V → V → ℝ) (hJ : ∀ a b, 0 ≤ J a b) (L : ℝ) (x y : V) (p : unitInterval)
    (hx : ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (hy : ∀ᵐ ω ∂law p, (cluster G ω y).Finite) (B : ℝ)
    (hB : ∀ Q : Finset E, bernoulliPolynomial Q (finiteSmallPairKernel G J L x y) p ≤ B) :
    (∫⁻ ω, smallPairKernel G (fun a b => ENNReal.ofReal (J a b)) L x y ω ∂law p) ≤ ENNReal.ofReal B := by
  let : Encodable E := Encodable.ofCountable E
  let Q := vertexExhaustion (V := E)
  let f := fun j ω => finiteSmallPairKernel G J L x y (domainBits (Q j) ω)
  have hfi (j : ℕ) : Integrable (f j) (law p) := integrable_finite_local (Q j) p (f j) (fun ω => by
    dsimp [f]; rw [domainBits_local])
  have hfn (j : ℕ) : 0 ≤ᵐ[law p] f j := Eventually.of_forall (fun ω => by
    dsimp [f,finiteSmallPairKernel]
    split_ifs
    · exact finitePairKernel_nonneg G J hJ _ x y
    · exact le_rfl)
  have heq : ∀ᵐ ω ∂law p,
      liminf (fun j => ENNReal.ofReal (f j ω)) atTop =
        smallPairKernel G (fun a b => ENNReal.ofReal (J a b)) L x y ω := by
    filter_upwards [hx,hy] with ω hωx hωy
    obtain ⟨jx,hjx⟩ := subset_vertexExhaustion (incidentSupport G hloc hωx.toFinset)
    obtain ⟨jy,hjy⟩ := subset_vertexExhaustion (incidentSupport G hloc hωy.toFinset)
    have he : (fun j => ENNReal.ofReal (f j ω)) =ᶠ[atTop]
        (fun _ => smallPairKernel G (fun a b => ENNReal.ofReal (J a b)) L x y ω) := by
      filter_upwards [eventually_ge_atTop (max jx jy)] with j hj
      exact smallPairKernel_eq_finite G hloc J hJ L ω x y hωx hωy (Q j)
        (hjx.trans (vertexExhaustion_mono (le_max_left jx jy |>.trans hj)))
        (hjy.trans (vertexExhaustion_mono (le_max_right jx jy |>.trans hj)))
    exact (tendsto_const_nhds.congr' he.symm).liminf_eq
  calc
    _ = ∫⁻ ω, liminf (fun j => ENNReal.ofReal (f j ω)) atTop ∂law p := lintegral_congr_ae (heq.mono (fun _ h => h.symm))
    _ ≤ liminf (fun j => ∫⁻ ω, ENNReal.ofReal (f j ω) ∂law p) atTop :=
      lintegral_liminf_le' (fun j => (hfi j).aemeasurable.ennreal_ofReal)
    _ ≤ ENNReal.ofReal B := liminf_le_of_frequently_le' (Eventually.frequently (Eventually.of_forall (fun j => by
      rw [←ofReal_integral_eq_lintegral_ofReal (hfi j) (hfn j)]
      apply ENNReal.ofReal_le_ofReal
      rw [show (∫ ω, f j ω ∂law p) = bernoulliPolynomial (Q j) (finiteSmallPairKernel G J L x y) p from
        integral_domainBits (Q j) p (finiteSmallPairKernel G J L x y)]
      exact hB (Q j))))

 

theorem smallPairKernel_moment_bound [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G)
    (J : V → V → ℝ) (hJ : ∀ a b, 0 ≤ J a b)
    (x y : V) (p : unitInterval) (L M α : ℝ) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hx : ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (hy : ∀ᵐ ω ∂law p, (cluster G ω y).Finite)
    (hI : Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law p))
    (hs : ∀ a, Summable (fun b => J a b*twoPoint G p y b))
    (hb : ∀ a, (∑' b, J a b*twoPoint G p y b) ≤ M) :
    (∫⁻ ω, smallPairKernel G (fun a b => ENNReal.ofReal (J a b)) L x y ω ∂law p) ≤
      ENNReal.ofReal (M*(L^(1-α)*(∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law p))) :=
  smallPairKernel_lintegral_le_of_finite G hloc J hJ L x y p hx hy _ (fun Q =>
    finiteSmallPairKernel_moment_bound G Q J hJ x y p L M α hL hM hα0 hα1 hx hI hs hb)

end SmallKernelFatou
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal ComplexOrder
section SmallTwoPointKernel
attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance] spectralRealOperatorScalarTower spectralRealOperatorSMulCommClass
local instance : NonUnitalContinuousFunctionalCalculus ℝ
    (Hilbert V →L[ℂ] Hilbert V) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus (A := Hilbert V →L[ℂ] Hilbert V)
local instance : ContinuousFunctionalCalculus ℝ
    (Hilbert V →L[ℂ] Hilbert V) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus (A := Hilbert V →L[ℂ] Hilbert V)

theorem matrixCoeff_positive_trace_norm {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : KernelInvariant Γ A) (hpos : 0 ≤ A) (x y : V) :
    ‖matrixCoeff A x y‖ ≤ c*(rootTrace root weight A).re := by
  have hd (z : V) : (matrixCoeff A z z).re ≤ c*(rootTrace root weight A).re := by
    have h := (Complex.le_def.mp (rootTrace_diag_le root weight hcov hw c hc hmin A hA hpos z)).1
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using h
  have hn (z : V) : 0 ≤ (matrixCoeff A z z).re := (Complex.nonneg_iff.mp (matrixCoeff_nonneg A hpos z)).1
  have hC : 0 ≤ c*(rootTrace root weight A).re := mul_nonneg hc
    (Complex.nonneg_iff.mp (rootTrace_nonneg root weight hw A hpos)).1
  have hs := matrixCoeff_positive_product_norm_sq_le A 1 hpos x y
  simp only [one_mul,star_one,mul_one] at hs
  have hp := mul_le_mul (hd x) (hd y) (hn y) hC
  nlinarith [norm_nonneg (matrixCoeff A x y)]

theorem smallPairKernel_twoPoint_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (x y : V) (p : unitInterval) (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (L α : ℝ) (hL : 0 ≤ L) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hx : ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (hy : ∀ᵐ ω ∂law p, (cluster G ω y).Finite)
    (hI : Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law p)) :
    (∫⁻ ω, smallPairKernel G (ennMatrixCoeff (T^2)) L x y ω ∂law p) ≤
      ENNReal.ofReal ((c*(rootTrace root weight (T^3)).re)*
        (L^(1-α)*(∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law p))) := by
  have hp := hT.positiveRealMatrix G p T
  have hpos : 0 ≤ T := ContinuousLinearMap.nonneg_iff_isPositive.mpr (hT.isPositive G p T)
  have hp3 := CStarAlgebra.pow_nonneg T 3 hpos
  have hTI : KernelInvariant Γ T := fun a ha => hT.invariant G p T a (hΓ ha)
  have hM : 0 ≤ c*(rootTrace root weight (T^3)).re := mul_nonneg hc
    (Complex.nonneg_iff.mp (rootTrace_nonneg root weight hw _ hp3)).1
  have he (b : V) : (matrixCoeff T b y).re = twoPoint G p y b := by
    change (T (lp.single 2 y (1:ℂ)) b).re = _
    rw [hT b y,Complex.ofReal_re,twoPoint_symm G p b y]
  have hs (a : V) : HasSum (fun b => (matrixCoeff (T^2) a b).re * twoPoint G p y b)
      (matrixCoeff (T^3) a y).re := by
    simpa only [he,←pow_succ] using (hp.pow 2).mul_hasSum T a y
  apply smallPairKernel_moment_bound G hloc (fun a b => (matrixCoeff (T^2) a b).re)
    (fun a b => ((hp.pow 2) a b).2) x y p L _ α hL hM hα0 hα1 hx hy hI
    (fun a => (hs a).summable)
  intro a
  rw [(hs a).tsum_eq]
  exact (Complex.re_le_norm _).trans (matrixCoeff_positive_trace_norm root weight Γ hcov hw c hc hmin _ (hTI.pow 3) hp3 a y)

end SmallTwoPointKernel
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ContactSmallReroot
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_smallPairKernel [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (J : V → V → ℝ≥0∞) (L : ℝ) (x y : V) :
    Measurable (smallPairKernel G J L x y) := by
  exact (measurable_clusterPairKernel G J x y).ite
    ((measurableSet_lt ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (measurable_cluster_ncard G hloc x))
      measurable_const).inter (measurableSet_conn G x y).compl) measurable_const

theorem smallPairKernel_cluster_constant (G : BondGraph V E) (J : V → V → ℝ≥0∞)
    (L : ℝ) (ω : Set E) (x y a b : V) (hxa : Conn G ω x a) (hyb : Conn G ω y b) :
    smallPairKernel G J L x y ω = smallPairKernel G J L a b ω := by
  have hc : Conn G ω x y ↔ Conn G ω a b := by
    constructor
    · intro h; exact conn_trans G ω (conn_symm G ω hxa) (conn_trans G ω h hyb)
    · intro h; exact conn_trans G ω hxa (conn_trans G ω h (conn_symm G ω hyb))
  simp only [smallPairKernel,cluster_eq_of_conn G ω hxa,hc,
    clusterPairKernel_cluster_constant G ω J x y a b hxa hyb]

theorem smallPairKernel_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (J : V → V → ℝ≥0∞) (hJ : ∀ x y, J (a x) (a y) = J x y)
    (L : ℝ) (ω : Set E) (x y : V) :
    smallPairKernel G J L x y (b ⁻¹' ω) = smallPairKernel G J L (a x) (a y) ω := by
  simp only [smallPairKernel,cluster_ncard_covariant G hab,conn_aut_iff G hab,
    clusterPairKernel_aut G hab J hJ]

theorem smallPairKernel_distinct (G : BondGraph V E) (J : V → V → ℝ≥0∞)
    (L : ℝ) (ω : Set E) (x y : V) :
    (if ¬Conn G ω x y then smallPairKernel G J L x y ω else 0) = smallPairKernel G J L x y ω := by
  by_cases h : Conn G ω x y
  · simp only [smallPairKernel,h,not_true_eq_false,and_false,ite_false]
  · exact ite_eq_left h

 
theorem contact_smallPairKernel_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1) (p : unitInterval)
    (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (J : V → V → ℝ≥0∞) (hJ : ∀ a ∈ Γ, ∀ x y, J (a x) (a y) = J x y)
    (L : ℝ) (d : ℕ) (hd : ∀ x, degree G x ≤ d) (B : ℝ)
    (hb : ∀ x y, (∫⁻ ω, smallPairKernel G J L x y ω ∂law p) ≤ ENNReal.ofReal B) :
    clusterPairFunctional G p root weight (fun ω x y =>
      clusterPairKernel G ω (indexedEdgeKernel G) x y * smallPairKernel G J L x y ω) ≤
      ENNReal.ofReal ((d:ℝ)*B) := by
  have hj : ∀ a ∈ Γ, ∀ x y, indexedEdgeKernel G (a x) (a y) = indexedEdgeKernel G x y := by
    intro a ha x y
    obtain ⟨b,hab⟩ := hΓ ha
    exact indexedEdgeKernel_aut G hab x y
  rw [clusterPairFunctional_reroot G hconn hloc root weight Γ hΓ htr hw p hfin
    (indexedEdgeKernel G) hj (fun ω x y => smallPairKernel G J L x y ω)
    (measurable_smallPairKernel G hloc J L)
    (fun ω x y a b hxa hyb => smallPairKernel_cluster_constant G J L ω x y a b hxa hyb)
    (fun a ha b hab ω x y => smallPairKernel_aut G hab J (hJ a ha) L ω x y)]
  simp_rw [smallPairKernel_distinct]
  have hr (x : V) : (∫⁻ ω, ∑' y, indexedEdgeKernel G x y * smallPairKernel G J L x y ω ∂law p) ≤
      ENNReal.ofReal ((d:ℝ)*B) := by
    have hm (y : V) : Measurable (fun ω => indexedEdgeKernel G x y * smallPairKernel G J L x y ω) :=
      (measurable_const : Measurable (fun _ : Set E => indexedEdgeKernel G x y)).mul (measurable_smallPairKernel G hloc J L x y)
    rw [lintegral_tsum (fun y => (hm y).aemeasurable)]
    simp_rw [lintegral_const_mul _ (measurable_smallPairKernel G hloc J L x _)]
    calc
      _ ≤ ∑' y, indexedEdgeKernel G x y * ENNReal.ofReal B := ENNReal.tsum_le_tsum (fun y => mul_le_mul_right (hb x y) _)
      _ = (degree G x:ℝ≥0∞)*ENNReal.ofReal B := by rw [ENNReal.tsum_mul_right,indexedEdgeKernel_row G hloc x]
      _ ≤ (d:ℝ≥0∞)*ENNReal.ofReal B := mul_le_mul_left (by exact_mod_cast hd x) _
      _ = _ := by rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_natCast]
  calc
    _ ≤ ∑ i, ENNReal.ofReal (weight i)*ENNReal.ofReal ((d:ℝ)*B) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_right (hr (root i)) _)
    _ = _ := by rw [←Finset.sum_mul,←ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i),hw1,ENNReal.ofReal_one,one_mul]

end ContactSmallReroot
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section PairMeasure
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def clusterPairMeasure [MeasurableSpace V]
    {ι : Type*} [MeasurableSpace ι] (G : BondGraph V E) (p : unitInterval)
    (root : ι → V) (weight : ι → ℝ) : Measure (Set E × (ι × V)) :=
  ((law p).prod Measure.count).withDensity (fun t => ENNReal.ofReal (weight t.2.1) *
    clusterPairMass G t.1 (fun _ _ => 1) (root t.2.1) t.2.2)

theorem clusterPairFunctional_eq_lintegral [Countable V] [Countable E]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    (root : ι → V) (weight : ι → ℝ)
    (F : Set E → V → V → ℝ≥0∞) (hF : ∀ x y, Measurable (fun ω => F ω x y)) :
    clusterPairFunctional G p root weight F =
      ∫⁻ t, F t.1 (root t.2.1) t.2.2 ∂clusterPairMeasure G p root weight := by
  let d : Set E × (ι × V) → ℝ≥0∞ := fun t => ENNReal.ofReal (weight t.2.1) *
    clusterPairMass G t.1 (fun _ _ => 1) (root t.2.1) t.2.2
  let f : Set E × (ι × V) → ℝ≥0∞ := fun t => F t.1 (root t.2.1) t.2.2
  have hd : Measurable d := by
    apply measurable_from_prod_countable_left
    intro q
    exact (measurable_const : Measurable (fun _ : Set E => ENNReal.ofReal (weight q.1))).mul
      (measurable_clusterPairMass G hloc (fun _ _ _ => 1) (fun _ _ => measurable_const) (root q.1) q.2)
  have hf : Measurable f := measurable_from_prod_countable_left (fun q => hF (root q.1) q.2)
  change _ = ∫⁻ t, f t ∂((law p).prod Measure.count).withDensity d
  rw [lintegral_withDensity_eq_lintegral_mul _ hd hf,lintegral_prod _ ((hd.mul hf).aemeasurable)]
  have he (ω : Set E) (i : ι) (y : V) :
      (d*f) (ω,(i,y)) = ENNReal.ofReal (weight i)*clusterPairMass G ω (F ω) (root i) y := by
    dsimp [d,f,clusterPairMass]
    (split_ifs <;> simp only [mul_one,mul_zero,zero_mul]); ring
  simp_rw [lintegral_count,ENNReal.tsum_prod',he,tsum_fintype]
  have hm (i : ι) : Measurable (fun ω => ∑' y, ENNReal.ofReal (weight i)*clusterPairMass G ω (F ω) (root i) y) :=
    Measurable.tsum (fun y => measurable_const.mul (measurable_clusterPairMass G hloc F hF (root i) y))
  rw [lintegral_finsetSum _ (fun i _ => hm i)]
  simp_rw [ENNReal.tsum_mul_left]
  rw [clusterPairFunctional]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_const_mul _ (Measurable.tsum (fun y => measurable_clusterPairMass G hloc F hF (root i) y))]
  congr 1
  apply lintegral_congr
  intro ω
  exact clusterPairDensity_eq_tsum G ω (F ω) (root i)

 

theorem clusterPairFunctional_cauchy_schwarz [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (F H : Set E → V → V → ℝ≥0∞)
    (hF : ∀ x y, Measurable (fun ω => F ω x y))
    (hH : ∀ x y, Measurable (fun ω => H ω x y)) :
    clusterPairFunctional G p root weight (fun ω x y => F ω x y*H ω x y) ≤
      (clusterPairFunctional G p root weight (fun ω x y => (F ω x y)^2))^((1:ℝ)/2) *
      (clusterPairFunctional G p root weight (fun ω x y => (H ω x y)^2))^((1:ℝ)/2) := by
  let : MeasurableSpace V := ⊤
  let : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  let : MeasurableSpace ι := ⊤
  let : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  rw [clusterPairFunctional_eq_lintegral G hloc p root weight (fun ω x y => F ω x y*H ω x y) (fun x y => (hF x y).mul (hH x y)),
    clusterPairFunctional_eq_lintegral G hloc p root weight (fun ω x y => (F ω x y)^2) (fun x y => (hF x y).pow_const 2),
    clusterPairFunctional_eq_lintegral G hloc p root weight (fun ω x y => (H ω x y)^2) (fun x y => (hH x y).pow_const 2)]
  have hf : Measurable (fun t : Set E × (ι × V) => F t.1 (root t.2.1) t.2.2) :=
    measurable_from_prod_countable_left (fun q => hF (root q.1) q.2)
  have hh : Measurable (fun t : Set E × (ι × V) => H t.1 (root t.2.1) t.2.2) :=
    measurable_from_prod_countable_left (fun q => hH (root q.1) q.2)
  simpa only [Pi.mul_apply,ENNReal.rpow_two] using
    ENNReal.lintegral_mul_le_Lp_mul_Lq (clusterPairMeasure G p root weight) Real.HolderConjugate.two_two hf.aemeasurable hh.aemeasurable

end PairMeasure
end Percolation

end OAI
