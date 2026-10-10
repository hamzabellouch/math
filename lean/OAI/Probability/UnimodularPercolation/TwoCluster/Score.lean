import Mathlib
import OAI.Probability.UnimodularPercolation.Exploration.TailBounds

namespace OAI

/-! Decision-tree scores and influences for two-cluster events. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
namespace ProbeTree

 
theorem score_mean_zero (p h : ℝ) (t : ProbeTree) :
    ∑ l, weight p h t l * score p t l = 0 := by
  induction t with
  | done b => simp [weight,score]
  | edge t₀ t₁ ih₀ ih₁ =>
    change (∑ l : t₀.Leaf ⊕ t₁.Leaf, _) = 0
    simp only [Fintype.sum_sum_type,weight,score]
    have h₀ (l : t₀.Leaf) : (1-p)*weight p h t₀ l*(score p t₀ l-p) =
        (1-p)*(weight p h t₀ l*score p t₀ l)-p*(1-p)*weight p h t₀ l := by ring
    have h₁ (l : t₁.Leaf) : p*weight p h t₁ l*(score p t₁ l+(1-p)) =
        p*(weight p h t₁ l*score p t₁ l)+p*(1-p)*weight p h t₁ l := by ring
    simp_rw [h₀,h₁]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,
      sum_weight,ih₀,ih₁]
    ring
  | mark t₀ t₁ ih₀ ih₁ =>
    change (∑ l : t₀.Leaf ⊕ t₁.Leaf, _) = 0
    simp only [Fintype.sum_sum_type,weight,score,mul_assoc,←Finset.mul_sum,ih₀,ih₁,mul_zero,add_zero]

 

theorem score_second_moment (p h : ℝ) (t : ProbeTree) :
    ∑ l, weight p h t l * score p t l ^ 2 =
      p*(1-p) * ∑ l, weight p h t l * (queries t l : ℝ) := by
  induction t with
  | done b => simp [weight,score,queries]
  | edge t₀ t₁ ih₀ ih₁ =>
    change (∑ l : t₀.Leaf ⊕ t₁.Leaf, _) = p*(1-p)*(∑ l : t₀.Leaf ⊕ t₁.Leaf, _)
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
    have h₀ : ∀ l : t₀.Leaf, weight p h (.edge t₀ t₁) (.inl l) * score p (.edge t₀ t₁) (.inl l)^2 =
        (1-p)*(weight p h t₀ l*score p t₀ l^2) -
        (2*p*(1-p))*(weight p h t₀ l*score p t₀ l) + p^2*(1-p)*weight p h t₀ l := by
      intro l; simp only [weight,score]; ring
    have h₁ : ∀ l : t₁.Leaf, weight p h (.edge t₀ t₁) (.inr l) * score p (.edge t₀ t₁) (.inr l)^2 =
        p*(weight p h t₁ l*score p t₁ l^2) +
        (2*p*(1-p))*(weight p h t₁ l*score p t₁ l) + p*(1-p)^2*weight p h t₁ l := by
      intro l; simp only [weight,score]; ring
    simp_rw [h₀,h₁]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,
      score_mean_zero,sum_weight,mul_zero,mul_one,sub_zero,add_zero,ih₀,ih₁,
      weight,queries,Nat.cast_add,Nat.cast_one]
    simp only [mul_add,mul_one,Finset.sum_add_distrib,mul_assoc,←Finset.mul_sum,sum_weight]
    ring
  | mark t₀ t₁ ih₀ ih₁ =>
    change (∑ l : t₀.Leaf ⊕ t₁.Leaf, _) = p*(1-p)*(∑ l : t₀.Leaf ⊕ t₁.Leaf, _)
    simp only [Fintype.sum_sum_type,weight,score,queries,mul_assoc,←Finset.mul_sum,ih₀,ih₁]
    ring

 
theorem score_abs_mean_le_sqrt (p h : unitInterval) (t : ProbeTree)
    (N : ℝ) (hN0 : 0 ≤ N)
    (hN : ∑ l, weight p h t l*(queries t l:ℝ) ≤ N) :
    ∑ l, weight p h t l * |score p t l| ≤ Real.sqrt N := by
  have hw := weight_nonneg p h t
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun l => Real.sqrt (weight p h t l))
    (fun l => Real.sqrt (weight p h t l)*|score p t l|)
  have he : (∑ l, weight p h t l * |score p t l|)^2 ≤
      ∑ l, weight p h t l * score p t l ^2 := by
    simpa only [mul_pow,Real.sq_sqrt (hw _),sq_abs,
      ←mul_assoc,Real.mul_self_sqrt (hw _),sum_weight,one_mul] using hc
  have hp : 0 ≤ (p:ℝ)*(1-p) := mul_nonneg p.2.1 (sub_nonneg.mpr p.2.2)
  have hp1 : (p:ℝ)*(1-p) ≤ 1 := by nlinarith [p.2.1,p.2.2]
  rw [score_second_moment] at he
  have hnon : 0 ≤ ∑ l, weight p h t l*|score p t l| :=
    Finset.sum_nonneg fun l _ => mul_nonneg (hw l) (abs_nonneg _)
  apply (Real.le_sqrt hnon hN0).mpr
  exact he.trans ((mul_le_mul_of_nonneg_left hN hp).trans (by nlinarith [hN0]))

end ProbeTree
namespace EdgeQueryTree
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem capped_score_abs_mean_le (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    (p : unitInterval) (N : ℕ) (hN : ∀ ω ⊆ Q, t.queryCount ω ≤ N) :
    bernoulliPolynomial Q (fun ω => |t.score p ω|) p ≤ Real.sqrt (N:ℝ) := by
  have hq : ∑ l, ProbeTree.weight p 0 t.forget l*(ProbeTree.queries t.forget l:ℝ) ≤ N := by
    rw [←t.leaf_expectation ht p (fun l => (ProbeTree.queries t.forget l:ℝ))]
    calc
      _ ≤ bernoulliPolynomial Q (fun _ => (N:ℝ)) p := by
        apply bernoulliPolynomial_mono _ _ _ p p.2
        intro ω hω
        exact_mod_cast hN ω hω
      _ = N := bernoulliPolynomial_const Q (N:ℝ) p
  change bernoulliPolynomial Q (fun ω => |ProbeTree.score p t.forget (t.leaf ω)|) p ≤ _
  rw [t.leaf_expectation ht p (fun l => |ProbeTree.score p t.forget l|)]
  exact ProbeTree.score_abs_mean_le_sqrt p 0 t.forget N (Nat.cast_nonneg N) hq

end EdgeQueryTree

theorem incidenceSearch_abs_mean_le (G : BondGraph V E) (N : ℕ) (Q : Finset E)
    (R : Finset V) (p : unitInterval) :
    bernoulliPolynomial Q (fun ω => |(incidenceSearch G N Q R).score p ω|) p ≤
      Real.sqrt (N:ℝ) := by
  classical
  exact EdgeQueryTree.capped_score_abs_mean_le _ (incidenceSearch_valid ..) p N
    (fun ω _ => incidenceSearch_cap G N Q R ω)

end Percolation

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteClusterScore (G : BondGraph V E) (Q : Finset E)
    (x : V) (p : ℝ) (ω : Finset E) : ℝ :=
  ∑ e ∈ incidentBonds G Q (finiteRootComponent G ω x), ((if e ∈ ω then 1 else 0)-p)

 
noncomputable def cappedDensity (n s : ℕ) : ℝ := min (n:ℝ) s / s

theorem cappedDensity_nonneg (n s : ℕ) : 0 ≤ cappedDensity n s := by
  unfold cappedDensity
  positivity

theorem cappedDensity_le_one (n s : ℕ) : cappedDensity n s ≤ 1 := by
  unfold cappedDensity
  by_cases hs : s = 0
  · simp [hs]
  · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hs))).mpr (min_le_right ..)

private theorem exists_four_scale (n s K : ℕ) (hs : n < s) (hK : s ≤ n*4^K) :
    ∃ j < K, n*4^j < s ∧ s ≤ n*4^(j+1) := by
  induction K with
  | zero => simp only [pow_zero,mul_one] at hK; omega
  | succ K ih =>
    by_cases h : s ≤ n*4^K
    · obtain ⟨j,hj,hj₁,hj₂⟩ := ih h
      exact ⟨j,by omega,hj₁,hj₂⟩
    · exact ⟨K,by omega,by omega,hK⟩

private theorem nat_le_four_pow (k : ℕ) : k ≤ 4^k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; have := Nat.one_le_pow k 4 (by omega); omega

private theorem cappedDensity_le_four_scale (n s j : ℕ) (hn : 0 < n)
    (hs : n*4^j < s) : cappedDensity n s ≤ (1/4:ℝ)^j := by
  have hpow : 1 ≤ 4^j := Nat.one_le_pow j 4 (by omega)
  have hns : n ≤ s := le_trans (by nlinarith : n ≤ n*4^j) hs.le
  have hs0 : 0 < (s:ℝ) := by exact_mod_cast (lt_of_lt_of_le hn hns)
  have hden : 0 < (n:ℝ)*4^j := mul_pos (Nat.cast_pos.mpr hn) (pow_pos (by norm_num) _)
  unfold cappedDensity
  rw [min_eq_left (by exact_mod_cast hns)]
  calc
    (n:ℝ)/s ≤ n/(n*4^j) := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hden (by exact_mod_cast hs.le)
    _ = (1/4:ℝ)^j := by rw [div_pow,one_pow]; field_simp

 

theorem cappedDensity_score_le_stopped (G : BondGraph V E) (Q : Finset E)
    (x : V) (p : ℝ) (d n K : ℕ) (hn : 0 < n)
    (hdeg : ∀ v, (Q.filter fun e => v ∈ G e).card ≤ d)
    (ω : Finset E) (hω : ω ⊆ Q)
    (hK : (finiteRootComponent G ω x).card ≤ n*4^K) :
    cappedDensity n (finiteRootComponent G ω x).card * |finiteClusterScore G Q x p ω| ≤
      |(incidenceSearch G (d*n) Q {x}).score p ω| +
        ∑ j ∈ Finset.range K, (1/4:ℝ)^j *
          |(incidenceSearch G (d*(n*4^(j+1))) Q {x}).score p ω| := by
  let s := (finiteRootComponent G ω x).card
  have hcomplete (N : ℕ) (hN : s ≤ N) :
      (incidenceSearch G (d*N) Q {x}).score p ω = finiteClusterScore G Q x p ω := by
    exact incidenceSearch_completed_score G (d*N) Q ω hω x p
      ((incidentBonds_card_le G Q _ d hdeg).trans (Nat.mul_le_mul_left d hN))
  have hterms : ∀ j, 0 ≤ (1/4:ℝ)^j *
      |(incidenceSearch G (d*(n*4^(j+1))) Q {x}).score p ω| := fun j => by positivity
  by_cases hs : s ≤ n
  · have he := hcomplete n hs
    rw [he]
    exact (mul_le_of_le_one_left (abs_nonneg _) (cappedDensity_le_one n s)).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hterms j))
  · obtain ⟨j,hj,hlo,hhi⟩ := exists_four_scale n s K (by omega) hK
    have he := hcomplete (n*4^(j+1)) hhi
    calc
      _ ≤ (1/4:ℝ)^j * |finiteClusterScore G Q x p ω| :=
        mul_le_mul_of_nonneg_right (cappedDensity_le_four_scale n s j hn hlo) (abs_nonneg _)
      _ = (1/4:ℝ)^j * |(incidenceSearch G (d*(n*4^(j+1))) Q {x}).score p ω| := by rw [he]
      _ ≤ ∑ j ∈ Finset.range K, (1/4:ℝ)^j *
          |(incidenceSearch G (d*(n*4^(j+1))) Q {x}).score p ω| :=
        Finset.single_le_sum (fun j _ => hterms j) (Finset.mem_range.mpr hj)
      _ ≤ _ := le_add_of_nonneg_left (abs_nonneg _)

private theorem sqrt_four_cap (d n j : ℕ) :
    Real.sqrt (d*(n*4^(j+1)):ℕ) = (2:ℝ)^(j+1)*Real.sqrt (d*n:ℕ) := by
  have he : (d*(n*4^(j+1)):ℕ) = (d*n)*4^(j+1) := by ring
  rw [he,Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg _)]
  rw [Nat.cast_pow,Nat.cast_ofNat,show (4:ℝ) = 2^2 by norm_num,←pow_mul,pow_mul',Real.sqrt_sq_eq_abs,
    abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)]
  ring

theorem cappedDensity_score_expectation_bound (G : BondGraph V E) (Q : Finset E)
    (x : V) (p : unitInterval) (d n : ℕ) (hn : 0 < n)
    (hdeg : ∀ v, (Q.filter fun e => v ∈ G e).card ≤ d) :
    bernoulliPolynomial Q (fun ω => cappedDensity n (finiteRootComponent G ω x).card *
      |finiteClusterScore G Q x p ω|) p ≤ 5*Real.sqrt (d*n:ℕ) := by
  let K := (insert x (searchVertices G Q)).card
  have hK (ω : Finset E) (hω : ω ⊆ Q) : (finiteRootComponent G ω x).card ≤ n*4^K := by
    have hs : (finiteRootComponent G ω x).card ≤ K :=
      Finset.card_le_card (finiteRootComponent_subset G Q _ x ω hω le_rfl)
    exact hs.trans ((nat_le_four_pow K).trans (by nlinarith [Nat.one_le_pow K 4 (by omega)]))
  have hp := bernoulliPolynomial_mono Q _ _ p p.2 (fun ω hω =>
    cappedDensity_score_le_stopped G Q x p d n K hn hdeg ω hω (hK ω hω))
  rw [bernoulliPolynomial_add,bernoulliPolynomial_sum] at hp
  simp_rw [bernoulliPolynomial_const_mul] at hp
  have hh := hp.trans (add_le_add (incidenceSearch_abs_mean_le G (d*n) Q {x} p)
    (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
      (incidenceSearch_abs_mean_le G (d*(n*4^(j+1))) Q {x} p) (by positivity)))
  simp_rw [sqrt_four_cap] at hh
  have he (j : ℕ) : (1/4:ℝ)^j*((2:ℝ)^(j+1)*Real.sqrt (d*n:ℕ)) =
      2*(1/2:ℝ)^j*Real.sqrt (d*n:ℕ) := by
    rw [pow_succ]
    calc
      _ = 2*((1/4:ℝ)^j*2^j)*Real.sqrt (d*n:ℕ) := by ring
      _ = _ := by rw [←mul_pow]; norm_num
  simp_rw [he] at hh
  rw [←Finset.sum_mul,←Finset.mul_sum] at hh
  have hg : ∑ j ∈ Finset.range K, (1/2:ℝ)^j ≤ 2 := by
    have hid : ∑ j ∈ Finset.range K, (1/2:ℝ)^j = 2-2*(1/2:ℝ)^K := by
      induction K with
      | zero => simp
      | succ K ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring
    rw [hid]
    linarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) K]
  exact hh.trans (by nlinarith [Real.sqrt_nonneg (d*n:ℕ)])

end Percolation

 

 

open MeasureTheory ProbabilityTheory
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem incident_cluster_insert_iff (G : BondGraph V E) (ω : Set E) (x : V) (e : E) :
    (∃ a, Conn G (insert e ω) x a ∧ a ∈ G e) ↔
      ∃ a, Conn G ω x a ∧ a ∈ G e := by
  obtain ⟨a,b,hab⟩ : ∃ a b, G e = s(a,b) := by
    obtain ⟨⟨a,b⟩,h⟩ := Quot.exists_rep (G e)
    exact ⟨a,b,h.symm⟩
  constructor
  · rintro ⟨z,hz,hze⟩
    rcases (conn_insert_iff G ω e a b x z hab).mp hz with hz | ⟨hxa,_⟩ | ⟨hxb,_⟩
    · exact ⟨z,hz,hze⟩
    · exact ⟨a,hxa,hab ▸ by simp⟩
    · exact ⟨b,hxb,hab ▸ by simp⟩
  · rintro ⟨z,hz,hze⟩
    exact ⟨z,conn_mono G (Set.subset_insert e ω) hz,hze⟩

theorem cluster_insert_eq_of_not_incident (G : BondGraph V E) (ω : Set E) (x : V) (e : E)
    (hn : ¬∃ a, Conn G ω x a ∧ a ∈ G e) :
    cluster G (insert e ω) x = cluster G ω x := by
  obtain ⟨a,b,hab⟩ : ∃ a b, G e = s(a,b) := by
    obtain ⟨⟨a,b⟩,h⟩ := Quot.exists_rep (G e)
    exact ⟨a,b,h.symm⟩
  ext z
  constructor
  · intro hz
    rcases (conn_insert_iff G ω e a b x z hab).mp hz with hz | ⟨hxa,_⟩ | ⟨hxb,_⟩
    · exact hz
    · exact (hn ⟨a,hxa,hab ▸ by simp⟩).elim
    · exact (hn ⟨b,hxb,hab ▸ by simp⟩).elim
  · exact conn_mono G (Set.subset_insert e ω)

theorem finite_incident_insert_iff (G : BondGraph V E) (Q ω : Finset E) (x : V) (e : E) :
    e ∈ incidentBonds G Q (finiteRootComponent G (insert e ω) x) ↔
      e ∈ incidentBonds G Q (finiteRootComponent G ω x) := by
  simp only [mem_incidentBonds]
  have hc (η : Finset E) (a : V) : a ∈ finiteRootComponent G η x ↔ Conn G (η:Set E) x a := by
    change a ∈ (finiteRootComponent G η x:Set V) ↔ _
    rw [coe_finiteRootComponent]
    rfl
  simp only [hc,Finset.coe_insert,incident_cluster_insert_iff]

theorem finiteRootComponent_insert_eq_of_not_incident (G : BondGraph V E)
    (Q ω : Finset E) (x : V) (e : E) (he : e ∈ Q)
    (hn : e ∉ incidentBonds G Q (finiteRootComponent G ω x)) :
    finiteRootComponent G (insert e ω) x = finiteRootComponent G ω x := by
  apply Finset.coe_injective
  rw [coe_finiteRootComponent,coe_finiteRootComponent,Finset.coe_insert]
  apply cluster_insert_eq_of_not_incident
  rintro ⟨a,ha,hae⟩
  apply hn
  apply (mem_incidentBonds G Q _ e).mpr
  refine ⟨he,a,?_,hae⟩
  change a ∈ (finiteRootComponent G ω x:Set V)
  rw [coe_finiteRootComponent]
  exact ha

theorem finiteRootComponent_card_pos (G : BondGraph V E) (ω : Finset E) (x : V) :
    0 < (finiteRootComponent G ω x).card := by
  apply Finset.card_pos.mpr
  refine ⟨x,?_⟩
  change x ∈ (finiteRootComponent G ω x:Set V)
  rw [coe_finiteRootComponent]
  exact mem_cluster_self G _ x

theorem cappedDensity_antitone (n : ℕ) {s t : ℕ} (hs : 0 < s) (hst : s ≤ t) :
    cappedDensity n t ≤ cappedDensity n s := by
  by_cases hn : s ≤ n
  · have he : cappedDensity n s = 1 := by
      unfold cappedDensity
      rw [min_eq_right (by exact_mod_cast hn),div_self (by exact_mod_cast Nat.ne_of_gt hs)]
    rw [he]
    exact cappedDensity_le_one n t
  · have hs' : (n:ℝ) ≤ s := by exact_mod_cast (le_of_lt (Nat.lt_of_not_ge hn))
    have ht' : (n:ℝ) ≤ t := hs'.trans (by exact_mod_cast hst)
    unfold cappedDensity
    rw [min_eq_left ht',min_eq_left hs']
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg n) (Nat.cast_pos.mpr hs) (by exact_mod_cast hst)

noncomputable def finiteDensity (G : BondGraph V E) (n : ℕ) (x : V) (ω : Finset E) : ℝ :=
  cappedDensity n (finiteRootComponent G ω x).card

noncomputable def finiteDensityInfluence (G : BondGraph V E) (n : ℕ) (x : V)
    (e : E) (ω : Finset E) : ℝ :=
  if e ∈ ω then 0 else finiteDensity G n x ω - finiteDensity G n x (insert e ω)

theorem finiteDensityInfluence_nonneg (G : BondGraph V E) (n : ℕ) (x : V)
    (e : E) (ω : Finset E) : 0 ≤ finiteDensityInfluence G n x e ω := by
  unfold finiteDensityInfluence
  split_ifs
  · rfl
  · apply sub_nonneg.mpr
    apply cappedDensity_antitone n (finiteRootComponent_card_pos G ω x)
    apply Finset.card_le_card
    intro y hy
    have hm (η : Finset E) : y ∈ finiteRootComponent G η x ↔ Conn G (η:Set E) x y := by
      change y ∈ (finiteRootComponent G η x:Set V) ↔ _
      rw [coe_finiteRootComponent]
      rfl
    rw [hm] at hy ⊢
    exact conn_mono G (by simp) hy

theorem finiteDensityInfluence_le_one (G : BondGraph V E) (n : ℕ) (x : V)
    (e : E) (ω : Finset E) : finiteDensityInfluence G n x e ω ≤ 1 := by
  unfold finiteDensityInfluence finiteDensity
  split_ifs
  · norm_num
  · exact (sub_le_self _ (cappedDensity_nonneg ..)).trans (cappedDensity_le_one ..)

 
theorem finiteDensity_score_one_bit (G : BondGraph V E) (Q : Finset E) (n : ℕ)
    (x : V) (p : ℝ) (e : E) (he : e ∈ Q) :
    bernoulliPolynomial Q (fun ω => if e ∈ incidentBonds G Q (finiteRootComponent G ω x)
      then ((if e ∈ ω then 1 else 0)-p)*finiteDensity G n x ω else 0) p =
      -p*bernoulliPolynomial Q (finiteDensityInfluence G n x e) p := by
  let f := finiteDensity G n x
  let I := fun ω : Finset E => e ∈ incidentBonds G Q (finiteRootComponent G ω x)
  let R := Q.erase e
  have heR : e ∉ R := Finset.notMem_erase e Q
  have hQ : insert e R = Q := Finset.insert_erase he
  rw [←hQ,bernoulliPolynomial_insert R e heR,bernoulliPolynomial_insert R e heR]
  rw [hQ]
  have hclosed (ω : Finset E) (hω : ω ⊆ R) : e ∉ ω := fun h => heR (hω h)
  have hc : bernoulliPolynomial R (fun ω => if I ω then ((if e ∈ ω then 1 else 0)-p)*f ω else 0) p =
      -p*bernoulliPolynomial R (fun ω => if I ω then f ω else 0) p := by
    rw [←bernoulliPolynomial_const_mul]
    apply bernoulliPolynomial_congr
    intro ω hω
    simp only [ite_eq_right (hclosed ω hω),zero_sub]
    split_ifs <;> ring
  have ho : bernoulliPolynomial R (fun ω => if I (insert e ω) then
      ((if e ∈ insert e ω then 1 else 0)-p)*f (insert e ω) else 0) p =
      (1-p)*bernoulliPolynomial R (fun ω => if I ω then f (insert e ω) else 0) p := by
    rw [←bernoulliPolynomial_const_mul]
    apply bernoulliPolynomial_congr
    intro ω _
    simp only [I,finite_incident_insert_iff,Finset.mem_insert_self,ite_true]
    split_ifs <;> ring
  have hi : bernoulliPolynomial R (finiteDensityInfluence G n x e) p =
      bernoulliPolynomial R (fun ω => if I ω then f ω else 0) p -
        bernoulliPolynomial R (fun ω => if I ω then f (insert e ω) else 0) p := by
    rw [←bernoulliPolynomial_sub]
    apply bernoulliPolynomial_congr
    intro ω hω
    unfold finiteDensityInfluence
    rw [ite_eq_right (hclosed ω hω)]
    by_cases hi : I ω
    · simp only [ite_eq_left hi,f]
    · have heq : f (insert e ω) = f ω := by
        unfold f finiteDensity
        rw [finiteRootComponent_insert_eq_of_not_incident G Q ω x e he hi]
      simp only [ite_eq_right hi,heq,sub_self,f]
  have hz : bernoulliPolynomial R (fun ω => finiteDensityInfluence G n x e (insert e ω)) p = 0 := by
    simp only [finiteDensityInfluence,Finset.mem_insert_self,ite_true,bernoulliPolynomial_zero]
  change _ = -p*((1-p)*bernoulliPolynomial R (finiteDensityInfluence G n x e) p+
    p*bernoulliPolynomial R (fun ω => finiteDensityInfluence G n x e (insert e ω)) p)
  rw [hc,ho,hi,hz]
  ring

 
theorem finiteDensity_score_identity (G : BondGraph V E) (Q : Finset E) (n : ℕ)
    (x : V) (p : ℝ) :
    bernoulliPolynomial Q (fun ω => finiteDensity G n x ω * finiteClusterScore G Q x p ω) p =
      -p * ∑ e ∈ Q, bernoulliPolynomial Q (finiteDensityInfluence G n x e) p := by
  have hf (ω : Finset E) : finiteDensity G n x ω * finiteClusterScore G Q x p ω =
      ∑ e ∈ Q, if e ∈ incidentBonds G Q (finiteRootComponent G ω x)
        then ((if e ∈ ω then 1 else 0)-p)*finiteDensity G n x ω else 0 := by
    unfold finiteClusterScore
    rw [Finset.mul_sum]
    symm
    rw [←Finset.sum_filter]
    have hs : Q.filter (fun e => e ∈ incidentBonds G Q (finiteRootComponent G ω x)) =
        incidentBonds G Q (finiteRootComponent G ω x) := by
      ext e
      simp only [Finset.mem_filter,mem_incidentBonds]
      tauto
    rw [hs]
    apply Finset.sum_congr rfl
    intro e _
    ring
  simp_rw [hf]
  rw [bernoulliPolynomial_sum,Finset.mul_sum]
  exact Finset.sum_congr rfl fun e he => finiteDensity_score_one_bit G Q n x p e he

 

theorem finiteDensityInfluence_sum_bound (G : BondGraph V E) (Q : Finset E)
    (x : V) (p : unitInterval) (d n : ℕ) (hn : 0 < n)
    (hdeg : ∀ v, (Q.filter fun e => v ∈ G e).card ≤ d) :
    (p:ℝ) * ∑ e ∈ Q, bernoulliPolynomial Q (finiteDensityInfluence G n x e) p ≤
      5*Real.sqrt (d*n:ℕ) := by
  have hid := finiteDensity_score_identity G Q n x p
  have hle := bernoulliPolynomial_mono Q
    (fun ω => -(finiteDensity G n x ω * finiteClusterScore G Q x p ω))
    (fun ω => cappedDensity n (finiteRootComponent G ω x).card * |finiteClusterScore G Q x p ω|)
    p p.2 (fun ω _ => by
      rw [←mul_neg]
      exact mul_le_mul_of_nonneg_left (neg_le_abs _) (cappedDensity_nonneg ..))
  have hneg : bernoulliPolynomial Q
      (fun ω => -(finiteDensity G n x ω * finiteClusterScore G Q x p ω)) p =
      -bernoulliPolynomial Q (fun ω => finiteDensity G n x ω * finiteClusterScore G Q x p ω) p := by
    simpa using bernoulliPolynomial_const_mul Q
      (fun ω => finiteDensity G n x ω * finiteClusterScore G Q x p ω) (-1) (p:ℝ)
  rw [hneg,hid] at hle
  have hb := cappedDensity_score_expectation_bound G Q x p d n hn hdeg
  linarith

end Percolation

end OAI
