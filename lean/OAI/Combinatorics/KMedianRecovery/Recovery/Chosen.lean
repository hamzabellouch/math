import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.ThresholdTimesPower

namespace OAI

namespace MetricKMedianRecovery.ShortSelection

lemma product_event {I X : Type*} [Fintype I] [Fintype X] [DecidableEq I]
    (p : I → X → ℝ) (E : I → X → Prop) [∀ i, DecidablePred (E i)] :
    (∑ f : I → X, if ∀ i, E i (f i) then ∏ i, p i (f i) else 0) =
      ∏ i, ∑ x, if E i x then p i x else 0 := by
  classical
  have hh := Finset.sum_prod_piFinset (ι := I) (Finset.univ : Finset X)
    (fun i x => if E i x then p i x else 0)
  simpa only [Fintype.piFinset_univ, Fintype.prod_ite_zero] using hh

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma pair_probability (i j : I) (hij : i ≠ j) :
    (∑ c : I → Bool, if c i = false ∧ c j = true then (1/2:ℝ)^(Fintype.card I) else 0) =
      1/4 := by
  classical
  let E := fun k : I => fun b : Bool => (k=i → b=false) ∧ (k=j → b=true)
  have he (c : I → Bool) : (∀ k, E k (c k)) ↔ c i = false ∧ c j = true := by
    constructor
    · intro h; exact ⟨(h i).1 rfl,(h j).2 rfl⟩
    · rintro ⟨hi,hj⟩ k
      exact ⟨fun h => h ▸ hi,fun h => h ▸ hj⟩
  have hh := product_event (fun (_ : I) (_ : Bool) => (1/2:ℝ)) E
  simp only [Finset.prod_const,Finset.card_univ,he] at hh
  rw [hh]
  have hs (k : I) : (∑ b : Bool, if E k b then (1/2:ℝ) else 0) =
      if k ∈ ({i,j}:Finset I) then 1/2 else 1 := by
    by_cases hki : k=i
    · subst k; simp [E,hij]
    · by_cases hkj : k=j
      · subst k; simp [E,Ne.symm hij]
      · simp [E,hki,hkj]
  simp_rw [hs]
  rw [Finset.prod_ite,Finset.filter_mem_eq_inter,Finset.univ_inter]
  norm_num [hij]

noncomputable def chosen (Q : Finset I) (neighbor : I → I) (c : I → Bool) : Finset I :=
  Q.filter (fun i => c i = false ∧ c (neighbor i) = true)

lemma uniform_total : (∑ _c : I → Bool, (1/2:ℝ)^(Fintype.card I)) = 1 := by
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_bool,
    nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [← mul_pow]
  norm_num

lemma mean_chosen (Q : Finset I) (neighbor : I → I) (hn : ∀ i ∈ Q, i ≠ neighbor i) :
    (∑ c : I → Bool, (chosen Q neighbor c).card*(1/2:ℝ)^(Fintype.card I)) = Q.card/4 := by
  have hc (c : I → Bool) : ((chosen Q neighbor c).card:ℝ) =
      ∑ i ∈ Q, if c i = false ∧ c (neighbor i) = true then (1:ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simp [chosen]
  simp_rw [hc,Finset.sum_mul]
  rw [Finset.sum_comm]
  have hi (i : I) (hiQ : i ∈ Q) :
      (∑ c : I → Bool, (if c i = false ∧ c (neighbor i) = true then (1:ℝ) else 0)*
        (1/2:ℝ)^(Fintype.card I)) = 1/4 := by
    simpa only [ite_mul,one_mul,zero_mul] using pair_probability i (neighbor i) (hn i hiQ)
  rw [Finset.sum_congr rfl hi]
  simp [div_eq_mul_inv]

theorem exists_simultaneous (Q : Finset I) (neighbor : I → I)
    (hn : ∀ i ∈ Q, i ≠ neighbor i) :
    ∃ R : Finset I, R ⊆ Q ∧ (Q.card:ℝ)/4 ≤ R.card ∧ ∀ i ∈ R, neighbor i ∉ R := by
  classical
  obtain ⟨c,hc⟩ := Finset.exists_max_image Finset.univ
    (fun c : I → Bool => (chosen Q neighbor c).card) Finset.univ_nonempty
  have hmax := hc.2
  have hbound : (Q.card:ℝ)/4 ≤ (chosen Q neighbor c).card := by
    rw [← mean_chosen Q neighbor hn]
    calc
      _ ≤ ∑ _d : I → Bool, ((chosen Q neighbor c).card:ℝ)*(1/2:ℝ)^(Fintype.card I) :=
        Finset.sum_le_sum (fun d hd => mul_le_mul_of_nonneg_right
          (by exact_mod_cast hmax d hd) (by positivity))
      _ = _ := by rw [← Finset.mul_sum,uniform_total,mul_one]
  refine ⟨chosen Q neighbor c,Finset.filter_subset _ _,hbound,?_⟩
  intro i hi hni
  have hi' := (Finset.mem_filter.mp hi).2.2
  have hn' := (Finset.mem_filter.mp hni).2.1
  exact Bool.noConfusion (hi'.symm.trans hn')

end MetricKMedianRecovery.ShortSelection

namespace MetricKMedianRecovery.Anchoring
open MetricKMedianRecovery.LocalSearch
variable {V : Type*} [MetricSpace V] [DecidableEq V]

omit [MetricSpace V] in
lemma erase_nonempty_of_two (O : Finset V) (hO2 : 2 ≤ O.card) (i : V) :
    (O.erase i).Nonempty := by
  have hc : 0 < (O.erase i).card := by
    by_cases hi : i ∈ O
    · have he := Finset.card_erase_add_one hi; omega
    · simpa only [Finset.erase_eq_of_notMem hi] using (lt_of_lt_of_le (by omega : 0 < 2) hO2)
  exact Finset.card_pos.mp hc

noncomputable def neighbor (O : Finset V) (hO2 : 2 ≤ O.card) (i : V) : V :=
  nearest (O.erase i) (erase_nonempty_of_two O hO2 i) i
lemma neighbor_mem (O : Finset V) (hO2 : 2 ≤ O.card) (i : V) : neighbor O hO2 i ∈ O :=
  Finset.mem_of_mem_erase (nearest_mem _ _ _)
lemma neighbor_ne (O : Finset V) (hO2 : 2 ≤ O.card) (i : V) : neighbor O hO2 i ≠ i :=
  (Finset.mem_erase.mp (nearest_mem _ _ _)).1
lemma neighbor_dist (O : Finset V) (hO2 : 2 ≤ O.card) (i : V) :
    dist i (neighbor O hO2 i) = separation O i := nearest_distance _ _ _

omit [MetricSpace V] in
lemma remaining_nonempty (O R : Finset V) (hO : O.Nonempty) (nu : V → V)
    (hnu : ∀ i ∈ O, nu i ∈ O) (hret : ∀ i ∈ R, nu i ∉ R) : (O \ R).Nonempty := by
  obtain ⟨i,hi⟩ := hO
  by_cases hiR : i ∈ R
  · exact ⟨nu i,Finset.mem_sdiff.mpr ⟨hnu i hi,hret i hiR⟩⟩
  · exact ⟨i,Finset.mem_sdiff.mpr ⟨hi,hiR⟩⟩

lemma removal_routing_bound (D O R : Finset V) (hO : O.Nonempty) (hO2 : 2 ≤ O.card)
    (hRO : R ⊆ O) (hret : ∀ i ∈ R, neighbor O hO2 i ∉ R) :
    cost D (O \ R) ≤ cost D O+
      ∑ i ∈ R, ((cluster D (nearest O hO) i).card:ℝ)*separation O i := by
  let assign := nearest O hO
  let extra := fun p => if assign p ∈ R then separation O (assign p) else 0
  have hpoint (p : V) : connection (O \ R) p ≤ connection O p+extra p := by
    by_cases hi : assign p ∈ R
    · have hm : neighbor O hO2 (assign p) ∈ O \ R :=
        Finset.mem_sdiff.mpr ⟨neighbor_mem O hO2 _,hret _ hi⟩
      calc
        _ ≤ dist p (neighbor O hO2 (assign p)) := connection_le hm
        _ ≤ dist p (assign p)+dist (assign p) (neighbor O hO2 (assign p)) := dist_triangle _ _ _
        _ = _ := by simp only [assign,nearest_distance,neighbor_dist,extra,hi,ite_true]
    · calc
        _ ≤ dist p (assign p) := connection_le (Finset.mem_sdiff.mpr ⟨nearest_mem O hO p,hi⟩)
        _ = _ := by simp only [assign,nearest_distance,extra,hi,ite_false,add_zero]
  have he : (∑ p ∈ D, extra p) = ∑ i ∈ R, ((cluster D assign i).card:ℝ)*separation O i := by
    have hf := Finset.sum_fiberwise_of_maps_to
      (fun p (_ : p ∈ D) => nearest_mem O hO p) extra
    change (∑ i ∈ O, ∑ p ∈ cluster D assign i, extra p) = ∑ p ∈ D, extra p at hf
    rw [← hf]
    have hinner (i : V) : (∑ p ∈ cluster D assign i, extra p) =
        if i ∈ R then (cluster D assign i).card*separation O i else 0 := by
      have hx (p : V) (hp : p ∈ cluster D assign i) : extra p =
          if i ∈ R then separation O i else 0 := by
        simp only [extra,(Finset.mem_filter.mp hp).2]
      rw [Finset.sum_congr rfl hx]
      split_ifs <;> simp
    simp_rw [hinner]
    rw [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.inter_eq_right.mpr hRO]
  have hh := Finset.sum_le_sum (s := D) (fun p _ => hpoint p)
  rw [Finset.sum_add_distrib,he] at hh
  exact hh

variable [Fintype V]

theorem short_removal (D O : Finset V) (hO : O.Nonempty) (hO2 : 2 ≤ O.card) (b : ℝ) :
    ∃ R : Finset V,
      R ⊆ O ∧ (O \ R).Nonempty ∧
      ((O.filter (fun i => ((cluster D (nearest O hO) i).card:ℝ)*separation O i < b)).card:ℝ)/4 ≤
        R.card ∧
      cost D (O \ R) ≤ cost D O+b*R.card := by
  classical
  let Q := O.filter (fun i => ((cluster D (nearest O hO) i).card:ℝ)*separation O i < b)
  obtain ⟨R,hRQ,hcard,hret⟩ := ShortSelection.exists_simultaneous Q (neighbor O hO2)
    (fun i _ => Ne.symm (neighbor_ne O hO2 i))
  have hRO : R ⊆ O := hRQ.trans (Finset.filter_subset _ _)
  refine ⟨R,hRO,remaining_nonempty O R hO (neighbor O hO2) (fun i _ => neighbor_mem O hO2 i)
    hret,hcard,?_⟩
  have hh := removal_routing_bound D O R hO hO2 hRO hret
  have hs : (∑ i ∈ R, ((cluster D (nearest O hO) i).card:ℝ)*separation O i) ≤ b*R.card := by
    calc
      _ ≤ ∑ _i ∈ R, b := Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp (hRQ hi)).2.le)
      _ = _ := by simp [mul_comm]
  linarith

end MetricKMedianRecovery.Anchoring

end OAI
