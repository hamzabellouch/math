import Mathlib
import OAI.Combinatorics.MatchingCount.Probability.Variance

namespace OAI

namespace MatchingFPRAS.Transport

section

noncomputable def tierClamp (c : ℝ) (t : ℕ) (w : ℝ) : ℝ :=
  max (c^t)⁻¹ (min (c^t) w)

lemma tierClamp_pos {c : ℝ} (hc : 0 < c) (t : ℕ) (w : ℝ) : 0 < tierClamp c t w :=
  lt_of_lt_of_le (inv_pos.mpr (pow_pos hc t)) (le_max_left _ _)

lemma clamp_comparison {c lo hi lo' hi' w : ℝ} (hc : 0 ≤ c)
    (hlo : lo' ≤ c*lo) (hhi : hi' ≤ c*hi) (hw : w ≤ c*w) :
    max lo' (min hi' w) ≤ c*max lo (min hi w) := by
  rw [mul_max_of_nonneg _ _ hc,mul_min_of_nonneg _ _ hc]
  exact max_le_max hlo (min_le_min hhi hw)

lemma tierClamp_adjacent {c : ℝ} (hc : 1 ≤ c) (t : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    tierClamp c (t+1) w ≤ c*tierClamp c t w ∧
      tierClamp c t w ≤ c*tierClamp c (t+1) w := by
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have ht : 0 < c^t := pow_pos hc0 t
  have ht1 : 0 < c^(t+1) := pow_pos hc0 _
  have hpow : c^t ≤ c^(t+1) := pow_le_pow_right₀ hc (by omega)
  have hi : (c^(t+1))⁻¹ ≤ (c^t)⁻¹ := inv_anti₀ ht hpow
  have hwc : w ≤ c*w := by nlinarith
  constructor
  · apply clamp_comparison hc0.le _ _ hwc
    · exact hi.trans (by nlinarith [inv_pos.mpr ht])
    · rw [pow_succ]; nlinarith
  · apply clamp_comparison hc0.le _ _ hwc
    · have he : (c^t)⁻¹ = c*(c^(t+1))⁻¹ := by
        rw [pow_succ,mul_inv_rev]; field_simp
      exact he.le
    · exact hpow.trans (by nlinarith)

lemma ladder_base_pow_bound (N : ℕ) (hN : 2 ≤ N) :
    (1+((N:ℝ)^2)⁻¹)^N ≤ 2 := by
  have hn2 : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hn : (0:ℝ) < N := by positivity
  have hx : 0 ≤ ((N:ℝ)^2)⁻¹ := by positivity
  have hbase : 0 ≤ 1+((N:ℝ)^2)⁻¹ := by positivity
  have hb : 1+((N:ℝ)^2)⁻¹ ≤ Real.exp (((N:ℝ)^2)⁻¹) := by simpa [add_comm] using Real.add_one_le_exp (((N:ℝ)^2)⁻¹)
  have hp := pow_le_pow_left₀ hbase hb N
  have he : (Real.exp (((N:ℝ)^2)⁻¹))^N = Real.exp ((N:ℝ)⁻¹) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [he] at hp
  have hinv : (N:ℝ)⁻¹ ≤ 1/2 := (inv_le_comm₀ hn (by norm_num)).mpr (by nlinarith)
  have hexp : Real.exp (1/2:ℝ) < 2 := by
    have hs : (Real.exp (1/2:ℝ))^2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h := Real.exp_one_lt_three
    have hpos := Real.exp_pos (1/2:ℝ)
    nlinarith
  exact hp.trans ((Real.exp_le_exp.mpr hinv).trans hexp.le)

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V) (hloop : ∀ e, ¬(ends e).IsDiag)

include hloop

omit [DecidableEq E] in
theorem adjacent_gibbs (hN : 2 ≤ Fintype.card V) (w : E → ℝ) (hw : ∀ e, 0 < w e)
    (t : ℕ) (A : PM (fun e v => v ∈ ends e)) :
    let c : ℝ := 1+((Fintype.card V:ℝ)^2)⁻¹
    let πt := gibbs (fun e => tierClamp c t (w e)) A
    let πnext := gibbs (fun e => tierClamp c (t+1) (w e)) A
    πnext/2 ≤ πt ∧ πt ≤ 2*πnext := by
  let c : ℝ := 1+((Fintype.card V:ℝ)^2)⁻¹
  have hc : 1 ≤ c := by
    dsimp [c]
    have : 0 ≤ ((Fintype.card V:ℝ)^2)⁻¹ := by positivity
    linarith
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  let z := fun e => tierClamp c t (w e)
  let z' := fun e => tierClamp c (t+1) (w e)
  have hz : ∀ e, 0 < z e := fun e => tierClamp_pos hc0 t (w e)
  have hz' : ∀ e, 0 < z' e := fun e => tierClamp_pos hc0 (t+1) (w e)
  have hh := fun e => tierClamp_adjacent hc t (hw e).le
  have h1 := gibbs_compare ends hloop hz hz' c hc0.le (fun e => (hh e).2) (fun e => (hh e).1) A
  have h2 := gibbs_compare ends hloop hz' hz c hc0.le (fun e => (hh e).1) (fun e => (hh e).2) A
  have hb : c^(Fintype.card V) ≤ 2 := ladder_base_pow_bound _ hN
  have hp := gibbs_pos z hz A
  have hp' := gibbs_pos z' hz' A
  change gibbs z' A/2 ≤ gibbs z A ∧ gibbs z A ≤ 2*gibbs z' A
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hb) hp.le,
    mul_nonneg (sub_nonneg.mpr hb) hp'.le]

end

section

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

omit [Fintype E] in
lemma exchange_inter (M N S : Finset E) :
    exchange M N S ∩ exchange N M S = M ∩ N := by
  ext e
  simp only [Finset.mem_inter,mem_exchange]
  tauto

noncomputable def cycleMove (p : PM inc × PM inc) (S : Finset E) : PM inc × PM inc := by
  classical
  exact if h : S ∈ components (inc := inc) (p.1.val ∪ p.2.val) then
    (⟨exchange p.1.val p.2.val S, exchange_matching p.1.property p.2.property
        (component_exchange_compatible h)⟩,
     ⟨exchange p.2.val p.1.val S, exchange_matching p.2.property p.1.property
        (component_exchange_compatible h).symm⟩) else p

omit [DecidableEq V] [Fintype E] in
lemma cycleMove_val (p : PM inc × PM inc) (S : Finset E)
    (h : S ∈ components (inc := inc) (p.1.val ∪ p.2.val)) :
    (cycleMove p S).1.val = exchange p.1.val p.2.val S ∧
    (cycleMove p S).2.val = exchange p.2.val p.1.val S := by
  classical
  simp only [cycleMove,dite_eq_left h,Subtype.coe_mk,and_self]

omit [DecidableEq V] [Fintype E] in
lemma cycleMove_union (p : PM inc × PM inc) (S : Finset E) :
    (cycleMove p S).1.val ∪ (cycleMove p S).2.val = p.1.val ∪ p.2.val := by
  classical
  unfold cycleMove
  split_ifs with h
  · exact exchange_union _ _ _
  · rfl

omit [DecidableEq V] [Fintype E] in
lemma cycleMove_inter (p : PM inc × PM inc) (S : Finset E) :
    (cycleMove p S).1.val ∩ (cycleMove p S).2.val = p.1.val ∩ p.2.val := by
  classical
  unfold cycleMove
  split_ifs with h
  · exact exchange_inter _ _ _
  · rfl

omit [DecidableEq V] [Fintype E] in
lemma cycleMove_discrepancy (p : PM inc × PM inc) (S : Finset E) :
    discrepancyComponents (cycleMove p S).1 (cycleMove p S).2 = discrepancyComponents p.1 p.2 := by
  classical
  unfold discrepancyComponents
  rw [cycleMove_union,cycleMove_inter]

omit [DecidableEq V] [Fintype E] in
lemma cycleMove_involution (p : PM inc × PM inc) (S : Finset E) :
    cycleMove (cycleMove p S) S = p := by
  classical
  by_cases h : S ∈ components (inc := inc) (p.1.val ∪ p.2.val)
  · have h' : S ∈ components (inc := inc) ((cycleMove p S).1.val ∪ (cycleMove p S).2.val) := by
      rwa [cycleMove_union]
    apply Prod.ext <;> apply Subtype.ext
    · rw [(cycleMove_val _ _ h').1,(cycleMove_val _ _ h).1,(cycleMove_val _ _ h).2]
      exact exchange_involution _ _ _
    · rw [(cycleMove_val _ _ h').2,(cycleMove_val _ _ h).1,(cycleMove_val _ _ h).2]
      exact exchange_involution _ _ _
  · simp only [cycleMove,dite_eq_right h]

omit [DecidableEq V] [Fintype E] in
lemma cycleMove_eq_iff (p q : PM inc × PM inc) (S : Finset E) :
    cycleMove p S = q ↔ cycleMove q S = p := by
  constructor <;> intro h <;> rw [← h,cycleMove_involution]

omit [DecidableEq V] in
lemma cycleMove_gibbs (w : E → ℝ) (p : PM inc × PM inc) (S : Finset E) :
    gibbs w (cycleMove p S).1*gibbs w (cycleMove p S).2 = gibbs w p.1*gibbs w p.2 := by
  classical
  by_cases h : S ∈ components (inc := inc) (p.1.val ∪ p.2.val)
  · unfold gibbs matchingWeight
    rw [(cycleMove_val _ _ h).1,(cycleMove_val _ _ h).2,div_mul_div_comm,exchange_weight]
    rw [div_mul_div_comm]
  · simp only [cycleMove,dite_eq_right h]

noncomputable def cycleTerm (p q : PM inc × PM inc) (S : Finset E) : ℝ := by
  classical
  exact if S ∈ discrepancyComponents p.1 p.2 ∧ cycleMove p S = q then
    ((discrepancyComponents p.1 p.2).card : ℝ)⁻¹ else 0

noncomputable def cycleProposal (p q : PM inc × PM inc) : ℝ := by
  classical
  exact if (discrepancyComponents p.1 p.2).Nonempty then ∑ S, cycleTerm p q S
    else if p = q then 1 else 0

omit [DecidableEq V] [Fintype E] in
lemma cycleTerm_symmetric (p q : PM inc × PM inc) (S : Finset E) :
    cycleTerm p q S = cycleTerm q p S := by
  classical
  have he : (S ∈ discrepancyComponents p.1 p.2 ∧ cycleMove p S = q) ↔
      (S ∈ discrepancyComponents q.1 q.2 ∧ cycleMove q S = p) := by
    constructor
    · rintro ⟨h,rfl⟩
      exact ⟨by rwa [cycleMove_discrepancy],cycleMove_involution _ _⟩
    · rintro ⟨h,rfl⟩
      exact ⟨by rwa [cycleMove_discrepancy],cycleMove_involution _ _⟩
  unfold cycleTerm
  by_cases h : S ∈ discrepancyComponents p.1 p.2 ∧ cycleMove p S = q
  · rw [ite_eq_left h,ite_eq_left (he.mp h),← h.2,cycleMove_discrepancy]
  · rw [ite_eq_right h,ite_eq_right (mt he.mpr h)]

omit [DecidableEq V] [Fintype E] in
lemma cycleTerm_nonneg (p q : PM inc × PM inc) (S : Finset E) : 0 ≤ cycleTerm p q S := by
  classical
  unfold cycleTerm
  split_ifs <;> positivity

omit [DecidableEq V] in
lemma cycleTerm_sum (p : PM inc × PM inc) (S : Finset E) :
    (∑ q, cycleTerm p q S) = if S ∈ discrepancyComponents p.1 p.2 then
      ((discrepancyComponents p.1 p.2).card : ℝ)⁻¹ else 0 := by
  classical
  by_cases h : S ∈ discrepancyComponents p.1 p.2
  · simp only [cycleTerm,h,true_and]
    simp
  · simp [cycleTerm,h]

omit [DecidableEq V] [Fintype E] in
lemma cycleTerm_zero (p q : PM inc × PM inc) (h : ¬(discrepancyComponents p.1 p.2).Nonempty)
    (S : Finset E) : cycleTerm p q S = 0 := by
  classical
  have he := Finset.not_nonempty_iff_eq_empty.mp h
  simp [cycleTerm,he]

omit [DecidableEq V] in
lemma cycleProposal_nonneg (p q : PM inc × PM inc) : 0 ≤ cycleProposal p q := by
  classical
  unfold cycleProposal
  split_ifs
  · exact Finset.sum_nonneg (fun S _ => cycleTerm_nonneg p q S)
  · norm_num
  · norm_num

omit [DecidableEq V] in
lemma cycleProposal_row (p : PM inc × PM inc) : (∑ q, cycleProposal p q) = 1 := by
  classical
  by_cases h : (discrepancyComponents p.1 p.2).Nonempty
  · simp only [cycleProposal,ite_eq_left h]
    rw [Finset.sum_comm]
    simp_rw [cycleTerm_sum]
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast ne_of_gt (Finset.card_pos.mpr h))
  · simp [cycleProposal,h]

omit [DecidableEq V] in
lemma cycleProposal_symmetric (p q : PM inc × PM inc) : cycleProposal p q = cycleProposal q p := by
  classical
  by_cases hp : (discrepancyComponents p.1 p.2).Nonempty <;>
    by_cases hq : (discrepancyComponents q.1 q.2).Nonempty
  · simp only [cycleProposal,ite_eq_left hp,ite_eq_left hq,cycleTerm_symmetric p q]
  · have hpq : p ≠ q := by rintro rfl; exact hq hp
    simp only [cycleProposal,ite_eq_left hp,ite_eq_right hq,ite_eq_right (Ne.symm hpq)]
    apply Finset.sum_eq_zero; intro S _
    rw [cycleTerm_symmetric,cycleTerm_zero _ _ hq]
  · exact (by
      have hpq : q ≠ p := by rintro rfl; exact hp hq
      simp only [cycleProposal,ite_eq_right hp,ite_eq_left hq,ite_eq_right (Ne.symm hpq)]
      symm; apply Finset.sum_eq_zero; intro S _
      rw [cycleTerm_symmetric,cycleTerm_zero _ _ hp])
  · simp only [cycleProposal,ite_eq_right hp,ite_eq_right hq,eq_comm]

omit [DecidableEq V] in
lemma cycleProposal_gibbs (w : E → ℝ) (p q : PM inc × PM inc) :
    gibbs w p.1*gibbs w p.2*cycleProposal p q =
      gibbs w q.1*gibbs w q.2*cycleProposal q p := by
  classical
  rw [cycleProposal_symmetric q p]
  by_cases h : (discrepancyComponents p.1 p.2).Nonempty
  · simp only [cycleProposal,ite_eq_left h,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    unfold cycleTerm
    split_ifs with he
    · rw [← he.2,cycleMove_gibbs]
    · simp
  · by_cases he : p = q
    · subst q; rfl
    · simp [cycleProposal,h,he]

omit [DecidableEq V] in
lemma cycleProposal_expectation (p : PM inc × PM inc) (F : PM inc × PM inc → ℝ) :
    (∑ q, cycleProposal p q * F q) =
      if (discrepancyComponents p.1 p.2).Nonempty then
        (∑ S ∈ discrepancyComponents p.1 p.2, F (cycleMove p S)) /
          (discrepancyComponents p.1 p.2).card else F p := by
  classical
  by_cases h : (discrepancyComponents p.1 p.2).Nonempty
  · simp only [cycleProposal,ite_eq_left h,Finset.sum_mul]
    rw [Finset.sum_comm]
    have hs (S : Finset E) : (∑ q, cycleTerm p q S*F q) =
        if S ∈ discrepancyComponents p.1 p.2 then
          F (cycleMove p S) / (discrepancyComponents p.1 p.2).card else 0 := by
      by_cases hm : S ∈ discrepancyComponents p.1 p.2
      · simp only [cycleTerm,hm,true_and,ite_eq_left,ite_mul,zero_mul]
        simp [div_eq_mul_inv,mul_comm]
      · simp [cycleTerm,hm]
    simp_rw [hs]
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_div]
  · simp [cycleProposal,h]




omit [DecidableEq V] in
theorem cycleProposal_dirichlet (w : E → ℝ) (f g : Finset E → ℝ) :
    (∑ A : PM inc, ∑ B : PM inc, gibbs w A*gibbs w B *
      (∑ q : PM inc × PM inc, cycleProposal (A,B) q *
        ((f A.val+g B.val)-(f q.1.val+g q.2.val))^2)) / 6 =
      cycleDirichlet (inc := inc) w f g := by
  classical
  unfold cycleDirichlet
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl; intro A _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl; intro B _
  rw [mul_div_assoc]
  congr 1
  rw [cycleProposal_expectation]
  by_cases h : (discrepancyComponents A B).Nonempty
  · rw [ite_eq_left h,div_div]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro S hS
    have hc : S ∈ components (inc := inc) (A.val ∪ B.val) := (Finset.mem_filter.mp hS).1
    rw [(cycleMove_val (A,B) S hc).1,(cycleMove_val (A,B) S hc).2]
    dsimp only [cycleSquare]
    rw [mul_comm ((discrepancyComponents A B).card:ℝ)]
  · have he := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he]

end

section

open Finset

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L}

noncomputable local instance tierClampBagEdgeFintype : Fintype (BagEdge bags) :=
  Fintype.ofFinite _

namespace BagEdge

noncomputable def parallels (e : BagEdge bags) : Finset (BagEdge bags) := by
  classical
  exact Finset.univ.filter (fun f => f.val.val.1 = e.val.val.1)

omit [DecidableEq L] in
lemma parallels_card_le (hb : ∀ v, (bags v).card ≤ 2) (e : BagEdge bags) :
    (parallels e).card ≤ 2 := by
  classical
  obtain ⟨v,hv⟩ := e.exists_incident
  let colorMap : ↥(parallels e) → ↥(bags v) := fun f => ⟨f.val.color, by
    apply f.val.color_mem
    change v ∈ f.val.val.val.1
    rw [(Finset.mem_filter.mp f.property).2]
    exact hv⟩
  have hinj : Function.Injective colorMap := by
    intro f g h
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    apply Prod.ext
    · exact (Finset.mem_filter.mp f.property).2.trans (Finset.mem_filter.mp g.property).2.symm
    · exact congrArg Subtype.val h
  have hc : (parallels e).card ≤ (bags v).card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective colorMap hinj
  exact hc.trans (hb v)

end BagEdge

end

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V)

omit [DecidableEq V] [Fintype E] in
lemma ColorChange.symm {A B : PM (fun e v => v ∈ ends e)} (h : ColorChange ends A B) :
    ColorChange ends B A := by
  obtain ⟨e,f,R,hef,hA,hB⟩ := h
  exact ⟨f,e,R,hef.symm,hB,hA⟩

omit [DecidableEq V] [Fintype E] in
lemma ColorChange.edit {A B : PM (fun e v => v ∈ ends e)} (h : ColorChange ends A B) :
    ∃ e ∈ A.val, ∃ f, ends f = ends e ∧ B.val = insert f (A.val.erase e) := by
  classical
  obtain ⟨e,f,R,hef,hA,hB⟩ := h
  have he : e ∈ A.val := by rw [hA]; simp
  refine ⟨e,he,f,hef.symm,?_⟩
  by_cases h : e = f
  · subst f
    rw [Finset.insert_erase he]
    exact hB.trans hA.symm
  · obtain ⟨v,hv⟩ : ∃ v, v ∈ ends e := Sym2.inductionOn (ends e) (fun u v => ⟨u,by simp⟩)
    have hr : e ∉ R := by
      intro hr
      exact h (B.property.unique (Finset.mem_univ v) (by rw [hB]; simp [hr]) hv
        (by rw [hB]; simp) (hef ▸ hv))
    rw [hA,hB]
    ext a
    simp only [Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,Finset.mem_erase]
    by_cases ha : a = e
    · subst a; simp [hr,h]
    · tauto

lemma colorDestinations_card_bound
    (hpar : ∀ e, (Finset.univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (A : PM (fun e v => v ∈ ends e)) : (colorDestinations ends A).card ≤ 2*A.val.card := by
  classical
  let options (e : E) : Finset (Finset E) :=
    (Finset.univ.filter (fun f => ends f = ends e)).image (fun f => insert f (A.val.erase e))
  have hsub : (colorDestinations ends A).image Subtype.val ⊆ A.val.biUnion options := by
    intro B hB
    obtain ⟨C,hC,hCB⟩ := Finset.mem_image.mp hB
    rw [← hCB]
    obtain ⟨e,he,f,hf,hval⟩ := ColorChange.edit ends ((Finset.mem_filter.mp hC).2)
    apply Finset.mem_biUnion.mpr
    exact ⟨e,he,Finset.mem_image.mpr ⟨f,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩,hval.symm⟩⟩
  have hi : (colorDestinations ends A).card = ((colorDestinations ends A).image Subtype.val).card := by
    symm; exact Finset.card_image_of_injective _ Subtype.val_injective
  calc
    _ = _ := hi
    _ ≤ (A.val.biUnion options).card := Finset.card_le_card hsub
    _ ≤ ∑ e ∈ A.val, (options e).card := Finset.card_biUnion_le
    _ ≤ ∑ e ∈ A.val, 2 := Finset.sum_le_sum (fun e _ => (Finset.card_image_le).trans (hpar e))
    _ = _ := by simp [Nat.mul_comm]

end MatchingFPRAS.Transport

end OAI
