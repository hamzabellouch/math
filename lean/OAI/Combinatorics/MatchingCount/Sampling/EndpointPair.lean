import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.ComponentOrder

namespace OAI

namespace MatchingFPRAS.Transport.CellDemands

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance : Fintype (BagEdge bags) := Fintype.ofFinite _

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

lemma componentDifference_cell_bound
    (p : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags)))
    (f : Finset (BagEdge bags) → ℝ) (i : ℕ) :
    (componentDifference (fun A => f A.val) p i)^2 ≤
      3 * (Fintype.card V : ℝ) * longCellCost (hbags := hbags) (hG := hG) p f + colorCost p.1 f := by
  classical
  change (f p.1.val - f (exchange p.1.val p.2.val
    (componentAt (inc := BagEdge.Incident) (p.1.val ∪ p.2.val) i)))^2 ≤ _
  unfold componentAt
  split_ifs with h
  · exact component_cell_bound p f (componentOrder (p.1.val ∪ p.2.val) ⟨i,h⟩).property
  · rw [exchange_empty, sub_self, zero_pow (by decide : 2≠0)]
    exact add_nonneg (mul_nonneg (by positivity) (longCellCost_nonneg p f)) (colorCost_nonneg p.1 f)

lemma sum_componentDifference_bound
    (p : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags)))
    (f : Finset (BagEdge bags) → ℝ) :
    (∑ i ∈ Finset.range (Fintype.card V), (componentDifference (fun A => f A.val) p i)^2) ≤
      (Fintype.card V : ℝ) *
        (3 * (Fintype.card V : ℝ) * longCellCost (hbags := hbags) (hG := hG) p f + colorCost p.1 f) := by
  have h := Finset.sum_le_sum (s := Finset.range (Fintype.card V))
    (fun i _ => componentDifference_cell_bound (hbags := hbags) (hG := hG) p f i)
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] using h

lemma sum_demand_eq (ρ : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags)) → ℝ)
    (f : Finset (BagEdge bags) → ℝ) :
    (∑ d : Demand hbags hG, ρ d.1 * d.cellCost f) =
      ∑ p : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags)),
        ρ p * longCellCost (hbags := hbags) (hG := hG) p f := by
  classical
  rw [arbitrary_sigma_sum]
  simp_rw [arbitrary_sigma_sum]
  simp only [longCellCost,Finset.mul_sum]

theorem variance_cell_demand_bound (w : BagEdge bags → ℝ) (hw : ∀ e, 0 < w e)
    (M : PM (BagEdge.Incident (bags := bags))) (f : Finset (BagEdge bags) → ℝ) :
    (∑ p : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags)),
        gibbs w p.1 * gibbs w p.2 * (f p.1.val-f p.2.val)^2) / 2 ≤
      3 * (Fintype.card V : ℝ)^3 *
        (∑ d : Demand hbags hG, gibbs w d.1.1 * gibbs w d.1.2 * d.cellCost f) +
      (Fintype.card V : ℝ)^2 * ∑ A : PM (BagEdge.Incident (bags := bags)), gibbs w A * colorCost A f := by
  classical
  have hv := cycle_demand_variance BagEdge.exists_incident w hw (fun A => f A.val)
  have hs := Finset.sum_le_sum
    (s := (Finset.univ : Finset (PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags)))))
    (fun p _ => mul_le_mul_of_nonneg_left (sum_componentDifference_bound (hbags := hbags) (hG := hG) p f)
      (mul_nonneg (le_of_lt (gibbs_pos w hw p.1)) (le_of_lt (gibbs_pos w hw p.2))))
  have h := hv.trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (Fintype.card V)))
  rw [sum_demand_eq (fun p => gibbs w p.1 * gibbs w p.2) f]
  have hc : (∑ p : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags)),
      gibbs w p.1 * gibbs w p.2 * colorCost p.1 f) =
        ∑ A : PM (BagEdge.Incident (bags := bags)), gibbs w A * colorCost A f := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro A _
    calc
      _ = (gibbs w A * colorCost A f) * ∑ B : PM (BagEdge.Incident (bags := bags)), gibbs w B := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro B _
        ring
      _ = _ := by rw [gibbs_sum w hw M,mul_one]
  have halgebra : (Fintype.card V : ℝ) *
      (∑ p : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags)),
        gibbs w p.1 * gibbs w p.2 * ((Fintype.card V : ℝ) *
          (3 * (Fintype.card V : ℝ) * longCellCost (hbags := hbags) (hG := hG) p f + colorCost p.1 f))) =
      3 * (Fintype.card V : ℝ)^3 *
        (∑ p : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags)),
          gibbs w p.1 * gibbs w p.2 * longCellCost (hbags := hbags) (hG := hG) p f) +
      (Fintype.card V : ℝ)^2 *
        (∑ p : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags)),
          gibbs w p.1 * gibbs w p.2 * colorCost p.1 f) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [halgebra,hc] at h
  exact h

end MatchingFPRAS.Transport.CellDemands

namespace MatchingFPRAS.Transport

section

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance endpointPairBagEdgeFintype : Fintype (BagEdge bags) :=
  Fintype.ofFinite _

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

variable (hG : G.IsAcyclic)

include hbags hG in
omit [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L] in
lemma label_memberships_le_two (v : V) : (bags v).card ≤ 2 := by
  by_contra h
  have hc : G.IsNClique ((bags v).card) (bags v) := by
    constructor
    · intro a ha b hb hab
      exact (hbags v a ha b hb).resolve_left hab
    · rfl
  exact hc.not_cliqueFree (hG.cliqueFree (by omega))

namespace BagEdge

noncomputable def endpointPair (e : BagEdge bags) : V × V :=
  Classical.choose (show ∃ p : V × V, e.val.val.1 = s(p.1,p.2) from
    Sym2.inductionOn e.val.val.1 (fun a b => ⟨(a,b),rfl⟩))

omit [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L] in
lemma endpointPair_eq (e : BagEdge bags) : e.val.val.1 = s(e.endpointPair.1,e.endpointPair.2) :=
  Classical.choose_spec (show ∃ p : V × V, e.val.val.1 = s(p.1,p.2) from
    Sym2.inductionOn e.val.val.1 (fun a b => ⟨(a,b),rfl⟩))

noncomputable def verticesColor (e : BagEdge bags) : Σ v : V, V × ↥(bags v) :=
  ⟨e.endpointPair.1,e.endpointPair.2,⟨e.color,e.property _ (by
    change e.endpointPair.1 ∈ e.val.val.1
    rw [e.endpointPair_eq]
    simp)⟩⟩

omit [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L] in
lemma verticesColor_injective : Function.Injective (verticesColor (bags := bags)) := by
  intro e f h
  have h₁ : e.endpointPair.1 = f.endpointPair.1 := congrArg Sigma.fst h
  have h₂ : e.endpointPair.2 = f.endpointPair.2 := congrArg (fun p => p.2.1) h
  have h₃ : e.color = f.color := congrArg (fun p => p.2.2.val) h
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rw [e.endpointPair_eq,f.endpointPair_eq,h₁,h₂]
  · exact h₃

end BagEdge

include hbags hG in
omit [DecidableEq V] [DecidableEq L] in
lemma bag_edges_card_le : Fintype.card (BagEdge bags) ≤ 2 * Fintype.card V ^ 2 := by
  classical
  calc
    _ ≤ Fintype.card (Σ v : V, V × ↥(bags v)) := Fintype.card_le_of_injective BagEdge.verticesColor BagEdge.verticesColor_injective
    _ = ∑ v : V, Fintype.card V * (bags v).card := by simp only [Fintype.card_sigma,Fintype.card_prod,Fintype.card_coe]
    _ ≤ ∑ _v : V, Fintype.card V * 2 :=
      Finset.sum_le_sum (fun v _ => Nat.mul_le_mul_left _ (label_memberships_le_two hbags hG v))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Nat.nsmul_eq_mul]; ring

end

section

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

omit [DecidableEq V] [Fintype E] in
lemma SafeSwitch.weight_ratio {w : E → ℝ} (hw : ∀ e, 0 < w e) {K : ℝ}
    {A B : PM inc} (h : SafeSwitch w K A B) : matchingWeight w A ≤ K^2 * matchingWeight w B := by
  classical
  obtain ⟨v,e,R,hv,he,hA,hB,hcomp⟩ := h
  have hne (i j : Fin 4) (hij : i ≠ j) (hij' : i ≠ j+1) : e i ≠ e j := by
    intro h
    have hi := (he i (v i)).mpr (Or.inl rfl)
    rw [h] at hi
    rcases (he j (v i)).mp hi with h | h
    · exact hij (hv h)
    · exact hij' (hv h)
  have h01 : e 0 ≠ e 1 := hne 0 1 (by decide) (by decide)
  have h23 : e 2 ≠ e 3 := hne 2 3 (by decide) (by decide)
  have h02 : e 0 ≠ e 2 := hne 0 2 (by decide) (by decide)
  have h13 : e 1 ≠ e 3 := hne 1 3 (by decide) (by decide)
  have hRA : R ⊆ A.val := by rw [hA]; exact Finset.subset_union_left
  have hRB : R ⊆ B.val := by rw [hB]; exact Finset.subset_union_left
  have ha0 : e 0 ∈ A.val := by rw [hA]; simp
  have ha2 : e 2 ∈ A.val := by rw [hA]; simp
  have hb1 : e 1 ∈ B.val := by rw [hB]; simp
  have hb3 : e 3 ∈ B.val := by rw [hB]; simp
  have hr0 : e 0 ∉ R := by
    intro hr
    exact h01 (B.property.unique (Finset.mem_univ (v 1)) (hRB hr)
      ((he 0 (v 1)).mpr (Or.inr rfl)) hb1 ((he 1 (v 1)).mpr (Or.inl rfl)))
  have hr1 : e 1 ∉ R := by
    intro hr
    exact h01 (A.property.unique (Finset.mem_univ (v 1)) ha0
      ((he 0 (v 1)).mpr (Or.inr rfl)) (hRA hr) ((he 1 (v 1)).mpr (Or.inl rfl)))
  have hr2 : e 2 ∉ R := by
    intro hr
    exact h23 (B.property.unique (Finset.mem_univ (v 3)) (hRB hr)
      ((he 2 (v 3)).mpr (Or.inr rfl)) hb3 ((he 3 (v 3)).mpr (Or.inl rfl)))
  have hr3 : e 3 ∉ R := by
    intro hr
    exact h23 (A.property.unique (Finset.mem_univ (v 3)) ha2
      ((he 2 (v 3)).mpr (Or.inr rfl)) (hRA hr) ((he 3 (v 3)).mpr (Or.inl rfl)))
  have hdA : Disjoint R {e 0,e 2} := by
    simp only [Finset.disjoint_insert_right,Finset.disjoint_singleton_right]
    exact ⟨hr0,hr2⟩
  have hdB : Disjoint R {e 1,e 3} := by
    simp only [Finset.disjoint_insert_right,Finset.disjoint_singleton_right]
    exact ⟨hr1,hr3⟩
  have hp := mul_le_mul (hcomp 0 1) (hcomp 2 3) (le_of_lt (hw (e 2)))
    (le_trans (le_of_lt (hw (e 0))) (hcomp 0 1))
  have hr : 0 ≤ ∏ a ∈ R, w a := Finset.prod_nonneg (fun a _ => le_of_lt (hw a))
  have h := mul_le_mul_of_nonneg_left hp hr
  simp only [matchingWeight,hA,hB,Finset.prod_union hdA,Finset.prod_union hdB,
    Finset.prod_pair h02,Finset.prod_pair h13]
  nlinarith only [h]

omit [DecidableEq V] in
lemma SafeSwitch.gibbs_ratio {w : E → ℝ} (hw : ∀ e, 0 < w e) {K : ℝ}
    {A B : PM inc} (h : SafeSwitch w K A B) : gibbs w A ≤ K^2 * gibbs w B := by
  dsimp only [gibbs]
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (h.weight_ratio hw) (le_of_lt (partition_pos w hw A))

omit [DecidableEq V] in
lemma SafeSwitch.min_capacity {w : E → ℝ} (hw : ∀ e, 0 < w e) {K : ℝ} (hK : 1 ≤ K)
    {A B : PM inc} (h : SafeSwitch w K A B) : gibbs w A ≤ K^2 * min (gibbs w A) (gibbs w B) := by
  rw [mul_min_of_nonneg _ _ (sq_nonneg K)]
  apply le_min
  · have hp := le_of_lt (gibbs_pos w hw A)
    have hsq : 1 ≤ K^2 := by nlinarith
    nlinarith
  · exact h.gibbs_ratio hw

end

section

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V)

omit [DecidableEq V] [Fintype E] in
lemma ColorChange.weight_ratio {w : E → ℝ} (hw : ∀ e, 0 < w e) {K : ℝ} (hK : 1 ≤ K)
    (hcomp : ∀ e f, ends e = ends f → w e ≤ K*w f)
    {A B : PM (fun e v => v ∈ ends e)} (h : ColorChange ends A B) :
    matchingWeight w A ≤ K * matchingWeight w B := by
  classical
  obtain ⟨e,f,R,hef,hA,hB⟩ := h
  by_cases heq : e = f
  · have hAB : A = B := Subtype.ext (by rw [hA,hB,heq])
    subst B
    have hp := le_of_lt (matchingWeight_pos w hw A)
    nlinarith
  · obtain ⟨v,hv⟩ : ∃ v, v ∈ ends e := by
      induction ends e using Sym2.inductionOn with | hf a b => exact ⟨a,by simp⟩
    have hRA : R ⊆ A.val := by rw [hA]; exact Finset.subset_union_left
    have hRB : R ⊆ B.val := by rw [hB]; exact Finset.subset_union_left
    have hae : e ∈ A.val := by rw [hA]; simp
    have hbf : f ∈ B.val := by rw [hB]; simp
    have hre : e ∉ R := by
      intro hr
      exact heq (B.property.unique (Finset.mem_univ v) (hRB hr) hv hbf (hef ▸ hv))
    have hrf : f ∉ R := by
      intro hr
      exact heq (A.property.unique (Finset.mem_univ v) hae hv (hRA hr) (hef ▸ hv))
    have hdA : Disjoint R {e} := Finset.disjoint_singleton_right.mpr hre
    have hdB : Disjoint R {f} := Finset.disjoint_singleton_right.mpr hrf
    have hr : 0 ≤ ∏ a ∈ R, w a := Finset.prod_nonneg (fun a _ => le_of_lt (hw a))
    have h := mul_le_mul_of_nonneg_left (hcomp e f hef) hr
    simp only [matchingWeight,hA,hB,Finset.prod_union hdA,Finset.prod_union hdB,Finset.prod_singleton]
    nlinarith only [h]

omit [DecidableEq V] in
lemma ColorChange.min_capacity {w : E → ℝ} (hw : ∀ e, 0 < w e) {K : ℝ} (hK : 1 ≤ K)
    (hcomp : ∀ e f, ends e = ends f → w e ≤ K*w f)
    {A B : PM (fun e v => v ∈ ends e)} (h : ColorChange ends A B) :
    gibbs w A ≤ K * min (gibbs w A) (gibbs w B) := by
  rw [mul_min_of_nonneg _ _ (by linarith : 0 ≤ K)]
  apply le_min
  · have hp := le_of_lt (gibbs_pos w hw A)
    nlinarith
  · dsimp only [gibbs]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (h.weight_ratio ends hw hK hcomp)
      (le_of_lt (partition_pos w hw A))

end

section

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

variable (lo hi : ℝ) (hlo : 0 < lo)

include hbags hheight hstep hD hw hlo in
omit [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L] in
lemma color_clamp_comparability (e f : BagEdge bags) (hef : e.val.val.1 = f.val.val.1) :
    max lo (min hi (w e)) ≤ (1000*D) * max lo (min hi (w f)) := by
  obtain ⟨v,hev⟩ := BagEdge.exists_incident e
  have hfv : f.Incident v := by
    change v ∈ f.val.val.1
    rw [← hef]
    exact hev
  have hc := hbags v _ (BagEdge.color_mem e hev) _ (BagEdge.color_mem f hfv)
  have hh : height e.color ≤ 2 * height f.color := by
    rcases hc with h | h
    · rw [h]; nlinarith [hheight f.color]
    · exact hstep _ _ h
  have hDpos : 0 < D := by linarith
  have hfpos : 0 < w f := lt_of_lt_of_le (div_pos (hheight f.color) hDpos) (hw f).1
  have hlow : height f.color ≤ w f * D := (div_le_iff₀ hDpos).mp (hw f).1
  apply IndexedCycle.common_clamp_ratio (le_of_lt hlo) (by linarith)
  nlinarith [(hw e).2,mul_pos hDpos hfpos]

end

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

def TwoEdgeSwitch (A B : PM inc) : Prop :=
  ∃ (v : Fin 4 → V) (e : Fin 4 → E) (R : Finset E),
    Function.Injective v ∧
    (∀ i x, inc (e i) x ↔ x = v i ∨ x = v (i+1)) ∧
    A.val = R ∪ {e 0,e 2} ∧ B.val = R ∪ {e 1,e 3}

omit [DecidableEq V] [Fintype E] in
lemma SafeSwitch.legal {w : E → ℝ} {K : ℝ} {A B : PM inc} (h : SafeSwitch w K A B) :
    TwoEdgeSwitch A B := by
  obtain ⟨v,e,R,hv,he,hA,hB,_⟩ := h
  exact ⟨v,e,R,hv,he,hA,hB⟩

omit [DecidableEq V] [Fintype E] in
lemma TwoEdgeSwitch.two_le {A B : PM inc} (h : TwoEdgeSwitch A B) : 2 ≤ A.val.card := by
  classical
  obtain ⟨v,e,R,hv,he,hA,hB⟩ := h
  have h02 : e 0 ≠ e 2 := by
    intro h
    have h0 := (he 0 (v 0)).mpr (Or.inl rfl)
    rw [h] at h0
    rcases (he 2 (v 0)).mp h0 with h | h
    · have := hv h; exact (by decide : (0:Fin 4) ≠ 2) this
    · have := hv h; exact (by decide : (0:Fin 4) ≠ 2+1) this
  have hs : {e 0,e 2} ⊆ A.val := by rw [hA]; exact Finset.subset_union_right
  simpa only [Finset.card_pair h02] using Finset.card_le_card hs

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma PM.card_le_vertices (hinc : ∀ e, ∃ v, inc e v) (A : PM inc) : A.val.card ≤ Fintype.card V := by
  classical
  let vertex : ↥A.val → V := fun e => Classical.choose (hinc e.val)
  have hv (e : ↥A.val) : inc e.val (vertex e) := Classical.choose_spec (hinc e.val)
  have hinj : Function.Injective vertex := by
    intro e f h
    apply Subtype.ext
    exact A.property.unique (Finset.mem_univ (vertex e)) e.property (hv e) f.property (h ▸ hv f)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective vertex hinj

noncomputable def switchDestinations (A : PM inc) : Finset (PM inc) := by
  classical
  exact Finset.univ.filter (TwoEdgeSwitch A)

noncomputable def discrepancyComponents (A B : PM inc) : Finset (Finset E) := by
  classical
  exact (components (inc := inc) (A.val ∪ B.val)).filter (fun S => ¬ S ⊆ A.val ∩ B.val)

noncomputable def switchDirichlet (w : E → ℝ) (f : Finset E → ℝ) : ℝ :=
  ∑ A : PM inc, ∑ B ∈ switchDestinations A,
    min (gibbs w A) (gibbs w B) * (f A.val-f B.val)^2 / (48 * (A.val.card.choose 2 : ℝ))

noncomputable def cycleSquare (f g : Finset E → ℝ) (A B : Finset E) (S : Finset E) : ℝ :=
  ((f A+g B)-(f (exchange A B S)+g (exchange B A S)))^2

noncomputable def cycleDirichlet (w : E → ℝ) (f g : Finset E → ℝ) : ℝ :=
  ∑ A : PM inc, ∑ B : PM inc, gibbs w A * gibbs w B *
    (∑ S ∈ discrepancyComponents A B, cycleSquare f g A.val B.val S /
      (6 * ((discrepancyComponents A B).card : ℝ)))

variable (ends : E → Sym2 V)

noncomputable def colorDirichlet (w : E → ℝ) (f : Finset E → ℝ) : ℝ :=
  ∑ A : PM (fun e v => v ∈ ends e), ∑ B ∈ colorDestinations ends A,
    min (gibbs w A) (gibbs w B) * (f A.val-f B.val)^2 / (12 * (A.val.card : ℝ))

noncomputable def pairDirichlet (w : E → ℝ) (f g : Finset E → ℝ) : ℝ :=
  switchDirichlet (inc := fun e v => v ∈ ends e) w f + colorDirichlet ends w f +
    cycleDirichlet (inc := fun e v => v ∈ ends e) w f g

lemma scale_div_lower {x a b : ℝ} (hx : 0 ≤ x) (ha : 0 < a) (hab : a ≤ b) :
    x ≤ b * (x/a) := by
  calc
    x = a * (x/a) := by field_simp [ne_of_gt ha]
    _ ≤ b * (x/a) := mul_le_mul_of_nonneg_right hab (div_nonneg hx (le_of_lt ha))

omit [DecidableEq V] in
lemma switchDirichlet_nonneg (w : E → ℝ) (hw : ∀ e, 0 < w e) (f : Finset E → ℝ) :
    0 ≤ switchDirichlet (inc := inc) w f := by
  apply Finset.sum_nonneg
  intro A _
  apply Finset.sum_nonneg
  intro B _
  exact div_nonneg (mul_nonneg (le_min (le_of_lt (gibbs_pos w hw A))
    (le_of_lt (gibbs_pos w hw B))) (sq_nonneg _)) (by positivity)

omit [DecidableEq V] in
lemma colorDirichlet_nonneg (w : E → ℝ) (hw : ∀ e, 0 < w e) (f : Finset E → ℝ) :
    0 ≤ colorDirichlet ends w f := by
  apply Finset.sum_nonneg
  intro A _
  apply Finset.sum_nonneg
  intro B _
  exact div_nonneg (mul_nonneg (le_min (le_of_lt (gibbs_pos w hw A))
    (le_of_lt (gibbs_pos w hw B))) (sq_nonneg _)) (by positivity)

omit [DecidableEq V] in
lemma cycleDirichlet_nonneg (w : E → ℝ) (hw : ∀ e, 0 < w e) (f g : Finset E → ℝ) :
    0 ≤ cycleDirichlet (inc := inc) w f g := by
  apply Finset.sum_nonneg
  intro A _
  apply Finset.sum_nonneg
  intro B _
  apply mul_nonneg (mul_nonneg (le_of_lt (gibbs_pos w hw A)) (le_of_lt (gibbs_pos w hw B)))
  exact Finset.sum_nonneg (fun S _ => div_nonneg (sq_nonneg _) (by positivity))

end MatchingFPRAS.Transport

end OAI
