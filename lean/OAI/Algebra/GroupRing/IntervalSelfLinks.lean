import Mathlib
import OAI.Algebra.GroupRing.MatchedLabels

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.IntervalSelfLinks
open scoped Classical

/-- Integer positions of one actual comparison within a single block. -/
def selfSlice (L U l u : ℤ) (rev : Bool) (a : ℤ) : Finset ℤ :=
  (Finset.Ico L U ∩ Finset.Ico l u).filter
    (fun q => (if rev then a-1-q else q+a) ∈ Finset.Ico L U)

theorem reflection_slice (L U l u a : ℤ) :
    selfSlice L U l u true a =
      Finset.Ico (max L (max l (a-U))) (min U (min u (a-L))) := by
  ext q
  simp only [selfSlice,Finset.mem_filter,Finset.mem_inter,Finset.mem_Ico,
    ite_true,max_le_iff,lt_min_iff]
  omega

theorem translation_slice (L U l u a : ℤ) :
    selfSlice L U l u false a =
      Finset.Ico (max L (max l (L-a))) (min U (min u (U-a))) := by
  ext q
  simp only [selfSlice,Finset.mem_filter,Finset.mem_inter,Finset.mem_Ico,
    Bool.false_eq_true,ite_false,max_le_iff,lt_min_iff]
  omega

/-- No reversed self-link on a reduced word can cover more than half a block. -/
theorem reflection_not_large {A : Type*} (bar : A → A)
    (hbar : Function.Involutive bar) (hfree : ∀ x, bar x ≠ x)
    (w : ℤ → A) (L U l u a : ℤ)
    (hred : ∀ q, L ≤ q → q+1 < U → w (q+1) ≠ bar (w q))
    (hcompare : ∀ q ∈ selfSlice L U l u true a, w q = bar (w (a-1-q))) :
    2*(selfSlice L U l u true a).card ≤ (Finset.Ico L U).card := by
  by_contra! hn
  rw [reflection_slice,Int.card_Ico,Int.card_Ico] at hn
  let l' := max L (max l (a-U))
  let u' := min U (min u (a-L))
  have hll : L ≤ l' := le_max_left _ _
  have hlb : a-U ≤ l' := (le_max_right _ _).trans (le_max_right _ _)
  have huU : u' ≤ U := min_le_left _ _
  have hub : u' ≤ a-L := (min_le_right _ _).trans (min_le_right _ _)
  have hne : l' < u' := by change _ < 2*(u'-l').toNat at hn; omega
  have hmass : U-L < 2*(u'-l') := by change (U-L).toNat < 2*(u'-l').toNat at hn; omega
  apply reflection_excluded bar hbar hfree w L U l' u' (a-1) hll huU hne
    (by omega) (by omega) hmass hred
  intro q hq hq'
  apply hcompare
  rw [reflection_slice]
  exact Finset.mem_Ico.mpr ⟨hq,hq'⟩

/-- The precise translation constraints retained by a self-link, with its
literal compared-position cardinality and no additional independence premise. -/
theorem translation_from_slice (L U l u a : ℤ) (ha : a ≠ 0) :
    ∃ tr : BlockConstraints.Translation (U-L).toNat,
      tr.domain.card = (selfSlice L U l u false a).card ∧
      ∀ (A : Type*) (w : Fin (U-L).toNat → A),
        (∀ q (hq : q ∈ selfSlice L U l u false a),
          w (coordinate L U ⟨q+a,by simpa [selfSlice] using (Finset.mem_filter.mp hq).2⟩) =
            w (coordinate L U ⟨q,(Finset.mem_inter.mp (Finset.mem_filter.mp hq).1).1⟩)) →
          ∀ k : tr.domain, w (tr.target k) = w k.val := by
  exact translation_representation L U a _ ha (by
    intro q hq
    refine ⟨(Finset.mem_inter.mp (Finset.mem_filter.mp hq).1).1,?_⟩
    simpa [selfSlice] using (Finset.mem_filter.mp hq).2)

/-- The same increasing coordinate, transported along the exact cardinality. -/
def coordinateN (L U : ℤ) (n : ℕ) (hn : n = (U-L).toNat) :
    Finset.Ico L U ≃ Fin n := (coordinate L U).trans (finCongr hn.symm)

theorem coordinateN_val (L U : ℤ) (n : ℕ) (hn : n = (U-L).toNat)
    (q : Finset.Ico L U) : ((coordinateN L U n hn q).val : ℤ) = q.val-L :=
  coordinate_val q

theorem translation_from_slice_at (L U l u a : ℤ) (ha : a ≠ 0)
    (n : ℕ) (hn : n = (U-L).toNat) :
    ∃ tr : BlockConstraints.Translation n,
      tr.domain.card = (selfSlice L U l u false a).card ∧
      ∀ (A : Type*) (w : Fin n → A),
        (∀ q (hq : q ∈ selfSlice L U l u false a),
          w (coordinateN L U n hn ⟨q+a,by simpa [selfSlice] using (Finset.mem_filter.mp hq).2⟩) =
            w (coordinateN L U n hn ⟨q,(Finset.mem_inter.mp (Finset.mem_filter.mp hq).1).1⟩)) →
          ∀ k : tr.domain, w (tr.target k) = w k.val := by
  subst n
  simpa [coordinateN] using translation_from_slice L U l u a ha

end TorsionFreeZeroDivisors.IntervalSelfLinks

/-!
Finite combinatorial and numerical bounds: occurrence pairings,
layer-cake stage counts and selection of one small stage. None of the graph
existence, matching estimates or topological assertions is an assumption here.
-/

namespace TorsionFreeZeroDivisors.EntropyStages

open scoped BigOperators

namespace Pairing

variable {O C : Type*} [Fintype O] [DecidableEq O] [DecidableEq C] (P : Pairing O)

abbrev Unmatched := {o : O // P.partner o = o}

/-- The exact link balance, including isolated blocks and multiple links.
A self-link is excluded only in the component where the bound is used. -/
theorem color_balance (color : O → C) (c : C)
    (hcross : ∀ o, P.partner o ≠ o → color (P.partner o) ≠ color o) :
    2 * Fintype.card {o : O // color o = c} ≤
      Fintype.card O + Fintype.card P.Unmatched := by
  classical
  let f : {o : O // color o = c} →
      {o : O // color o ≠ c} ⊕ P.Unmatched := fun o =>
    if h : P.partner o.val = o.val then .inr ⟨o.val,h⟩
    else .inl ⟨P.partner o.val, by simpa only [o.property] using hcross o.val h⟩
  have hf : Function.Injective f := by
    intro o p he
    dsimp [f] at he
    by_cases ho : P.partner o.val = o.val
    · by_cases hp : P.partner p.val = p.val
      · simp only [dite_eq_left ho, dite_eq_left hp] at he
        exact Subtype.ext (congrArg (fun q : P.Unmatched => q.val) (Sum.inr.inj he))
      · simp only [dite_eq_left ho, dite_eq_right hp, reduceCtorEq] at he
    · by_cases hp : P.partner p.val = p.val
      · simp only [dite_eq_right ho, dite_eq_left hp, reduceCtorEq] at he
      · simp only [dite_eq_right ho, dite_eq_right hp] at he
        exact Subtype.ext (P.involutive.injective
          (congrArg (fun q : {o : O // color o ≠ c} => q.val) (Sum.inl.inj he)))
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_sum] at hcard
  have htotal : Fintype.card {o : O // color o ≠ c} +
      Fintype.card {o : O // color o = c} = Fintype.card O := by
    rw [Fintype.card_subtype_compl]
    have hle := Fintype.card_subtype_le (fun o : O => color o = c)
    omega
  omega

end Pairing

/-- Exact finite layer-cake identity. Stage j+1 is present precisely when
j is smaller than the occurrence multiplicity. -/
theorem stage_sum (M k : ℕ) (hk : k ≤ M) (a : ℝ) :
    (∑ j ∈ Finset.range M, if j < k then a else 0) = k * a := by
  rw [← Finset.sum_filter]
  have he : (Finset.range M).filter (· < k) = Finset.range k := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [he]
  simp

/-- Multiplying the numerical stage bounds is equivalent to summing their
logarithms; their shared edge/word costs are counted with multiplicity. -/
theorem sum_stage_costs {I : Type*} [Fintype I]
    (M : ℕ) (m : I → ℕ) (hm : ∀ i, m i ≤ M) (d : I → ℝ) :
    (∑ j ∈ Finset.range M, ∑ i, if j < m i then d i else 0) =
      ∑ i, (m i : ℝ) * d i := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => stage_sum M (m i) (hm i) (d i)

/-- A bound for the product of numerical stage estimates selects one stage;
no independence between the random variables at different stages is used. -/
theorem select_stage (M : ℕ) (hM : 0 < M) (logB : Fin M → ℝ) (decay : ℝ)
    (hprod : (∑ j, logB j) ≤ -decay) :
    ∃ j, logB j ≤ -decay / M := by
  by_contra! hn
  have hs : (∑ _j : Fin M, -decay / M) < ∑ j, logB j := by
    exact Finset.sum_lt_sum_of_nonempty ⟨⟨0,hM⟩,Finset.mem_univ _⟩ (fun j _ => hn j)
  have hMr : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)
  have he : (∑ _j : Fin M, -decay / M) = -decay := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [he] at hs
  linarith

/-- Markov/union-bound conclusions can use this exponential version directly. -/
theorem select_exponential_stage (M : ℕ) (hM : 0 < M) (logB : Fin M → ℝ)
    (decay : ℝ) (hprod : (∑ j, logB j) ≤ -decay) :
    ∃ j, Real.exp (logB j) ≤ Real.exp (-decay / M) := by
  obtain ⟨j,hj⟩ := select_stage M hM logB decay hprod
  exact ⟨j,Real.exp_le_exp.mpr hj⟩

end TorsionFreeZeroDivisors.EntropyStages

namespace TorsionFreeZeroDivisors
open scoped BigOperators
/-- The cost estimate for a component without a self-link, with the
lower bin bound and unmatched-occurrence correction. -/
theorem component_cost_bound {J : Type*} [Fintype J]
    (m d : J → ℝ) (dmin δ s a₀ z b : ℝ)
    (hm : ∀ i, 0 ≤ m i) (hmin : ∀ i, dmin ≤ d i)
    (hlow : δ * s / 2 ≤ dmin) (hhigh : dmin ≤ a₀ * s)
    (hδ : 0 ≤ δ) (hs : 0 ≤ s) (ha : 0 ≤ a₀) (hb : 0 ≤ b)
    (hbalance : 2 * z ≤ (∑ i, m i) + b) :
    -(∑ i, m i * d i) + 2 * z * dmin - δ * s * z ≤
      a₀ * s * b - δ / 2 * s * (∑ i, m i) := by
  have hsum : (∑ i, m i) * dmin ≤ ∑ i, m i * d i := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hmin i) (hm i)
  have hds : 0 ≤ δ * s := mul_nonneg hδ hs
  have hab : 0 ≤ a₀ * s * b := mul_nonneg (mul_nonneg ha hs) hb
  by_cases h : 2 * z ≤ ∑ i, m i
  · have hc : 0 ≤ (∑ i, m i) - 2 * z := sub_nonneg.mpr h
    have hh := mul_le_mul_of_nonneg_left hlow hc
    nlinarith
  · have hc : 0 ≤ 2 * z - ∑ i, m i := by linarith
    have hh := mul_le_mul_of_nonneg_left hhigh hc
    have hz : (2 * z - ∑ i, m i) * (a₀ * s) ≤ b * (a₀ * s) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg ha hs)
      linarith
    have hz' := mul_le_mul_of_nonneg_left hc hds
    nlinarith

/-- A self-link removes the root-word entropy. The remaining cost has the
same decay term, with no unmatched-occurrence correction. -/
theorem selflinked_component_cost_bound {J : Type*} [Fintype J]
    (m d : J → ℝ) (δ s : ℝ) (hm : ∀ i, 0 ≤ m i)
    (hlow : ∀ i, δ * s / 2 ≤ d i) :
    -(∑ i, m i * d i) ≤ -δ / 2 * s * (∑ i, m i) := by
  have hsum : (∑ i, m i) * (δ * s / 2) ≤ ∑ i, m i * d i := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hlow i) (hm i)
  nlinarith

end TorsionFreeZeroDivisors

namespace TorsionFreeZeroDivisors.StageFusion

section
open scoped BigOperators
open EntropyStages

/-- Layer-cake identity in the `Fin M` indexing of the selected stages. -/
theorem layers (M k : ℕ) (hk : k ≤ M) (a : ℝ) :
    (∑ j : Fin M, if j.val < k then a else 0) = k*a := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j < k then a else 0)]
  exact stage_sum M k hk a

section Components
variable {C : Type*} [Fintype C] {I : C → Type*} [∀ c, Fintype (I c)]

def componentCost (self : C → Prop) [DecidablePred self]
    (m : ∀ c, I c → ℕ) (d : ∀ c, I c → ℝ) (z : C → ℕ)
    (dmin : C → ℝ) (δ s : ℝ) (c : C) : ℝ :=
  -(∑ i, (m c i : ℝ)*d c i) + if self c then 0 else (2*dmin c - δ*s) * z c

/-- The component costs added together. Every condition here is the
local bin/link balance, not an assumed probability or conclusion. -/
theorem total_component_cost (self : C → Prop) [DecidablePred self]
    (m : ∀ c, I c → ℕ) (d : ∀ c, I c → ℝ) (z : C → ℕ)
    (dmin b : C → ℝ) (δ s a : ℝ)
    (hδ : 0 ≤ δ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hb : ∀ c, 0 ≤ b c)
    (hlow : ∀ c i, δ*s/2 ≤ d c i)
    (hmin : ∀ c, ¬self c → ∀ i, dmin c ≤ d c i)
    (hminlow : ∀ c, ¬self c → δ*s/2 ≤ dmin c)
    (hminhigh : ∀ c, ¬self c → dmin c ≤ a*s)
    (hbalance : ∀ c, ¬self c → 2*(z c : ℝ) ≤ (∑ i, (m c i : ℝ)) + b c) :
    (∑ c, componentCost self m d z dmin δ s c) ≤
      a*s*(∑ c, b c) - δ/2*s*(∑ c, ∑ i, (m c i : ℝ)) := by
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro c _
  dsimp [componentCost]
  by_cases hc : self c
  · rw [ite_eq_left hc,add_zero]
    have h := selflinked_component_cost_bound (fun i => (m c i : ℝ)) (d c) δ s
      (fun _ => Nat.cast_nonneg _) (hlow c)
    have hh := mul_nonneg (mul_nonneg ha hs) (hb c)
    linarith
  · rw [ite_eq_right hc]
    have h := component_cost_bound (fun i => (m c i : ℝ)) (d c) (dmin c) δ s a (z c) (b c)
      (fun _ => Nat.cast_nonneg _) (hmin c hc) (hminlow c hc) (hminhigh c hc)
      hδ hs ha (hb c) (hbalance c hc)
    nlinarith

/-- Exact logarithm of a numerical stage bound. `power` is V_j-E_j-k_j;
`err` contains the independently controlled endpoint/block errors. -/
def stageLog (M : ℕ) (self : C → Prop) [DecidablePred self]
    (m : ∀ c, I c → ℕ) (d : ∀ c, I c → ℝ) (z : C → ℕ)
    (dmin : C → ℝ) (δ s logn : ℝ) (power err : Fin M → ℝ) (j : Fin M) : ℝ :=
  power j * logn - (∑ c, ∑ i, if j.val < m c i then d c i else 0) +
    (∑ c, if j.val < z c then (if self c then 0 else 2*dmin c-δ*s) else 0) + err j

/-- No multiplication of random variables: this is solely an identity between
finite sums of logs of bounds and finite sums of local component costs. -/
theorem sum_stageLog (M : ℕ) (self : C → Prop) [DecidablePred self]
    (m : ∀ c, I c → ℕ) (d : ∀ c, I c → ℝ) (z : C → ℕ)
    (hm : ∀ c i, m c i ≤ M) (hz : ∀ c, z c ≤ M)
    (dmin : C → ℝ) (δ s logn : ℝ) (power err : Fin M → ℝ) :
    (∑ j, stageLog M self m d z dmin δ s logn power err j) =
      (∑ j, power j)*logn + (∑ c, componentCost self m d z dmin δ s c) + ∑ j, err j := by
  simp only [stageLog,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_mul]
  have hm' : (∑ j : Fin M, ∑ c, ∑ i, if j.val < m c i then d c i else 0) =
      ∑ c, ∑ i, (m c i : ℝ)*d c i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => layers M (m c i) (hm c i) (d c i)
  have hz' : (∑ j : Fin M, ∑ c, if j.val < z c then
      (if self c then 0 else 2*dmin c-δ*s) else 0) =
      ∑ c, if self c then 0 else (2*dmin c-δ*s)*(z c : ℝ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    rw [layers M (z c) (hz c)]
    split_ifs <;> ring
  rw [hm',hz']
  simp only [componentCost,Finset.sum_add_distrib,Finset.sum_neg_distrib]
  ring

end Components

/-- The error threshold is fixed using only the universal weight constants. -/
def epsilon (δ a : ℝ) : ℝ := min (1/4) (δ/(16*(1+a)))

theorem epsilon_pos {δ a : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) : 0 < epsilon δ a := by
  apply lt_min (by norm_num)
  exact div_pos hδ (by positivity)

/-- Deterministic final absorption of the unmatched mass and sublinear errors. -/
theorem absorb_errors {δ a H b e : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (hH : 0 ≤ H)
    (hb : b ≤ epsilon δ a * H) (he : e ≤ δ*H/8) :
    -δ/2*H + a*b + e ≤ -δ*H/4 := by
  have hd : 0 < 16*(1+a) := by positivity
  have hε : epsilon δ a ≤ δ/(16*(1+a)) := min_le_right _ _
  have hab : a*b ≤ a*(δ/(16*(1+a))*H) := by
    exact mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_right hε hH)) ha
  have hratio : a*(δ/(16*(1+a))) ≤ δ/16 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<16)).mpr
    have hh : δ/(16*(1+a)) * (16*(1+a)) = δ := div_mul_cancel₀ _ (ne_of_gt hd)
    have hp : 0 ≤ δ/(16*(1+a)) := div_nonneg hδ.le hd.le
    nlinarith
  have hab' := mul_le_mul_of_nonneg_right hratio hH
  nlinarith

end

open scoped Classical BigOperators

section FiniteProbability
variable {Ω P : Type*} [Fintype P] (sample : Finset Ω) (hsample : sample.Nonempty)

/-- Elementary finite Markov bound, including sample restriction. -/
theorem markov_count (Bad : Ω → Prop) [DecidablePred Bad] (X : Ω → ℕ)
    (hX : ∀ ω ∈ sample, Bad ω → 1 ≤ X ω) :
    ((sample.filter Bad).card : ℝ) / sample.card ≤
      ((∑ ω ∈ sample, X ω : ℕ) : ℝ) / sample.card := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (show (sample.filter Bad).card ≤ ∑ ω ∈ sample, X ω from by
    calc
      _ = ∑ ω ∈ sample, if Bad ω then 1 else 0 := by simp
      _ ≤ _ := Finset.sum_le_sum fun ω hω => by
        split_ifs with h
        · exact hX ω hω h
        · exact Nat.zero_le _)

/-- Select a single numerical stage for each pattern. No independence is a
premise, and the chosen stage can depend on the pattern. -/
theorem one_pattern (M : ℕ) (hM : 0 < M) (Bad : Ω → Prop) [DecidablePred Bad]
    (X : Fin M → Ω → ℕ) (logB : Fin M → ℝ) (decay : ℝ)
    (hX : ∀ j ω, ω ∈ sample → Bad ω → 1 ≤ X j ω)
    (hexpect : ∀ j, ((∑ ω ∈ sample, X j ω : ℕ) : ℝ) / sample.card ≤ Real.exp (logB j))
    (hproduct : (∑ j, logB j) ≤ -decay) :
    ((sample.filter Bad).card : ℝ) / sample.card ≤ Real.exp (-decay/M) := by
  obtain ⟨j,hj⟩ := EntropyStages.select_exponential_stage M hM logB decay hproduct
  exact (markov_count sample Bad (X j) (hX j)).trans ((hexpect j).trans hj)

include hsample in
/-- Union bound over the enlarged unlabelled patterns. -/
theorem pattern_union (Bad : P → Ω → Prop) [∀ p, DecidablePred (Bad p)] (B : ℝ)
    (hB : ∀ p, ((sample.filter (Bad p)).card : ℝ) / sample.card ≤ B) :
    ((sample.filter (fun ω => ∃ p, Bad p ω)).card : ℝ) / sample.card ≤
      (Fintype.card P : ℝ)*B := by
  have ho : (0 : ℝ) < sample.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hsample)
  let e : Finset Ω := Finset.univ.biUnion (fun p : P => sample.filter (Bad p))
  have he : sample.filter (fun ω => ∃ p, Bad p ω) = e := by
    ext ω
    simp only [e,Finset.mem_filter,Finset.mem_biUnion,Finset.mem_univ,true_and]
    aesop
  rw [he]
  have hc : e.card ≤ ∑ p, (sample.filter (Bad p)).card := Finset.card_biUnion_le
  have hc' : (e.card : ℝ) ≤ ∑ p, ((sample.filter (Bad p)).card : ℝ) := by
    exact_mod_cast hc
  calc
    _ ≤ (∑ p, ((sample.filter (Bad p)).card : ℝ))/sample.card :=
      div_le_div_of_nonneg_right hc' ho.le
    _ = ∑ p, ((sample.filter (Bad p)).card : ℝ)/sample.card := Finset.sum_div _ _ _
    _ ≤ ∑ _p : P, B := Finset.sum_le_sum (fun p _ => hB p)
    _ = _ := by simp

end FiniteProbability

/-- Explicit finite version of exp(o(L)) times exponential decay. -/
theorem subexponential_union {N : ℕ} {δ M L error : ℝ}
    (_hM : 0 < M) (_hδ : 0 ≤ δ)
    (hN : (N : ℝ) ≤ Real.exp error) (he : error ≤ δ*L/(8*M)) :
    (N : ℝ)*Real.exp (-δ*L/(4*M)) ≤ Real.exp (-δ*L/(8*M)) := by
  calc
    _ ≤ Real.exp error * Real.exp (-δ*L/(4*M)) :=
      mul_le_mul_of_nonneg_right hN (Real.exp_pos _).le
    _ = Real.exp (error + -δ*L/(4*M)) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hid : -δ*L/(4*M) = 2*(-δ*L/(8*M)) := by ring
      rw [hid]
      have hn : -δ*L/(8*M) = -(δ*L/(8*M)) := by ring
      rw [hn]
      linarith

end TorsionFreeZeroDivisors.StageFusion

end

end OAI
