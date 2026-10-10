import OAI.Probability.FKMaps.MarkedSpines

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma marked_exp_vanish {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun n : ℕ => (((2*n+1:ℕ):ℝ)+1)*Real.exp (-κ*Real.sqrt ((2*n+1:ℕ):ℝ)))
      atTop (𝓝 0) := by
  have h := (polynomial_exp_sqrt hκ 2).add (polynomial_exp_sqrt hκ 0)
  simp only [zero_add] at h
  convert h using 1
  funext n
  rw [Real.sq_sqrt (by positivity)]
  simp only [pow_zero,one_mul]
  ring


variable {A : Type*} [MeasurableSpace A]

lemma CriticalEvenOffspring.marked_short_unconditional_bound (p : CriticalEvenOffspring)
    (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)]
    (b : (ℕ×ℕ) → A → ℝ) (hb : ∀ z,Measurable (b z)) {R : ℝ} (hR : 0 < R)
    (hbound : ∀ z a,|b z a| ≤ R) (n K : ℕ) {r : ℝ} (hr : 0 < r) :
    (p.markedCodeLaw κ n).real {x | ∃ v : Fin (2*n+2),height x.1.val v.val ≤ K ∧
      r ≤ |markedSpineSum b x.1 (by omega : v.val ≤ 2*n+1) x.2-
        codeSpineSum (fun z => ∫ a,b z a ∂κ z.1) x.1 v.val|} ≤
      ((2*n+1:ℕ)+1:ℝ)*2*Real.exp (-r^2/(2*K*R^2)) := by
  refine compProd_real_bound (p.codeLaw n) (codeMarkKernel κ (2*n+1)) ?_ (by positivity) ?_
  · simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro v
    have hh : MeasurableSet {x : Code (2*n+1) × (Fin (2*n+1) → A) | height x.1.val v.val ≤ K} :=
      (Set.to_countable {d : Code (2*n+1) | height d.val v.val ≤ K}).measurableSet.preimage measurable_fst
    exact hh.inter (measurableSet_le measurable_const
      (((measurable_marked_spine_joint b hb (by omega : v.val ≤ 2*n+1)).sub
        ((measurable_of_countable (fun d : Code (2*n+1) => codeSpineSum (fun z => ∫ a,b z a ∂κ z.1) d v.val)).comp measurable_fst)).abs))
  · intro d
    change (codeMarkLaw κ d).real {a | ∃ v : Fin (2*n+2),height d.val v.val ≤ K ∧
      r ≤ |markedSpineSum b d (by omega : v.val ≤ 2*n+1) a-
        codeSpineSum (fun z => ∫ a,b z a ∂κ z.1) d v.val|} ≤ _
    simpa only [Nat.add_assoc,show 1+1=2 by rfl] using marked_short_spine_bound κ b hb hR hbound d K hr

/-- Random marks are negligible relative to their conditional path means, uniformly over vertices. -/
lemma CriticalEvenOffspring.uniform_mark_noise (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)]
    (b : (ℕ×ℕ) → A → ℝ) (hb : ∀ z,Measurable (b z)) {R : ℝ} (hR : 0 < R)
    (hbound : ∀ z a,|b z a| ≤ R) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (p.markedCodeLaw κ n).real {x | ∃ v : Fin (2*n+2),
      ε*Real.sqrt ((2*n+1:ℕ):ℝ) < |markedSpineSum b x.1 (by omega : v.val ≤ 2*n+1) x.2-
        codeSpineSum (fun z => ∫ a,b z a ∂κ z.1) x.1 v.val|}) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun _ => ha.trans_le measureReal_nonneg)
  intro η hη
  obtain ⟨C,hC,htight⟩ := p.code_height_tight hB (by positivity : 0 < η/3)
  let δ := ε^2/(2*(C+1)*R^2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hlim := (marked_exp_vanish hδ).const_mul 2
  simp only [mul_zero] at hlim
  filter_upwards [htight,hlim.eventually (gt_mem_nhds (by positivity : (0:ℝ) < η/3))] with n hn hl
  let N := 2*n+1
  let s := Real.sqrt (N:ℝ)
  let K := ⌈C*s⌉₊
  let E0 := {d : Code N | ∃ v ≤ N,C*s < height d.val v}
  let E1 := {x : Code N × (Fin N → A) | ∃ v : Fin (N+1),height x.1.val v.val ≤ K ∧
      ε*s ≤ |markedSpineSum b x.1 (Nat.le_of_lt_succ v.isLt) x.2-
        codeSpineSum (fun z => ∫ a,b z a ∂κ z.1) x.1 v.val|}
  have hsub : {x : Code N × (Fin N → A) | ∃ v : Fin (N+1),ε*s <
      |markedSpineSum b x.1 (Nat.le_of_lt_succ v.isLt) x.2-
        codeSpineSum (fun z => ∫ a,b z a ∂κ z.1) x.1 v.val|} ⊆ (Prod.fst ⁻¹' E0)∪E1 := by
    rintro x ⟨v,hv⟩
    by_cases hh : C*s < (height x.1.val v.val:ℝ)
    · exact Or.inl ⟨v.val,Nat.le_of_lt_succ v.isLt,hh⟩
    · exact Or.inr ⟨v,by exact_mod_cast (not_lt.mp hh).trans (Nat.le_ceil (C*s)),hv.le⟩
  have hs : 1 ≤ s := by
    change 1 ≤ Real.sqrt (N:ℝ)
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    dsimp [N]; norm_num
  have hK : (K:ℝ) ≤ (C+1)*s := by
    have h := (Nat.ceil_lt_add_one (mul_nonneg hC.le (lt_of_lt_of_le zero_lt_one hs).le)).le
    dsimp [K]; nlinarith
  have hK0 : 0 < (K:ℝ) := (mul_pos hC (lt_of_lt_of_le zero_lt_one hs)).trans_le (Nat.le_ceil _)
  have he : -(ε*s)^2/(2*K*R^2) ≤ -δ*s := by
    rw [neg_div,neg_mul]
    apply neg_le_neg
    apply (le_div_iff₀ (by positivity : 0 < 2*(K:ℝ)*R^2)).mpr
    have heq : δ*s*(2*(C+1)*s*R^2)=(ε*s)^2 := by dsimp [δ]; field_simp
    calc
      _ ≤ δ*s*(2*(C+1)*s*R^2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [mul_le_mul_of_nonneg_right hK (sq_nonneg R)]
      _ = _ := heq
  have hbnd : (p.markedCodeLaw κ n).real E1 ≤ 2*((N:ℝ)+1)*Real.exp (-δ*s) := by
    apply (p.marked_short_unconditional_bound κ b hb hR hbound n K
      (mul_pos hε (lt_of_lt_of_le zero_lt_one hs))).trans
    change ((N:ℝ)+1)*2*Real.exp (-(ε*s)^2/(2*K*R^2)) ≤ _
    nlinarith [mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity : 0 ≤ ((N:ℝ)+1)*2)]
  have hprob := (measureReal_mono (μ := p.markedCodeLaw κ n) hsub).trans (measureReal_union_le _ _)
  rw [p.markedCodeLaw_fst] at hprob
  change (p.codeLaw n).real E0 ≤ η/3 at hn
  simp only [← mul_assoc] at hl
  change 2*(((2*n+1:ℕ):ℝ)+1)*Real.exp (-δ*Real.sqrt ((2*n+1:ℕ):ℝ)) < η/3 at hl
  change 2*((N:ℝ)+1)*Real.exp (-δ*s) < η/3 at hl
  exact hprob.trans_lt (by linarith)

lemma markMean_bound (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)]
    (b : (ℕ×ℕ) → A → ℝ) {R : ℝ} (hb : ∀ z a,|b z a| ≤ R) (z : ℕ×ℕ) :
    |∫ a,b z a ∂κ z.1| ≤ R := by
  have h := norm_integral_le_of_norm_le_const (μ := κ z.1) (f := b z) (C := R)
    (ae_of_all _ (fun a => by simpa only [Real.norm_eq_abs] using hb z a))
  simpa [Real.norm_eq_abs,Measure.real] using h

/-- The bounded marked theorem with the source's genuine spine mean. -/
theorem CriticalEvenOffspring.uniform_bounded_marked_spine (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)]
    (b : (ℕ×ℕ) → A → ℝ) (hb : ∀ z,Measurable (b z)) {R : ℝ} (hR : 0 < R)
    (hbound : ∀ z a,|b z a| ≤ R) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (p.markedCodeLaw κ n).real {x | ∃ v : Fin (2*n+2),
      ε*Real.sqrt ((2*n+1:ℕ):ℝ) < |markedSpineSum b x.1 (by omega : v.val ≤ 2*n+1) x.2-
        (∫ z,∫ a,b z a ∂κ z.1 ∂p.spineLaw)*height x.1.val v.val|}) atTop (𝓝 0) := by
  let bm := fun z => ∫ a,b z a ∂κ z.1
  have h ε' (hε' : 0 < ε') := p.uniform_mark_noise hB κ b hb hR hbound hε'
  have ht := p.uniform_bounded_spine_limit hB bm hR (markMean_bound κ b hbound) (by positivity : 0 < ε/2)
  have hn := h (ε/2) (by positivity)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa only [zero_add] using hn.add ht)
    (fun _ => measureReal_nonneg)
  intro n
  let N := 2*n+1
  let s := Real.sqrt (N:ℝ)
  let E0 := {x : Code N × (Fin N → A) | ∃ v : Fin (N+1),(ε/2)*s <
      |markedSpineSum b x.1 (Nat.le_of_lt_succ v.isLt) x.2-codeSpineSum bm x.1 v.val|}
  let E1 := {d : Code N | ∃ v ≤ N,(ε/2)*s <
      |codeSpineSum bm d v-(∫ z,bm z ∂p.spineLaw)*height d.val v|}
  have hsub : {x : Code N × (Fin N → A) | ∃ v : Fin (N+1),ε*s <
      |markedSpineSum b x.1 (Nat.le_of_lt_succ v.isLt) x.2-(∫ z,bm z ∂p.spineLaw)*height x.1.val v.val|}
      ⊆ E0 ∪ (Prod.fst ⁻¹' E1) := by
    rintro x ⟨v,hv⟩
    by_contra hnot
    simp only [Set.mem_union,not_or] at hnot
    have h0 : |markedSpineSum b x.1 (Nat.le_of_lt_succ v.isLt) x.2-codeSpineSum bm x.1 v.val| ≤ (ε/2)*s := by
      by_contra hn; exact hnot.1 ⟨v,lt_of_not_ge hn⟩
    have h1 : |codeSpineSum bm x.1 v.val-(∫ z,bm z ∂p.spineLaw)*height x.1.val v.val| ≤ (ε/2)*s := by
      by_contra hn; exact hnot.2 ⟨v.val,Nat.le_of_lt_succ v.isLt,lt_of_not_ge hn⟩
    have hh := abs_sub_le (markedSpineSum b x.1 (Nat.le_of_lt_succ v.isLt) x.2)
      (codeSpineSum bm x.1 v.val) ((∫ z,bm z ∂p.spineLaw)*height x.1.val v.val)
    linarith
  have hh := (measureReal_mono (μ := p.markedCodeLaw κ n) hsub).trans (measureReal_union_le _ _)
  rw [p.markedCodeLaw_fst] at hh
  exact hh

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
variable {A : Type*} [MeasurableSpace A]

def markedTrunc (m : ℕ) (b : (ℕ×ℕ) → A → ℝ) (z : ℕ×ℕ) (a : A) : ℝ :=
  if z.1 ≤ m then b z a else 0

lemma measurable_markedTrunc (m : ℕ) (b : (ℕ×ℕ) → A → ℝ) (hb : ∀ z,Measurable (b z)) (z : ℕ×ℕ) :
    Measurable (markedTrunc m b z) := by
  unfold markedTrunc; split_ifs
  · exact hb z
  · exact measurable_const

omit [MeasurableSpace A] in
lemma markedTrunc_bound (m : ℕ) (b : (ℕ×ℕ) → A → ℝ) (hb : ∀ z a,|b z a| ≤ z.1) (z : ℕ×ℕ) (a : A) :
    |markedTrunc m b z a| ≤ m := by
  exact spineTrunc_bound m (fun z => b z a) (fun z => hb z a) z

lemma markedTrunc_mean (κ : ℕ → Measure A) (m : ℕ) (b : (ℕ×ℕ) → A → ℝ) (z : ℕ×ℕ) :
    (∫ a,markedTrunc m b z a ∂κ z.1)=spineTrunc m (fun z => ∫ a,b z a ∂κ z.1) z := by
  unfold markedTrunc spineTrunc
  split_ifs <;> simp

omit [MeasurableSpace A] in
lemma markedSpineSum_sub {N : ℕ} (b c : (ℕ×ℕ) → A → ℝ) (d : Code N)
    {v : ℕ} (hv : v ≤ N) (a : Fin N → A) :
    markedSpineSum (fun z a => b z a-c z a) d hv a=markedSpineSum b d hv a-markedSpineSum c d hv a := by
  unfold markedSpineSum
  exact Finset.sum_sub_distrib _ _

omit [MeasurableSpace A] in
lemma markedSpineSum_abs_dom {N : ℕ} (b : (ℕ×ℕ) → A → ℝ) (c : ℕ×ℕ → ℝ)
    (hb : ∀ z a,|b z a| ≤ c z) (d : Code N) {v : ℕ} (hv : v ≤ N) (a : Fin N → A) :
    |markedSpineSum b d hv a| ≤ codeSpineSum c d v := by
  rw [← markedSpineSum_deterministic c d hv a]
  unfold markedSpineSum
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun t _ => hb _ _))

lemma marked_spine_tail_control {N : ℕ} (p : CriticalEvenOffspring)
    (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)] (d : Code N)
    (b : (ℕ×ℕ) → A → ℝ) (hb : ∀ z a,|b z a| ≤ z.1) (m : ℕ)
    {v : ℕ} (hv : v ≤ N) (a : Fin N → A) :
    |markedSpineSum b d hv a-(∫ z,∫ a,b z a ∂κ z.1 ∂p.spineLaw)*height d.val v| ≤
      |markedSpineSum (markedTrunc m b) d hv a-
        (∫ z,∫ a,markedTrunc m b z a ∂κ z.1 ∂p.spineLaw)*height d.val v|+
      |codeSpineSum (fun z => (z.1:ℝ)) d v-(p.variance+1)*height d.val v|+
      |codeSpineSum (spineTrunc m (fun z => (z.1:ℝ))) d v-
        (∫ z,spineTrunc m (fun z => (z.1:ℝ)) z ∂p.spineLaw)*height d.val v|+
      2*(∫ z,spineTail m z ∂p.spineLaw)*height d.val v := by
  let bm := fun z => ∫ a,b z a ∂κ z.1
  have hbm : ∀ z,|bm z| ≤ z.1 := by
    intro z
    have hh := norm_integral_le_of_norm_le_const (μ := κ z.1) (f := b z) (C := (z.1:ℝ))
      (ae_of_all _ (fun a => by simpa only [Real.norm_eq_abs] using hb z a))
    simpa [bm,Real.norm_eq_abs,Measure.real] using hh
  let h : ℝ := height d.val v
  have h0 : 0 ≤ h := by dsimp [h]; positivity
  have hd := markedSpineSum_abs_dom (fun z a => b z a-markedTrunc m b z a) (spineTail m)
    (fun z a => spineTrunc_tail_bound m (fun z => b z a) (fun z => hb z a) z) d hv a
  rw [markedSpineSum_sub] at hd
  have he := p.spineTrunc_integral_error m bm hbm
  have hmean : (fun z => ∫ a,markedTrunc m b z a ∂κ z.1)=spineTrunc m bm := by
    funext z; exact markedTrunc_mean κ m b z
  have hi : (∫ z,spineTail m z ∂p.spineLaw)=p.variance+1-
      ∫ z,spineTrunc m (fun z => (z.1:ℝ)) z ∂p.spineLaw := by
    rw [spineTail_eq,integral_sub p.spine_integrable_fst (p.spine_integrable_dom _ (fun z => by
      unfold spineTrunc; split_ifs <;> simp)),p.spine_integral_fst]
  have hs : codeSpineSum (spineTail m) d v=codeSpineSum (fun z => (z.1:ℝ)) d v-
      codeSpineSum (spineTrunc m (fun z => (z.1:ℝ))) d v := by rw [spineTail_eq,codeSpineSum_sub]
  rw [hmean]
  change |markedSpineSum b d hv a-(∫ z,bm z ∂p.spineLaw)*h| ≤
    |markedSpineSum (markedTrunc m b) d hv a-(∫ z,spineTrunc m bm z ∂p.spineLaw)*h|+_+_+_
  have he1 := abs_add_le (markedSpineSum (markedTrunc m b) d hv a-(∫ z,spineTrunc m bm z ∂p.spineLaw)*h)
    ((markedSpineSum b d hv a-markedSpineSum (markedTrunc m b) d hv a)-
      ((∫ z,bm z ∂p.spineLaw)-(∫ z,spineTrunc m bm z ∂p.spineLaw))*h)
  have he2 := abs_sub (markedSpineSum b d hv a-markedSpineSum (markedTrunc m b) d hv a)
      (((∫ z,bm z ∂p.spineLaw)-(∫ z,spineTrunc m bm z ∂p.spineLaw))*h)
  rw [abs_mul,abs_of_nonneg h0] at he2
  have he3 := mul_le_mul_of_nonneg_right he h0
  have hsum : markedSpineSum (markedTrunc m b) d hv a-(∫ z,spineTrunc m bm z ∂p.spineLaw)*h+
    ((markedSpineSum b d hv a-markedSpineSum (markedTrunc m b) d hv a)-
      ((∫ z,bm z ∂p.spineLaw)-(∫ z,spineTrunc m bm z ∂p.spineLaw))*h)=
    markedSpineSum b d hv a-(∫ z,bm z ∂p.spineLaw)*h := by ring
  rw [hs] at hd
  rw [hsum] at he1
  have hK := le_abs_self (codeSpineSum (fun z => (z.1:ℝ)) d v-(p.variance+1)*h)
  have hk := neg_le_abs (codeSpineSum (spineTrunc m (fun z => (z.1:ℝ))) d v-
    (∫ z,spineTrunc m (fun z => (z.1:ℝ)) z ∂p.spineLaw)*h)
  nlinarith

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

/-- The source's full uniform marked ancestral theorem, under the actual conditional
independent-mark law, with only the offspring second moment. -/
theorem CriticalEvenOffspring.uniform_integrable_marked_spine (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    {A : Type*} [MeasurableSpace A] (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)]
    (b : (ℕ×ℕ) → A → ℝ) (hbmeas : ∀ z,Measurable (b z)) (hb : ∀ z a,|b z a| ≤ z.1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (p.markedCodeLaw κ n).real {x | ∃ v : Fin (2*n+1),
      ε*Real.sqrt ((2*n+1:ℕ):ℝ) < |markedSpineSum b x.1 v.isLt.le x.2-
        (∫ z,∫ a,b z a ∂κ z.1 ∂p.spineLaw)*height x.1.val v.val|})
      atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun _ =>  ha.trans_le measureReal_nonneg)
  intro η hη
  obtain ⟨C,hC,hheight⟩ := p.code_height_tight hB (by positivity : 0 < η/4)
  obtain ⟨m,hm⟩ := (p.spine_tail_integral_tendsto.eventually
    (gt_mem_nhds (by positivity : (0:ℝ) < ε/(8*C)))).exists
  have ht0 : 0 ≤ ∫ z,spineTail m z ∂p.spineLaw := integral_nonneg (spineTail_nonneg m)
  have hK := p.uniform_degree_spine_limit hB (by positivity : 0 < ε/4)
  have hbR := p.uniform_bounded_marked_spine hB κ (markedTrunc m b)
    (measurable_markedTrunc m b hbmeas) (R := (m:ℝ)+1) (by positivity)
    (fun z a => (markedTrunc_bound m b hb z a).trans (by linarith))
    (by positivity : 0 < ε/4)
  have hkR := p.uniform_bounded_spine_limit hB (spineTrunc m (fun z =>  (z.1:ℝ)))
    (R := (m:ℝ)+1) (by positivity) (fun z => 
      (spineTrunc_bound m (fun z =>  (z.1:ℝ)) (fun z =>  by simp) z).trans (by linarith))
    (by positivity : 0 < ε/4)
  filter_upwards [hheight,hK.eventually (gt_mem_nhds (by positivity : (0:ℝ) < η/4)),
    hbR.eventually (gt_mem_nhds (by positivity : (0:ℝ) < η/4)),
    hkR.eventually (gt_mem_nhds (by positivity : (0:ℝ) < η/4))] with n hh hK hbR hkR
  let N := 2*n+1
  let s := Real.sqrt (N:ℝ)
  let A0 := {d : Code N | ∃ v ≤ N,C*s < height d.val v}
  let A1 := {d : Code N | ∃ v < N,(ε/4)*s < 
    |codeSpineSum (fun z =>  (z.1:ℝ)) d v-(p.variance+1)*height d.val v|}
  let A2 := {x : Code N × (Fin N → A) | ∃ v : Fin (N+1),(ε/4)*s <
    |markedSpineSum (markedTrunc m b) x.1 (Nat.le_of_lt_succ v.isLt) x.2-
      (∫ z,∫ a,markedTrunc m b z a ∂κ z.1 ∂p.spineLaw)*height x.1.val v.val|}
  let A3 := {d : Code N | ∃ v ≤ N,(ε/4)*s < 
    |codeSpineSum (spineTrunc m (fun z =>  (z.1:ℝ))) d v-
      (∫ z,spineTrunc m (fun z =>  (z.1:ℝ)) z ∂p.spineLaw)*height d.val v|}
  have hsub : {x : Code N × (Fin N → A) | ∃ v : Fin N,ε*s <
      |markedSpineSum b x.1 v.isLt.le x.2-(∫ z,∫ a,b z a ∂κ z.1 ∂p.spineLaw)*height x.1.val v.val|}
      ⊆ ((Prod.fst ⁻¹' A0)∪(Prod.fst ⁻¹' A1))∪(A2∪(Prod.fst ⁻¹' A3)) := by
    rintro x ⟨v,hbad⟩
    by_contra hn
    simp only [Set.mem_union,not_or] at hn
    have hhv : (height x.1.val v.val:ℝ) ≤ C*s := by
      by_contra h; exact hn.1.1 ⟨v.val,v.isLt.le,lt_of_not_ge h⟩
    have hKv : |codeSpineSum (fun z =>  (z.1:ℝ)) x.1 v.val-(p.variance+1)*height x.1.val v.val| ≤ (ε/4)*s := by
      by_contra h; exact hn.1.2 ⟨v.val,v.isLt,lt_of_not_ge h⟩
    have hbv : |markedSpineSum (markedTrunc m b) x.1 v.isLt.le x.2-
        (∫ z,∫ a,markedTrunc m b z a ∂κ z.1 ∂p.spineLaw)*height x.1.val v.val| ≤ (ε/4)*s := by
      by_contra h; exact hn.2.1 ⟨⟨v.val,by omega⟩,lt_of_not_ge h⟩
    have hkv : |codeSpineSum (spineTrunc m (fun z =>  (z.1:ℝ))) x.1 v.val-
        (∫ z,spineTrunc m (fun z =>  (z.1:ℝ)) z ∂p.spineLaw)*height x.1.val v.val| ≤ (ε/4)*s := by
      by_contra h; exact hn.2.2 ⟨v.val,v.isLt.le,lt_of_not_ge h⟩
    have ht : 2*(∫ z,spineTail m z ∂p.spineLaw)*height x.1.val v.val ≤ (ε/4)*s := by
      have hm' : (∫ z,spineTail m z ∂p.spineLaw)*(8*C) ≤ ε := (le_div_iff₀ (by positivity)).mp hm.le
      have hs : 0 ≤ s := Real.sqrt_nonneg _
      have h1 := mul_le_mul_of_nonneg_left hhv (show 0 ≤ 2*(∫ z,spineTail m z ∂p.spineLaw) by positivity)
      have h2 := mul_le_mul_of_nonneg_right hm' hs
      nlinarith
    have hc := marked_spine_tail_control p κ x.1 b hb m v.isLt.le x.2
    linarith
  have hprob : (p.markedCodeLaw κ n).real {x : Code N × (Fin N → A) | ∃ v : Fin N,ε*s <
        |markedSpineSum b x.1 v.isLt.le x.2-(∫ z,∫ a,b z a ∂κ z.1 ∂p.spineLaw)*height x.1.val v.val|} ≤
      (p.codeLaw n).real A0+(p.codeLaw n).real A1+(p.markedCodeLaw κ n).real A2+(p.codeLaw n).real A3 := by
    apply (measureReal_mono hsub).trans
    have h01 := measureReal_union_le (μ := p.markedCodeLaw κ n) (Prod.fst ⁻¹' A0) (Prod.fst ⁻¹' A1)
    have h23 := measureReal_union_le (μ := p.markedCodeLaw κ n) A2 (Prod.fst ⁻¹' A3)
    have htop := measureReal_union_le (μ := p.markedCodeLaw κ n)
      ((Prod.fst ⁻¹' A0)∪(Prod.fst ⁻¹' A1)) (A2∪(Prod.fst ⁻¹' A3))
    rw [p.markedCodeLaw_fst,p.markedCodeLaw_fst] at h01
    rw [p.markedCodeLaw_fst] at h23
    linarith
  change (p.codeLaw n).real A0 ≤ η/4 at hh
  change (p.codeLaw n).real A1 < η/4 at hK
  change (p.markedCodeLaw κ n).real A2 < η/4 at hbR
  change (p.codeLaw n).real A3 < η/4 at hkR
  exact hprob.trans_lt (by linarith)

end FKCRT.TreeCoding
end

end OAI
