import OAI.Probability.FKMaps.SpineBounds

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
namespace PlaneTree

lemma Profile.walkSum {t v a} (h : Profile t v a) :
    (incrementWord (t.degrees.take v)).sum=(a.map (fun z => (z.2:ℤ))).sum := by
  induction h with
  | root t => simp [incrementWord]
  | @child pre t post v a h ih =>
    rw [degrees_take_child pre t post h.bound.le]
    simp only [incrementWord,List.map_cons,List.sum_cons,List.map_append,List.sum_append]
    change ((pre++t::post).length:ℤ)-1+((incrementWord (forestDegrees pre)).sum+
      (incrementWord (t.degrees.take v)).sum) = _
    rw [(forest_properties pre).1,ih]
    simp only [List.length_append,List.length_cons,Nat.cast_add,Nat.cast_one]
    omega

end PlaneTree

lemma codeSpineSum_one {N : ℕ} (d : Code N) {v : ℕ} (hv : v≤N) :
    codeSpineSum (fun _ => 1) d v=(height d.val v:ℝ) := by
  unfold codeSpineSum recordSpineSum
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
  congr 1
  rw [record_count_reverse]
  apply Eq.trans (recordHeight_congr_prefix hv (fun k hk => integerSum_arrayStream_bridge ⟨d.val,d.property.1⟩ hk))
  exact (height_eq_recordHeight d.val hv).symm

lemma code_profile_height {N : ℕ} (d : Code N) {v a}
    (h : PlaneTree.Profile (PlaneTree.ofCode d) v a) : height d.val v=a.length := by
  have hv : v≤N := by have := h.bound; rw [PlaneTree.ofCode_size] at this; omega
  have hh := h.spineSum (fun _ => (1:ℝ))
  rw [← code_profileSum d _ hv,codeSpineSum_one d hv] at hh
  simpa using hh

lemma code_profile_walk {N : ℕ} (d : Code N) {v a}
    (h : PlaneTree.Profile (PlaneTree.ofCode d) v a) :
    walk d.val v=(a.map (fun z => (z.2:ℤ))).sum := by
  rw [← h.walkSum,PlaneTree.ofCode_degrees,PlaneTree.incrementWord,List.map_take]
  change walk d.val v=prefixSum _ v
  rw [List.map_ofFn]
  exact (degreeList_prefixSum d.val v).symm

/-- Mirror exploration counts the left siblings on exactly the same ancestral path. -/
lemma code_spine_mirror_identity {N : ℕ} (d : Code N) {v : ℕ} (hv : v<N) :
    ∃ w<N,height (PlaneTree.mirrored d).val w=height d.val v ∧
      codeSpineSum (fun z => (z.1:ℝ)) d v=
        (walk d.val v:ℝ)+(walk (PlaneTree.mirrored d).val w:ℝ)+height d.val v := by
  obtain ⟨a,ha⟩ := PlaneTree.exists_profile (PlaneTree.ofCode d) (by simpa [PlaneTree.ofCode_size] using hv)
  obtain ⟨w,hw⟩ := ha.mirrored
  rw [← PlaneTree.ofCode_mirrored] at hw
  refine ⟨w,by have := hw.bound; simpa [PlaneTree.ofCode_size] using this,?_,?_⟩
  · rw [code_profile_height _ hw,code_profile_height _ ha,List.length_map]
  · rw [code_profileSum d _ hv.le,ha.spineSum,code_profile_walk _ ha,
      code_profile_walk _ hw,code_profile_height _ ha]
    have hs : ∀ z∈a,(z.1:ℝ)=(z.2:ℝ)+((PlaneTree.flipSlot z).2:ℝ)+1 := by
      intro z hz
      have := ha.slots z hz
      dsimp [PlaneTree.flipSlot]
      exact_mod_cast (show z.1=z.2+(z.1-1-z.2)+1 by omega)
    simp only [List.map_map]
    push_cast
    simp only [List.map_map,Function.comp_def,Int.cast_natCast]
    clear ha hw
    induction a with
    | nil => simp
    | cons z a ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      have he := hs z (by simp)
      have hi := ih (fun z hz => hs z (by simp [hz]))
      linarith

/-- Uniform path sum of offspring degrees needs only the original second moment.
This is the deterministic two-sided exploration truncation bound, not a third-moment estimate. -/
theorem CriticalEvenOffspring.uniform_degree_spine_limit (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun n => (p.codeLaw n).real {d | ∃ v<2*n+1,
      ε*Real.sqrt ((2*n+1:ℕ):ℝ)< |codeSpineSum (fun z => (z.1:ℝ)) d v-
        (p.variance+1)*height d.val v|}) atTop (𝓝 0) := by
  have ht := p.uniform_height_error_limit hB (half_pos hε)
  apply squeeze_zero (fun _ => measureReal_nonneg) _ (by simpa only [zero_add] using ht.add ht)
  intro n
  let N := 2*n+1
  let E := {d : Code N | ∃ j<N, (ε/2)*Real.sqrt (N:ℝ)<
    |(walk d.val j:ℝ)-(p.variance/2)*height d.val j|}
  have hsub : {d : Code N | ∃ v<N,ε*Real.sqrt (N:ℝ)<
      |codeSpineSum (fun z => (z.1:ℝ)) d v-(p.variance+1)*height d.val v|}
      ⊆ E∪(PlaneTree.mirrorEquiv N ⁻¹' E) := by
    rintro d ⟨v,hv,hbad⟩
    by_contra hn
    have hn' := not_or.mp hn
    obtain ⟨w,hw,hh,hs⟩ := code_spine_mirror_identity d hv
    have h1 : |(walk d.val v:ℝ)-(p.variance/2)*height d.val v|≤(ε/2)*Real.sqrt (N:ℝ) := by
      by_contra hc; exact hn'.1 ⟨v,hv,lt_of_not_ge hc⟩
    have h2 : |(walk (PlaneTree.mirrored d).val w:ℝ)-(p.variance/2)*height d.val v|≤
        (ε/2)*Real.sqrt (N:ℝ) := by
      by_contra hc
      apply hn'.2
      refine ⟨w,hw,?_⟩
      change (ε/2)*Real.sqrt (N:ℝ)<
        |(walk (PlaneTree.mirrored d).val w:ℝ)-(p.variance/2)*height (PlaneTree.mirrored d).val w|
      rw [hh]
      exact lt_of_not_ge hc
    rw [hs] at hbad
    have he : (walk d.val v:ℝ)+(walk (PlaneTree.mirrored d).val w:ℝ)+height d.val v-
      (p.variance+1)*height d.val v = ((walk d.val v:ℝ)-(p.variance/2)*height d.val v)+
      ((walk (PlaneTree.mirrored d).val w:ℝ)-(p.variance/2)*height d.val v) := by ring
    rw [he] at hbad
    have := abs_add_le ((walk d.val v:ℝ)-(p.variance/2)*height d.val v)
      ((walk (PlaneTree.mirrored d).val w:ℝ)-(p.variance/2)*height d.val v)
    linarith
  calc
    _ ≤ (p.codeLaw n).real (E∪(PlaneTree.mirrorEquiv N ⁻¹' E)) := measureReal_mono hsub
    _ ≤ (p.codeLaw n).real E+(p.codeLaw n).real (PlaneTree.mirrorEquiv N ⁻¹' E) := measureReal_union_le _ _
    _ = _ := by rw [(PlaneTree.mirrorEquiv_preserving p n).measureReal_preimage (Set.to_countable E).measurableSet.nullMeasurableSet]

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

def spineTail (m : ℕ) (z : ℕ×ℕ) : ℝ := if m < z.1 then (z.1:ℝ) else 0
def spineTrunc (m : ℕ) (b : ℕ×ℕ → ℝ) (z : ℕ×ℕ) : ℝ := if z.1 ≤ m then b z else 0

lemma spineTail_nonneg (m : ℕ) (z : ℕ×ℕ) : 0 ≤ spineTail m z := by
  unfold spineTail; split_ifs  <;>  positivity

lemma spineTail_le (m : ℕ) (z : ℕ×ℕ) : spineTail m z ≤ z.1 := by
  unfold spineTail; split_ifs
  · exact le_rfl
  · positivity

lemma spineTrunc_bound (m : ℕ) (b : ℕ×ℕ → ℝ) (hb : ∀ z,|b z| ≤ z.1) (z : ℕ×ℕ) :
    |spineTrunc m b z| ≤ m := by
  unfold spineTrunc
  split_ifs with h
  · exact (hb z).trans (by exact_mod_cast h)
  · simp

lemma spineTrunc_tail_bound (m : ℕ) (b : ℕ×ℕ → ℝ) (hb : ∀ z,|b z| ≤ z.1) (z : ℕ×ℕ) :
    |b z-spineTrunc m b z| ≤ spineTail m z := by
  by_cases h : z.1 ≤ m
  · simp [spineTrunc,spineTail,h,not_lt.mpr h]
  · simp [spineTrunc,spineTail,h,lt_of_not_ge h,hb]

lemma CriticalEvenOffspring.spine_integrable_dom (p : CriticalEvenOffspring) (b : ℕ×ℕ → ℝ)
    (hb : ∀ z,|b z| ≤ z.1) : Integrable b p.spineLaw := by
  exact p.spine_integrable_fst.mono' (measurable_of_countable b).aestronglyMeasurable
    (ae_of_all _ (fun z =>  by simpa only [Real.norm_eq_abs] using hb z))

lemma CriticalEvenOffspring.spine_tail_integral_tendsto (p : CriticalEvenOffspring) :
    Tendsto (fun m =>  ∫ z,spineTail m z ∂p.spineLaw) atTop (𝓝 0) := by
  have hh := tendsto_integral_of_dominated_convergence (μ := p.spineLaw) (f := fun _ => (0:ℝ)) (fun z : ℕ×ℕ =>  (z.1:ℝ))
    (fun m =>  (measurable_of_countable (spineTail m)).aestronglyMeasurable)
    p.spine_integrable_fst
    (fun m =>  ae_of_all _ (fun z =>  by simpa only [Real.norm_eq_abs,abs_of_nonneg (spineTail_nonneg m z)] using spineTail_le m z))
    (ae_of_all _ (fun z =>  by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop z.1] with m hm
      simp [spineTail,not_lt.mpr hm]))
  simpa using hh

lemma codeSpineSum_sub {N : ℕ} (d : Code N) (b c : ℕ×ℕ → ℝ) (v : ℕ) :
    codeSpineSum (fun z =>  b z-c z) d v=codeSpineSum b d v-codeSpineSum c d v := by
  simp [codeSpineSum,recordSpineSum,Finset.sum_sub_distrib]

lemma codeSpineSum_abs_le {N : ℕ} (d : Code N) (b c : ℕ×ℕ → ℝ) (v : ℕ)
    (h : ∀ z,|b z| ≤ c z) : |codeSpineSum b d v| ≤ codeSpineSum c d v := by
  unfold codeSpineSum recordSpineSum
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun _ _ =>  h _))

lemma CriticalEvenOffspring.spineTrunc_integral_error (p : CriticalEvenOffspring)
    (m : ℕ) (b : ℕ×ℕ → ℝ) (hb : ∀ z,|b z| ≤ z.1) :
    |(∫ z,b z ∂p.spineLaw)-(∫ z,spineTrunc m b z ∂p.spineLaw)| ≤ ∫ z,spineTail m z ∂p.spineLaw := by
  have hi := p.spine_integrable_dom b hb
  have hj := p.spine_integrable_dom (spineTrunc m b) (fun z =>  by
    unfold spineTrunc; split_ifs  <;>  simp [hb z])
  rw [← integral_sub hi hj]
  apply (abs_integral_le_integral_abs).trans
  apply integral_mono (hi.sub hj).abs (p.spine_integrable_dom (spineTail m) (fun z =>  by
    rw [abs_of_nonneg (spineTail_nonneg m z)]; exact spineTail_le m z))
  exact spineTrunc_tail_bound m b hb

lemma spineTail_eq (m : ℕ) : spineTail m=(fun z =>  (z.1:ℝ)-spineTrunc m (fun z =>  (z.1:ℝ)) z) := by
  funext z
  by_cases h : z.1 ≤ m  <;>  simp [spineTail,spineTrunc,h,not_lt.mpr,lt_of_not_ge]

lemma spine_tail_control {N : ℕ} (p : CriticalEvenOffspring) (d : Code N)
    (b : ℕ×ℕ → ℝ) (hb : ∀ z,|b z| ≤ z.1) (m v : ℕ) :
    |codeSpineSum b d v-(∫ z,b z ∂p.spineLaw)*height d.val v|  ≤ 
      |codeSpineSum (spineTrunc m b) d v-(∫ z,spineTrunc m b z ∂p.spineLaw)*height d.val v|+
      |codeSpineSum (fun z =>  (z.1:ℝ)) d v-(p.variance+1)*height d.val v|+
      |codeSpineSum (spineTrunc m (fun z =>  (z.1:ℝ))) d v-
        (∫ z,spineTrunc m (fun z =>  (z.1:ℝ)) z ∂p.spineLaw)*height d.val v|+
      2*(∫ z,spineTail m z ∂p.spineLaw)*height d.val v := by
  let h : ℝ := height d.val v
  have h0 : 0 ≤ h := by dsimp [h]; positivity
  have hd := codeSpineSum_abs_le d (fun z =>  b z-spineTrunc m b z) (spineTail m) v (spineTrunc_tail_bound m b hb)
  rw [codeSpineSum_sub] at hd
  have he := p.spineTrunc_integral_error m b hb
  have hi : (∫ z,spineTail m z ∂p.spineLaw)=p.variance+1-
      ∫ z,spineTrunc m (fun z =>  (z.1:ℝ)) z ∂p.spineLaw := by
    rw [spineTail_eq,integral_sub p.spine_integrable_fst (p.spine_integrable_dom _ (fun z =>  by
      unfold spineTrunc; split_ifs  <;>  simp))]
    rw [p.spine_integral_fst]
  have hs : codeSpineSum (spineTail m) d v=codeSpineSum (fun z =>  (z.1:ℝ)) d v-
      codeSpineSum (spineTrunc m (fun z =>  (z.1:ℝ))) d v := by
    rw [spineTail_eq,codeSpineSum_sub]
  have he1 := abs_add_le (codeSpineSum (spineTrunc m b) d v-(∫ z,spineTrunc m b z ∂p.spineLaw)*h)
    ((codeSpineSum b d v-codeSpineSum (spineTrunc m b) d v)-
      ((∫ z,b z ∂p.spineLaw)-(∫ z,spineTrunc m b z ∂p.spineLaw))*h)
  have he2 := abs_sub (codeSpineSum b d v-codeSpineSum (spineTrunc m b) d v)
      (((∫ z,b z ∂p.spineLaw)-(∫ z,spineTrunc m b z ∂p.spineLaw))*h)
  rw [abs_mul,abs_of_nonneg h0] at he2
  have he3 := mul_le_mul_of_nonneg_right he h0
  have hsum : codeSpineSum (spineTrunc m b) d v-(∫ z,spineTrunc m b z ∂p.spineLaw)*h+
    ((codeSpineSum b d v-codeSpineSum (spineTrunc m b) d v)-
      ((∫ z,b z ∂p.spineLaw)-(∫ z,spineTrunc m b z ∂p.spineLaw))*h)=
    codeSpineSum b d v-(∫ z,b z ∂p.spineLaw)*h := by ring
  rw [hs] at hd
  rw [hsum] at he1
  have hK := le_abs_self (codeSpineSum (fun z =>  (z.1:ℝ)) d v-(p.variance+1)*h)
  have hk := neg_le_abs (codeSpineSum (spineTrunc m (fun z =>  (z.1:ℝ))) d v-
    (∫ z,spineTrunc m (fun z =>  (z.1:ℝ)) z ∂p.spineLaw)*h)
  change _ ≤ _+_+_+2*(∫ z,spineTail m z ∂p.spineLaw)*h
  nlinarith

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

/-- The full finite-variance all-vertex ancestral LLN for any deterministic slot label
bounded in absolute value by the offspring count. No third moment or exponential upper tail. -/
theorem CriticalEvenOffspring.uniform_integrable_spine_limit (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (b : ℕ×ℕ → ℝ) (hb : ∀ z,|b z| ≤ z.1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n =>  (p.codeLaw n).real {d | ∃ v < 2*n+1,
      ε*Real.sqrt ((2*n+1:ℕ):ℝ) <  |codeSpineSum b d v-(∫ z,b z ∂p.spineLaw)*height d.val v|})
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
  have hbR := p.uniform_bounded_spine_limit hB (spineTrunc m b)
    (R := (m:ℝ)+1) (by positivity) (fun z =>  (spineTrunc_bound m b hb z).trans (by linarith))
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
  let A2 := {d : Code N | ∃ v ≤ N,(ε/4)*s < 
    |codeSpineSum (spineTrunc m b) d v-(∫ z,spineTrunc m b z ∂p.spineLaw)*height d.val v|}
  let A3 := {d : Code N | ∃ v ≤ N,(ε/4)*s < 
    |codeSpineSum (spineTrunc m (fun z =>  (z.1:ℝ))) d v-
      (∫ z,spineTrunc m (fun z =>  (z.1:ℝ)) z ∂p.spineLaw)*height d.val v|}
  have hsub : {d : Code N | ∃ v < N,ε*s < 
      |codeSpineSum b d v-(∫ z,b z ∂p.spineLaw)*height d.val v|}⊆(A0∪A1)∪(A2∪A3) := by
    rintro d ⟨v,hv,hbad⟩
    by_contra hn
    simp only [Set.mem_union,not_or] at hn
    have hhv : (height d.val v:ℝ) ≤ C*s := by
      by_contra h; exact hn.1.1 ⟨v,hv.le,lt_of_not_ge h⟩
    have hKv : |codeSpineSum (fun z =>  (z.1:ℝ)) d v-(p.variance+1)*height d.val v| ≤ (ε/4)*s := by
      by_contra h; exact hn.1.2 ⟨v,hv,lt_of_not_ge h⟩
    have hbv : |codeSpineSum (spineTrunc m b) d v-
        (∫ z,spineTrunc m b z ∂p.spineLaw)*height d.val v| ≤ (ε/4)*s := by
      by_contra h; exact hn.2.1 ⟨v,hv.le,lt_of_not_ge h⟩
    have hkv : |codeSpineSum (spineTrunc m (fun z =>  (z.1:ℝ))) d v-
        (∫ z,spineTrunc m (fun z =>  (z.1:ℝ)) z ∂p.spineLaw)*height d.val v| ≤ (ε/4)*s := by
      by_contra h; exact hn.2.2 ⟨v,hv.le,lt_of_not_ge h⟩
    have ht : 2*(∫ z,spineTail m z ∂p.spineLaw)*height d.val v ≤ (ε/4)*s := by
      have hm' : (∫ z,spineTail m z ∂p.spineLaw)*(8*C) ≤ ε := (le_div_iff₀ (by positivity)).mp hm.le
      have hs : 0 ≤ s := Real.sqrt_nonneg _
      have h1 := mul_le_mul_of_nonneg_left hhv (show 0 ≤ 2*(∫ z,spineTail m z ∂p.spineLaw) by positivity)
      have h2 := mul_le_mul_of_nonneg_right hm' hs
      nlinarith
    have hc := spine_tail_control p d b hb m v
    linarith
  have hprob : (p.codeLaw n).real {d : Code N | ∃ v < N,ε*s < 
        |codeSpineSum b d v-(∫ z,b z ∂p.spineLaw)*height d.val v|}  ≤ 
      (p.codeLaw n).real A0+(p.codeLaw n).real A1+(p.codeLaw n).real A2+(p.codeLaw n).real A3 := by
    apply (measureReal_mono hsub).trans
    have h01 := measureReal_union_le (μ := p.codeLaw n) A0 A1
    have h23 := measureReal_union_le (μ := p.codeLaw n) A2 A3
    have htop := measureReal_union_le (μ := p.codeLaw n) (A0∪A1) (A2∪A3)
    linarith
  change (p.codeLaw n).real A0 ≤ η/4 at hh
  change (p.codeLaw n).real A1 < η/4 at hK
  change (p.codeLaw n).real A2 < η/4 at hbR
  change (p.codeLaw n).real A3 < η/4 at hkR
  exact hprob.trans_lt (by linarith)

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

abbrev SpineRecords {N : ℕ} (d : Code N) (v : ℕ) :=
  ↥(weakRecords (integerSum (reverseFirst v (arrayStream (codeEmbedding N d)))) v)

def spineRecordType {N : ℕ} (d : Code N) (v : ℕ) (t : SpineRecords d v) : ℕ×ℕ :=
  recordTypeAt (reverseFirst v (arrayStream (codeEmbedding N d))) t.val

lemma spineRecord_bounds {N : ℕ} (d : Code N) (v : ℕ) (t : SpineRecords d v) :
    1 ≤ t.val ∧ t.val ≤ v := by
  have h := (mem_weakRecords _ _ _).mp t.property
  exact ⟨h.1,h.2.1⟩

def spineRecordVertex {N : ℕ} (d : Code N) {v : ℕ} (hv : v ≤ N) (t : SpineRecords d v) : Fin N :=
  ⟨v-t.val,by have h := spineRecord_bounds d v t; omega⟩

lemma spineRecordVertex_injective {N : ℕ} (d : Code N) {v : ℕ} (hv : v ≤ N) :
    Function.Injective (spineRecordVertex d hv) := by
  intro t u he
  have ht := spineRecord_bounds d v t
  have hu := spineRecord_bounds d v u
  apply Subtype.ext
  have h := congrArg Fin.val he
  dsimp [spineRecordVertex] at h
  omega

lemma spineRecordType_fst {N : ℕ} (d : Code N) {v : ℕ} (hv : v ≤ N) (t : SpineRecords d v) :
    (spineRecordType d v t).1=(d.val (spineRecordVertex d hv t)).val := by
  have ht := spineRecord_bounds d v t
  have hlt : t.val-1 < v := by omega
  have he : v-1-(t.val-1)=v-t.val := by omega
  simp [spineRecordType,recordTypeAt,reverseFirst,reverseIndex,hlt,he,arrayStream,
    show v-t.val < N by omega,codeEmbedding,bridgeEmbedding,spineRecordVertex]
  rfl

lemma spineRecords_card {N : ℕ} (d : Code N) {v : ℕ} (hv : v ≤ N) :
    Fintype.card (SpineRecords d v)=height d.val v := by
  have h := codeSpineSum_one d hv
  simp only [codeSpineSum,recordSpineSum,Finset.sum_const,nsmul_eq_mul,mul_one] at h
  rw [Fintype.card_coe]
  exact_mod_cast h

variable {A : Type*} [MeasurableSpace A]

def codeMarkLaw (κ : ℕ → Measure A) {N : ℕ} (d : Code N) : Measure (Fin N → A) :=
  Measure.pi (fun i => κ (d.val i).val)

instance codeMarkLaw_probability (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)]
    {N : ℕ} (d : Code N) : IsProbabilityMeasure (codeMarkLaw κ d) := by
  unfold codeMarkLaw; infer_instance

def markedSpineSum {N : ℕ} (b : (ℕ×ℕ) → A → ℝ) (d : Code N) {v : ℕ}
    (hv : v ≤ N) (a : Fin N → A) : ℝ :=
  ∑ t : SpineRecords d v,b (spineRecordType d v t) (a (spineRecordVertex d hv t))

omit [MeasurableSpace A] in
lemma markedSpineSum_deterministic {N : ℕ} (b : ℕ×ℕ → ℝ) (d : Code N) {v : ℕ}
    (hv : v ≤ N) (a : Fin N → A) :
    markedSpineSum (fun z _ => b z) d hv a=codeSpineSum b d v := by
  unfold markedSpineSum codeSpineSum recordSpineSum
  exact Finset.sum_coe_sort _ (fun t => b (recordTypeAt (reverseFirst v (arrayStream (codeEmbedding N d))) t))

lemma measurable_markedSpineSum {N : ℕ} (b : (ℕ×ℕ) → A → ℝ)
    (hb : ∀ z,Measurable (b z)) (d : Code N) {v : ℕ} (hv : v ≤ N) :
    Measurable (markedSpineSum b d hv) := by
  exact Finset.measurable_sum _ (fun t _ => (hb _).comp (measurable_pi_apply _))

/-- Conditional on the actual tree, distinct ancestors carry independent correctly sampled marks. -/
lemma markedSpine_iIndep {N : ℕ} (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)]
    (d : Code N) {v : ℕ} (hv : v ≤ N) :
    iIndepFun (fun t : SpineRecords d v => fun a : Fin N → A => a (spineRecordVertex d hv t))
      (codeMarkLaw κ d) := by
  exact (iIndepFun_pi (μ := fun i => κ (d.val i).val)
    (X := fun _ => id) (fun _ => measurable_id.aemeasurable)).precomp (spineRecordVertex_injective d hv)

lemma markedSpine_hasLaw {N : ℕ} (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)]
    (d : Code N) {v : ℕ} (hv : v ≤ N) (t : SpineRecords d v) :
    HasLaw (fun a : Fin N → A => a (spineRecordVertex d hv t))
      (κ (spineRecordType d v t).1) (codeMarkLaw κ d) := by
  rw [spineRecordType_fst d hv t]
  exact (measurePreserving_eval (fun i => κ (d.val i).val) _).hasLaw

/-- Bounded random marks concentrate round their conditional ancestral means. -/
lemma markedSpine_deviation {N : ℕ} (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)]
    (b : (ℕ×ℕ) → A → ℝ) (hb : ∀ z,Measurable (b z)) {R : ℝ}
    (hbound : ∀ z a,|b z a| ≤ R) (d : Code N) {v : ℕ} (hv : v ≤ N)
    {r : ℝ} (hr : 0 ≤ r) :
    (codeMarkLaw κ d).real {a | r ≤ |markedSpineSum b d hv a-
      codeSpineSum (fun z => ∫ a,b z a ∂κ z.1) d v|} ≤
        2*Real.exp (-r^2/(2*(height d.val v)*R^2)) := by
  let Y : SpineRecords d v → (Fin N → A) → ℝ := fun t a =>
    b (spineRecordType d v t) (a (spineRecordVertex d hv t))-
      ∫ a,b (spineRecordType d v t) a ∂κ (spineRecordType d v t).1
  have hind : iIndepFun Y (codeMarkLaw κ d) :=
    (markedSpine_iIndep κ d hv).comp (fun t a => b (spineRecordType d v t) a-
      ∫ a,b (spineRecordType d v t) a ∂κ (spineRecordType d v t).1)
      (fun t => (hb _).sub measurable_const)
  have hG : ∀ t,HasSubgaussianMGF (Y t) ((‖(R:ℝ)-(-R)‖₊/2)^2) (codeMarkLaw κ d) := by
    intro t
    have hh := hasSubgaussianMGF_of_mem_Icc (μ := codeMarkLaw κ d)
      ((hb _).comp (measurable_pi_apply _)).aemeasurable
      (ae_of_all _ (fun a => abs_le.mp (hbound (spineRecordType d v t) (a (spineRecordVertex d hv t)))))
    have he := (markedSpine_hasLaw κ d hv t).integral_comp (hb (spineRecordType d v t)).aestronglyMeasurable
    rw [he] at hh
    simpa only [Function.comp_def,Y] using hh
  have hp := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (s := Finset.univ) hind (fun t _ => hG t) hr
  have hn := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (s := Finset.univ)
    (hind.comp (fun _ x => -x) (fun _ => measurable_neg)) (fun t _ => (hG t).neg) hr
  have he (a : Fin N → A) : markedSpineSum b d hv a-
      codeSpineSum (fun z => ∫ a,b z a ∂κ z.1) d v=∑ t,Y t a := by
    rw [← markedSpineSum_deterministic (A := A) _ d hv a]
    unfold markedSpineSum
    exact (Finset.sum_sub_distrib _ _).symm
  have hsub : {a : Fin N → A | r ≤ |markedSpineSum b d hv a-
      codeSpineSum (fun z => ∫ a,b z a ∂κ z.1) d v|} ⊆
      {a | r ≤ ∑ t,Y t a} ∪ {a | r ≤ ∑ t,-Y t a} := by
    intro a ha
    change r ≤ |_| at ha
    rw [he] at ha
    rcases le_abs.mp ha with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa only [Set.mem_ofPred_eq,Finset.sum_neg_distrib] using h)
  have hle := (measureReal_mono (μ := codeMarkLaw κ d) hsub).trans (measureReal_union_le _ _)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hp hn
  push_cast at hp hn
  simp only [Real.norm_eq_abs,div_pow,sq_abs,show (R- -R)^2/2^2=R^2 by ring,
    spineRecords_card d hv,Function.comp_def] at hp hn
  simp only [mul_assoc]
  linarith

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

variable {A : Type*} [MeasurableSpace A]

def codeMarkKernel (κ : ℕ → Measure A) (N : ℕ) : Kernel (Code N) (Fin N → A) :=
  ⟨codeMarkLaw κ,measurable_of_countable _⟩

instance codeMarkKernel_markov (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)] (N : ℕ) :
    IsMarkovKernel (codeMarkKernel κ N) := ⟨fun _ => codeMarkLaw_probability _ _⟩

def CriticalEvenOffspring.markedCodeLaw (p : CriticalEvenOffspring) (κ : ℕ → Measure A) (n : ℕ) :
    Measure (Code (2*n+1) × (Fin (2*n+1) → A)) := p.codeLaw n ⊗ₘ codeMarkKernel κ (2*n+1)

instance CriticalEvenOffspring.markedCodeLaw_probability (p : CriticalEvenOffspring)
    (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)] (n : ℕ) :
    IsProbabilityMeasure (p.markedCodeLaw κ n) := by unfold CriticalEvenOffspring.markedCodeLaw; infer_instance

lemma compProd_real_bound {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (κ : Kernel α β) [IsMarkovKernel κ]
    {E : Set (α×β)} (hE : MeasurableSet E) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x,(κ x).real (Prod.mk x ⁻¹' E) ≤ C) : (μ ⊗ₘ κ).real E ≤ C := by
  have he : (μ ⊗ₘ κ) E ≤ ENNReal.ofReal C := by
    rw [Measure.compProd_apply hE]
    calc
      _ ≤ ∫⁻ _,ENNReal.ofReal C ∂μ := lintegral_mono (fun x => by
        rw [← ofReal_measureReal]
        exact ENNReal.ofReal_le_ofReal (hb x))
      _ = _ := by simp
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans_eq (ENNReal.toReal_ofReal hC)

lemma CriticalEvenOffspring.markedCodeLaw_fst (p : CriticalEvenOffspring)
    (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)] (n : ℕ) (E : Set (Code (2*n+1))) :
    (p.markedCodeLaw κ n).real (Prod.fst ⁻¹' E)=(p.codeLaw n).real E := by
  have hh : Prod.fst ⁻¹' E=E×ˢ(Set.univ : Set (Fin (2*n+1) → A)) := by ext x; simp
  unfold Measure.real
  rw [hh,CriticalEvenOffspring.markedCodeLaw,Measure.compProd_apply_prod (Set.to_countable E).measurableSet MeasurableSet.univ]
  simp

lemma measurable_marked_spine_joint {N : ℕ} (b : (ℕ×ℕ) → A → ℝ) (hb : ∀ z,Measurable (b z))
    {v : ℕ} (hv : v ≤ N) :
    Measurable (fun x : Code N × (Fin N → A) => markedSpineSum b x.1 hv x.2) :=
  measurable_from_prod_countable_right (fun d => measurable_markedSpineSum b hb d hv)

omit [MeasurableSpace A] in
lemma markedSpineSum_zero_height {N : ℕ} (b : (ℕ×ℕ) → A → ℝ) (d : Code N)
    {v : ℕ} (hv : v ≤ N) (hh : height d.val v=0) (a : Fin N → A) :
    markedSpineSum b d hv a=0 := by
  have hc : Fintype.card (SpineRecords d v)=0 := (spineRecords_card d hv).trans hh
  let : IsEmpty (SpineRecords d v) := Fintype.card_eq_zero_iff.mp hc
  simp [markedSpineSum]

lemma marked_short_spine_bound {N : ℕ} (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)]
    (b : (ℕ×ℕ) → A → ℝ) (hb : ∀ z,Measurable (b z)) {R : ℝ} (hR : 0 < R)
    (hbound : ∀ z a,|b z a| ≤ R) (d : Code N) (K : ℕ) {r : ℝ} (hr : 0 < r) :
    (codeMarkLaw κ d).real {a | ∃ v : Fin (N+1),height d.val v.val ≤ K ∧
      r ≤ |markedSpineSum b d (Nat.le_of_lt_succ v.isLt) a-
        codeSpineSum (fun z => ∫ a,b z a ∂κ z.1) d v.val|} ≤
      (N+1:ℝ)*2*Real.exp (-r^2/(2*K*R^2)) := by
  let E : Fin (N+1) → Set (Fin N → A) := fun v => {a | height d.val v.val ≤ K ∧
    r ≤ |markedSpineSum b d (Nat.le_of_lt_succ v.isLt) a-
      codeSpineSum (fun z => ∫ a,b z a ∂κ z.1) d v.val|}
  have he : {a | ∃ v : Fin (N+1),height d.val v.val ≤ K ∧
      r ≤ |markedSpineSum b d (Nat.le_of_lt_succ v.isLt) a-
        codeSpineSum (fun z => ∫ a,b z a ∂κ z.1) d v.val|}=⋃ v,E v := by ext a; simp [E]
  rw [he]
  apply (measureReal_iUnion_fintype_le E).trans
  calc
    _ ≤ ∑ _ : Fin (N+1),2*Real.exp (-r^2/(2*K*R^2)) := Finset.sum_le_sum (by
      intro v _
      by_cases hh : height d.val v.val ≤ K
      · by_cases h0 : height d.val v.val=0
        · have hE : E v=∅ := by
            ext a
            have hz := markedSpineSum_zero_height b d (Nat.le_of_lt_succ v.isLt) h0 a
            have hm := markedSpineSum_zero_height (fun z (_ : A) => ∫ a,b z a ∂κ z.1) d
              (Nat.le_of_lt_succ v.isLt) h0 a
            rw [markedSpineSum_deterministic] at hm
            simp [E,hz,hm,not_le.mpr hr]
          rw [hE,measureReal_empty]
          positivity
        · have hpos : 0 < (height d.val v.val:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
          have hKpos : 0 < (K:ℝ) := hpos.trans_le (by exact_mod_cast hh)
          have hm := markedSpine_deviation κ b hb hbound d (Nat.le_of_lt_succ v.isLt) hr.le
          have hes : E v={a | r ≤ |markedSpineSum b d (Nat.le_of_lt_succ v.isLt) a-
            codeSpineSum (fun z => ∫ a,b z a ∂κ z.1) d v.val|} := by ext a; simp [E,hh]
          rw [hes]
          apply hm.trans
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
          rw [neg_div,neg_div]
          apply neg_le_neg
          apply div_le_div_of_nonneg_left (sq_nonneg r) (by positivity)
          have hle : (height d.val v.val:ℝ) ≤ K := by exact_mod_cast hh
          nlinarith [mul_le_mul_of_nonneg_right hle (sq_nonneg R)]
      · have hE : E v=∅ := by ext a; simp [E,hh]
        rw [hE,measureReal_empty]
        positivity)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]; ring

end FKCRT.TreeCoding
end

end OAI
