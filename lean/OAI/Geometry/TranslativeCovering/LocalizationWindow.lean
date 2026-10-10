import OAI.Geometry.TranslativeCovering.LatticeAveraging

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal

universe u_1 u_2

namespace LocalizationWindow
open Set MeasureTheory LatticeAveraging
open scoped ENNReal Pointwise BigOperators

lemma periodic_integral_translate {n : ℕ} (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ]
    {F : Set (Space n)} (hF : IsAddFundamentalDomain Λ F volume)
    (f : Space n → ℝ≥0∞) (hp : ∀ (l : Λ) y,f (y+l.val) = f y) (x : Space n) :
    ∫⁻ y in F,f (y+x) = ∫⁻ y in F,f y := by
  let : Countable Λ := countable_of_Lindelof_of_discrete
  let : VAddInvariantMeasure Λ (Space n) volume :=
    inferInstanceAs (VAddInvariantMeasure Λ.toAddSubgroup (Space n) volume)
  have htrans : ∫⁻ y in F,f (x+y) = ∫⁻ y in x +ᵥ F,f y := by
    exact (measurePreserving_add_left volume x).setLIntegral_comp_emb
      (Homeomorph.addLeft x).measurableEmbedding f F
  have ht := hF.setLIntegral_eq (hF.vadd_of_comm x) f (fun l y => by
    change f (l.val+y) = f y
    rw [add_comm]; exact hp l y)
  simpa only [add_comm] using htrans.trans ht.symm

lemma periodic_average_translate {n : ℕ} (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ]
    {F : Set (Space n)} (hF : IsAddFundamentalDomain Λ F volume)
    (f : Space n → ℝ≥0∞) (hp : ∀ (l : Λ) y,f (y+l.val) = f y) (x : Space n) :
    ∫⁻ y,f (y+x) ∂uniformWindow F = ∫⁻ y,f y ∂uniformWindow F := by
  simp only [uniformWindow,lintegral_smul_measure]
  rw [periodic_integral_translate Λ hF f hp x]

lemma overlapping_windows {n : ℕ} (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ]
    {F B : Set (Space n)} (hF : IsAddFundamentalDomain Λ F volume)
    (hF0 : volume F ≠ 0) (hFtop : volume F ≠ ∞)
    (f : Space n → ℝ≥0∞) (hf : Measurable f)
    (hp : ∀ (l : Λ) y,f (y+l.val) = f y) :
    ∫⁻ z,(∫⁻ y in B,f (z+y)) ∂uniformWindow F =
      volume B * ∫⁻ z,f z ∂uniformWindow F := by
  let := probability_window hF0 hFtop
  have hh : Measurable (fun p : Space n × Space n => f (p.1+p.2)) :=
    hf.comp (measurable_fst.add measurable_snd)
  rw [lintegral_lintegral_swap hh.aemeasurable]
  simp_rw [periodic_average_translate Λ hF f hp]
  rw [lintegral_const,Measure.restrict_apply_univ,mul_comm]

lemma slide {Ω : Type u_1} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M Z : Ω → ℝ≥0∞) (hM : Measurable M) (hZ : Measurable Z) {N L : ℝ≥0∞}
    (hN : N ≠ 0) (hNtop : N ≠ ∞) (hL : L ≠ 0) (hLtop : L ≠ ∞)
    (heM : ∫⁻ z,M z ∂P ≤ N/40) (heZ : ∫⁻ z,Z z ∂P ≤ L/100) :
    ∃ z,M z ≤ N ∧ Z z ≤ L/2 := by
  have hint : ∫⁻ z,(M z/N+2*(Z z/L)) ∂P < 1 := by
    rw [lintegral_add_left (hM.div_const N),lintegral_const_mul _ (hZ.div_const L)]
    simp_rw [div_eq_mul_inv,lintegral_mul_const _ hM,lintegral_mul_const _ hZ]
    change (∫⁻ z,M z ∂P)/N+2*((∫⁻ z,Z z ∂P)/L) < 1
    have hm := ENNReal.div_le_div_right heM N
    have hz : 2*((∫⁻ z,Z z ∂P)/L) ≤ 2*((L/100)/L) := by gcongr
    have hmn : (N/40)/N = 1/40 := by
      rw [ENNReal.div_right_comm,ENNReal.div_self hN hNtop]
    have hln : (L/100)/L = 1/100 := by
      rw [ENNReal.div_right_comm,ENNReal.div_self hL hLtop]
    rw [hmn] at hm
    rw [hln] at hz
    exact (add_le_add hm hz).trans_lt (by
      apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      norm_num [ENNReal.toReal_mul,ENNReal.toReal_div])
  by_contra! hall
  have hone (z : Ω) : 1 ≤ M z/N+2*(Z z/L) := by
    by_cases hm : M z ≤ N
    · have hz := hall z hm
      have hz' : 1/2 < Z z/L := by
        apply (ENNReal.lt_div_iff_mul_lt (Or.inl hL) (Or.inl hLtop)).mpr
        simpa [div_eq_mul_inv,mul_comm] using hz
      have htwo : (2:ℝ≥0∞)*(1/2) ≤ 2*(Z z/L) := by gcongr
      have hh : (1:ℝ≥0∞) ≤ 2*(Z z/L) := by simpa only [one_div,ENNReal.mul_inv_cancel (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num : (2:ℝ≥0∞) ≠ ∞)] using htwo
      exact hh.trans (le_add_self)
    · have hh : 1 < M z/N := by
        apply (ENNReal.lt_div_iff_mul_lt (Or.inl hN) (Or.inl hNtop)).mpr
        simpa using lt_of_not_ge hm
      exact hh.le.trans (le_self_add)
  have hmono := lintegral_mono (μ := P) hone
  simp only [lintegral_const,measure_univ,mul_one] at hmono
  exact (not_lt_of_ge hmono) hint

lemma finite_occurrences {n : ℕ} {I : Type u_2} [Fintype I]
    (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ] (p : I → Space n)
    {B : Set (Space n)} (hB : Bornology.IsBounded B) :
    {q : I×Λ | p q.1+q.2.val ∈ B}.Finite := by
  have each (i : I) : {l : Λ | p i+l.val ∈ B}.Finite := by
    have hb : Bornology.IsBounded ((fun x : Space n => -p i+x) '' B) :=
      (isometry_add_left (-p i)).lipschitzWith.isBounded_image hB
    have hc : IsClosed (Λ : Set (Space n)) := AddSubgroup.isClosed_of_discreteTopology (U := Λ.toAddSubgroup)
    have hf := Metric.finite_isBounded_inter_isClosed
      (s := (Λ : Set (Space n))) DiscreteTopology.isDiscrete hb hc
    apply Set.Finite.of_injOn (f := fun l : Λ => l.val) (t := _ ∩ (Λ : Set (Space n)))
      ?_ (Subtype.val_injective.injOn) hf
    intro l hl
    refine ⟨⟨p i+l.val,hl,by simp⟩,l.property⟩
  apply (Set.finite_iUnion (fun i => (each i).image (fun l => (i,l)))).subset
  intro q hq
  exact Set.mem_iUnion.mpr ⟨q.1,⟨q.2,hq,rfl⟩⟩

end LocalizationWindow

end OAI
