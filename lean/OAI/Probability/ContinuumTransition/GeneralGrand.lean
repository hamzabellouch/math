import OAI.Probability.ContinuumTransition.ExactAssignments

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

abbrev ConfigFamily := (ι : Type) → [Fintype ι] → (ι → Space) → ℝ

def RelabelInvariant (F : ConfigFamily) : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (e : ι ≃ κ) (x : κ → Space),
    F ι (x ∘ e) = F κ x

noncomputable def familyIntegral (F : ConfigFamily) (A : Set Space)
    (ι : Type) [Fintype ι] : ℝ :=
  ∫ x in {x : ι → Space | ∀ i, x i ∈ A}, F ι x

noncomputable def familyTerm (F : ConfigFamily) (A : Set Space) (n : ℕ) : ℝ :=
  familyIntegral F A (Fin n)/(n.factorial : ℝ)

noncomputable def grandIntegral (F : ConfigFamily) (A : Set Space) : ℝ :=
  ∑' n : ℕ, familyTerm F A n

theorem familyIntegral_relabel (F : ConfigFamily) (hF : RelabelInvariant F)
    (A : Set Space) {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    familyIntegral F A ι = familyIntegral F A κ := by
  let p : (ι → Space) ≃ᵐ (κ → Space) := MeasurableEquiv.piCongrLeft (fun _ : κ => Space) e
  have hp : MeasurePreserving p volume volume := by
    simpa only [volume_pi] using measurePreserving_piCongrLeft (fun _ : κ => volume) e
  have hpx (x : ι → Space) : p x = x ∘ e.symm := by
    funext i
    simpa only [p, Equiv.apply_symm_apply, Function.comp_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply e (β := fun _ : κ => Space) x (e.symm i))
  have heq := hp.setIntegral_preimage_emb p.measurableEmbedding (F κ)
    {x : κ → Space | ∀ i, x i ∈ A}
  have hpre : p ⁻¹' {x : κ → Space | ∀ i, x i ∈ A} =
      {x : ι → Space | ∀ i, x i ∈ A} := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, hpx, Function.comp_apply]
    constructor
    · intro hh i
      simpa only [Equiv.symm_apply_apply] using hh (e i)
    · intro hh i
      exact hh (e.symm i)
  rw [hpre] at heq
  simpa only [familyIntegral, hpx, hF κ ι e.symm] using heq

theorem familyIntegral_eq_Fin (F : ConfigFamily) (hF : RelabelInvariant F)
    (A : Set Space) (ι : Type) [Fintype ι] :
    familyIntegral F A ι = familyIntegral F A (Fin (Fintype.card ι)) :=
  familyIntegral_relabel F hF A (Fintype.equivFin ι)

theorem integral_binary_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    {A B : Set Space} (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    {F : (ι → Space) → ℝ} (a b : ℕ → ℝ)
    (hF : IntegrableOn F {x : ι → Space | ∀ i, x i ∈ A ∪ B})
    (hbound : ∀ s : Finset ι, (∫ x in binaryRegion A B s, F x) ≤
      a s.card*b (Fintype.card ι-s.card)) :
    (∫ x in {x : ι → Space | ∀ i, x i ∈ A ∪ B}, F x) ≤
      ∑ k ∈ Finset.range (Fintype.card ι+1),
        ((Fintype.card ι).choose k : ℝ)*a k*b (Fintype.card ι-k) := by
  rw [show volume = Measure.pi (fun _ : ι => (volume : Measure Space)) by exact volume_pi]
  rw [integral_binary_assignments_eq volume hA hB hd (by simpa only [← volume_pi] using hF)]
  calc
    _ ≤ ∑ s : Finset ι, a s.card*b (Fintype.card ι-s.card) := by
      apply Finset.sum_le_sum
      intro s _
      simpa only [← volume_pi] using hbound s
    _ = _ := by
      have hh := Finset.sum_powerset_apply_card (fun k => a k*b (Fintype.card ι-k))
        (x := (Finset.univ : Finset ι))
      simpa only [Finset.powerset_univ, Finset.card_univ, nsmul_eq_mul, mul_assoc] using hh

theorem factorial_binomial_sum (a b : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range (N+1), (N.choose k : ℝ)*a k*b (N-k))/(N.factorial : ℝ) =
      ∑ k ∈ Finset.range (N+1), (a k/(k.factorial : ℝ))*(b (N-k)/((N-k).factorial : ℝ)) := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.cast_choose ℝ (by have := Finset.mem_range.mp hk; omega)]
  have hN : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  field_simp

theorem familyTerm_nonneg (F : ConfigFamily) (A : Set Space)
    (hF : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x) (n : ℕ) :
    0 ≤ familyTerm F A n := by
  apply div_nonneg (integral_nonneg (hF (Fin n)))
  positivity

theorem integrableOn_family_of_bound (F : ConfigFamily) {A : Set Space}
    (hA : volume A ≠ ⊤) {ι : Type} [Fintype ι]
    (hFm : Measurable (F ι)) (hF0 : ∀ x, 0 ≤ F ι x)
    {C : ℝ} (hbound : ∀ x, F ι x ≤ C) :
    IntegrableOn (F ι) {x : ι → Space | ∀ i, x i ∈ A} := by
  have hvol : volume {x : ι → Space | ∀ i, x i ∈ A} ≠ ⊤ := by
    rw [volume_generalConfigurations]
    exact ENNReal.pow_ne_top hA
  let : IsFiniteMeasure (volume.restrict {x : ι → Space | ∀ i, x i ∈ A}) := ⟨by
    simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hvol⟩
  apply (integrable_const C).mono' hFm.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (hF0 x)]
  exact hbound x

theorem familyTerm_le_exponential (F : ConfigFamily) {A : Set Space}
    (hA : volume A ≠ ⊤) {d : ℝ}
    (hFm : ∀ (ι : Type) [Fintype ι], Measurable (F ι))
    (hF0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hbound : ∀ (ι : Type) [Fintype ι] (x : ι → Space),
      F ι x ≤ Real.exp (d*Fintype.card ι)) (n : ℕ) :
    familyTerm F A n ≤ (volume.real A*Real.exp d)^n/(n.factorial : ℝ) := by
  have hvol : volume {x : Fin n → Space | ∀ i, x i ∈ A} ≠ ⊤ := by
    rw [volume_generalConfigurations]
    exact ENNReal.pow_ne_top hA
  let : IsFiniteMeasure (volume.restrict {x : Fin n → Space | ∀ i, x i ∈ A}) := ⟨by
    simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hvol⟩
  have hh := integral_mono (integrableOn_family_of_bound F hA (hFm (Fin n))
    (hF0 (Fin n)) (hbound (Fin n))) (integrable_const _) (hbound (Fin n))
  have hn : (0 : ℝ) ≤ n.factorial := Nat.cast_nonneg _
  apply (div_le_div_of_nonneg_right hh hn).trans_eq
  rw [setIntegral_const, Measure.real, volume_generalConfigurations, ENNReal.toReal_pow,
    Fintype.card_fin, smul_eq_mul, mul_comm d (n : ℝ), Real.exp_nat_mul, mul_pow]
  rfl

theorem summable_familyTerm_of_bound (F : ConfigFamily) {A : Set Space}
    (hA : volume A ≠ ⊤) {d : ℝ}
    (hFm : ∀ (ι : Type) [Fintype ι], Measurable (F ι))
    (hF0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hbound : ∀ (ι : Type) [Fintype ι] (x : ι → Space),
      F ι x ≤ Real.exp (d*Fintype.card ι)) : Summable (familyTerm F A) :=
  Summable.of_nonneg_of_le (familyTerm_nonneg F A hF0)
    (familyTerm_le_exponential F hA hFm hF0 hbound)
    (Real.summable_pow_div_factorial _)

theorem tsum_le_convolution {f a b : ℕ → ℝ} (hf : Summable f)
    (ha : Summable a) (hb : Summable b)
    (hle : ∀ n, f n ≤ ∑ k ∈ Finset.range (n+1), a k*b (n-k)) :
    (∑' n, f n) ≤ (∑' n, a n)*(∑' n, b n) := by
  have hab : Summable (fun p : ℕ × ℕ => a p.1*b p.2) :=
    summable_mul_of_summable_norm (summable_norm_iff.mpr ha) (summable_norm_iff.mpr hb)
  rw [ha.tsum_mul_tsum_eq_tsum_sum_range hb hab]
  exact hf.tsum_le_tsum hle (summable_sum_mul_range_of_summable_mul hab)

theorem grandIntegral_insertion_bound (F G : ConfigFamily)
    (hG : RelabelInvariant G) {A B : Set Space}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    (hAfin : volume A ≠ ⊤)
    (hFi : ∀ n, IntegrableOn (F (Fin n)) {x | ∀ i, x i ∈ A ∪ B})
    (hGi : ∀ (ι : Type) [Fintype ι], IntegrableOn (G ι) {x | ∀ i, x i ∈ B})
    (hFs : Summable (familyTerm F (A ∪ B))) (hGs : Summable (familyTerm G B))
    {d : ℝ}
    (hbound : ∀ (n : ℕ) (s : Finset (Fin n)) (x : Fin n → Space),
      x ∈ binaryRegion A B s → F (Fin n) x ≤
        Real.exp (d*s.card) * G {i : Fin n // i ∉ s} (fun i => x i)) :
    grandIntegral F (A ∪ B) ≤
      Real.exp (volume.real A*Real.exp d)*grandIntegral G B := by
  let a (n : ℕ) := (volume.real A*Real.exp d)^n/(n.factorial : ℝ)
  have ha : HasSum a (Real.exp (volume.real A*Real.exp d)) :=
    by
      simpa only [a, Real.exp_eq_exp_ℝ] using
        NormedSpace.expSeries_div_hasSum_exp (volume.real A*Real.exp d)
  change (∑' n, familyTerm F (A ∪ B) n) ≤
    Real.exp (volume.real A*Real.exp d)*(∑' n, familyTerm G B n)
  rw [← ha.tsum_eq]
  apply tsum_le_convolution hFs ha.summable hGs
  intro n
  have hb := integral_binary_bound hA hB hd
    (fun k => (volume.real A)^k*Real.exp (d*k))
    (fun k => familyIntegral G B (Fin k)) (hFi n) ?_
  swap
  · intro s
    have hv : volume {x : {i : Fin n // i ∈ s} → Space | ∀ i, x i ∈ A} ≠ ⊤ := by
      rw [volume_generalConfigurations]
      exact ENNReal.pow_ne_top hAfin
    let : IsFiniteMeasure (volume.restrict
        {x : {i : Fin n // i ∈ s} → Space | ∀ i, x i ∈ A}) := ⟨by
      simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hv⟩
    have hprod := integrableOn_binary_product volume A B s
      (integrable_const (Real.exp (d*s.card))) (by simpa only [← volume_pi] using hGi {i : Fin n // i ∉ s})
    have hi := setIntegral_mono_on
      ((hFi n).mono_set (binaryRegion_subset_union A B s))
      (by simpa only [← volume_pi] using hprod)
      (measurableSet_binaryRegion hA hB s) (hbound n s)
    rw [show volume = Measure.pi (fun _ : Fin n => (volume : Measure Space)) by exact volume_pi,
      setIntegral_binary_product volume A B s (fun _ => Real.exp (d*s.card))
        (G {i : Fin n // i ∉ s})] at hi
    simp only [← volume_pi] at hi
    have heg := familyIntegral_eq_Fin G hG B {i : Fin n // i ∉ s}
    have hgc : familyIntegral G B {i : Fin n // i ∉ s} =
        familyIntegral G B (Fin (n-s.card)) := by
      have hc : Fintype.card {i : Fin n // i ∉ s} = n-s.card := by
        rw [Fintype.card_subtype_compl (fun i : Fin n => i ∈ s),
          Fintype.card_fin, Fintype.card_coe]
      rw [hc] at heg
      exact heg
    rw [setIntegral_const, Measure.real, volume_generalConfigurations, ENNReal.toReal_pow,
      Fintype.card_coe, smul_eq_mul] at hi
    exact hi.trans_eq (by
      change volume.real A ^ s.card * Real.exp (d*s.card) *
        familyIntegral G B {i : Fin n // i ∉ s} = _
      rw [hgc, Fintype.card_fin])
  have hf : (0 : ℝ) ≤ n.factorial := Nat.cast_nonneg _
  have hh := div_le_div_of_nonneg_right hb hf
  rw [Fintype.card_fin, factorial_binomial_sum
    (fun k => (volume.real A)^k*Real.exp (d*k))
    (fun k => familyIntegral G B (Fin k)) n] at hh
  apply hh.trans_eq
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [a, familyTerm]
  rw [mul_comm d (k : ℝ), Real.exp_nat_mul, mul_pow]

end ContinuumTemperature
end

end OAI
