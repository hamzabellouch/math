import Mathlib
import OAI.Combinatorics.IndependentSets.Encoding.Normalizer

namespace OAI

namespace LargeIndependentSets.Coefficient
open MeasureTheory Set
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def Full {m : ℕ} (t : ι → Fin (m+1)) : Prop := ∃ i, (t i).val = m

lemma no_full_mass {m : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (∑ t : ι → Fin (m+1), if Full t then 0 else mass m ρ t) =
      (1-levelMass m ρ ⟨m, by omega⟩)^Fintype.card ι := by
  have ht (t : ι → Fin (m+1)) : (if Full t then 0 else mass m ρ t) =
      ∏ i, if (t i).val = m then 0 else levelMass m ρ (t i) := by
    by_cases h : Full t
    · rw [ite_eq_left h]
      obtain ⟨i, hi⟩ := h
      exact (Finset.prod_eq_zero (f:=fun j => if (t j).val = m then (0:ℝ) else levelMass m ρ (t j))
        (Finset.mem_univ i) (ite_eq_left hi)).symm
    · rw [ite_eq_right h]
      apply Finset.prod_congr rfl
      intro i _
      rw [ite_eq_right (fun hi => h ⟨i,hi⟩)]
  simp_rw [ht]
  rw [← Fintype.prod_sum (fun (_ : ι) (k : Fin (m+1)) => if k.val = m then (0:ℝ) else levelMass m ρ k)]
  have hk : (∑ k : Fin (m+1), if k.val = m then 0 else levelMass m ρ k) =
      1-levelMass m ρ ⟨m, by omega⟩ := by
    have he : (∑ k : Fin (m+1), if k.val = m then levelMass m ρ k else 0) =
        levelMass m ρ ⟨m, by omega⟩ := by
      rw [Finset.sum_eq_single ⟨m, by omega⟩]
      · simp
      · intro b _ hb
        exact ite_eq_right (fun h => hb (Fin.ext h))
      · simp
    have hf : (∑ k : Fin (m+1), if k.val = m then 0 else levelMass m ρ k) +
        (∑ k : Fin (m+1), if k.val = m then levelMass m ρ k else 0) = 1 := by
      rw [← Finset.sum_add_distrib]
      convert levelMass_total m hρ using 1
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> simp
    linarith
  simp only [hk, Finset.prod_const, Finset.card_univ]

theorem coefficient_mean_square_ae {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    {m : ℕ} {ρ β γ ε K : ℝ} (hρ : 0 ≤ ρ) (hβ : 0 < β) (hγ : 0 < γ) (hε : 0 < ε)
    (hrare : (1-levelMass m ρ ⟨m, by omega⟩)^Fintype.card ι < ε)
    (hpositive : ρ*K < ε) (hzero : (Fintype.card ι : ℝ)*(2*γ)^2/β^2 < ε)
    (X : (ι → Fin (m+1)) → Ω → ℝ) (D : (ι → Fin (m+1)) → Ω → ι → ℝ)
    (hXm : ∀ t, Measurable (X t)) (hXb : ∀ t θ, 0 ≤ X t θ ∧ X t θ ≤ 1)
    (hDm : ∀ t i, Measurable (fun θ => D t θ i)) (hDb : ∀ t θ i, |D t θ i| ≤ 1)
    (hdetect : ∀ t θ, ε < X t θ → ∃ i, β ≤ D t θ i)
    (hstep : ∀ᵐ θ ∂ν, ∀ t i, 0 < (t i).val → |D t θ i-D (lower i t) θ i| < β/2)
    (hcount : ∀ t θ, ((Finset.univ.filter (fun i => β/2 ≤ D t θ i)).card : ℝ) ≤ K)
    (hz : ∀ t i, Full t → (t i).val = 0 → (∫ θ, (D t θ i)^2 ∂ν) < (2*γ)^2) :
    (∑ t, mass m ρ t * ∫ θ, X t θ ∂ν) < 4*ε := by
  let P (t : ι → Fin (m+1)) (θ : Ω) : Prop := ∃ i, 0 < (t i).val ∧ β ≤ D t θ i
  let Z (t : ι → Fin (m+1)) (θ : Ω) : ℝ :=
    ∑ i, if Full t ∧ (t i).val = 0 then (D t θ i)^2/β^2 else 0
  have hznon (t : ι → Fin (m+1)) (θ : Ω) : 0 ≤ Z t θ := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> positivity
  have hpoint (t : ι → Fin (m+1)) (θ : Ω) : X t θ ≤
      ε + (if Full t then 0 else 1) + Z t θ + (if P t θ then 1 else 0) := by
    by_cases hfull : Full t
    · rw [ite_eq_left hfull]
      by_cases hp : P t θ
      · rw [ite_eq_left hp]
        linarith [hXb t θ, hznon t θ]
      · rw [ite_eq_right hp]
        by_cases hx : X t θ ≤ ε
        · linarith [hznon t θ]
        · obtain ⟨i,hi⟩ := hdetect t θ (lt_of_not_ge hx)
          have hti : (t i).val = 0 := by
            by_contra hn
            exact hp ⟨i, by omega, hi⟩
          have hd : 1 ≤ (D t θ i)^2/β^2 := (le_div_iff₀ (sq_pos_of_pos hβ)).mpr (by nlinarith)
          have hzle : (D t θ i)^2/β^2 ≤ Z t θ := by
            calc
              _ = if Full t ∧ (t i).val = 0 then (D t θ i)^2/β^2 else 0 := (ite_eq_left ⟨hfull,hti⟩).symm
              _ ≤ _ := Finset.single_le_sum (f:=fun j => if Full t ∧ (t j).val = 0 then (D t θ j)^2/β^2 else 0)
                (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ i)
          linarith [hXb t θ]
    · rw [ite_eq_right hfull]
      have hp : 0 ≤ (if P t θ then (1:ℝ) else 0) := by split_ifs <;> norm_num
      linarith [hXb t θ,hznon t θ]
  have hpos (θ : Ω) (hθ : ∀ t i, 0 < (t i).val → |D t θ i-D (lower i t) θ i| < β/2) : (∑ t : ι → Fin (m+1), mass m ρ t * (if P t θ then 1 else 0)) ≤ ρ*K := by
    have h := positive_coefficient_bound hρ (fun t i => D t θ i)
      (fun t i ht => hθ t i ht) (fun t => hcount t θ)
    simpa only [Finset.sum_filter, P, mul_ite, mul_one, mul_zero] using h
  have hsum : ∀ᵐ θ ∂ν, (∑ t, mass m ρ t * X t θ) ≤
      ε + (1-levelMass m ρ ⟨m, by omega⟩)^Fintype.card ι +
        (∑ t, mass m ρ t * Z t θ) + ρ*K := by
    filter_upwards [hstep] with θ hθ
    have hp := Finset.sum_le_sum (s:=Finset.univ) (fun t _ => mul_le_mul_of_nonneg_left (hpoint t θ) (mass_nonneg m hρ t))
    simp only [mul_add, Finset.sum_add_distrib] at hp
    have he : (∑ t : ι → Fin (m+1), mass m ρ t * ε) = ε := by
      rw [← Finset.sum_mul, mass_total m hρ, one_mul]
    have hf : (∑ t : ι → Fin (m+1), mass m ρ t * (if Full t then 0 else 1)) =
        (1-levelMass m ρ ⟨m, by omega⟩)^Fintype.card ι := by
      simpa only [mul_ite, mul_zero, mul_one] using (no_full_mass (ι:=ι) (m:=m) hρ)
    rw [he,hf] at hp
    linarith [hpos θ hθ]
  have hXi (t : ι → Fin (m+1)) : Integrable (X t) ν :=
    Integrable.of_bound (hXm t).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun θ => by rw [Real.norm_eq_abs, abs_of_nonneg (hXb t θ).1]; exact (hXb t θ).2))
  have hDi (t : ι → Fin (m+1)) (i : ι) : Integrable (fun θ => (D t θ i)^2/β^2) ν := by
    apply Integrable.div_const
    apply Integrable.of_bound ((hDm t i).pow_const 2).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro θ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hDb t θ i, sq_abs (D t θ i), abs_nonneg (D t θ i)]
  have hZi (t : ι → Fin (m+1)) : Integrable (Z t) ν := by
    apply integrable_finsetSum
    intro i _
    by_cases hi : Full t ∧ (t i).val = 0
    · simpa only [hi, and_self, ↓reduceIte] using hDi t i
    · simp only [hi, ↓reduceIte]; exact integrable_zero _ _ _
  have hZe (t : ι → Fin (m+1)) : (∫ θ, Z t θ ∂ν) ≤ (Fintype.card ι : ℝ)*(2*γ)^2/β^2 := by
    rw [show Z t = fun θ => ∑ i, if Full t ∧ (t i).val = 0 then (D t θ i)^2/β^2 else 0 from rfl]
    rw [integral_finsetSum _ (fun i _ => by
      by_cases hi : Full t ∧ (t i).val = 0
      · simpa only [hi, and_self, ↓reduceIte] using hDi t i
      · simp only [hi, ↓reduceIte]; exact integrable_zero _ _ _)]
    calc
      _ ≤ ∑ _ : ι, (2*γ)^2/β^2 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : Full t ∧ (t i).val = 0
        · simp only [hi, and_self, ↓reduceIte, integral_div]
          exact div_le_div_of_nonneg_right (hz t i hi.1 hi.2).le (sq_nonneg _)
        · simp only [hi, ↓reduceIte, integral_zero]; positivity
      _ = _ := by simp [div_eq_mul_inv]; ring
  have hUi : Integrable (fun θ => ∑ t, mass m ρ t * X t θ) ν :=
    integrable_finsetSum _ (fun t _ => (hXi t).const_mul _)
  have hVi : Integrable (fun θ => ∑ t, mass m ρ t * Z t θ) ν :=
    integrable_finsetSum _ (fun t _ => (hZi t).const_mul _)
  have hWi : Integrable (fun θ => ε + (1-levelMass m ρ ⟨m, by omega⟩)^Fintype.card ι +
      ∑ t, mass m ρ t * Z t θ) ν := (integrable_const _).add hVi
  have hint := integral_mono_ae hUi (hWi.add (integrable_const _)) hsum
  simp only [Pi.add_apply] at hint
  rw [integral_add hWi (integrable_const (ρ*K)),
    integral_add (integrable_const (ε + (1-levelMass m ρ ⟨m, by omega⟩)^Fintype.card ι)) hVi] at hint
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hint
  rw [integral_finsetSum _ (fun t _ => (hXi t).const_mul _)] at hint
  simp only [integral_const_mul] at hint
  have hZtotal : (∫ θ, ∑ t, mass m ρ t * Z t θ ∂ν) ≤ (Fintype.card ι : ℝ)*(2*γ)^2/β^2 := by
    rw [integral_finsetSum _ (fun t _ => (hZi t).const_mul _)]
    simp only [integral_const_mul]
    calc
      _ ≤ ∑ t : ι → Fin (m+1), mass m ρ t * ((Fintype.card ι : ℝ)*(2*γ)^2/β^2) :=
        Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (hZe t) (mass_nonneg m hρ t))
      _ = _ := by rw [← Finset.sum_mul, mass_total m hρ, one_mul]
  linarith
end LargeIndependentSets.Coefficient

end OAI
