import OAI.Probability.DilutedSpin.CavityIndex
import OAI.Probability.DilutedSpin.FullSelectedThermal

namespace OAI

section
section
namespace DilutedSpinGlass.SizeCoupling
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

variable {Z I : Type} [MeasurableSpace Z] [Countable I] [MeasurableSpace I]
  [MeasurableSingletonClass I] {A : I → Type} [∀ i, Fintype (A i)]

noncomputable def parameterMean (π : Measure Z) (ν : Measure I) {p r N : ℕ} [NeZero N]
    (M : Model p) (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (ψ : Z → (i : I) → Spin → FinitePath (A i) (r+1) → ℝ) : ℝ :=
  ∫ z, perturbedMean (N := N) M.disorder.toMeasure M.field.toMeasure ν
    id id Q m (ψ z) (M.alpha*N) (scoreRate N) ∂π

lemma scoreScale_div {N : ℕ} (hN : 0 < N) : scoreScale N/N = (N:ℝ)^(-(1:ℝ)/4) := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  rw [scoreScale]
  convert (Real.rpow_sub hn ((3:ℝ)/4) 1).symm using 1 <;> norm_num

lemma parameterMean_normalized_error (π : Measure Z) [IsProbabilityMeasure π]
    (ν : Measure I) [IsProbabilityMeasure ν] {p r : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (hend : m (Fin.last r) = 1)
    (ψ : Z → (i : I) → Spin → FinitePath (A i) (r+1) → ℝ)
    (hψm : ∀ i σ a, Measurable (fun z => ψ z i σ a))
    {D : ℝ} (hψ : ∀ z i σ a, |Real.log (ψ z i σ a)| ≤ D) :
    Tendsto (fun n => parameterMean (N := n+1) π ν M Q m ψ/((n:ℝ)+1)-pressure M (n+1))
      atTop (𝓝 0) := by
  have hb (n : ℕ) : ‖parameterMean (N := n+1) π ν M Q m ψ/((n:ℝ)+1)-pressure M (n+1)‖ ≤
      D*((n:ℝ)+1)^(-(1:ℝ)/4) := by
    have hc := (parameter_average_negligible (N := n+1) π ν M hθ hh Q m hm hend ψ hψm hψ (scoreRate (n+1))).2
    have hn : (0:ℝ) < (n:ℝ)+1 := by positivity
    have he : parameterMean (N := n+1) π ν M Q m ψ/((n:ℝ)+1)-pressure M (n+1) =
        (parameterMean (N := n+1) π ν M Q m ψ-((n:ℝ)+1)*pressure M (n+1))/((n:ℝ)+1) := by
      rw [sub_div, mul_div_cancel_left₀ _ hn.ne']
    rw [he,Real.norm_eq_abs,abs_div,abs_of_pos hn]
    have hs : scoreScale (n+1)/((n:ℝ)+1) = ((n:ℝ)+1)^(-(1:ℝ)/4) := by
      simpa only [Nat.cast_add,Nat.cast_one] using scoreScale_div (show 0 < n+1 by omega)
    simp only [Nat.cast_add,Nat.cast_one] at hc
    have hrate : ((scoreRate (n+1)):ℝ) = scoreScale (n+1) := rfl
    have hc' := div_le_div_of_nonneg_right hc hn.le
    rw [hrate,mul_div_assoc,hs] at hc'
    simpa only [parameterMean,Nat.cast_add,Nat.cast_one] using hc'
  apply squeeze_zero_norm hb
  have ht := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/4)).comp
    (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop)
  simpa only [mul_zero,neg_div,Function.comp_apply] using ht.const_mul D

 
theorem actual_low_averaged_increments (π : Measure Z) [IsProbabilityMeasure π]
    (ν : Measure I) [IsProbabilityMeasure ν] {p r : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (hend : m (Fin.last r) = 1)
    (ψ : Z → (i : I) → Spin → FinitePath (A i) (r+1) → ℝ)
    (hψm : ∀ i σ a, Measurable (fun z => ψ z i σ a))
    {D : ℝ} (hψ : ∀ z i σ a, |Real.log (ψ z i σ a)| ≤ D)
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ∃ N, n ≤ N ∧ (∫ z,
      perturbedMean (N := N+2) M.disorder.toMeasure M.field.toMeasure ν id id Q m (ψ z)
        (M.alpha*(N+2)) (scoreRate (N+2))-
      perturbedMean (N := N+1) M.disorder.toMeasure M.field.toMeasure ν id id Q m (ψ z)
        (M.alpha*(N+1)) (scoreRate (N+1)) ∂π) ≤ liminf (pressure M) atTop+ε := by
  let P (n : ℕ) := parameterMean (N := n+1) π ν M Q m ψ
  let f (n : ℕ) := pressure M (n+1)
  have hb (n : ℕ) : |f n-Real.log 2| ≤ M.alpha*interactionMoment M+fieldMoment M :=
    (disorderAverage_integrable_and_pressure_bound M hθ hh (Nat.succ_pos n)).2
  have hlo : atTop.IsBoundedUnder (· ≥ ·) f := by
    apply isBoundedUnder_of_eventually_le (α := OrderDual ℝ) (a := Real.log 2-((M.alpha:ℝ)*interactionMoment M+fieldMoment M))
    exact Eventually.of_forall (fun n => by
      change Real.log 2-((M.alpha:ℝ)*interactionMoment M+fieldMoment M) ≤ f n
      have := (abs_le.mp (hb n)).1
      linarith)
  have hup : atTop.IsCoboundedUnder (· ≥ ·) f :=
    isCoboundedUnder_ge_of_le atTop (x := Real.log 2+M.alpha*interactionMoment M+fieldMoment M)
      (fun n => by have := (abs_le.mp (hb n)).2; linarith)
  have he : liminf f atTop = liminf (pressure M) atTop := liminf_nat_add _ 1
  obtain ⟨N,hN,hloN⟩ := arbitrarily_large_low_increment P f hlo hup
    (parameterMean_normalized_error π ν M hθ hh Q m hm hend ψ hψm hψ)
    (show liminf f atTop < liminf (pressure M) atTop+ε by rw [he]; linarith) n
  refine ⟨N,hN,?_⟩
  have hi (k : ℕ) := (parameter_average_negligible (N := k+1) π ν M hθ hh Q m hm hend ψ hψm hψ (scoreRate (k+1))).1
  have his := integral_sub (hi (N+1)) (hi N)
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,add_assoc,one_add_one_eq_two] at his
  rw [his]
  simpa only [P,parameterMean,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,add_assoc,one_add_one_eq_two] using hloN

end DilutedSpinGlass.SizeCoupling
end

end

end OAI
