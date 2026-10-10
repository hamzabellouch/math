import OAI.Analysis.AncientFlat.Kernel.ClassicalBase

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff SchwartzMap
namespace FlatDuality
open BiharmonicKernel
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma schwartz_jet_majorant (n : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : SchwartzMap V E) (a b : ℝ) (ha : 0<a) (K : ℕ) :
    ∃ B : V → ℝ, Integrable B ∧ Integrable (fun x => (1+‖x‖)*B x) ∧
      (∀ x, 0≤B x) ∧ ∀ c ∈ Icc a b, ∀ x,
        ‖c⁻¹^K • iteratedFDeriv ℝ n g (c⁻¹ • x)‖≤B x := by
  induction n generalizing E with
  | zero =>
    obtain ⟨B,hi,hw,hn,hb⟩ := SchwartzConvolution.scaled_weighted_majorant g a b ha K 1
    refine ⟨B,hi,by simpa only [pow_one] using hw,hn,fun c hc x => ?_⟩
    simpa only [norm_smul,norm_iteratedFDeriv_zero] using hb c hc x
  | succ n ih =>
    obtain ⟨B,hi,hw,hn,hb⟩ := ih (SchwartzMap.fderivCLM ℝ V E g)
    refine ⟨B,hi,hw,hn,fun c hc x => ?_⟩
    have he : ((SchwartzMap.fderivCLM ℝ V E g : SchwartzMap V (V →L[ℝ] E)) : V → (V →L[ℝ] E)) = fderiv ℝ g := rfl
    simpa only [norm_smul,he,norm_iteratedFDeriv_fderiv] using hb c hc x
lemma kernel_jet_weighted_majorant (n : ℕ) (a b : ℝ) (ha : 0<a) :
    ∃ B : V → ℝ, Integrable B ∧ Integrable (fun x => (1+‖x‖)*B x) ∧
      (∀ x, 0≤B x) ∧ ∀ t ∈ Icc a b, ∀ x,
        ‖iteratedFDeriv ℝ n (kernel (V := V) t) x‖≤B x := by
  let r := fun t : ℝ => Real.sqrt (Real.sqrt t)
  obtain ⟨B,hi,hw,hn,hb⟩ := schwartz_jet_majorant n (heatKernel (V := V) 1 zero_lt_one)
    (r a) (r b) (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr ha)) (Module.finrank ℝ V+n)
  refine ⟨B,hi,hw,hn,fun t ht x => ?_⟩
  have hp : 0<t := ha.trans_le ht.1
  have hr : 0<r t := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hp)
  have hrs : r t^4=t := by
    dsimp [r]
    nlinarith [Real.sq_sqrt (Real.sqrt_nonneg t),Real.sq_sqrt hp.le]
  have he : (kernel (V := V) t)=(heatKernel t hp : V → ℂ) := by
    exact (heatKernel_eq_kernel t hp).symm
  rw [he]
  have hs := heatKernel_deriv_scaling (V := V) 1 zero_lt_one (r t) hr n x
  simp only [mul_one,hrs] at hs
  rw [hs,←inv_pow,←pow_add]
  exact hb (r t) ⟨Real.sqrt_le_sqrt (Real.sqrt_le_sqrt ht.1),
    Real.sqrt_le_sqrt (Real.sqrt_le_sqrt ht.2)⟩ x
lemma kernel_four_jet_majorant (a b : ℝ) (ha : 0<a) :
    ∃ B : V → ℝ, Integrable B ∧ Integrable (fun x => (1+‖x‖)*B x) ∧
      (∀ x, 0≤B x) ∧ ∀ t ∈ Icc a b, ∀ n : ℕ, n≤4 → ∀ x,
        ‖iteratedFDeriv ℝ n (kernel (V := V) t) x‖≤B x := by
  choose B hi hw hn hb using fun n => kernel_jet_weighted_majorant (V := V) n a b ha
  refine ⟨fun x => ∑ n ∈ Finset.range 5,B n x,integrable_finsetSum _ (fun n _ => hi n),?_,
    fun x => Finset.sum_nonneg (fun n _ => hn n x),?_⟩
  · simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ (fun n _ => hw n)
  · intro t ht n hn' x
    exact (hb n t ht x).trans
      (Finset.single_le_sum (fun i _ => hn i x) (show n ∈ Finset.range 5 by simpa only [Finset.mem_range] using Nat.lt_succ_of_le hn'))
end FlatDuality

end

end OAI
