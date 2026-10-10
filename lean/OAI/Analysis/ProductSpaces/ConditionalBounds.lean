import OAI.Analysis.ProductSpaces.MidpointModulus

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uΛ uΩ uι

namespace IndependentProducts
section ConditionalScalar
variable {ι : Type uι} {Ω : Type uΩ} [Fintype ι] [MeasurableSpace Ω]
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (ν : Measure Ω)
variable (hμ : MemLp (fun w : ℝ => w) 2 μ)

/-- A finite first-exit polynomial on conditionally independent coefficient blocks. -/
def firstExitSum (B : ι → Ω → ℝ) (z : (ι → Ω) × (ι → ℝ)) : ℝ :=
  ∑ i, (B i (z.1 i) * z.2 i - ∫ b, B i b ∂ν)

lemma measurable_firstExitSum [IsProbabilityMeasure ν]
    (B : ι → Ω → ℝ) (hBm : ∀ i, Measurable (B i)) :
    Measurable (firstExitSum ν B) := by unfold firstExitSum; fun_prop

variable [IsProbabilityMeasure ν]

include hμ in
lemma integrable_firstExitSum (B : ι → Ω → ℝ) (hB : ∀ i, Integrable (B i) ν)
    (hBm : ∀ i, Measurable (B i)) :
    Integrable (firstExitSum ν B) ((Measure.pi (fun _ : ι => ν)).prod (Measure.pi (fun _ : ι => μ))) := by
  apply integrable_finsetSum
  intro i hi
  have hb : Integrable (fun b : ι → Ω => B i (b i)) (Measure.pi (fun _ : ι => ν)) :=
    (measurePreserving_eval (fun _ : ι => ν) i).integrable_comp (hBm i).aestronglyMeasurable |>.mpr (hB i)
  have hw : Integrable (fun w : ι → ℝ => w i) (Measure.pi (fun _ : ι => μ)) :=
    (hμ.comp_measurePreserving (measurePreserving_eval (fun _ : ι => μ) i)).integrable (by norm_num)
  exact (hb.mul_prod hw).sub (integrable_const _)

include hμ in
lemma first_exit_scalar_bound (B : ι → Ω → ℝ) (hB : ∀ i, Integrable (B i) ν)
    (hBm : ∀ i, Measurable (B i)) (t A D r : ℝ)
    (hscalar : ∀ a : ι → ℝ, ∀ b : ℝ,
      A * euclidSize a - D * r ≤
        ∫ w : ι → ℝ, excess t r (b + ∑ i, a i * w i) ∂Measure.pi (fun _ : ι => μ)) :
    A * (∫ b : ι → Ω, euclidSize (fun i => B i (b i)) ∂Measure.pi (fun _ : ι => ν)) - D * r ≤
      ∫ z : (ι → Ω) × (ι → ℝ), excess t r (firstExitSum ν B z)
        ∂(Measure.pi (fun _ : ι => ν)).prod (Measure.pi (fun _ : ι => μ)) := by
  let Pb := Measure.pi (fun _ : ι => ν)
  let Pw := Measure.pi (fun _ : ι => μ)
  have hB' : ∀ i, Integrable (fun b : ι → Ω => B i (b i)) Pb := fun i =>
    (measurePreserving_eval (fun _ : ι => ν) i).integrable_comp (hBm i).aestronglyMeasurable |>.mpr (hB i)
  have hs := integrable_euclidSize (fun i (b : ι → Ω) => B i (b i)) hB'
  have hp := integrable_excess (integrable_firstExitSum μ ν hμ B hB hBm) t r
  rw [integral_prod _ hp]
  calc
    _ = ∫ b : ι → Ω, (A * euclidSize (fun i => B i (b i)) - D * r) ∂Pb := by
      rw [integral_sub (hs.const_mul _) (integrable_const _), integral_const_mul, integral_const]
      simp [Pb]
    _ ≤ _ := by
      apply integral_mono ((hs.const_mul _).sub (integrable_const _)) hp.integral_prod_left
      intro b
      have he : ∀ w : ι → ℝ, firstExitSum ν B (b, w) =
          -(∑ i, ∫ u, B i u ∂ν) + ∑ i, B i (b i) * w i := by
        intro w
        simp only [firstExitSum, Finset.sum_sub_distrib]
        ring
      simp_rw [he]
      exact hscalar (fun i => B i (b i)) _

end ConditionalScalar

lemma real_midpoint_excess (a c : ℝ) :
    (|a + c| + |a - c|) / 2 - |a| = max (|c| - |a|) 0 := by
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

lemma midpointGain_eq_integral_excess {Ω : Type uΩ} [MeasurableSpace Ω] (P : Measure Ω)
    (x y : Lp ℝ 1 P) (f g : Ω → ℝ) (hf : x =ᵐ[P] f) (hg : y =ᵐ[P] g)
    (t : ℝ) (ht : 0 ≤ t) :
    midpointGain t x y = ∫ ω, excess t |f ω| (g ω) ∂P := by
  have hx : Integrable (fun ω => x ω) P := memLp_one_iff_integrable.mp (Lp.memLp x)
  have hy : Integrable (fun ω => y ω) P := memLp_one_iff_integrable.mp (Lp.memLp y)
  have hp : Integrable (fun ω => |x ω + t * y ω|) P := (hx.add (hy.const_mul t)).abs
  have hm : Integrable (fun ω => |x ω - t * y ω|) P := (hx.sub (hy.const_mul t)).abs
  have he : (fun ω => excess t |x ω| (y ω)) =
      fun ω => (|x ω + t * y ω| + |x ω - t * y ω|) / 2 - |x ω| := by
    funext ω
    rw [real_midpoint_excess, abs_mul, abs_of_nonneg ht]
    rfl
  have hp' : ‖x + t • y‖ = ∫ ω, |x ω + t * y ω| ∂P := by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add x (t • y), Lp.coeFn_smul t y] with ω h1 h2
    simp only [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
  have hm' : ‖x - t • y‖ = ∫ ω, |x ω - t * y ω| ∂P := by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub x (t • y), Lp.coeFn_smul t y] with ω h1 h2
    simp only [h1, Pi.sub_apply, h2, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
  calc
    _ = ∫ ω, excess t |x ω| (y ω) ∂P := by
      have hs : Integrable (fun ω => (|x ω + t * y ω| + |x ω - t * y ω|) / 2) P := by
        simpa only [Pi.add_apply] using (hp.add hm).div_const 2
      have hi := integral_add hp hm
      rw [he, integral_sub hs hx.abs, integral_div, hi]
      unfold midpointGain
      rw [hp', hm', L1.norm_eq_integral_norm]
      simp only [Real.norm_eq_abs]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf, hg] with ω h1 h2
      rw [h1, h2]

end IndependentProducts

namespace IndependentProducts
section IntegratedConditional
variable {ι : Type uι} {Ω : Type uΩ} {Λ : Type uΛ}
  [Fintype ι] [MeasurableSpace Ω] [MeasurableSpace Λ]
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
variable (η : Measure Λ) [IsProbabilityMeasure η]

lemma integrated_first_exit_affine
    (hμ : MemLp (fun w : ℝ => w) 2 μ) (hmean : ∫ w : ℝ, w ∂μ = 1)
    (B : Λ → ι → Ω → ℝ) (hB : ∀ old i, Integrable (B old i) ν)
    (hBm : ∀ old i, Measurable (B old i))
    (U : Λ → ℝ) (hU : Integrable U η)
    (hS : Integrable (fun z : (ι → Ω) × Λ => euclidSize (fun i => B z.2 i (z.1 i)))
      ((Measure.pi (fun _ : ι => ν)).prod η))
    (hY : Integrable (fun z : ((ι → Ω) × (ι → ℝ)) × Λ => firstExitSum ν (B z.2) z.1)
      (((Measure.pi (fun _ : ι => ν)).prod (Measure.pi (fun _ : ι => μ))).prod η))
    (t A D : ℝ) (hA : 0 ≤ A) (hC : 0 < 2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ))
    (hscalar : ∀ a : ι → ℝ, ∀ b r : ℝ, 0 ≤ r →
      A * euclidSize a - D * r ≤
        ∫ w : ι → ℝ, excess t r (b + ∑ i, a i * w i) ∂Measure.pi (fun _ : ι => μ)) :
    (A / (2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ))) *
      (∫ z : ((ι → Ω) × (ι → ℝ)) × Λ, |firstExitSum ν (B z.2) z.1|
        ∂((Measure.pi (fun _ : ι => ν)).prod (Measure.pi (fun _ : ι => μ))).prod η) -
      D * (∫ old, |U old| ∂η) ≤
      ∫ z : ((ι → Ω) × (ι → ℝ)) × Λ, excess t |U z.2| (firstExitSum ν (B z.2) z.1)
        ∂((Measure.pi (fun _ : ι => ν)).prod (Measure.pi (fun _ : ι => μ))).prod η := by
  let Pb := Measure.pi (fun _ : ι => ν)
  let Pw := Measure.pi (fun _ : ι => μ)
  let C := 2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ)
  let S : Λ → ℝ := fun old => ∫ b : ι → Ω, euclidSize (fun i => B old i (b i)) ∂Pb
  have hs : Integrable S η := hS.integral_prod_right
  have hphi : Integrable (fun z : ((ι → Ω) × (ι → ℝ)) × Λ =>
      excess t |U z.2| (firstExitSum ν (B z.2) z.1)) ((Pb.prod Pw).prod η) :=
    ((hY.abs.const_mul t).sub (hU.abs.comp_snd (Pb.prod Pw))).sup (integrable_const 0)
  rw [integral_prod_symm _ hY.abs, integral_prod_symm _ hphi]
  have hn : (∫ old, ∫ z : (ι → Ω) × (ι → ℝ), |firstExitSum ν (B old) z| ∂Pb.prod Pw ∂η) ≤
      C * ∫ old, S old ∂η := by
    rw [← integral_const_mul]
    apply integral_mono hY.abs.integral_prod_right (hs.const_mul C)
    intro old
    exact signed_first_moment μ hμ hmean (fun _ : ι => ν) (B old) (hB old) (hBm old)
  have hg : A * (∫ old, S old ∂η) - D * (∫ old, |U old| ∂η) ≤
      ∫ old, ∫ z : (ι → Ω) × (ι → ℝ), excess t |U old| (firstExitSum ν (B old) z) ∂Pb.prod Pw ∂η := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hs.const_mul A) (hU.abs.const_mul D)]
    apply integral_mono ((hs.const_mul A).sub (hU.abs.const_mul D)) hphi.integral_prod_right
    intro old
    exact first_exit_scalar_bound μ ν hμ (B old) (hB old) (hBm old) t A D |U old|
      (fun a b => hscalar a b |U old| (abs_nonneg _))
  have hd : (∫ old, ∫ z : (ι → Ω) × (ι → ℝ), |firstExitSum ν (B old) z| ∂Pb.prod Pw ∂η) / C ≤
      ∫ old, S old ∂η := (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hn)
  have hh := mul_le_mul_of_nonneg_left hd hA
  change A / C * _ - D * _ ≤ _
  calc
    _ = A * ((∫ old, ∫ z : (ι → Ω) × (ι → ℝ), |firstExitSum ν (B old) z| ∂Pb.prod Pw ∂η) / C) -
        D * (∫ old, |U old| ∂η) := by ring
    _ ≤ A * (∫ old, S old ∂η) - D * (∫ old, |U old| ∂η) := sub_le_sub_right hh _
    _ ≤ _ := hg

end IntegratedConditional
end IndependentProducts

end

end OAI
