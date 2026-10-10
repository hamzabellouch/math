import OAI.Probability.DilutedSpin.JointRootParam

namespace OAI

section
section
namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
variable {X I Y : Type} [MeasurableSpace X] [MeasurableSpace I] [MeasurableSpace Y] {M : ℕ}
variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0)

theorem fullRoot_count_deviation :
    rootDeviation (fullRootLaw ξ μ ν r s) (fun z : FullRootState Y X I M => (z.2.2.1:ℝ)) ≤ Real.sqrt s := by
  rw [rootDeviation,fullRoot_count_mean]
  change (∫ z, (fun w : Sigma (RootPath X) × Sigma (RootPath I) => |(w.2.1:ℝ)-s|) z.2
    ∂(rootLaw M ξ).prod ((compoundRootLaw μ r).prod (compoundRootLaw ν s))) ≤ _
  rw [integral_fun_snd (fun w : Sigma (RootPath X) × Sigma (RootPath I) => |(w.2.1:ℝ)-s|),
    integral_fun_snd (fun w : Sigma (RootPath I) => |(w.1:ℝ)-s|)]
  simp only [probReal_univ,one_smul]
  exact familyPoisson_count_deviation (fun n => rootLaw n (fun _ => ν)) s

theorem fullRoot_deviation_sub_count {f : FullRootState Y X I M → ℝ}
    (hf : Integrable f (fullRootLaw ξ μ ν r s)) (c : ℝ) :
    rootDeviation (fullRootLaw ξ μ ν r s) (fun z => f z-c*(z.2.2.1:ℝ)) ≤
      rootDeviation (fullRootLaw ξ μ ν r s) f+|c| *Real.sqrt s := by
  have h := rootDeviation_sub_le (fullRootLaw ξ μ ν r s) hf
    (((fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)).const_mul c)
  rw [rootDeviation_smul] at h
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (fullRoot_count_deviation ξ μ ν r s) (abs_nonneg c)))

theorem fullRoot_deviation_sub_count_integral
    {G : FullRootState Y X I M → ℝ → ℝ}
    (hG : Measurable (fun z : FullRootState Y X I M × ℝ => G z.1 z.2))
    {B : FullRootState Y X I M → ℝ} (hB : Integrable B (fullRootLaw ξ μ ν r s))
    {a b : ℝ} (hab : a ≤ b)
    (hb : ∀ z u, u ∈ Icc a b → |G z u| ≤ B z)
    {c : ℝ → ℝ} (hc : Measurable c) (hcb : ∀ u ∈ Icc a b, |c u| ≤ 1) :
    (∫ u in a..b, rootDeviation (fullRootLaw ξ μ ν r s)
      (fun z => G z u-c u*(z.2.2.1:ℝ))) ≤
    (∫ u in a..b, rootDeviation (fullRootLaw ξ μ ν r s) (fun z => G z u)) +
      (b-a)*Real.sqrt s := by
  let P := fullRootLaw ξ μ ν r s
  have hcount : Measurable (fun z : FullRootState Y X I M × ℝ => (z.1.2.2.1:ℝ)) :=
    (measurable_sigmaUncurry (f := fun n (_ : RootPath I n) => (n:ℝ))
      (fun _ => measurable_const)).comp measurable_fst.snd.snd
  have hci := (fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)
  have hF : Measurable (fun z : FullRootState Y X I M × ℝ => G z.1 z.2-c z.2*(z.1.2.2.1:ℝ)) :=
    hG.sub ((hc.comp measurable_snd).mul hcount)
  have hFi : IntervalIntegrable (fun u => rootDeviation P
      (fun z => G z u-c u*(z.2.2.1:ℝ))) volume a b := by
    apply intervalIntegrable_rootDeviation P hF (hB.add hci) hab
    intro z u hu
    have hn : 0 ≤ (z.2.2.1:ℝ) := Nat.cast_nonneg _
    simpa only [Pi.add_apply] using
      (abs_sub (G z u) (c u*(z.2.2.1:ℝ))).trans
        (add_le_add (hb z u hu) (by rw [abs_mul,abs_of_nonneg hn]; nlinarith [hcb u hu]))
  have hGi := intervalIntegrable_rootDeviation P hG hB hab hb
  have hh := intervalIntegral.integral_mono_on hab hFi (hGi.add intervalIntegrable_const)
    (fun u hu => (fullRoot_deviation_sub_count ξ μ ν r s
      (hB.mono' (hG.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
        (ae_of_all _ (fun z => by change |G z u| ≤ B z; exact hb z u hu))) (c u)).trans
          (add_le_add le_rfl (show |c u| *Real.sqrt s ≤ Real.sqrt s by
            nlinarith [hcb u hu,Real.sqrt_nonneg (s:ℝ)])))
  simpa only [intervalIntegral.integral_add hGi intervalIntegrable_const,
    intervalIntegral.integral_const,smul_eq_mul] using hh

end DilutedSpinGlass
end

end

end OAI
