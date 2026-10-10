import OAI.Analysis.TriangularHilbert.BoundedBox

namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section

def cyclicKernelOutput (B C : ℝ×ℝ → ℂ) (K : ℝ → ℝ) (z : ℝ×ℝ) : ℂ :=
  ∫ c : ℝ, B (z.2,c)*C (c,z.1)*(K (z.1+z.2+c):ℂ)

def sampledIntegrand (B C : ℝ×ℝ → ℂ) (h : ℝ) (K : ℝ → ℝ) (z : ℝ×ℝ) (c : ℝ) : ℂ :=
  B (gridPoint h z.2,gridPoint h c)*C (gridPoint h c,gridPoint h z.1)*
    (K (gridPoint h z.1+gridPoint h z.2+gridPoint h c):ℂ)

def sampledKernelOutput (B C : ℝ×ℝ → ℂ) (h : ℝ) (K : ℝ → ℝ) (z : ℝ×ℝ) : ℂ :=
  ∫ c : ℝ, sampledIntegrand B C h K z c

lemma sampledKernelOutput_eq_sum (B C : ℝ×ℝ → ℂ) {h M : ℝ} (hh : 0 < h)
    (hB : BoxSupport B M) (K : ℝ → ℝ) (z : ℝ×ℝ) :
    sampledKernelOutput B C h K z = ∑ k : sampleIndices h M,
      (h:ℂ)*B (gridPoint h z.2,h*(k:ℤ))*C (h*(k:ℤ),gridPoint h z.1)*
        (K (gridPoint h z.1+gridPoint h z.2+h*(k:ℤ)):ℂ) := by
  have hs (c : ℝ) (hc : B (gridPoint h z.2,c)*C (c,gridPoint h z.1)*
      (K (gridPoint h z.1+gridPoint h z.2+c):ℂ) ≠ 0) : |c| ≤ M := by
    exact (hB (gridPoint h z.2,c) (fun he => hc (by simp only [he,zero_mul]))).2
  have he := integral_sampled_line (fun c => B (gridPoint h z.2,c)*C (c,gridPoint h z.1)*
      (K (gridPoint h z.1+gridPoint h z.2+c):ℂ)) hh hs
  rw [show sampledKernelOutput B C h K z = _ from he]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Complex.real_smul]
  ring

lemma gridLift_kernelOutput_eq (B C : ℝ×ℝ → ℂ) {h M : ℝ} (hh : 0 < h)
    (hB : BoxSupport B M) (hC : BoxSupport C M) (K : ℝ → ℝ) (z : ℝ×ℝ) :
    gridLift (sampleIndices h M) h (kernelOutput (sampledMatrix B h M) (sampledMatrix C h M) h
      (fun m => h*(m:ℤ)) (fun _ _ => K)) z = sampledKernelOutput B C h K z := by
  rw [gridLift_eq hh,sampledKernelOutput_eq_sum B C hh hB K z]
  split_ifs with hi hj
  · rfl
  · symm
    apply Finset.sum_eq_zero
    intro k _
    have he : B (gridPoint h z.2,h*(k:ℤ)) = 0 := by
      by_contra he
      exact hj ((mem_sampleIndices hh M _).mpr (hB _ he).1)
    simp only [he,mul_zero,zero_mul]
  · symm
    apply Finset.sum_eq_zero
    intro k _
    have he : C (h*(k:ℤ),gridPoint h z.1) = 0 := by
      by_contra he
      exact hi ((mem_sampleIndices hh M _).mpr (hC _ he).2)
    simp only [he,mul_zero,zero_mul]

lemma measurable_sampledIntegrand (B C : ℝ×ℝ → ℂ) (hB : Measurable B) (hC : Measurable C)
    (h : ℝ) (K : ℝ → ℝ) (hK : Measurable K) :
    Measurable (fun q : (ℝ×ℝ)×ℝ => sampledIntegrand B C h K q.1 q.2) := by
  have ha : Measurable (fun q : (ℝ×ℝ)×ℝ => gridPoint h q.1.1) := (measurable_gridPoint h).comp (measurable_fst.comp measurable_fst)
  have hb : Measurable (fun q : (ℝ×ℝ)×ℝ => gridPoint h q.1.2) := (measurable_gridPoint h).comp (measurable_snd.comp measurable_fst)
  have hc : Measurable (fun q : (ℝ×ℝ)×ℝ => gridPoint h q.2) := (measurable_gridPoint h).comp measurable_snd
  exact ((hB.comp (hb.prodMk hc)).mul (hC.comp (hc.prodMk ha))).mul
    (Complex.measurable_ofReal.comp (hK.comp ((ha.add hb).add hc)))

lemma measurable_sampledKernelOutput (B C : ℝ×ℝ → ℂ) (hB : Measurable B) (hC : Measurable C)
    (h : ℝ) (K : ℝ → ℝ) (hK : Measurable K) : Measurable (sampledKernelOutput B C h K) :=
  (measurable_sampledIntegrand B C hB hC h K hK).stronglyMeasurable.integral_prod_right'.measurable

lemma sampledIntegrand_support_c (B C : ℝ×ℝ → ℂ) {h M : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hB : BoxSupport B M) (K : ℝ → ℝ) (z : ℝ×ℝ) (c : ℝ)
    (hc : sampledIntegrand B C h K z c ≠ 0) : |c| ≤ M+1 := by
  have hne : B (gridSquare h (z.2,c)) ≠ 0 := fun he => hc (by simp only [sampledIntegrand,gridSquare] at he ⊢; rw [he]; simp)
  exact (sampled_support B hh hh1 hB (z.2,c) hne).2

lemma sampledIntegrand_support_z (B C : ℝ×ℝ → ℂ) {h M : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hB : BoxSupport B M) (hC : BoxSupport C M) (K : ℝ → ℝ) (z : ℝ×ℝ) (c : ℝ)
    (hc : sampledIntegrand B C h K z c ≠ 0) : z ∈ closedBox (M+1) := by
  apply (mem_closedBox _ _).mpr
  have hneB : B (gridSquare h (z.2,c)) ≠ 0 := fun he => hc (by simp only [sampledIntegrand,gridSquare] at he ⊢; rw [he]; simp)
  have hneC : C (gridSquare h (c,z.1)) ≠ 0 := fun he => hc (by simp only [sampledIntegrand,gridSquare] at he ⊢; rw [he]; simp)
  exact ⟨(sampled_support C hh hh1 hC (c,z.1) hneC).2,(sampled_support B hh hh1 hB (z.2,c) hneB).1⟩

lemma sampledKernelOutput_support (B C : ℝ×ℝ → ℂ) {h M : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hB : BoxSupport B M) (hC : BoxSupport C M) (K : ℝ → ℝ) (z : ℝ×ℝ) (hz : z ∉ closedBox (M+1)) :
    sampledKernelOutput B C h K z = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with c
  by_contra hc
  exact hz (sampledIntegrand_support_z B C hh hh1 hB hC K z c hc)
end
end TriangularHilbert.Heat
end

end OAI
