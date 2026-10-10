import OAI.Analysis.TriangularHilbert.GaussianTriple

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section

lemma density_mul_windowRatio {s : ℝ} (hs : 0 < s) (t : ℝ) :
    density ((11/10)*s) t * windowRatio s t = oddWindow s t := by
  unfold windowRatio
  exact mul_div_cancel₀ _ (density_pos (by positivity) _).ne'

lemma abs_oddWindow_le {s : ℝ} (hs : 0 < s) (t : ℝ) :
    |oddWindow s t| ≤ 44*density ((11/10)*s) t := by
  rw [← density_mul_windowRatio hs t,abs_mul,abs_of_nonneg (density_nonneg (by positivity) _)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (abs_windowRatio_le hs t) (density_nonneg (by positivity) t)

lemma continuous_oddWindow (s : ℝ) : Continuous (oddWindow s) := by
  unfold oddWindow
  exact (continuous_id.div_const _).mul (continuous_density s)

lemma oddWindow_triple_integrable {s : ℝ} (hs : 0 < s) (a b c : ℝ) :
    Integrable (fun z : ℝ×ℝ => oddWindow s (a-z.1)*oddWindow s (b-z.2)*oddWindow s (c+z.1+z.2)) := by
  have hi := (density_triple_integrable (by positivity : 0 < (11/10)*s)
    (by positivity : 0 < (11/10)*s) (by positivity : 0 < (11/10)*s) a b c).const_mul (44^3:ℝ)
  apply hi.mono'
  · exact (((continuous_oddWindow s).comp (continuous_const.sub continuous_fst)).mul
      ((continuous_oddWindow s).comp (continuous_const.sub continuous_snd)) |>.mul
        ((continuous_oddWindow s).comp ((continuous_const.add continuous_fst).add continuous_snd))).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs,abs_mul,abs_mul]
    have h0 := abs_oddWindow_le hs (a-z.1)
    have h1 := abs_oddWindow_le hs (b-z.2)
    have h2 := abs_oddWindow_le hs (c+z.1+z.2)
    have hd0 := density_nonneg (by positivity : 0 ≤ (11/10)*s) (a-z.1)
    have hd1 := density_nonneg (by positivity : 0 ≤ (11/10)*s) (b-z.2)
    calc
      _ ≤ (44*density ((11/10)*s) (a-z.1))*(44*density ((11/10)*s) (b-z.2))*(44*density ((11/10)*s) (c+z.1+z.2)) := by gcongr
      _ = _ := by ring

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma windowTrace_eq (A : Three → Matrix ι ι ℂ) {h s : ℝ} (hh : 0 < h) (hs : 0 < s)
    (u : ι → ℝ) (p : Three → ℝ) :
    windowTrace A h u p s = ∑ i, ∑ j, ∑ k,
      (h^3:ℝ)* (A 0 i j*A 1 j k*A 2 k i) *
        ((oddWindow s (u i-p 0)*oddWindow s (u j-p 1)*oddWindow s (u k-p 2):ℝ):ℂ) := by
  unfold windowTrace windowDiags heatArray
  have hg (v : Three) (i : ι) : 0 ≤ heatWeights h u p (fun _ => (11/10)*s) v i :=
    (weight_pos hh (by positivity) _ _).le
  rw [trace_weighted_triangle A (heatWeights h u p (fun _ => (11/10)*s))
    (fun v i => windowRatio s (u i-p v)) hg]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  have he (v : Three) (i : ι) : heatWeights h u p (fun _ => (11/10)*s) v i * windowRatio s (u i-p v) =
      h*oddWindow s (u i-p v) := by
    unfold heatWeights weight
    rw [mul_assoc,density_mul_windowRatio hs]
  rw [he,he,he]
  push_cast
  ring

end
end TriangularHilbert.Heat
end

end OAI
