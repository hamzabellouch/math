import OAI.Analysis.TriangularHilbert.GaussianDom

namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
open MatrixEnergy
noncomputable section

def chart (i : Three) (d : ℝ) (z : ℝ × ℝ) : Three → ℝ :=
  if i = 0 then ![d-z.1-z.2, z.1, z.2]
  else if i = 1 then ![z.1, d-z.1-z.2, z.2]
  else ![z.1, z.2, d-z.1-z.2]

lemma chart_continuous (i : Three) : Continuous (fun q : ℝ × (ℝ × ℝ) => chart i q.1 q.2) := by
  unfold chart
  split_ifs <;> fun_prop

lemma chart_hasDerivAt (i : Three) (d : ℝ) (z : ℝ × ℝ) :
    HasDerivAt (fun e => chart i e z i) 1 d := by
  have he : (fun e => chart i e z i) = (fun e => e-z.1-z.2) := by
    funext e
    fin_cases i <;> simp [chart]
  rw [he]
  exact ((hasDerivAt_id d).sub_const z.1).sub_const z.2

def chartReflection (d : ℝ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun z := (z.1, d-z.1-z.2)
  invFun z := (z.1, d-z.1-z.2)
  left_inv z := by exact Prod.ext rfl (by dsimp; ring)
  right_inv z := by exact Prod.ext rfl (by dsimp; ring)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

lemma chartReflection_preserving (d : ℝ) : MeasurePreserving (chartReflection d) := by
  exact (MeasurePreserving.id volume).skew_product
    (g := fun x y : ℝ => d-x-y) (by fun_prop)
    (Filter.Eventually.of_forall (fun x => (volume.measurePreserving_sub_left (d-x)).map_eq))

lemma swap_preserving : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) :=
  ⟨measurable_swap, Measure.prod_swap⟩

def chartChange (i : Three) (d : ℝ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  if i = 0 then (chartReflection d).trans (Homeomorph.prodComm ℝ ℝ)
  else if i = 1 then chartReflection d
  else Homeomorph.refl _

lemma chartChange_preserving (i : Three) (d : ℝ) : MeasurePreserving (chartChange i d) := by
  unfold chartChange
  split_ifs
  · exact swap_preserving.comp (chartReflection_preserving d)
  · exact chartReflection_preserving d
  · exact MeasurePreserving.id volume

lemma chartChange_eq (i : Three) (d : ℝ) (z : ℝ × ℝ) :
    chart i d z = chart 2 d (chartChange i d z) := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [chart, chartChange, chartReflection]
  all_goals ring

lemma integral_chart_eq (i j : Three) (d : ℝ) (f : (Three → ℝ) → ℝ) :
    (∫ z : ℝ × ℝ, f (chart i d z)) = ∫ z : ℝ × ℝ, f (chart j d z) := by
  have hi k : (∫ z : ℝ × ℝ, f (chart k d z)) = ∫ z : ℝ × ℝ, f (chart 2 d z) := by
    simp_rw [chartChange_eq k d]
    exact (chartChange_preserving k d).integral_comp (chartChange k d).measurableEmbedding
      (fun z : ℝ × ℝ => f (chart 2 d z))
  exact (hi i).trans (hi j).symm

lemma chart_pair_bound {D : ℝ} {d : ℝ} (hd : |d| ≤ D) (i j k : Three) (hjk : j ≠ k)
    (z : ℝ × ℝ) : z.1^2+z.2^2 ≤ 4*((chart i d z j)^2+(chart i d z k)^2)+3*D^2 := by
  have hD : 0 ≤ D := (abs_nonneg d).trans hd
  have hd2 : d^2 ≤ D^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hD).2 hd
  have hgen (x y : ℝ) : x^2+y^2+(d-x-y)^2 ≤ 4*(x^2+y^2)+3*D^2 := by
    nlinarith [sq_nonneg (x-y), sq_nonneg (d+x), sq_nonneg (d+y)]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num at hjk
  all_goals norm_num [chart]
  all_goals nlinarith [hgen z.1 z.2, hgen (d-z.1-z.2) z.1, hgen (d-z.1-z.2) z.2,
    sq_nonneg z.1, sq_nonneg z.2, sq_nonneg (d-z.1-z.2)]

end
end TriangularHilbert.Heat
end

end OAI
