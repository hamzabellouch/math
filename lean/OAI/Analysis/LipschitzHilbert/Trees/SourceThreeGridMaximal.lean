import OAI.Analysis.LipschitzHilbert.Trees.SourceAllDyadicMaximal
import OAI.Analysis.LipschitzHilbert.Geometry.SourceThreeGridCover
import OAI.Analysis.LipschitzHilbert.Estimates.FiniteEnergySchur

namespace OAI

/-! An actual interval maximal majorant built from three nested grids.
The exceptional set is independent of the real interval parameters. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.DyadicLineGrid

abbrev GridChoice := {q : ℤ // q∈Finset.Icc (-1) 1}

def threeGridMaximal (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ q : GridChoice, allDyadicMaximal q.val f x

theorem gridChoice_card : Fintype.card GridChoice=3 := by
  norm_num [GridChoice]

theorem threeGridMaximal_nonneg (f : ℝ → ℝ) (x : ℝ) :
    0≤threeGridMaximal f x :=
  Finset.sum_nonneg (fun _ _ => allDyadicMaximal_nonneg _ _ _)

theorem threeGridMaximal_measurable (f : ℝ → ℝ) : Measurable (threeGridMaximal f) :=
  Finset.measurable_sum _ (fun _ _ => allDyadicMaximal_measurable _ _)

theorem allDyadicMaximal_le_three (q : GridChoice) (f : ℝ → ℝ) (x : ℝ) :
    allDyadicMaximal q.val f x≤threeGridMaximal f x :=
  Finset.single_le_sum (fun _ _ => allDyadicMaximal_nonneg _ _ _) (Finset.mem_univ q)

theorem threeGridMaximal_energy {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    MemLp (threeGridMaximal f) 2 volume ∧
    (∫ x, (threeGridMaximal f x)^2)≤36*∫ x, (f x)^2 := by
  have hq (q : GridChoice) := allDyadicMaximal_energy q.val hf
  have hm : MemLp (threeGridMaximal f) 2 volume :=
    memLp_finsetSum Finset.univ (fun q _ => (hq q).1)
  have he := weighted_integral_sum_square volume
    (fun q : GridChoice => allDyadicMaximal q.val f) (fun q => (hq q).1)
    (fun _ => (1:ℝ)) (fun _ => by norm_num)
  simp only [div_one,Real.norm_eq_abs,sq_abs,Finset.sum_const,Finset.card_univ,
    gridChoice_card,nsmul_eq_mul,mul_one] at he
  refine ⟨hm,he.trans ?_⟩
  calc
    _ ≤ 3*∑ q : GridChoice, (4*∫ x, (f x)^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun q _ => (hq q).2.1)) (by norm_num)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,gridChoice_card,nsmul_eq_mul]; ring

/-- All real intervals containing a point are controlled simultaneously,
not merely an a.e. set chosen separately for each interval. -/
theorem interval_average_le_threeGridMaximal {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hf0 : ∀ x, 0≤f x) :
    ∀ᵐ x ∂volume, ∀ c r : ℝ, 0<r → x∈Icc (c-r) (c+r) →
      (∫ y in Icc (c-r) (c+r), f y)/(2*r)≤6*threeGridMaximal f x := by
  have hdom : ∀ᵐ x ∂volume, ∀ q : GridChoice, ∀ k : ℤ,
      |cellMean q.val k f x|≤allDyadicMaximal q.val f x :=
    ae_all_iff.mpr (fun q => (allDyadicMaximal_energy q.val hf).2.2)
  filter_upwards [hdom] with x hx
  intro c r hr hxc
  obtain ⟨q,hq,k,j,hsub,hscale⟩ := exists_comparable_three_grid_cover c r hr
  let Q : GridChoice := ⟨q,hq⟩
  have hxcell := hsub hxc
  have hint : IntegrableOn f (cell q k j) :=
    (show MemLp f 2 (rootMeasure q k j) from hf.restrict _).integrable (by norm_num)
  have hI : (∫ y in Icc (c-r) (c+r), f y)≤∫ y in cell q k j, f y :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hsub)
  have heq : (∫ y in cell q k j, f y)=scale k*cellMean q k f x := by
    unfold cellMean
    rw [index_eq_of_mem hxcell]
    field_simp [(scale_pos k).ne']
  have hmean : cellMean q k f x≤threeGridMaximal f x :=
    (le_abs_self _).trans ((hx Q k).trans (allDyadicMaximal_le_three Q f x))
  apply (div_le_iff₀ (by positivity : 0<2*r)).mpr
  calc
    _ ≤ scale k*cellMean q k f x := hI.trans_eq heq
    _ ≤ scale k*threeGridMaximal f x := mul_le_mul_of_nonneg_left hmean (scale_pos k).le
    _ ≤ (12*r)*threeGridMaximal f x :=
      mul_le_mul_of_nonneg_right hscale (threeGridMaximal_nonneg f x)
    _ = _ := by ring

end LipschitzHilbert.DyadicLineGrid

end

end OAI
