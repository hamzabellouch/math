import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.NeumannCounts

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CubeDensity_scope

open MeasureTheory Set Filter
open scoped BigOperators unitInterval

variable {N : ℕ} {d : Type*} [Fintype d]

lemma integral_sameCube_y (t x : d → ℝ) : (∫ y, sameCube t x y) = 1 := by
  have he : (fun y => sameCube t x y) =
      fun y => (floorCube (cubeIndex (x-t))).indicator (fun _ => (1:ℝ)) (y-t) := by
    funext y
    have hm : y-t ∈ floorCube (cubeIndex (x-t)) ↔ cubeIndex (x-t)=cubeIndex (y-t) := by
      simp only [floorCube,mem_ofPred_eq,cubeIndex,funext_iff]
      exact forall_congr' (fun i => eq_comm)
    simp only [sameCube,Set.indicator,hm]
  rw [he,integral_sub_right_eq_self,integral_indicator (floorCube_measurable _),setIntegral_const]
  simp [measureReal_def,volume_floorCube]

lemma sameCube_y_integrable (t x : d → ℝ) : Integrable (fun y => sameCube t x y) := by
  have hi := ((integrableOn_const (C := (1:ℝ)) (μ := volume) (s := floorCube (cubeIndex (x-t)))
    (by simp [volume_floorCube])).integrable_indicator (floorCube_measurable _)).comp_sub_right t
  convert hi using 1
  funext y
  have hm : y-t ∈ floorCube (cubeIndex (x-t)) ↔ cubeIndex (x-t)=cubeIndex (y-t) := by
    simp only [floorCube,mem_ofPred_eq,cubeIndex,funext_iff]
    exact forall_congr' (fun i => eq_comm)
  simp only [sameCube,Set.indicator,hm]

def cubeDensity (t : d → ℝ) (x : Fin N → d → ℝ) (y : d → ℝ) : ℝ :=
  ∑ i, sameCube t (x i) y

def cubeAssignment (t : d → ℝ) (x : Fin N → d → ℝ) (i : Fin N) : d → ℤ :=
  cubeIndex (x i-t)

lemma cubeDensity_count (t : d → ℝ) (x : Fin N → d → ℝ) (y : d → ℝ) :
    cubeDensity t x y = (cellCount (cubeAssignment t x) (cubeIndex (y-t)):ℝ) := by
  classical
  simp only [cubeDensity,sameCube,cubeAssignment,cellCount]
  rw [Finset.sum_boole]
  congr 1

lemma cubeDensity_nonneg (t : d → ℝ) (x : Fin N → d → ℝ) (y : d → ℝ) :
    0 ≤ cubeDensity t x y := Finset.sum_nonneg (fun _ _ => sameCube_nonneg _ _ _)

lemma cubeDensity_le (t : d → ℝ) (x : Fin N → d → ℝ) (y : d → ℝ) : cubeDensity t x y ≤ N := by
  rw [cubeDensity_count]
  exact_mod_cast cellCount_le (cubeAssignment t x) (cubeIndex (y-t))

lemma cellCount_rpow_query {C : Type*} [DecidableEq C] (c : Fin N → C) (q : C) :
    (cellCount c q:ℝ)^(5/3:ℝ) = ∑ i, if c i=q then (cellCount c (c i):ℝ)^(2/3:ℝ) else 0 := by
  classical
  have he : (∑ i : Fin N, if c i=q then (cellCount c (c i):ℝ)^(2/3:ℝ) else 0) =
      (cellCount c q:ℝ)*(cellCount c q:ℝ)^(2/3:ℝ) := by
    simp_rw [←Finset.sum_filter]
    calc
      _ = ∑ i ∈ Finset.univ.filter (fun i => c i=q), (cellCount c q:ℝ)^(2/3:ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
      _ = _ := by simp [cellCount]
  rw [he,show (5/3:ℝ)=1+(2/3:ℝ) by norm_num,
    Real.rpow_add' (Nat.cast_nonneg _) (by norm_num),Real.rpow_one]

lemma cubeDensity_rpow (t : d → ℝ) (x : Fin N → d → ℝ) (y : d → ℝ) :
    cubeDensity t x y^(5/3:ℝ) =
      ∑ i, sameCube t (x i) y*(cellCount (cubeAssignment t x) (cubeAssignment t x i):ℝ)^(2/3:ℝ) := by
  rw [cubeDensity_count,cellCount_rpow_query]
  apply Finset.sum_congr rfl
  intro i _
  unfold sameCube cubeAssignment
  split_ifs <;> simp

lemma cubeDensity_rpow_integrable (t : d → ℝ) (x : Fin N → d → ℝ) :
    Integrable (fun y => cubeDensity t x y^(5/3:ℝ)) := by
  simp_rw [cubeDensity_rpow]
  exact integrable_finsetSum _ (fun i _ => (sameCube_y_integrable t (x i)).mul_const _)

theorem integral_cubeDensity_rpow (t : d → ℝ) (x : Fin N → d → ℝ) :
    (∫ y, cubeDensity t x y^(5/3:ℝ)) = cellPressure (cubeAssignment t x) := by
  simp_rw [cubeDensity_rpow]
  rw [integral_finsetSum _ (fun i _ => (sameCube_y_integrable t (x i)).mul_const _)]
  simp only [integral_mul_const,integral_sameCube_y,one_mul,cellPressure]

lemma integral_cubeDensity_t (x : Fin N → d → ℝ) (y : d → ℝ) :
    (∫ t : d → I, cubeDensity (fun a => (t a:ℝ)) x y) = ∑ i, cubeOverlap (x i-y) := by
  unfold cubeDensity
  rw [integral_finsetSum _ (fun i _ => sameCube_I_integrable (x i) y)]
  simp only [integral_sameCube]

end Work_CubeDensity_scope

open MeasureTheory Set Filter
open scoped BigOperators

variable {A Y : Type*} [MeasurableSpace A] [MeasurableSpace Y]
  {μ : Measure A} {ν : Measure Y} [IsProbabilityMeasure μ] [SFinite ν]

theorem average_pressure
    {f : A → Y → ℝ} (hm : Measurable (Function.uncurry f))
    (hn : ∀ a y, 0 ≤ f a y) {C B : ℝ} (hc : ∀ a y, f a y ≤ C)
    (hi : ∀ a, Integrable (fun y => (f a y)^(5/3:ℝ)) ν)
    (hb : ∀ a, (∫ y, (f a y)^(5/3:ℝ) ∂ν) ≤ B) :
    Integrable (fun y => (∫ a, f a y ∂μ)^(5/3:ℝ)) ν ∧
      (∫ y, (∫ a, f a y ∂μ)^(5/3:ℝ) ∂ν) ≤ ∫ a, (∫ y, (f a y)^(5/3:ℝ) ∂ν) ∂μ := by
  have hpm : Measurable (fun p : A × Y => (f p.1 p.2)^(5/3:ℝ)) :=
    hm.pow_const _
  have hpi : Integrable (fun p : A × Y => (f p.1 p.2)^(5/3:ℝ)) (μ.prod ν) := by
    apply (integrable_prod_iff hpm.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall hi,?_⟩
    simp only [Real.norm_of_nonneg (Real.rpow_nonneg (hn _ _) _)]
    apply (integrable_const B).mono' hpm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
    exact Eventually.of_forall fun a => by
      rw [Real.norm_of_nonneg (integral_nonneg (fun y => Real.rpow_nonneg (hn a y) _))]
      exact hb a
  have hfi (y : Y) : Integrable (fun a => f a y) μ := by
    apply (integrable_const C).mono' (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    exact Eventually.of_forall (fun a => by change ‖f a y‖ ≤ C; rw [Real.norm_of_nonneg (hn a y)]; exact hc a y)
  have hpiy (y : Y) : Integrable (fun a => (f a y)^(5/3:ℝ)) μ := by
    apply (integrable_const ((max C 0)^(5/3:ℝ))).mono'
      (hpm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    exact Eventually.of_forall fun a => by
      change ‖(f a y)^(5/3:ℝ)‖ ≤ (max C 0)^(5/3:ℝ)
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (hn a y) _)]
      exact Real.rpow_le_rpow (hn a y) ((hc a y).trans (le_max_left _ _)) (by norm_num)
  have hj (y : Y) : (∫ a, f a y ∂μ)^(5/3:ℝ) ≤ ∫ a, (f a y)^(5/3:ℝ) ∂μ := by
    apply (convexOn_rpow (by norm_num : (1:ℝ) ≤ 5/3)).map_integral_le
      (Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 5/3)).continuousOn isClosed_Ici (Eventually.of_forall (fun a => hn a y)) (hfi y) (hpiy y)
  have han (y : Y) : 0 ≤ (∫ a, f a y ∂μ)^(5/3:ℝ) :=
    Real.rpow_nonneg (integral_nonneg (fun a => hn a y)) _
  have hai : Integrable (fun y => (∫ a, f a y ∂μ)^(5/3:ℝ)) ν := by
    apply hpi.integral_prod_right.mono'
      (hm.stronglyMeasurable.integral_prod_left'.measurable.pow_const _).aestronglyMeasurable
    exact Eventually.of_forall (fun y => by change ‖(∫ a, f a y ∂μ)^(5/3:ℝ)‖ ≤ ∫ a, (f a y)^(5/3:ℝ) ∂μ; rw [Real.norm_of_nonneg (han y)]; exact hj y)
  refine ⟨hai,?_⟩
  calc
    _ ≤ ∫ y, ∫ a, (f a y)^(5/3:ℝ) ∂μ ∂ν := integral_mono hai hpi.integral_prod_right hj
    _ = _ := (integral_integral_swap hpi).symm

end CoulombNeumann

end

end OAI
