import OAI.Geometry.IsometricImmersion.Flows.FlowJointSmooth
import OAI.Geometry.IsometricImmersion.Darboux.ModelPrincipal
import OAI.Geometry.IsometricImmersion.Energy.MultiplierIntegral

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model

def capChartDomain : Set Coord := coordinateRectangle 2 (-2) 2

def capFlowHeight (Y : ℝ → ℝ → ℝ) (p : Coord) : ℝ := Y (p 1) (p 0)

def capChart (Y : ℝ → ℝ → ℝ) (p : Coord) : Coord :=
  coordinatePoint (p 0) (capFlowHeight Y p)

def capChartRho (Y : ℝ → ℝ → ℝ) (p : Coord) : ℝ :=
  1 / coordPartial 1 (capFlowHeight Y) p

def capModelCurvature (kappa : ℝ) (Y : ℝ → ℝ → ℝ) : Coord → ℝ :=
  fun p => modelCurvature kappa (capChart Y p)

theorem capChartDomain_isOpen : IsOpen capChartDomain := coordinateRectangle_isOpen _ _ _

theorem capChart_zero (Y : ℝ → ℝ → ℝ) (p : Coord) : capChart Y p 0 = p 0 := by
  simp [capChart, coordinatePoint]

theorem capChart_one (Y : ℝ → ℝ → ℝ) (p : Coord) : capChart Y p 1 = capFlowHeight Y p := by
  simp [capChart, coordinatePoint]

theorem capChart_eq_vec (Y : ℝ → ℝ → ℝ) (p : Coord) :
    capChart Y p = ![p 0, capFlowHeight Y p] := by
  ext i
  fin_cases i <;> simp [capChart_zero, capChart_one]

variable {Y : ℝ → ℝ → ℝ}

theorem capFlowHeight_contDiffOn
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2)) :
    ContDiffOn ℝ ∞ (capFlowHeight Y) capChartDomain := by
  exact hY.comp ((contDiffOn_apply ℝ ℝ 0 _).prodMk (contDiffOn_apply ℝ ℝ 1 _))
    (fun p hp => hp)

theorem capChart_contDiffOn
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2)) :
    ContDiffOn ℝ ∞ (capChart Y) capChartDomain := by
  exact ((contDiffOn_apply ℝ ℝ 0 _).smul contDiffOn_const).add
    ((capFlowHeight_contDiffOn hY).smul contDiffOn_const)

theorem capModelCurvature_contDiffOn (kappa : ℝ)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2)) :
    ContDiffOn ℝ ∞ (capModelCurvature kappa Y) capChartDomain :=
  (modelCurvature_contDiff kappa).comp_contDiffOn (capChart_contDiffOn hY)

theorem boxPoint_coord_eta (p : Coord) : boxPoint (p 0) (p 1) = p := by
  ext i
  fin_cases i <;> simp [boxPoint]

theorem capFlowHeight_hasDerivAt_time {p : Coord}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hp : p ∈ capChartDomain) :
    HasDerivAt (Y (p 1)) (coordPartial 0 (capFlowHeight Y) p) (p 0) := by
  have hd : DifferentiableAt ℝ (capFlowHeight Y) p :=
    ((capFlowHeight_contDiffOn hY).contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)
  have hd' : DifferentiableAt ℝ (capFlowHeight Y) (boxPoint (p 0) (p 1)) := by
    simpa only [boxPoint_coord_eta] using hd
  have hline := hd'.hasFDerivAt.comp_hasDerivAt (p 0) (boxPoint_hasDerivAt_t (p 0) (p 1))
  change HasDerivAt (fun t => capFlowHeight Y (boxPoint t (p 1)))
    (coordPartial 0 (capFlowHeight Y) (boxPoint (p 0) (p 1))) (p 0) at hline
  have hfun : (fun t => capFlowHeight Y (boxPoint t (p 1))) = Y (p 1) := by
    funext t
    simp [capFlowHeight, boxPoint]
  rw [hfun, boxPoint_coord_eta] at hline
  exact hline

theorem capFlowHeight_hasDerivAt_initial {p : Coord}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hp : p ∈ capChartDomain) :
    HasDerivAt (fun s => Y s (p 0)) (coordPartial 1 (capFlowHeight Y) p) (p 1) := by
  have hd : DifferentiableAt ℝ (capFlowHeight Y) p :=
    ((capFlowHeight_contDiffOn hY).contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)
  have hd' : DifferentiableAt ℝ (capFlowHeight Y) (boxPoint (p 0) (p 1)) := by
    simpa only [boxPoint_coord_eta] using hd
  have hline := hd'.hasFDerivAt.comp_hasDerivAt (p 1) (boxPoint_hasDerivAt_s (p 0) (p 1))
  change HasDerivAt (fun s => capFlowHeight Y (boxPoint (p 0) s))
    (coordPartial 1 (capFlowHeight Y) (boxPoint (p 0) (p 1))) (p 1) at hline
  have hfun : (fun s => capFlowHeight Y (boxPoint (p 0) s)) = (fun s => Y s (p 0)) := by
    funext s
    simp [capFlowHeight, boxPoint]
  rw [hfun, boxPoint_coord_eta] at hline
  exact hline

variable {q : Coord → ℝ}

theorem capFlowHeight_partial_time {p : Coord}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hp : p ∈ capChartDomain) :
    coordPartial 0 (capFlowHeight Y) p = -q (capChart Y p) := by
  have ht : p 0 ∈ Ioo (-2 : ℝ) 2 := hp.1
  have hs : p 1 ∈ Ioo (-2 : ℝ) 2 := hp.2
  have ho := (hode (p 1) ⟨hs.1.le, hs.2.le⟩ (p 0) ⟨ht.1.le, ht.2.le⟩).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)
  exact (capFlowHeight_hasDerivAt_time hY hp).unique ho

theorem capFlowHeight_partial_initial_pos {p : Coord}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s)
    (hp : p ∈ capChartDomain) : 0 < coordPartial 1 (capFlowHeight Y) p := by
  rw [← (capFlowHeight_hasDerivAt_initial hY hp).deriv]
  exact hvar (p 1) hp.2 (p 0) hp.1

theorem capChartRho_pos {p : Coord}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s)
    (hp : p ∈ capChartDomain) : 0 < capChartRho Y p :=
  one_div_pos.mpr (capFlowHeight_partial_initial_pos hY hvar hp)

theorem capChartRho_contDiffOn
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s) :
    ContDiffOn ℝ ∞ (capChartRho Y) capChartDomain :=
  contDiffOn_const.div (partial_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen 1)
    (fun _ hp => (capFlowHeight_partial_initial_pos hY hvar hp).ne')

theorem capModelCurvature_partial (kappa : ℝ) {p : Coord}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hp : p ∈ capChartDomain) (i : Fin 2) :
    coordPartial i (capModelCurvature kappa Y) p =
      (if i = 0 then 2 * kappa * p 0 else 0) +
        coordPartial 1 (modelCurvature kappa) (capChart Y p) * coordPartial i (capFlowHeight Y) p := by
  have hheight : DifferentiableAt ℝ (capFlowHeight Y) p :=
    ((capFlowHeight_contDiffOn hY).contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)
  have hh := ((modelProfile_contDiff.differentiable (by simp) (capFlowHeight Y p)).hasDerivAt).comp_hasFDerivAt
    p hheight.hasFDerivAt
  have hx := hasFDerivAt_apply (𝕜 := ℝ) 0 p
  have hd := ((hx.pow 2).sub hh).const_mul kappa
  simp only [Function.comp_def, Pi.sub_def] at hd
  have hfun : capModelCurvature kappa Y =
      (fun z => kappa * ((z 0) ^ 2 - modelProfile (capFlowHeight Y z))) := by
    funext z
    simp only [capModelCurvature, modelCurvature, capChart_zero, capChart_one]
  rw [hfun, modelCurvature_partial]
  simp only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, capChart_one, coordPartial]
  rw [hd.fderiv]
  fin_cases i <;> simp <;> ring

theorem capModelCurvature_partial_time (kappa : ℝ) {p : Coord}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hp : p ∈ capChartDomain) :
    coordPartial 0 (capModelCurvature kappa Y) p = 2 * kappa * p 0 -
      q (capChart Y p) * coordPartial 1 (modelCurvature kappa) (capChart Y p) := by
  rw [capModelCurvature_partial kappa hY hp 0, capFlowHeight_partial_time hY hode hp]
  norm_num only [↓reduceIte]
  ring

theorem capModelCurvature_partial_initial (kappa : ℝ) {p : Coord}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hp : p ∈ capChartDomain) :
    coordPartial 1 (capModelCurvature kappa Y) p =
      coordPartial 1 (modelCurvature kappa) (capChart Y p) / capChartRho Y p := by
  rw [capModelCurvature_partial kappa hY hp 1]
  simp [capChartRho, div_eq_mul_inv]

theorem capChart_mem_modelSquare {p : Coord} (hp : p ∈ capChartDomain)
    (hdisp : |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50) :
    capChart Y p ∈ modelSquare := by
  apply coordinatePoint_mem_modelSquare
  · exact ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
  · have hd := abs_le.mp hdisp
    exact ⟨by linarith [hp.2.1, hd.1], by linarith [hp.2.2, hd.2]⟩

theorem cap_model_full_principal_lower
    {G : Coord → ℝ} {p : Coord} {kappa g0 rhoMax epsilon MG : ℝ}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s)
    (hdisp : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      |Y s t - s| ≤ (1 : ℝ) / 50)
    (hqsmall : ∀ z ∈ modelSquare, |q z| ≤ (1 : ℝ) / 100)
    (hp : p ∈ capChartDomain) (hs : p 1 ≤ 0) (ell : ℕ)
    (hGdiff : DifferentiableAt ℝ G p) (hkappa : 0 < kappa) (hg0 : 0 < g0)
    (hG : g0 ≤ G p) (hrhoMax : capChartRho Y p ≤ rhoMax)
    (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hsmall : epsilon * 2 * ((1 : ℝ) / 100) ≤ ((ell : ℝ) + 1 / 2) / rhoMax)
    (hGsi : |coordPartial 1 G p| ≤ MG) (hGti : |coordPartial 0 G p| ≤ MG)
    (hKsmall : |capModelCurvature kappa Y p| ≤
      modelPrincipalRadius g0 kappa rhoMax epsilon 2 MG ell) :
    modelCoercivityMargin g0 kappa rhoMax epsilon ell / 2 ≤
      directedPrincipal (fun z => G z * capModelCurvature kappa Y z) ell epsilon p := by
  have hdispP : |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50 :=
    hdisp (p 1) ⟨hp.2.1.le, hp.2.2.le⟩ (p 0) ⟨hp.1.1.le, hp.1.2.le⟩
  have hy : capFlowHeight Y p ≤ 1 / 50 := by linarith [(abs_le.mp hdispP).2]
  have hKdiff : DifferentiableAt ℝ (capModelCurvature kappa Y) p :=
    ((capModelCurvature_contDiffOn kappa hY).contDiffAt
      (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)
  have hKvalue : capModelCurvature kappa Y p =
      modelCurvature kappa ![p 0, capFlowHeight Y p] := by
    unfold capModelCurvature
    rw [capChart_eq_vec]
  have hKs : coordPartial 1 (capModelCurvature kappa Y) p =
      coordPartial 1 (modelCurvature kappa) ![p 0, capFlowHeight Y p] / capChartRho Y p := by
    rw [capModelCurvature_partial_initial kappa hY hp, capChart_eq_vec]
  have hKt : coordPartial 0 (capModelCurvature kappa Y) p =
      2 * kappa * p 0 - q (capChart Y p) *
        coordPartial 1 (modelCurvature kappa) ![p 0, capFlowHeight Y p] := by
    rw [capModelCurvature_partial_time kappa hY hode hp]
    rw [capChart_eq_vec]
  exact model_full_principal_lower ell hGdiff hKdiff hkappa hg0 hG
    (capChartRho_pos hY hvar hp) hrhoMax heps heps1 (abs_lt.mpr hp.1).le
    (hqsmall _ (capChart_mem_modelSquare hp hdispP)) hsmall hy hGsi hGti hKvalue hKs hKt hKsmall

theorem exists_cap_curvature_chart {U : Set Coord}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hsmall : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100) :
    ∃ Y : ℝ → ℝ → ℝ,
      ContDiffOn ℝ ∞ (capChart Y) capChartDomain ∧
      ContDiffOn ℝ ∞ (capChartRho Y) capChartDomain ∧
      (∀ p ∈ capChartDomain, 0 < capChartRho Y p) ∧
      (∀ p ∈ capChartDomain, |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50) ∧
      (∀ kappa : ℝ, ContDiffOn ℝ ∞ (capModelCurvature kappa Y) capChartDomain) ∧
      (∀ kappa : ℝ, ∀ p ∈ capChartDomain,
        coordPartial 0 (capModelCurvature kappa Y) p = 2 * kappa * p 0 -
          q (capChart Y p) * coordPartial 1 (modelCurvature kappa) (capChart Y p) ∧
        coordPartial 1 (capModelCurvature kappa Y) p =
          coordPartial 1 (modelCurvature kappa) (capChart Y p) / capChartRho Y p) := by
  obtain ⟨Y, hY, hstart, hode, hdisp, hvar⟩ := exists_smooth_cap_flow hq hU hSU hsmall
  have hvarpos : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s := fun s hs t ht => (hvar s hs t ht).2
  refine ⟨Y, capChart_contDiffOn hY, capChartRho_contDiffOn hY hvarpos,
    fun p hp => capChartRho_pos hY hvarpos hp, ?_,
    fun kappa => capModelCurvature_contDiffOn kappa hY, ?_⟩
  · intro p hp
    exact hdisp (p 1) ⟨hp.2.1.le, hp.2.2.le⟩ (p 0) ⟨hp.1.1.le, hp.1.2.le⟩
  · intro kappa p hp
    exact ⟨capModelCurvature_partial_time kappa hY hode hp,
      capModelCurvature_partial_initial kappa hY hp⟩

end SmoothLocal.Flow

end

end OAI
