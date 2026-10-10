import OAI.NumberTheory.Jacobsthal.Probability.ThirdInnerKernel

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionBindings
open ErdosContinuousOmission ErdosContinuousBoundary ErdosBoundaryLoss

noncomputable def thirdLowerIntegral (p : ℝ×ℝ) : ℝ :=
  ∫ t : ℝ in 1..baseCutoff p.2,clampedThird p.1 p.2 t

noncomputable def thirdUpperIntegral (p : ℝ×ℝ) : ℝ :=
  ∫ x : ℝ in baseCutoff p.1..2,clampedThird x p.1 p.2

theorem thirdLowerIntegral_continuous : Continuous thirdLowerIntegral := by
  let F : (ℝ×ℝ) → ℝ → ℝ := fun p t => clampedThird p.1 p.2 t
  have hF : Continuous F.uncurry := by
    change Continuous ((fun q : ℝ×ℝ×ℝ => clampedThird q.1 q.2.1 q.2.2) ∘
      (fun p : (ℝ×ℝ)×ℝ => (p.1.1,p.1.2,p.2)))
    exact clampedThird_continuous.comp
      (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
  exact continuous_variable_upper_integral F hF (fun p => baseCutoff p.2)
    (baseCutoff_continuous.comp continuous_snd)

theorem thirdUpperIntegral_continuous : Continuous thirdUpperIntegral := by
  let F : (ℝ×ℝ) → ℝ → ℝ := fun p x => clampedThird x p.1 p.2
  have hF : Continuous F.uncurry := by
    change Continuous ((fun q : ℝ×ℝ×ℝ => clampedThird q.1 q.2.1 q.2.2) ∘
      (fun p : (ℝ×ℝ)×ℝ => (p.2,p.1.1,p.1.2)))
    exact clampedThird_continuous.comp
      (continuous_snd.prodMk (continuous_fst.fst.prodMk continuous_fst.snd))
  have h2 := continuous_variable_upper_integral F hF (fun _ => (2:ℝ)) continuous_const
  have hc := continuous_variable_upper_integral F hF (fun p => baseCutoff p.1)
    (baseCutoff_continuous.comp continuous_fst)
  have he (p : ℝ×ℝ) : (∫ x : ℝ in 1..2,F p x)-(∫ x : ℝ in 1..baseCutoff p.1,F p x)=thirdUpperIntegral p := by
    have hf : Continuous (F p) := by
      change Continuous (F.uncurry ∘ (fun x : ℝ => (p,x)))
      exact hF.comp (continuous_const.prodMk continuous_id)
    have hi := intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (μ := volume) 1 (baseCutoff p.1))
      (hf.intervalIntegrable (μ := volume) (baseCutoff p.1) 2)
    change (∫ x in 1..2,F p x)-(∫ x in 1..baseCutoff p.1,F p x)=∫ x in baseCutoff p.1..2,F p x
    linarith
  exact (h2.sub hc).congr he

theorem thirdLowerIntegral_bound (p : ℝ×ℝ) : |thirdLowerIntegral p| ≤ 64 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a:=1) (b:=baseCutoff p.2)
    (C:=64) (f:=fun t => clampedThird p.1 p.2 t)
    (fun t _ => by simpa only [Real.norm_eq_abs] using clampedThird_bound p.1 p.2 t)
  have hc := baseCutoff_bounds p.2
  change |thirdLowerIntegral p| ≤ 64
  rw [Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ baseCutoff p.2-1)] at h
  exact h.trans (by nlinarith)

theorem thirdUpperIntegral_bound (p : ℝ×ℝ) : |thirdUpperIntegral p| ≤ 64 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a:=baseCutoff p.1) (b:=2)
    (C:=64) (f:=fun x => clampedThird x p.1 p.2)
    (fun x _ => by simpa only [Real.norm_eq_abs] using clampedThird_bound x p.1 p.2)
  have hc := baseCutoff_bounds p.1
  change |thirdUpperIntegral p| ≤ 64
  rw [Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ 2-baseCutoff p.1)] at h
  exact h.trans (by nlinarith)

theorem thirdLowerIntegral_eq {x u : ℝ} (hx : x ∈ Icc (1:ℝ) 2) (hu : u ∈ Icc (1:ℝ) 2) :
    thirdLowerIntegral (x,u)=∫ t : ℝ in 1..u,loss3Kernel t u x := by
  rw [thirdLowerIntegral,baseCutoff_on hu.1 hu.2]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hu.1] at ht
  exact clampedThird_eq hx hu ⟨ht.1,ht.2.trans hu.2⟩

theorem thirdUpperIntegral_eq {u t : ℝ} (hu : u ∈ Icc (1:ℝ) 2) (ht : t ∈ Icc (1:ℝ) 2) :
    thirdUpperIntegral (u,t)=∫ x : ℝ in u..2,loss3Kernel t u x := by
  rw [thirdUpperIntegral,baseCutoff_on hu.1 hu.2]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hu.2] at hx
  exact clampedThird_eq ⟨hu.1.trans hx.1,hx.2⟩ hu ht

end ErdosOmissionBindings

end

end Erdos970

end OAI
