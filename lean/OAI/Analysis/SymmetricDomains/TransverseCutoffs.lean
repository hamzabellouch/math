import Mathlib
import OAI.Analysis.SymmetricDomains.BishopBoundarySolution
import OAI.Analysis.SymmetricDomains.RealMeanPositive
import OAI.Analysis.SymmetricDomains.SchwarzRadialExpansion

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
namespace Release061.Wiener

lemma vanishingFactor_real : conjugate vanishingFactor = vanishingFactor := by
  have h2 : conjugate (2 : Space) = 2 := by
    rw [show (2 : Space) = 1+1 by ring,map_add,conjugate_one]
  simp only [vanishingFactor,map_sub,h2,conjugate_single,map_one,neg_neg]
  ring

def vanishingReal : realAlgebra := ⟨vanishingFactor,vanishingFactor_real⟩

lemma vanishingReal_eval (θ : Circle) : realEvaluation θ vanishingReal = 2-2*circleCos θ := by
  change (boundary (2-((AddMonoidAlgebra.single 1 1 : Poly) : Space)-
    ((AddMonoidAlgebra.single (-1) 1 : Poly) : Space)) θ).re = _
  have h2 : boundary (2 : Space) = 2 := by
    rw [show (2 : Space) = 1+1 by ring,map_add,boundary_one]
    ring
  simp only [map_sub,h2,boundary_single,one_smul,ContinuousMap.sub_apply,
    Complex.sub_re,fourier_neg,Complex.conj_re]
  change (2 : ℂ).re-(fourier 1 θ).re-(fourier 1 θ).re = _
  norm_num [circleCos]
  ring

lemma vanishingReal_nonneg (θ : Circle) : 0 ≤ realEvaluation θ vanishingReal := by
  rw [vanishingReal_eval]
  have hn : (fourier 1 θ).re ≤ 1 := by
    apply (Complex.re_le_norm _).trans
    simpa only [fourier_one] using (_root_.Circle.norm_coe (AddCircle.toCircle θ)).le
  change 0 ≤ 2-2*(fourier 1 θ).re
  linarith

lemma coeff_zero_real (g : realAlgebra) : (coeff 0 (g : Space)).im = 0 := by
  have hint : Integrable (fun θ => boundary (g : Space) θ) AddCircle.haarAddCircle :=
    (boundary (g : Space)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (fourierCoeff (boundary (g : Space)) 0).im = 0
  simp only [fourierCoeff,neg_zero,fourier_zero,one_smul]
  have hi := integral_im hint
  change (∫ θ, (boundary (g : Space) θ).im ∂AddCircle.haarAddCircle) =
    (∫ θ, boundary (g : Space) θ ∂AddCircle.haarAddCircle).im at hi
  rw [← hi]
  simp only [realAlgebra_boundary_im,integral_zero]

def realMean : realAlgebra →L[ℝ] ℝ :=
  Complex.reCLM.comp (((coeff 0).restrictScalars ℝ).comp realAlgebra.toSubmodule.subtypeL)

lemma coeff_zero_eq_realMean (g : realAlgebra) : coeff 0 (g : Space) = (realMean g : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using coeff_zero_real g

lemma localized_division {κ : realAlgebra}
    (hκ : ∀ θ, dist (circleCos θ) (-1 : ℝ) ≤ 1/2 →
      (2-2*circleCos θ)*realEvaluation θ κ = 1)
    {Y : realAlgebra}
    (hY : ∀ θ, (1/2 : ℝ) < dist (circleCos θ) (-1 : ℝ) → realEvaluation θ Y = 0) :
    Y = vanishingReal*(κ*Y) := by
  apply realEvaluation_ext
  intro θ
  rw [map_mul,map_mul,vanishingReal_eval]
  by_cases hθ : dist (circleCos θ) (-1 : ℝ) ≤ 1/2
  · rw [← mul_assoc,hκ θ hθ,one_mul]
  · rw [hY θ (lt_of_not_ge hθ),mul_zero,mul_zero]

lemma localized_radial_expansion {κ : realAlgebra}
    (hκ : ∀ θ, dist (circleCos θ) (-1 : ℝ) ≤ 1/2 →
      (2-2*circleCos θ)*realEvaluation θ κ = 1)
    {Y : realAlgebra}
    (hY : ∀ θ, (1/2 : ℝ) < dist (circleCos θ) (-1 : ℝ) → realEvaluation θ Y = 0)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    discValue (Y : Space) (1-(t : ℂ)) =
      Complex.I*(t : ℂ)*(2*realMean (κ*Y) : ℝ) -
        (t : ℂ)^2/(1-(t : ℂ))*(discValue (κ*Y : Space) (1-(t : ℂ))-discValue (κ*Y : Space) 0) := by
  have he := congrArg (fun f : realAlgebra => (f : Space)) (localized_division hκ hY)
  change (Y : Space) = vanishingFactor*((κ*Y : realAlgebra) : Space) at he
  have hs := schwarz_radial_expansion ((κ*Y : realAlgebra) : Space) ht ht1
  rw [← he,coeff_zero_eq_realMean] at hs
  rw [hs]
  push_cast
  ring

theorem exists_transverse_cutoffs :
    ∃ lam η κ : realAlgebra,
      (∀ θ, 0 ≤ realEvaluation θ lam ∧ 0 ≤ realEvaluation θ η) ∧
      (∀ θ, (1/2 : ℝ) ≤ dist (circleCos θ) (-1 : ℝ) →
        realEvaluation θ lam = 0 ∧ realEvaluation θ η = 0) ∧
      (∀ θ, realEvaluation θ η ≠ 0 → realEvaluation θ lam = 1) ∧
      (∀ θ, dist (circleCos θ) (-1 : ℝ) ≤ 1/2 →
        (2-2*circleCos θ)*realEvaluation θ κ = 1) ∧
      0 < 2*realMean (κ*η) := by
  let L : ContDiffBump (-1 : ℝ) := ⟨1/4,1/2,by norm_num,by norm_num⟩
  let H : ContDiffBump (-1 : ℝ) := ⟨1/16,1/8,by norm_num,by norm_num⟩
  obtain ⟨lam,hlam⟩ := exists_real_boundary_of_weighted_summable
    (cosineBump (1/4) (1/2) (by norm_num) (by norm_num))
    (cosineBump_weighted_summable _ _ _ _ (by norm_num))
  obtain ⟨g,hg⟩ := exists_real_boundary_of_weighted_summable
    (cosineBump (1/16) (1/8) (by norm_num) (by norm_num))
    (cosineBump_weighted_summable _ _ _ _ (by norm_num))
  have hl (θ : Circle) : realEvaluation θ lam = L (circleCos θ) := hlam θ
  have hh (θ : Circle) : realEvaluation θ g = H (circleCos θ) := hg θ
  obtain ⟨κ,hκ⟩ := exists_localized_reciprocal
  let η := vanishingReal*g
  have hgs : ∀ θ, (1/2 : ℝ) < dist (circleCos θ) (-1 : ℝ) → realEvaluation θ g = 0 := by
    intro θ hθ
    rw [hh]
    apply H.zero_of_le_dist
    change (1/8 : ℝ) ≤ _
    linarith
  have hkg : κ*η = g := by
    have he := localized_division hκ hgs
    calc
      κ*η = vanishingReal*(κ*g) := by dsimp only [η]; ring
      _ = g := he.symm
  refine ⟨lam,η,κ,?_,?_,?_,hκ,?_⟩
  · intro θ
    rw [hl]
    refine ⟨L.nonneg,?_⟩
    change 0 ≤ realEvaluation θ (vanishingReal*g)
    rw [map_mul,hh]
    exact mul_nonneg (vanishingReal_nonneg θ) H.nonneg
  · intro θ hθ
    rw [hl]
    have hz : H (circleCos θ) = 0 := H.zero_of_le_dist (by change (1/8 : ℝ) ≤ _; linarith)
    refine ⟨L.zero_of_le_dist hθ,?_⟩
    change realEvaluation θ (vanishingReal*g) = 0
    rw [map_mul,hh,hz,mul_zero]
  · intro θ hθ
    rw [hl]
    have hgθ : H (circleCos θ) ≠ 0 := by
      intro hz
      apply hθ
      change realEvaluation θ (vanishingReal*g) = 0
      rw [map_mul,hh,hz,mul_zero]
    have hd : dist (circleCos θ) (-1 : ℝ) < (1/8 : ℝ) := by
      by_contra hn
      exact hgθ (H.zero_of_le_dist (le_of_not_gt hn))
    exact L.one_of_mem_closedBall (by change dist (circleCos θ) (-1 : ℝ) ≤ 1/4; linarith)
  · rw [hkg]
    apply mul_pos (by norm_num : (0 : ℝ) < 2)
    apply real_mean_positive g (fun θ => by rw [hh]; exact H.nonneg)
      (θ₀ := ((1/2 : ℝ) : Circle))
    rw [hh,circleCos_half,H.one_of_mem_closedBall (by simp [H,Metric.mem_closedBall])]
    exact one_ne_zero

end Release061.Wiener

end

end OAI
