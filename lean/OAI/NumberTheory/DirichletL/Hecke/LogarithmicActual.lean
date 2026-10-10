import OAI.NumberTheory.DirichletL.Hecke.Logarithmic
import OAI.NumberTheory.DirichletL.Hecke.EulerLog
import OAI.NumberTheory.DirichletL.Hecke.DeletionReciprocal

namespace OAI

noncomputable section
open scoped Classical Topology
open Set Metric
namespace SevenEighths.HeckeLogarithmicActual
open HeckeFamily HeckeLogarithmicInput HeckeLogarithmic

def eulerLog (η : Character) : ℂ → ℂ :=
  if η.residue = 1 then HeckeEulerLog.principalEulerLog (idealCoeff η)
  else HeckeEulerLog.eulerLog (idealCoeff η)

def innerBound : ℝ := 3+HeckeEulerLog.eulerLogBound

theorem innerBound_ge_one : 1 ≤ innerBound := by
  unfold innerBound
  linarith [HeckeEulerLog.eulerLogBound_ge_one]

theorem actual_inner_log (η : Character) (t : ℝ) :
    DifferentiableOn ℂ (eulerLog η) (ball ((2 : ℂ)+t*Complex.I) (1/2)) ∧
    EqOn (Complex.exp ∘ eulerLog η) (regular η) (ball ((2 : ℂ)+t*Complex.I) (1/2)) ∧
    ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (49/100), ‖eulerLog η z‖ ≤ innerBound := by
  by_cases hη : η.residue = 1
  · have hright (s : ℂ) (hs : 1<s.re) : regular η s =
        ((s-1)/(s+1))*IdealEuler.series (idealCoeff η) s := by
      have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
      have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
      simp only [regular, ite_eq_left hη, HeckePrincipalStrip.sourceNormalized]
      rw [HeckeOrigin.poleRemoved_eq η h0 h1, LFunction_eq_series η hs]
      ring
    simpa only [eulerLog, ite_eq_left hη, innerBound] using
      HeckeEulerLog.principal_continued_inner_disk (idealCoeff η) (idealCoeff_norm_le_one η)
        (regular η) hright t
  · have hright (s : ℂ) (hs : 1<s.re) : regular η s = IdealEuler.series (idealCoeff η) s := by
      rw [regular_eq_nonprincipal η hη]
      exact LFunction_eq_series η hs
    obtain ⟨hd,he,hb⟩ := HeckeEulerLog.continued_inner_disk (idealCoeff η)
      (idealCoeff_norm_le_one η) (regular η) hright t
    simp only [eulerLog, ite_eq_right hη]
    refine ⟨hd,he,?_⟩
    intro z hz
    have h := hb z hz
    unfold innerBound
    linarith

theorem disk_control (e ε : ℝ) (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ D B : ℝ, 0<D ∧ 0≤B ∧ ∀ (η : Character),
      FiniteFourier.IsPrimitiveOnIdeals η.residue → ∀ a t : ℝ,
      1/2≤a → a≤1 →
      (∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), regular η z ≠ 0) →
      (∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-6*e),
        ‖regular η z‖ + ‖(regular η z)⁻¹‖ ≤ D*(complexity η t)^ε) ∧
      (∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-8*e),
        ‖deriv (regular η) z / regular η z‖ ≤ B*Real.log (complexity η t)) := by
  obtain ⟨D,B,hD,hB,hb⟩ := disk_control_of_euler_log e innerBound ε he he' innerBound_ge_one hε
  refine ⟨D,B,hD,hB,?_⟩
  intro η hp a t ha ha' hzero
  obtain ⟨hE,hEL,hEb⟩ := actual_inner_log η t
  exact hb η hp a t (eulerLog η) ha ha' hzero hE hEL hEb

theorem primitive_reciprocal_subpower (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ D : ℝ, 0<D ∧ ∀ (η : Character), FiniteFourier.IsPrimitiveOnIdeals η.residue →
      ∀ s : ℂ, HeckeZeroSupremum.beta+8*e ≤ s.re →
        ‖HeckeReciprocal.reciprocal η s‖ ≤ D*(complexity η s.im)^ε := by
  obtain ⟨D,B,hD,_,hb⟩ := disk_control e ε he he' hε
  have hEuler : 0 ≤ HeckeReciprocalBound.bound 2 := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨D+HeckeReciprocalBound.bound 2, by linarith, ?_⟩
  intro η hp s hs
  have hcomp : 1 ≤ (complexity η s.im)^ε := Real.one_le_rpow
    ((Real.one_le_exp (by norm_num : (0 : ℝ)≤1)).trans (complexity_ge_exp η s.im)) hε.le
  by_cases hs2 : s.re ≤ 2
  · have hbound := (hb η hp HeckeZeroSupremum.beta s.im HeckeZeroSupremum.half_le_beta
      HeckeZeroSupremum.beta_le_one (fun z hz => regular_ne_zero_on_disk η HeckeZeroSupremum.beta e s.im le_rfl he hz)).1
    have hmem : s ∈ closedBall ((2 : ℂ)+s.im*Complex.I) (2-HeckeZeroSupremum.beta-6*e) := by
      have h := LogarithmicControl.same_height_mem_disk (a := HeckeZeroSupremum.beta)
        (e := e) (t := s.im) (v := 8*e) le_rfl hs hs2
      rw [Complex.re_add_im] at h
      exact closedBall_subset_closedBall (by linarith) h
    have hz := hbound s hmem
    have hr := reciprocal_norm_le_regular_inverse η (by linarith : HeckeZeroSupremum.beta<s.re)
    have hcp : 0 ≤ (complexity η s.im)^ε := by linarith
    nlinarith [norm_nonneg (regular η s)]
  · have hr := HeckeReciprocalBound.reciprocal_norm_le η (by norm_num : (1 : ℝ)<2)
      (le_of_not_ge hs2)
    have hp0 : 0 ≤ D+HeckeReciprocalBound.bound 2 := by linarith
    exact hr.trans ((by linarith : HeckeReciprocalBound.bound 2 ≤ D+HeckeReciprocalBound.bound 2).trans
      (le_mul_of_one_le_right hp0 hcomp))

end SevenEighths.HeckeLogarithmicActual

end

end OAI
