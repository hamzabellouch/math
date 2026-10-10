import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSiegelReduction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMobiusContinuity

namespace OAI

/-! A finite compact-core and cusp cover of the principal quotient. All
charts are actual hyperbolic transformations of the single Siegel set. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaSiegelCore (V : ℝ) : Set (ℂ × ℝ) :=
  Metric.closedBall (0:ℂ) 1 ×ˢ Icc (1/2:ℝ) V

lemma cubicThetaSiegelCore_compact (V : ℝ) : IsCompact (cubicThetaSiegelCore V) :=
  (isCompact_closedBall (0:ℂ) 1).prod isCompact_Icc

lemma cubicThetaSiegelCore_positive {V : ℝ} {p : ℂ × ℝ}
    (hp : p∈cubicThetaSiegelCore V) : 0<p.2 := by
  have h : (1/2:ℝ) ≤ p.2 := hp.2.1
  linarith

def cubicThetaCompactCore (S : Finset SL(2,Eisenstein)) (V : ℝ) : Set (ℂ × ℝ) :=
  ⋃ δ∈S, cubicThetaMobius (cubicThetaFullComplex δ⁻¹) '' cubicThetaSiegelCore V

def cubicThetaCuspCharts (S : Finset SL(2,Eisenstein)) (V : ℝ) : Set (ℂ × ℝ) :=
  ⋃ δ∈S, cubicThetaMobius (cubicThetaFullComplex δ⁻¹) '' {q | q∈cubicThetaSiegelSet ∧ V<q.2}

lemma cubicThetaCompactCore_compact (S : Finset SL(2,Eisenstein)) (V : ℝ) :
    IsCompact (cubicThetaCompactCore S V) := by
  apply S.isCompact_biUnion
  intro δ _
  apply (cubicThetaSiegelCore_compact V).image_of_continuousOn
  exact cubicThetaMobius_continuousOn _ (fun _ hp => cubicThetaSiegelCore_positive hp)

lemma cubicThetaSiegelSet_mem_core {V : ℝ} {q : ℂ × ℝ} (hq : q∈cubicThetaSiegelSet)
    (hV : q.2 ≤ V) : q∈cubicThetaSiegelCore V := by
  refine ⟨?_,hq.2.2,hV⟩
  rw [Metric.mem_closedBall,dist_zero_right]
  have hn := hq.2.1
  rw [Complex.normSq_eq_norm_sq] at hn
  nlinarith [_root_.norm_nonneg q.1]

theorem cubicThetaCompactCoreCuspCover :
    ∃ S : Finset SL(2,Eisenstein), ∀ V : ℝ, ∀ p : ℂ × ℝ, 0<p.2 →
      ∃ k : cubicThetaPrincipalGroup,
        cubicThetaMobius (cubicThetaPrincipalComplex k) p∈
          cubicThetaCompactCore S V ∪ cubicThetaCuspCharts S V := by
  obtain ⟨S,hS⟩ := cubicThetaFiniteSiegelCover
  refine ⟨S,?_⟩
  intro V p hp
  obtain ⟨δ,hδ,k,hk⟩ := hS p hp
  let q := cubicThetaMobius (cubicThetaFullComplex (δ*k.val)) p
  have hq : q∈cubicThetaSiegelSet := hk
  have he : cubicThetaMobius (cubicThetaFullComplex δ⁻¹) q=
      cubicThetaMobius (cubicThetaPrincipalComplex k) p := by
    dsimp [q]
    rw [cubicThetaMobius_comp _ _ hp,← map_mul]
    simp only [inv_mul_cancel_left]
    rfl
  refine ⟨k,?_⟩
  by_cases hV : q.2 ≤ V
  · left
    apply mem_iUnion_of_mem δ
    apply mem_iUnion_of_mem hδ
    exact ⟨q,cubicThetaSiegelSet_mem_core hq hV,he⟩
  · right
    apply mem_iUnion_of_mem δ
    apply mem_iUnion_of_mem hδ
    exact ⟨q,⟨hq,lt_of_not_ge hV⟩,he⟩

end CubicFirstMoment

end

end OAI
