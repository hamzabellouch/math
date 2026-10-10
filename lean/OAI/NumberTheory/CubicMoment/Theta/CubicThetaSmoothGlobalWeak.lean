import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSmoothWeakDefect

namespace OAI

/-! Finite compact chart reconstruction and energy completion turn the
actual smooth pointwise equation into the global weak equation. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaSmoothWeakDefect_compact (G : cubicThetaSmoothTests) (J : CubicThetaSection)
    (hJ : HasCompactSupport (cubicThetaSectionNorm J)) (lam : ℂ)
    (hEq : ∀ p : ℂ × ℝ, 0<p.2 →
      cubicThetaCoordinateLaplacian (cubicThetaSectionFunction G) p=
        lam*cubicThetaSectionFunction G p-cubicThetaSectionFunction J p)
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) :
    cubicThetaSmoothWeakDefect G J hJ lam (cubicThetaC1EnergyData F hF hc)=0 := by
  obtain ⟨S,V,hSV⟩ := cubicThetaCompact_subset_core hc
  obtain ⟨A,hA⟩ := cubicThetaCoreDenominator_covers S V
  have hn : ∀ q∈tsupport (cubicThetaSectionNorm F), cubicThetaCoreDenominator A q≠0 := by
    intro q hq
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (hA q (hSV hq)))
  let D := cubicThetaCoreDenominator A
  let H := cubicThetaSectionDivide F D (cubicThetaCoreDenominator_continuous A) hn
  have hH : ContDiffOn ℝ 1 (cubicThetaSectionFunction H) {y : ℂ × ℝ | 0<y.2} :=
    cubicThetaSectionDivide_regular F hF D (cubicThetaCoreDenominator_continuous A) hn
      (cubicThetaCoreDenominator_pullback A)
  let P := fun c : CubicThetaQuotient => cubicThetaPoincareSection
    (cubicThetaCoordinateSeed (cubicThetaC1CoreFunction c H)
      (cubicThetaC1CoreFunction_regular c H hH).continuous
      (cubicThetaC1CoreFunction_compact c H)
      ((cubicThetaC1CoreFunction_support c H).trans (cubicThetaCoreProfile_support_positive c)))
  have hP (c : CubicThetaQuotient) :
      ContDiffOn ℝ 1 (cubicThetaSectionFunction (P c)) {y : ℂ × ℝ | 0<y.2} :=
    cubicThetaCoordinateSection_regular (cubicThetaC1CoreFunction_regular c H hH)
      (cubicThetaC1CoreFunction_compact c H)
      ((cubicThetaC1CoreFunction_support c H).trans (cubicThetaCoreProfile_support_positive c))
  have hcP (c : CubicThetaQuotient) : HasCompactSupport (cubicThetaSectionNorm (P c)) :=
    cubicThetaPoincareSection_compact _
  have hzP (c : CubicThetaQuotient) :
      cubicThetaSmoothWeakDefect G J hJ lam (cubicThetaC1EnergyData (P c) (hP c) (hcP c))=0 := by
    apply cubicThetaSmoothWeakDefect_coordinate G J hJ lam hEq
      (cubicThetaC1CoreFunction_regular c H hH) (cubicThetaC1CoreFunction_compact c H)
      (cubicThetaCoreProfile_compact c) (cubicThetaCoreProfile_support_positive c)
      (cubicThetaC1CoreFunction_support c H)
      (cubicThetaCoveringChart (cubicThetaQuotientLift c)) (cubicThetaCoveringChart_coe _)
    rintro p ⟨y,hy,rfl⟩
    exact (cubicThetaCoreProfile_support_target c hy).2
  have hsum : (∑ c∈A, P c)=F := by
    calc
      _ = ∑ c∈A, cubicThetaSectionCutoff (cubicThetaCoreSquare c) H := by
        apply Finset.sum_congr rfl
        intro c hcA
        exact cubicThetaC1CoreFunction_periodization c H hH
      _ = F := cubicThetaCoreDivision_reconstruction A F hn
  have he : cubicThetaC1EnergyData F hF hc=
      ∑ c∈A, cubicThetaC1EnergyData (P c) (hP c) (hcP c) := by
    rw [← cubicThetaC1EnergyData_sum A P hP hcP]
    congr 1
    exact hsum.symm
  rw [he,map_sum]
  exact Finset.sum_eq_zero (fun c _ => hzP c)

lemma cubicThetaSmoothWeakDefect_energy (G : cubicThetaSmoothTests) (J : CubicThetaSection)
    (hJ : HasCompactSupport (cubicThetaSectionNorm J)) (lam : ℂ)
    (hEq : ∀ p : ℂ × ℝ, 0<p.2 →
      cubicThetaCoordinateLaplacian (cubicThetaSectionFunction G) p=
        lam*cubicThetaSectionFunction G p-cubicThetaSectionFunction J p)
    (v : cubicThetaGlobalEnergySpace) :
    cubicThetaSmoothWeakDefect G J hJ lam (v:CubicThetaGlobalEnergyAmbient)=0 := by
  have hc : IsClosed {u : CubicThetaGlobalEnergyAmbient | cubicThetaSmoothWeakDefect G J hJ lam u=0} :=
    isClosed_eq (cubicThetaSmoothWeakDefect_continuous G J hJ lam) continuous_const
  have hr : (cubicThetaGlobalEnergyGraph.range : Set CubicThetaGlobalEnergyAmbient)⊆
      {u | cubicThetaSmoothWeakDefect G J hJ lam u=0} := by
    rintro u ⟨F,rfl⟩
    rw [← cubicThetaC1EnergyData_smooth F]
    exact cubicThetaSmoothWeakDefect_compact G J hJ lam hEq F (F.property.1.of_le (by simp)) F.property.2
  have hv : (v:CubicThetaGlobalEnergyAmbient)∈
      closure (cubicThetaGlobalEnergyGraph.range : Set CubicThetaGlobalEnergyAmbient) := v.property
  exact closure_minimal hr hc hv

theorem cubicThetaSmooth_global_weak (G : cubicThetaSmoothTests) (J : CubicThetaSection)
    (hJ : HasCompactSupport (cubicThetaSectionNorm J)) (lam : ℂ)
    (hEq : ∀ p : ℂ × ℝ, 0<p.2 →
      cubicThetaCoordinateLaplacian (cubicThetaSectionFunction G) p=
        lam*cubicThetaSectionFunction G p-cubicThetaSectionFunction J p)
    (v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaGlobalEnergyGradient v) (cubicThetaGlobalGradient G)+
      lam*inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaGlobalMass G)=
      inner ℂ (cubicThetaGlobalInclusion v) ((cubicThetaCompactSection_memLp J hJ).toLp _) := by
  exact sub_eq_zero.mp (cubicThetaSmoothWeakDefect_energy G J hJ lam hEq v)

end CubicFirstMoment

end

end OAI
