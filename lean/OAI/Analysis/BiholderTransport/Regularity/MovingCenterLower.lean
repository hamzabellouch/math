import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.MovingCenterUpper

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section MovingCenterLower
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma moving_center_sequential_lower {a c:M} {q:Model n}
    (hq:(show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a)
    (hc:riemannianExp a q=c) {bj qj:ℕ → Model n} {tj:ℕ → ℝ}
    (hb:Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hqq:Tendsto qj atTop (𝓝 q)) (ht:Tendsto tj atTop (𝓝 1))
    {Gj:ℕ → M → ℝ}
    (hnear:∀ᶠ i in atTop,∀ᶠ z in 𝓝 (movingPrefixChart a c (tj i) (bj i) (qj i)),
      DifferentiableAt ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w)) z)
    (hder:∀ᶠ i in atTop,DifferentiableAt ℝ
      (fderiv ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w)))
        (movingPrefixChart a c (tj i) (bj i) (qj i)))
    {P C:ℝ} (hP:0 ≤ P) (hC:0 ≤ C)
    (hp:∀ᶠ i in atTop,‖fderiv ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w))
      (movingPrefixChart a c (tj i) (bj i) (qj i))‖ ≤ P)
    (hB:∀ᶠ i in atTop,∀d,-C*‖d‖^2 ≤ coordinateCenterMatrix a (tj i) (Gj i) (bj i) (qj i) d d) :
    ∃K≥0,∀ᶠ i in atTop,∀d,
      fderiv ℝ (fderiv ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w)))
        (movingPrefixChart a c (tj i) (bj i) (qj i)) d d ≥ -K*‖d‖^2 := by
  let g:(ℝ×Model n) → Model n → Model n:=fun z r=>movingPrefixChart a c z.1 z.2 r
  obtain ⟨hA,hAlim,hQlim,hElim,hbt,hct⟩:=moving_center_limit_data hq hc hb hqq ht
  have he:∀ᶠ i in atTop,∀d,
      coordinateCenterMatrix a (tj i) (Gj i) (bj i) (qj i) d d=
      fderiv ℝ (fderiv ℝ (movingPrefixEnergy a (tj i) (bj i))) (qj i) d d+
      fderiv ℝ (fderiv ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w)))
        (g (tj i,bj i) (qj i)) (fderiv ℝ (g (tj i,bj i)) (qj i) d)
          (fderiv ℝ (g (tj i,bj i)) (qj i) d)+
      fderiv ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w))
        (g (tj i,bj i) (qj i)) (fderiv ℝ (fderiv ℝ (g (tj i,bj i))) (qj i) d d) := by
    filter_upwards [hbt,hct,hnear,hder] with i hbi hci hni hdi
    exact coordinateCenterMatrix_chain hbi hci hni hdi
  have heNeg:∀ᶠ i in atTop,∀d,
      (-coordinateCenterMatrix a (tj i) (Gj i) (bj i) (qj i)) d d=
      (-fderiv ℝ (fderiv ℝ (movingPrefixEnergy a (tj i) (bj i))) (qj i)) d d+
      (-fderiv ℝ (fderiv ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w)))
        (g (tj i,bj i) (qj i))) (fderiv ℝ (g (tj i,bj i)) (qj i) d)
          (fderiv ℝ (g (tj i,bj i)) (qj i) d)+
      (-fderiv ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w))
        (g (tj i,bj i) (qj i))) (fderiv ℝ (fderiv ℝ (g (tj i,bj i))) (qj i) d d) := by
    filter_upwards [he] with i hi
    intro d
    simp only [neg_apply]
    linarith only [hi d]
  have hpNeg:∀ᶠ i in atTop,‖-fderiv ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w))
      (g (tj i,bj i) (qj i))‖≤P := by simpa only [norm_neg] using hp
  have hBNeg:∀ᶠ i in atTop,∀d,(-coordinateCenterMatrix a (tj i) (Gj i) (bj i) (qj i)) d d≤C*‖d‖^2 := by
    filter_upwards [hB] with i hi
    intro d
    simp only [neg_apply]
    linarith only [hi d]
  obtain ⟨K,hK,HK⟩:=sequential_quadratic_upper_transfer hA hAlim hElim.neg hQlim heNeg hP hC hpNeg hBNeg
  refine ⟨K,hK,?_⟩
  filter_upwards [HK] with i hi
  intro d
  have H:=hi d
  simp only [neg_apply] at H
  linarith only [H]

end MovingCenterLower
end WeakMTWTransport

end
end

end OAI
