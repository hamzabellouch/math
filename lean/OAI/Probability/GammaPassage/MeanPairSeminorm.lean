import OAI.Probability.GammaPassage.RationalMeanAlgebra
import OAI.Probability.GammaPassage.RealMeanExtension
import OAI.Probability.GammaPassage.MeanLipschitz

namespace OAI

namespace GammaFPP
open MeasureTheory PlanarFPP

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

noncomputable def gammaMeanPairSeminorm
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    Seminorm ℝ (ℝ × ℝ) := by
  let m : Vertex → ℝ := directionalMeanConstant h hs hr
  have hn : ∀ (k : ℕ) (x : Vertex), m (k • x) = (k : ℝ)*m x :=
    fun k x => h.directionalMeanConstant_nsmul hs hr x k
  have hz : ∀ (k : ℤ) (x : Vertex), m (k • x) = (k.natAbs : ℝ)*m x :=
    fun k x => h.directionalMeanConstant_zsmul hs hr x k
  exact realMeanSeminorm (rationalMean m) ⟨shape/rate, (div_pos hs hr).le⟩
    (rationalMean_l1 m hn (shape/rate) (h.directionalMeanConstant_l1_lipschitz hs hr))
    (rationalMean_zero m hn (h.directionalMeanConstant_zero hs hr))
    (rationalMean_add_le m hn (h.directionalMeanConstant_add_le hs hr))
    (rationalMean_neg m hn (h.directionalMeanConstant_neg hs hr))
    (rationalMean_smul m hn hz)

/-- The extended mean seminorm agrees on lattice points with the normalized
expectation limit of passage times. -/
theorem gammaMeanPairSeminorm_integerPair
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (x : Vertex) : gammaMeanPairSeminorm h hs hr ((x.1 : ℝ), (x.2 : ℝ)) =
      directionalMeanConstant h hs hr x := by
  change realMeanExtension (rationalMean (directionalMeanConstant h hs hr))
    ((x.1 : ℝ), (x.2 : ℝ)) = _
  apply realMeanExtension_integerPair (directionalMeanConstant h hs hr)
    (fun k z => h.directionalMeanConstant_nsmul hs hr z k)
    ⟨shape/rate, (div_pos hs hr).le⟩
  exact rationalMean_l1 _ (fun k z => h.directionalMeanConstant_nsmul hs hr z k)
    (shape/rate) (h.directionalMeanConstant_l1_lipschitz hs hr)

end GammaFPP

end OAI
