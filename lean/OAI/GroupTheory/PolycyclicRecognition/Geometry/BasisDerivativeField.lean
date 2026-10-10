import OAI.GroupTheory.PolycyclicRecognition.Algebra.CoordinateWeakLinearity

namespace OAI

/-! # A finite basis assembles the actual horizontal derivative field -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory Module

def basisDerivativeField {I H G W : Type*} [AddCommGroup H] [Module ℝ H]
    [AddCommGroup W] [Module ℝ W] (b : Basis I ℝ H) (q : H → G → W) (g : G) : H →ₗ[ℝ] W :=
  b.constr ℝ (fun i => q (b i) g)

theorem ae_eq_basisDerivativeField
    {I H G W : Type*} [Fintype I] [AddCommGroup H] [Module ℝ H]
    [AddCommGroup W] [Module ℝ W] [MeasurableSpace G]
    (μ : Measure G) (Ω : Set G) (b : Basis I ℝ H) (q : H → G → W)
    (hadd : ∀ v w, ∀ᵐ g ∂μ, g ∈ Ω → q (v + w) g = q v g + q w g)
    (hsmul : ∀ (c : ℝ) v g, q (c • v) g = c • q v g) (v : H) :
    ∀ᵐ g ∂μ, g ∈ Ω → q v g = basisDerivativeField b q g v := by
  classical
  have hzero (g : G) : q 0 g = 0 := by simpa using hsmul 0 0 g
  have hsum (s : Finset I) : ∀ᵐ g ∂μ, g ∈ Ω →
      q (∑ i ∈ s, b.equivFun v i • b i) g =
        ∑ i ∈ s, b.equivFun v i • q (b i) g := by
    induction s using Finset.induction_on with
    | empty => exact Eventually.of_forall (fun g _ => by simp [hzero])
    | @insert i s hi ih =>
      filter_upwards [ih, hadd (b.equivFun v i • b i) (∑ j ∈ s, b.equivFun v j • b j)]
        with g hg ha hgΩ
      simp only [Finset.sum_insert hi]
      rw [ha hgΩ, hg hgΩ, hsmul]
  filter_upwards [hsum Finset.univ] with g hg hgΩ
  have hb : (∑ i, b.equivFun v i • b i) = v := by
    simpa only [Basis.equivFun_apply] using b.sum_repr v
  simpa only [hb, basisDerivativeField, Basis.constr_apply_fintype] using hg hgΩ

end PolycyclicRecognition

end

end OAI
