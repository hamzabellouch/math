import Mathlib
import OAI.Geometry.SmoothYau.Spectrum.ThreeCoupledNormedSpace

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
local instance threeFormulaNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeFormulaContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
local instance threeFormula_dimension_fact (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1))=n+1) := ⟨by simp [Euclidean]⟩
lemma three_gradient_pair_of_ambient_derivative (p : ThreeManifold) (u : ThreeManifold → ℝ)
    (a : Euclidean 3) (b : ℂ)
    (hd : ∀ v : ThreeModel, fderiv ℝ (u ∘ (chartAt ThreeModel p).symm) 0 v=
      inner ℝ (unitSphereFrame (n:=2) p.1 v.fst) a+
      inner ℝ (unitSphereFrame (n:=1) p.2 v.snd) b) :
    coordinateGradientPair threeBackgroundMetric u u p=
      inner ℝ a a-(inner ℝ (p.1:Euclidean 3) a)^2+
        (inner ℝ b b-(inner ℝ (p.2:ℂ) b)^2) := by
  let V : ThreeModel := WithLp.toLp 2
    (unitSphereCoordinates (n:=2) p.1 a,unitSphereCoordinates (n:=1) p.2 b)
  have hinner (v : ThreeModel) : fderiv ℝ (u ∘ (chartAt ThreeModel p).symm) 0 v=inner ℝ v V := by
    rw [hd]
    erw [unitSphereFrame_inner,unitSphereFrame_inner]
    rfl
  rw [coordinateGradientPair,three_chart_center,three_metricCoefficients_zero]
  simp only [hinner]
  have hswap (i j) :
      (Matrix.gram ℝ (Module.finBasis ℝ ThreeModel))⁻¹ i j *
        inner ℝ (Module.finBasis ℝ ThreeModel i) V * inner ℝ (Module.finBasis ℝ ThreeModel j) V =
      (Matrix.gram ℝ (Module.finBasis ℝ ThreeModel))⁻¹ i j *
        inner ℝ (Module.finBasis ℝ ThreeModel j) V * inner ℝ (Module.finBasis ℝ ThreeModel i) V := by ring
  calc
    _ = ∑ i, ∑ j, (Matrix.gram ℝ (Module.finBasis ℝ ThreeModel))⁻¹ i j *
        inner ℝ (Module.finBasis ℝ ThreeModel j) V * inner ℝ (Module.finBasis ℝ ThreeModel i) V := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hswap i j
    _ = inner ℝ V V := inverse_gram_contraction _ _ _
    _ = _ := ?_

  change inner ℝ (unitSphereCoordinates (n:=2) p.1 a) (unitSphereCoordinates (n:=2) p.1 a)+
    inner ℝ (unitSphereCoordinates (n:=1) p.2 b) (unitSphereCoordinates (n:=1) p.2 b)=_
  erw [unitSphereCoordinates_inner,unitSphereCoordinates_inner]
  ring

def threeAmbientSphereGradient (r : ℝ) (k : ℕ) (p : ThreeManifold) : Euclidean 3 :=
  let α := (p.2:ℂ)^k*productA p.1^(k-1)
  let β := (p.2:ℂ)^k*(r:ℂ)^k*productB p.1^(k-1)
  (k:ℝ) • ((α.re+β.re) • productAxis 0-α.im • productAxis 1-β.im • productAxis 2)
def threeAmbientCircleGradient (r : ℝ) (k : ℕ) (p : ThreeManifold) : ℂ :=
  (-(k:ℝ)*(threeCoupledComplex r k p).im) • (Complex.I*(p.2:ℂ))

lemma threeCoupled_ambient_derivative (r : ℝ) (k : ℕ) (hk : 1 ≤ k) (p : ThreeManifold)
    (v : ThreeModel) :
    fderiv ℝ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) 0 v=
      inner ℝ (unitSphereFrame (n:=2) p.1 v.fst) (threeAmbientSphereGradient r k p)+
      inner ℝ (unitSphereFrame (n:=1) p.2 v.snd) (threeAmbientCircleGradient r k p) := by
  rw [threeCoupled_chart_first]
  have hz : (p.2:ℂ)^(k-1)*(p.2:ℂ)=(p.2:ℂ)^k := by rw [←pow_succ,Nat.sub_add_cancel hk]
  have horth := unitSphereFrame_orthogonal (n:=1) p.2 v.snd
  have hn : Complex.normSq (p.2:ℂ)=1 := by rw [Complex.normSq_eq_norm_sq,p.2.norm_coe]; norm_num
  have hrot : unitSphereFrame (n:=1) p.2 v.snd=
      inner ℝ (unitSphereFrame (n:=1) p.2 v.snd) (Complex.I*(p.2:ℂ)) • (Complex.I*(p.2:ℂ)) := by
    apply Complex.ext <;> simp only [Complex.inner,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
      zero_mul,one_mul,sub_zero,zero_add,Complex.real_smul,Complex.ofReal_re,Complex.ofReal_im,
      Complex.conj_re,Complex.conj_im,Complex.normSq_apply] at *
    · linear_combination -((unitSphereFrame (n:=1) p.2 v.snd).re)*hn + ((p.2:ℂ).re)*horth
    · linear_combination -((unitSphereFrame (n:=1) p.2 v.snd).im)*hn + ((p.2:ℂ).im)*horth
  let α := (p.2:ℂ)^k*productA p.1^(k-1)
  let β := (p.2:ℂ)^k*(r:ℂ)^k*productB p.1^(k-1)
  have hs : (k:ℂ)*(p.2:ℂ)^k*(productA p.1^(k-1)*productA (unitSphereFrame (n:=2) p.1 v.fst)+
        (r:ℂ)^k*productB p.1^(k-1)*productB (unitSphereFrame (n:=2) p.1 v.fst))=
      (k:ℂ)*(α*productA (unitSphereFrame (n:=2) p.1 v.fst)+β*productB (unitSphereFrame (n:=2) p.1 v.fst)) := by
    dsimp [α,β]; ring
  have hep : (k:ℂ)*(p.2:ℂ)^(k-1)*(unitSphereFrame (n:=1) p.2 v.snd)*
      (productA p.1^k+(r:ℂ)^k*productB p.1^k)=
      ((inner ℝ (unitSphereFrame (n:=1) p.2 v.snd) (Complex.I*(p.2:ℂ))):ℂ)*
        (k:ℂ)*Complex.I*threeCoupledComplex r k p := by
    conv_lhs => rw [hrot]
    dsimp only [threeCoupledComplex]
    simp only [Complex.real_smul]
    rw [←hz]
    ring
  rw [hs,hep]
  change _ = inner ℝ (unitSphereFrame (n:=2) p.1 v.fst)
    ((k:ℝ) • ((α.re+β.re) • productAxis 0-α.im • productAxis 1-β.im • productAxis 2))+
    inner ℝ (unitSphereFrame (n:=1) p.2 v.snd)
      ((-(k:ℝ)*(threeCoupledComplex r k p).im) • (Complex.I*(p.2:ℂ)))
  simp only [inner_smul_right,inner_sub_right]
  have haxis (i : Fin 3) : inner ℝ (unitSphereFrame (n:=2) p.1 v.fst) (productAxis i)=
      (unitSphereFrame (n:=2) p.1 v.fst) i := by rw [real_inner_comm,productAxis_coord]
  simp only [haxis,Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.natCast_re,Complex.natCast_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,productA_re,productA_im,
    productB_re,productB_im]
  ring
end YauCounterexamples
end

end OAI
