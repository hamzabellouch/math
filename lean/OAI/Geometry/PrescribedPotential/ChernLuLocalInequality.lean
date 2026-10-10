import Mathlib
import OAI.Geometry.PrescribedPotential.InverseTraceFunction
import OAI.Geometry.PrescribedPotential.LogHessianCalculus
import OAI.Geometry.PrescribedPotential.MatrixTraceInequalities

namespace OAI

/-! Chern Lu Local Inequality. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

def curvatureDiagonal (G : V n → Matrix (Fin n) (Fin n) ℂ) (z v : V n) :=
  mderiv Complex.I v (mderiv (-Complex.I) v G) z -
    (mderiv (-Complex.I) v G z)ᴴ*(G z)⁻¹*mderiv (-Complex.I) v G z

lemma trace_gradient_sum_bound (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef)
    (X Y W : Fin n → Matrix (Fin n) (Fin n) ℂ) :
    ∑ k, ‖(Y k-X k*G).trace‖^2 ≤ G.trace.re *
      ((∑ k, (X k*(X k)ᴴ*G-X k*(Y k)ᴴ-(X k)ᴴ*Y k+W k).trace.re) -
        ∑ k, (W k-(Y k)ᴴ*G⁻¹*Y k).trace.re) := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun k _ => trace_gradient_square_bound hG (X k) (Y k))
  rw [← Finset.mul_sum] at h
  have he : ((∑ k, (X k*(X k)ᴴ*G-X k*(Y k)ᴴ-(X k)ᴴ*Y k+W k).trace.re) -
      ∑ k, (W k-(Y k)ᴴ*G⁻¹*Y k).trace.re) =
      ∑ k, ((X k*(X k)ᴴ*G).trace.re-(X k*(Y k)ᴴ).trace.re-
        ((X k)ᴴ*Y k).trace.re+((Y k)ᴴ*G⁻¹*Y k).trace.re) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Matrix.trace_add,Matrix.trace_sub,Complex.add_re,Complex.sub_re]
    ring
  rw [he]
  exact h

lemma log_hessian_trace {U : Set (V n)} (hU : IsOpen U)
    {f : V n → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hp : ∀ y ∈ U, f y ≠ 0)
    {z : V n} (hz : z ∈ U) :
    (PotentialKaehler.potentialMatrix (fun y => Real.log (f y)) z).trace.re =
      (f z)⁻¹*(PotentialKaehler.potentialMatrix f z).trace.re -
      (f z)^(-2 : ℤ)*(∑ k, ‖dz (e k) (fun y => (f y : ℂ)) z‖^2) := by
  simp only [Matrix.trace,Matrix.diag_apply,Complex.re_sum]
  simp_rw [log_hessian_diagonal hU hf hp hz]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum]

lemma scalar_log_cancellation {s d l r q c a : ℝ} (hs : 0 < s)
    (hl : l = s⁻¹*d - s^(-2 : ℤ)*a) (hd : d = -r+q)
    (ha : a ≤ s*(q-c)) : -r+c ≤ s*l := by
  have he : s^2*l = s*d-a := by
    rw [hl]
    simp only [_root_.zpow_neg,zpow_ofNat]
    field_simp
  have hh : s*(-r+c) ≤ s^2*l := by rw [he,hd]; nlinarith
  have hf : s^2*l = s*(s*l) := by ring
  rw [hf] at hh
  exact (mul_le_mul_iff_right₀ hs).mp hh

lemma inverseTrace_log_inequality_at_one [Nonempty (Fin n)]
    {U : Set (V n)} (hU : IsOpen U)
    {M G : V n → Matrix (Fin n) (Fin n) ℂ} (hM : ContDiffOn ℝ ∞ M U)
    (hp : ∀ y ∈ U, (M y).PosDef)
    (hclosed : ∀ y ∈ U, ∀ u v w : V n,
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) v w) y u +
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) w u) y v +
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) u v) y w = 0)
    (hG : ContDiffOn ℝ ∞ G U) (hGp : ∀ y ∈ U, (G y).PosDef)
    {z : V n} (hz : z ∈ U) (hMz : M z = 1) :
    -(PotentialKaehler.potentialMatrix (fun y => Real.log (M y).det.re) z*G z).trace.re +
      ∑ k, (curvatureDiagonal G z (e k)).trace.re ≤
      inverseTrace M G z *
        (PotentialKaehler.potentialMatrix (fun y => Real.log (inverseTrace M G y)) z).trace.re := by
  let X := fun k => mderiv (-Complex.I) (e k) M z
  let Y := fun k => mderiv (-Complex.I) (e k) G z
  let W := fun k => mderiv Complex.I (e k) (mderiv (-Complex.I) (e k) G) z
  have hGh : ∀ y ∈ U, (G y).IsHermitian := fun y hy => (hGp y hy).isHermitian
  have hpos : ∀ y ∈ U, 0 < inverseTrace M G y := fun y hy => inverseTrace_pos (hp y hy) (hGp y hy)
  have hl := log_hessian_trace hU (inverseTrace_smooth hU hM hp hG)
    (fun y hy => ne_of_gt (hpos y hy)) hz
  have hd := inverseTrace_second_at_one hU hM hp hclosed hG hGh hz hMz
  have hg := trace_gradient_sum_bound (G z) (hGp z hz) X Y W
  have hs : inverseTrace M G z = (G z).trace.re := by simp [inverseTrace,hMz]
  have he : (∑ k, ‖dz (e k) (fun y => (inverseTrace M G y : ℂ)) z‖^2) =
      ∑ k, ‖(Y k-X k*G z).trace‖^2 := by
    apply Finset.sum_congr rfl
    intro k _
    rw [inverseTrace_dz_at_one hU hM hp hG hGh hz hMz]
  rw [he] at hl
  rw [← hs] at hg
  exact scalar_log_cancellation (hpos z hz) hl hd hg
end KaehlerCalculus

end
end

end OAI
