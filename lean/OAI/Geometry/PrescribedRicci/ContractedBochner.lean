import Mathlib
import OAI.Geometry.PrescribedRicci.ChernBochner
import OAI.Geometry.PrescribedRicci.HermitianTensorEnergy
import OAI.Geometry.PrescribedRicci.MatrixWirtingerExtra

namespace OAI

/-! Contracted Bochner. -/

noncomputable section
open Matrix Set Filter Topology
open scoped ComplexOrder ContDiff MatrixOrder
namespace MongeAmpere
variable {n : Type*} [Fintype n]
lemma hermPair_self_ofReal {K : Matrix n n ℂ} (hK : K.IsHermitian) (v : n → ℂ) :
    ((hermPair K v v).re : ℂ) = hermPair K v v := by
  have he := congrArg Complex.im (hermPair_conj K hK v v)
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    simp only [Complex.star_def,Complex.conj_im] at he
    linarith
end MongeAmpere
namespace Anticanonical.SourceSmooth.KaehlerMetric
open MongeAmpere
variable {d : ℕ} {n : Type*} [Fintype n]

lemma hessian_hermPair {s : Set (Coordinates d)} (hs : IsOpen s)
    {K : Coordinates d → Matrix n n ℂ} {f : Coordinates d → n → ℂ}
    {z : Coordinates d} (hz : z ∈ s)
    (hK : ∀ y ∈ s, (K y).IsHermitian)
    (hKs : ∀ y ∈ s, ∀ i j, ContDiffAt ℝ ∞ (fun w => K w i j) y)
    (hf : ∀ y ∈ s, ∀ i, ContDiffAt ℝ ∞ (fun w => f w i) y) (a b : Fin d) :
    PotentialKaehler.potentialMatrix (fun y => (hermPair (K y) (f y) (f y)).re) z b a =
      barDeriv (fun y => holDeriv (fun w => hermPair (K w) (f w) (f w)) y a) z b := by
  have hdr (y : Coordinates d) (hy : y ∈ s) :
      ContDiffAt ℝ ∞ (fun w => (hermPair (K w) (f w) (f w)).re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y (hermPair_smooth (hKs y hy) (hf y hy) (hf y hy))
  rw [← barDeriv_holRealDeriv (hdr z hz)]
  apply barDeriv_congr
  filter_upwards [hs.mem_nhds hz] with y hy
  rw [← holDeriv_ofReal ((hdr y hy).differentiableAt (by simp))]
  apply holDeriv_congr
  filter_upwards [hs.mem_nhds hy] with w hw
  exact hermPair_self_ofReal (hK w hw) _

lemma contracted_bochners_identity {s : Set (Coordinates d)} (hs : IsOpen s)
    {K : Coordinates d → Matrix n n ℂ} {C : Coordinates d → Fin d → Matrix n n ℂ}
    {f : Coordinates d → n → ℂ} {z : Coordinates d} (hz : z ∈ s)
    (hK : ∀ y ∈ s, ∀ i j, ContDiffAt ℝ ∞ (fun w => K w i j) y)
    (hC : ∀ y ∈ s, ∀ a i j, ContDiffAt ℝ ∞ (fun w => C w a i j) y)
    (hf : ∀ y ∈ s, ∀ i, ContDiffAt ℝ ∞ (fun w => f w i) y)
    (hKh : ∀ y ∈ s, (K y).IsHermitian)
    (hhol : ∀ y ∈ s, ∀ a, holArray K y a = K y*C y a)
    (hbar : ∀ y ∈ s, ∀ a, barArray K y a = (C y a)ᴴ*K y)
    (B : Matrix (Fin d) (Fin d) ℂ) (hB : B.IsHermitian) :
    (B*PotentialKaehler.potentialMatrix (fun y => (hermPair (K y) (f y) (f y)).re) z).trace.re =
      (tensorEnergy B (K z) (barVector f z)).re+
      (tensorEnergy B.transpose (K z) (covHol C f z)).re+
      2*(hermPair (K z) (f z)
        (∑ a, ∑ b, B a b • covHol C (fun y => barVector f y b) z a)).re+
      (hermPair (K z) (f z)
        ((∑ a, ∑ b, B a b • barArray (fun y => C y a) z b)*ᵥ f z)).re := by
  have he (a b : Fin d) := hermPair_bochners_identity hs hz hK hC hf hhol hbar a b
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply]
  simp_rw [hessian_hermPair hs hz hKh hK hf,he]
  simp only [mul_add,Finset.sum_add_distrib]
  rw [hermPair_weighted_rough_left B hB,hermPair_weighted_rough_right,
    hermPair_weighted_curvature,tensorEnergy_flip]
  change (hermPair (K z)
      (∑ a, ∑ b, B a b • covHol C (fun y => barVector f y b) z a) (f z)+
    tensorEnergy B (K z) (barVector f z)+
    tensorEnergy B.transpose (K z) (covHol C f z)+
    hermPair (K z) (f z)
      (∑ a, ∑ b, B a b • covHol C (fun y => barVector f y b) z a)+
    hermPair (K z) (f z)
      ((∑ a, ∑ b, B a b • barArray (fun y => C y a) z b)*ᵥ f z)).re = _
  have hc := congrArg Complex.re (hermPair_conj (K z) (hKh z hz) (f z)
    (∑ a, ∑ b, B a b • covHol C (fun y => barVector f y b) z a))
  simp only [Complex.add_re,Complex.star_def,Complex.conj_re] at hc ⊢
  linarith

end Anticanonical.SourceSmooth.KaehlerMetric

end

end OAI
