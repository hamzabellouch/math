import OAI.Analysis.LipschitzHilbert.Trees.SourceLocalLabelVectorEnergy
import OAI.Analysis.LipschitzHilbert.Estimates.SeparatedPlanarSynthesis

namespace OAI

/-! At one spatial scale, first sum sites on each genuine lattice and
then use local angular multiplicity to sum the labels. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem planar_label_scale_energy {Λ κ : Type*} [Fintype Λ] [Fintype κ]
    {ι : Λ → Type*} [∀ l, Fintype (ι l)]
    (c : ∀ l, ι l → EuclideanSpace ℂ κ)
    (f : ∀ l, ι l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (site : ∀ l, ι l → ℤ×ℤ) (hinj : ∀ l, Function.Injective (site l))
    (a b theta : Λ → ℝ) (ell W C w cStar cEta CEta : ℝ)
    (hell : 0<ell) (hW : 0<W) (hw : 0<w) (hcEta : 0<cEta)
    (M Q : ℕ) (hQ : 2*cStar/cEta≤Q)
    (hmultiplicity : SourceSlopeLabels.LocalMultiplicity Finset.univ theta (w/ell) M)
    (hspectrum : ∀ l u k xi eta, planarAngularFourier (f l u k) (xi,eta)≠0 →
      |xi+theta l*eta|≤cStar/ell ∧ cEta≤w*eta ∧ w*eta≤CEta)
    (henv : ∀ l u k z, ‖f l u k z‖≤C*
      (lineEnvelope (a l+ell*(site l u).1) ell 1 z.1*
        lineEnvelope (b l+W*(site l u).2) W 1 (z.2-theta l*z.1))) :
    (∫ z, ‖∑ l, planarFixedSynthesis (c l) (f l) z‖^2 ∂volume.prod volume)≤
      (((2*Q+1)*M:ℕ):ℝ)*((4*Real.pi)^2*C^2*Real.pi^2)*
        ∑ l, ∑ u, ‖c l u‖^2*ell*W := by
  let F := fun l k => (∑ u, c l u k • f l u k : SchwartzMap (ℝ×ℝ) ℂ)
  have hF (l : Λ) (z : ℝ×ℝ) :
      (WithLp.toLp 2 (fun k => F l k z) : EuclideanSpace ℂ κ)=
        planarFixedSynthesis (c l) (f l) z := by
    ext k
    simp only [F,planarFixedSynthesis,WithLp.ofLp_toLp,sum_apply,smul_apply,smul_eq_mul]
  have hspec (l : Λ) (k : κ) (xi eta : ℝ)
      (hne : planarAngularFourier (F l k) (xi,eta)≠0) :
      |xi+theta l*eta|≤cStar/ell ∧ cEta≤w*eta ∧ w*eta≤CEta := by
    by_contra hout
    have hz (u : ι l) : planarAngularFourier (f l u k) (xi,eta)=0 := by
      by_contra hnonzero
      exact hout (hspectrum l u k xi eta hnonzero)
    apply hne
    dsimp only [F,planarAngularFourier]
    rw [planarFourier_finsetSum]
    simp only [planarFourier_smul]
    change (∑ u, c l u k*planarAngularFourier (f l u k) (xi,eta))=0
    simp only [hz,mul_zero,Finset.sum_const_zero]
  have h := equal_length_label_vector_energy F theta ell w cStar cEta CEta
    hell hw hcEta M Q hQ hmultiplicity hspec
  simp only [hF] at h
  calc
    _ ≤ (((2*Q+1)*M:ℕ):ℝ)*∑ l,
        ∫ z, ‖planarFixedSynthesis (c l) (f l) z‖^2 ∂volume.prod volume := h
    _ ≤ (((2*Q+1)*M:ℕ):ℝ)*∑ l,
        ((4*Real.pi)^2*C^2*Real.pi^2)*∑ u, ‖c l u‖^2*ell*W := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum fun l _ => planar_fixed_scale_energy (c l) (f l)
        (site l) (hinj l) (a l) (b l) ell W (theta l) C hell hW (henv l)
    _ = _ := by rw [←Finset.mul_sum]; ring

end LipschitzHilbert

end

end OAI
