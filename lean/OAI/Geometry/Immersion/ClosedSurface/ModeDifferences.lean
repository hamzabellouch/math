import OAI.Geometry.Immersion.ClosedSurface.ModeBounds
import OAI.Geometry.Immersion.ClosedSurface.QuadraticMean

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes

lemma component_sub (f g : Tensor) (i : Fin 3) :
    component (fun p => f p - g p) i = fun p => component f i p - component g i p := rfl

lemma reducedKx_sub {n : ℕ} (G V W : Field n) (a b c d : Scalar) :
    reducedKx G (fun p => V p - W p) (fun p => a p - c p) (fun p => b p - d p) =
      fun p => reducedKx G V a b p - reducedKx G W c d p := by
  funext p
  simp only [reducedKx, dotProduct_sub]
  ring

lemma reducedKy_sub {n : ℕ} (G V W : Field n) (a b c d : Scalar) :
    reducedKy G (fun p => V p - W p) (fun p => a p - c p) (fun p => b p - d p) =
      fun p => reducedKy G V a b p - reducedKy G W c d p := by
  funext p
  simp only [reducedKy, dotProduct_sub]
  ring

lemma connectionTerm_sub {n : ℕ} (G : Field n) (a b c d : Scalar) (p v w : Base) :
    connectionTerm G (fun q => a q - c q) (fun q => b q - d q) v w p =
      connectionTerm G a b v w p - connectionTerm G c d v w p := by
  unfold connectionTerm
  ring

lemma amplitudeCorrection_sub {n : ℕ} {G V W : Field n} {f g : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p) (hW : ContDiffAt ℝ ∞ W p)
    (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    amplitudeCorrection G (fun q => V q - W q) (fun q => f q - g q) p =
      amplitudeCorrection G V f p - amplitudeCorrection G W g p := by
  have hyf := contDiffAt_reducedKy hG hV (contDiffAt_pi.mp hf 1) (contDiffAt_pi.mp hf 2) hD hb
  have hyg := contDiffAt_reducedKy hG hW (contDiffAt_pi.mp hg 1) (contDiffAt_pi.mp hg 2) hD hb
  simp only [amplitudeCorrection, component_sub]
  rw [reducedKx_sub, reducedKy_sub]
  unfold component
  rw [partial_sub (hyf.differentiableAt (by simp)) (hyg.differentiableAt (by simp)), connectionTerm_sub]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma initialAmplitude_sub {n : ℕ} (τ : ℝ) {G V W : Field n} {f g : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p) (hW : ContDiffAt ℝ ∞ W p)
    (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    initialAmplitude τ G (fun q => V q - W q) (fun q => f q - g q) p =
      initialAmplitude τ G V f p - initialAmplitude τ G W g p := by
  rw [initialAmplitude_expansion τ hG (hV.sub hW) (hf.sub hg) hD hb,
    initialAmplitude_expansion τ hG hV hf hD hb,
    initialAmplitude_expansion τ hG hW hg hD hb,
    amplitudeCorrection_sub hG hV hW hf hg hD hb]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma zeroParametrix_sub {n : ℕ} (τ : ℝ) {G : Field n} {f g : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    zeroParametrix τ G (fun q => f q - g q) p =
      zeroParametrix τ G f p - zeroParametrix τ G g p := by
  simpa only [zeroParametrix, sub_self] using
    initialAmplitude_sub τ hG (contDiffAt_const (c := (0 : Ambient n)))
      (contDiffAt_const (c := (0 : Ambient n))) hf hg hD hb




theorem modeApprox_sub {n : ℕ} (τ : ℝ) {G V W : Field n} {U : Set Base}
    (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (hV : ContDiffOn ℝ ∞ V U) (hW : ContDiffOn ℝ ∞ W U)
    {f g : Tensor} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) (q : ℕ) :
    EqOn (modeApprox τ G (fun p => V p - W p) (fun p => f p - g p) q)
      (fun p => modeApprox τ G V f q p - modeApprox τ G W g q p) U := by
  have atU {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {a : Base → E} (ha : ContDiffOn ℝ ∞ a U) {p : Base} (hp : p ∈ U) :
      ContDiffAt ℝ ∞ a p := (ha p hp).contDiffAt (h.isOpen.mem_nhds hp)
  induction q with
  | zero =>
    intro p hp
    exact initialAmplitude_sub τ hG.contDiffAt (atU hV hp) (atU hW hp)
      (atU hf hp) (atU hg hp) (h.determinant p hp) (h.good p hp)
  | succ q ih =>
    have hZ := contDiffOn_modeApprox τ h hV hf q
    have hY := contDiffOn_modeApprox τ h hW hg q
    have he : EqOn
        (residual τ G (fun p => f p - g p)
          (modeApprox τ G (fun p => V p - W p) (fun p => f p - g p) q))
        (fun p => residual τ G f (modeApprox τ G V f q) p -
          residual τ G g (modeApprox τ G W g q) p) U := by
      intro p hp
      have hei : modeApprox τ G (fun p => V p - W p) (fun p => f p - g p) q =ᶠ[nhds p]
          (fun p => modeApprox τ G V f q p - modeApprox τ G W g q p) :=
        Filter.Eventually.mono (h.isOpen.mem_nhds hp) (fun z hz => ih hz)
      unfold residual
      rw [conjugatedD_congr τ G hei,
        conjugatedD_sub τ G ((atU hZ hp).differentiableAt (by simp))
          ((atU hY hp).differentiableAt (by simp))]
      ext i
      simp only [Pi.sub_apply]
      ring
    intro p hp
    have hee := Filter.Eventually.mono (h.isOpen.mem_nhds hp) (fun z hz => he hz)
    change modeApprox τ G _ _ q p - initialAmplitude τ G (fun _ => 0) _ p = _
    rw [ih hp, initialAmplitude_congr τ G (Filter.EventuallyEq.refl _ _) hee]
    have hs := zeroParametrix_sub τ hG.contDiffAt
      (contDiffAt_residual τ hG.contDiffAt (atU hZ hp) (atU hf hp))
      (contDiffAt_residual τ hG.contDiffAt (atU hY hp) (atU hg hp))
      (h.determinant p hp) (h.good p hp)
    change initialAmplitude τ G (fun _ => 0) _ p = _ at hs
    rw [hs]
    simp only [modeApprox]
    ext i
    simp only [Pi.sub_apply]
    ring

end ClosedSurfaceR4.SmallModes

end

end OAI
