import OAI.Geometry.Relativity.CKS.CollarExpansionWeighted

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma actualScalarJet_congr {f g : Point → ℝ} {x : Point} (h : f =ᶠ[𝓝 x] g) :
    actualScalarJet f x = actualScalarJet g x := by
  apply Prod.ext
  · exact h.eq_of_nhds
  apply Prod.ext
  · ext a
    exact D_congr h (basis a)
  · ext a b
    have hd : D (basis b) f =ᶠ[𝓝 x] D (basis b) g := by
      filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
      exact congrArg (fun L : Point →L[ℝ] ℝ => L (basis b)) hy
    exact D_congr hd (basis a)

lemma actualScalarJet_linear (c d : ℝ) {f g : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    actualScalarJet (fun y => c*f y+d*g y) x = c • actualScalarJet f x+d • actualScalarJet g x := by
  have hcf : ContDiffAt ℝ 2 (fun y => c*f y) x := by simpa only [smul_eq_mul] using hf.const_smul c
  have hdg : ContDiffAt ℝ 2 (fun y => d*g y) x := by simpa only [smul_eq_mul] using hg.const_smul d
  rw [actualScalarJet_add hcf hdg,
    actualScalarJet_smul c hf,actualScalarJet_smul d hg]

lemma actualScalarJet_D_linear (c d : ℝ) {f g : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ 3 f x) (hg : ContDiffAt ℝ 3 g x) (a : I) :
    actualScalarJet (D (basis a) (fun y => c*f y+d*g y)) x =
      c • actualScalarJet (D (basis a) f) x+d • actualScalarJet (D (basis a) g) x := by
  have heq : D (basis a) (fun y => c*f y+d*g y) =ᶠ[𝓝 x]
      (fun y => c*D (basis a) f y+d*D (basis a) g y) := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with y hyf hyg
    have hfd := hyf.differentiableAt (by norm_num)
    have hgd := hyg.differentiableAt (by norm_num)
    rw [D_add _ (hfd.const_mul c) (hgd.const_mul d),D_const_mul _ c hfd,D_const_mul _ d hgd]
  rw [actualScalarJet_congr heq]
  exact actualScalarJet_linear c d (contDiffAt_D hf (by norm_num) (basis a))
    (contDiffAt_D hg (by norm_num) (basis a))

lemma matrixScalarJets_linear (c d : ℝ) {q p : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (hp : ContDiffAt ℝ 2 p x) :
    matrixScalarJets (fun y => c • q y+d • p y) x =
      c • matrixScalarJets q x+d • matrixScalarJets p x := by
  funext i k
  change actualScalarJet (fun y => c*q y i k+d*p y i k) x = _
  exact actualScalarJet_linear c d (component_diff hq i k) (component_diff hp i k)

theorem actual_collarExpansionInput (e θ : ℝ) {q σ Q : Point → Mat} {S : Point → Point} {x : Point}
    (hq : ContDiffAt ℝ 3 q x) (hσ : ContDiffAt ℝ 3 σ x)
    (hQ : ContDiffAt ℝ 2 Q x) (hS : ContDiffAt ℝ 3 S x) :
    actualExpansionInput (fun y => (1-e) • q y+e • σ y)
      (fun y => (1-e) • Q y+θ • (σ y-q y)) (fun y => (1-e) • S y) x =
    collarExpansionInput e θ (actualExpansionInput q Q S x)
      (matrixScalarJets σ x)
      (fun a => matrixScalarJets (fun y i k => D (basis a) (fun z => σ z i k) y) x) := by
  have hq2 : ContDiffAt ℝ 2 q x := hq.of_le (by norm_num)
  have hσ2 : ContDiffAt ℝ 2 σ x := hσ.of_le (by norm_num)
  have hs (a : I) := contDiffAt_pi.mp hS a
  have zero3 : ContDiffAt ℝ 3 (fun _ : Point => (0:ℝ)) x := contDiffAt_const
  apply Prod.ext
  · simpa [collarExpansionInput,actualExpansionInput,expansionReference,radialCorrection] using
      matrixScalarJets_linear (1-e) e hq2 hσ2
  apply Prod.ext
  · funext a i k
    simpa [collarExpansionInput,actualExpansionInput,expansionReference,radialCorrection,matrixScalarJets] using
      actualScalarJet_D_linear (1-e) e (component_three hq i k) (component_three hσ i k) a
  apply Prod.ext
  · funext i k
    change actualScalarJet (fun y => (1-e)*Q y i k+θ*(σ y i k-q y i k)) x = _
    rw [actualScalarJet_linear (1-e) θ (component_diff hQ i k)
      ((component_diff hσ2 i k).sub (component_diff hq2 i k)),
      actualScalarJet_sub (component_diff hσ2 i k) (component_diff hq2 i k)]
    simp [collarExpansionInput,actualExpansionInput,expansionReference,radialCorrection,matrixScalarJets]
  apply Prod.ext
  · funext a
    change actualScalarJet (fun y => (1-e)*S y a) x = _
    rw [actualScalarJet_smul _ ((hs a).of_le (by norm_num))]
    simp [collarExpansionInput,actualExpansionInput,expansionReference,radialCorrection]
  · funext a b
    have hh := actualScalarJet_D_linear (1-e) 0 (hs b) zero3 a
    simpa [collarExpansionInput,actualExpansionInput,expansionReference,radialCorrection] using hh

theorem radial_interpolation_deriv {q e : ℝ → ℝ} {r : ℝ} (σ : ℝ)
    (hq : DifferentiableAt ℝ q r) (he : DifferentiableAt ℝ e r) :
    r*deriv (fun ρ => (1-e ρ)*q ρ+e ρ*σ) r =
      (1-e r)*(r*deriv q r)+(r*deriv e r)*(σ-q r) := by
  have hh := (((hasDerivAt_const r (1:ℝ)).sub he.hasDerivAt).mul hq.hasDerivAt).add
    (he.hasDerivAt.mul_const σ)
  have hd : HasDerivAt (fun ρ => (1-e ρ)*q ρ+e ρ*σ)
      ((1-e r)*deriv q r+deriv e r*(σ-q r)) r := by
    convert! hh using 1
    dsimp
    ring
  rw [hd.deriv]
  ring

end
end CKSAngularGeometry

end

end OAI
