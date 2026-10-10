import Mathlib
import OAI.Analysis.Conductivity.Sobolev.OriginalSmoothMultiplier

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

variable {χ : R3 → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)

lemma originalMulJetCLM_mem_H1 (u : H1) : originalMulJetCLM hχ hc u∈H1Space := by
  have hclosed : IsClosed {u : H1 | originalMulJetCLM hχ hc u∈H1Space} :=
    H1_isClosed.preimage (originalMulJetCLM hχ hc).continuous
  apply (closure_minimal (s:={u : H1 | u.val∈smoothJets}) ?_ hclosed) (smoothH1_dense u)
  rintro v ⟨f,hf,hm,he⟩
  have hv : v=smoothH1 f hf := Subtype.ext he
  change originalMulJetCLM hχ hc v∈H1Space
  rw [hv,originalMulJetCLM_smooth]
  exact (smoothH1 (χ*f) (hχ.mul hf)).property

def originalMulH1CLM : H1 →L[ℝ] H1 :=
  (originalMulJetCLM hχ hc).codRestrict H1Space (originalMulJetCLM_mem_H1 hχ hc)

lemma originalMulH1_smooth {f : R3 → ℝ} (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    originalMulH1CLM hχ hc (smoothH1 f hf)=smoothH1 (χ*f) (hχ.mul hf) :=
  Subtype.ext (originalMulJetCLM_smooth hχ hc hf)

lemma originalMulH1_value (u : H1) :
    weakValue (originalMulH1CLM hχ hc u)=ᵐ[ballMeasure] (fun x => χ x*weakValue u x) := by
  filter_upwards [originalMulJetCLM_ae hχ hc u] with x hx
  exact congrArg (fun z : JetFiber => z 0) hx

lemma originalMulH1_gradient (u : H1) :
    weakGradient (originalMulH1CLM hχ hc u)=ᵐ[ballMeasure]
      (fun x => weakValue u x • gradient χ x+χ x • weakGradient u x) := by
  filter_upwards [originalMulJetCLM_ae hχ hc u] with x hx
  change jetGradient (originalMulJetCLM hχ hc u x)=_
  rw [hx]
  ext j
  change fderiv ℝ χ x (EuclideanSpace.single j 1)*weakValue u x+χ x*weakGradient u x j=
    weakValue u x*gradient χ x j+χ x*weakGradient u x j
  rw [gradient_apply_single]
  ring

end ScalarConductivity

end
end

end OAI
