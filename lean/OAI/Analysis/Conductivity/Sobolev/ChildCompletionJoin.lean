import Mathlib
import OAI.Analysis.Conductivity.Branching.ChildLocalizedJet

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : ℝ} (ha : 0<a)
  (k : Fin 2)
  {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)
  (hχb : ∀ x,|χ x|≤1)
  (hχs : tsupport χ⊆sourceClosedCollarBand (-2*centralThickness) 0)

include hχb hχs in
lemma childLocalJetCLM_smooth_H10 (f : centralSmoothFunctions) :
    childLocalJetCLM s hs ha k hχ hc (centralEmbedL s f)∈zeroTraceAmbient := by
  have hq := ((central_smooth f).comp sourcePairCLE.contDiff).comp (sourceChildCoordinates_contDiff (actualChildSign k))
  obtain ⟨w,hw,hwe⟩ := smoothCollarTrace_localJoined_H1 hs hq hχ hc hχb ha.ne'
    (show (0:ℝ)<centralThickness by norm_num [centralThickness])
    (show -(1:ℝ)/100≤(-centralThickness)-centralThickness by norm_num [centralThickness])
    (show (-centralThickness)+centralThickness≤(1:ℝ)/100 by norm_num [centralThickness])
    (by
      convert hχs using 1
      congr 1 <;> ring)
  dsimp only at hwe
  rw [central_child_trace_eq s k f] at hwe
  have he : childLocalJetCLM s hs ha k hχ hc (centralEmbedL s f)=w.val := by
    apply Lp.ext
    filter_upwards [childLocalJetCLM_smooth_ae s hs ha k hχ hc hχs f,hwe] with x hx hwx
    rw [hx]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hwx.1.symm
    · exact (hwx.2 j).symm
  rw [he]
  exact hw

include hχb hχs in

theorem childLocalJetCLM_central_H10 (u : centralEnergySpace s) :
    childLocalJetCLM s hs ha k hχ hc u.val∈zeroTraceAmbient := by
  let T := (zeroTraceAmbient.comap (childLocalJetCLM s hs ha k hχ hc).toLinearMap)
  have ht : IsClosed (T : Set (CentralAmbient s)) :=
    (Submodule.isClosed_topologicalClosure (Submodule.span ℝ compactSmoothJets)).preimage
      (childLocalJetCLM s hs ha k hχ hc).continuous
  have hr : LinearMap.range (centralEmbedL s)≤T := by
    rintro z ⟨f,rfl⟩
    exact childLocalJetCLM_smooth_H10 s hs ha k hχ hc hχb hχs f
  exact (Submodule.topologicalClosure_minimal _ hr ht) u.property

def childCompletionJoin : centralEnergySpace s →L[ℝ] H1 :=
  ((childLocalJetCLM s hs ha k hχ hc).comp (centralEnergySpace s).subtypeL).codRestrict H1Space
    (fun u => zeroTraceAmbient_le_H1Space (childLocalJetCLM_central_H10 s hs ha k hχ hc hχb hχs u))

lemma childCompletionJoin_mem_H10 (u : centralEnergySpace s) :
    childCompletionJoin s hs ha k hχ hc hχb hχs u∈H10 :=
  childLocalJetCLM_central_H10 s hs ha k hχ hc hχb hχs u

end ScalarConductivity

end

end OAI
