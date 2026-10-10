import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def conjugateInvolutionBiholomorph {n : ℕ} (a : E ≃L[ℂ] Affine n)
    (S : Set E) (F : E → E) (hF : AnalyticOnNhd ℂ F S)
    (hm : MapsTo F S S) (hinv : ∀ x ∈ S, F (F x) = x) :
    Biholomorph (a '' S) (a '' S) := by
  let G : Affine n → Affine n := fun x => a (F (a.symm x))
  have ha : AnalyticOnNhd ℂ G (a '' S) := by
    rintro _ ⟨x,hx,rfl⟩
    exact (a.analyticAt _).comp ((hF _ (by simpa using hx)).comp (a.symm.analyticAt _))
  have hG : MapsTo G (a '' S) (a '' S) := by
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨F x,hm hx,by simp [G]⟩
  have hi : ∀ x ∈ a '' S, G (G x) = x := by
    rintro _ ⟨x,hx,rfl⟩
    simp only [G,a.symm_apply_apply,hinv x hx]
  exact biholomorphOfAmbientInverse _ _ G G ha ha hG hG hi hi

lemma conjugateInvolutionBiholomorph_apply {n : ℕ} (a : E ≃L[ℂ] Affine n)
    (S : Set E) (F : E → E) (hF : AnalyticOnNhd ℂ F S)
    (hm : MapsTo F S S) (hinv : ∀ x ∈ S, F (F x) = x)
    (x : a '' S) :
    ((conjugateInvolutionBiholomorph a S F hF hm hinv).toHomeomorph x : Affine n) =
      a (F (a.symm x)) := rfl

lemma conjugateInvolutionBiholomorph_involutive {n : ℕ} (a : E ≃L[ℂ] Affine n)
    (S : Set E) (F : E → E) (hF : AnalyticOnNhd ℂ F S)
    (hm : MapsTo F S S) (hinv : ∀ x ∈ S, F (F x) = x) :
    Function.Involutive (conjugateInvolutionBiholomorph a S F hF hm hinv).toHomeomorph := by
  intro x
  apply Subtype.ext
  rw [conjugateInvolutionBiholomorph_apply,conjugateInvolutionBiholomorph_apply,
    a.symm_apply_apply]
  have hx : a.symm x ∈ S := by
    obtain ⟨y,hy,he⟩ := x.property
    rw [← he,a.symm_apply_apply]
    exact hy
  rw [hinv _ hx,a.apply_symm_apply]

theorem Biholomorph.transfer_symmetries {n m : ℕ}
    {S : Set (Affine n)} {T : Set (Affine m)} (e : Biholomorph S T)
    (hS : ∀ p : S, ∃ σ : Biholomorph S S,
      Function.Involutive σ.toHomeomorph ∧ σ.toHomeomorph p = p ∧
      ∃ W : Set S, IsOpen W ∧ p ∈ W ∧ ∀ q ∈ W, σ.toHomeomorph q = q → q = p) :
    ∀ p : T, ∃ σ : Biholomorph T T,
      Function.Involutive σ.toHomeomorph ∧ σ.toHomeomorph p = p ∧
      ∃ W : Set T, IsOpen W ∧ p ∈ W ∧ ∀ q ∈ W, σ.toHomeomorph q = q → q = p := by
  intro p
  obtain ⟨s,hs,hfix,W,hWo,hpW,hW⟩ := hS (e.toHomeomorph.symm p)
  let t := (e.symm.trans s).trans e
  refine ⟨t,?_,?_,e.toHomeomorph.symm ⁻¹' W,hWo.preimage e.toHomeomorph.symm.continuous,
    hpW,?_⟩
  · intro q
    change e.toHomeomorph (s.toHomeomorph (e.toHomeomorph.symm
      (e.toHomeomorph (s.toHomeomorph (e.toHomeomorph.symm q))))) = q
    rw [Homeomorph.symm_apply_apply,hs,Homeomorph.apply_symm_apply]
  · change e.toHomeomorph (s.toHomeomorph (e.toHomeomorph.symm p)) = p
    rw [hfix,Homeomorph.apply_symm_apply]
  · intro q hq hqfix
    apply e.toHomeomorph.symm.injective
    apply hW _ hq
    have hh := congrArg e.toHomeomorph.symm hqfix
    simpa only [t,Biholomorph.trans,Biholomorph.symm,Homeomorph.trans_apply,
      Homeomorph.symm_apply_apply] using hh

end Release061

end

end OAI
