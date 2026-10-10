import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationPrimePriorsGridDefs
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSourceScalesBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open Filter TemplateOneSidedSourceScales

theorem eventually_original_prime_priors_finite_grid
    {τ ι : Type} [Fintype τ] [Fintype ι]
    (C z c : ℝ) (d : ℕ) {α βLong : ℝ} (β γ γLong : ι → ℝ)
    (hC : 0 ≤ C) (hz : 0 < z) (hc : 0 ≤ c) (hα : 0 < α)
    (hαβ : ∀i,α ≤ β i) (hβγ : ∀i,β i < γ i)
    (hγLong : ∀i,γ i < γLong i) (hβLong : 0 ≤ βLong) :
    ∃δ : ℝ,0 < δ ∧ ∀ᶠ L : ℝ in atTop,∀i,
      OriginalPrimePriorBound τ C z c d α (β i) (γLong i) βLong δ L := by
  classical
  have h (i : ι) : ∃δ : ℝ,0 < δ ∧ ∀ᶠ L : ℝ in atTop,
      OriginalPrimePriorBound τ C z c d α (β i) (γLong i) βLong δ L :=
    eventually_original_prime_priors_scale_gap C z c d hC hz hc hα
      (hαβ i) (hβγ i) (hγLong i) hβLong
  choose δ hδ hbound using h
  by_cases hi : Nonempty ι
  · let : Nonempty ι := hi
    let S : Finset ℝ := Finset.univ.image δ
    have hS : S.Nonempty := Finset.univ_nonempty.image δ
    let rate := S.min' hS
    have hrate : 0 < rate := by
      obtain ⟨i,hi,he⟩ := Finset.mem_image.mp (Finset.min'_mem S hS)
      change 0 < S.min' hS
      rw [← he]
      exact hδ i
    have hle (i : ι) : rate ≤ δ i :=
      Finset.min'_le S (δ i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    refine ⟨rate,hrate,?_⟩
    filter_upwards [Filter.eventually_all.mpr hbound] with L hL
    exact fun i=>OriginalPrimePriorBound.mono (hL i) (hle i)
  · refine ⟨1,zero_lt_one,Filter.Eventually.of_forall ?_⟩
    intro L i
    exact False.elim (hi ⟨i⟩)

theorem eventually_original_prime_priors_scale_grid
    {τ : Type} [Fintype τ] (C z c : ℝ) (d : ℕ)
    (α βGlobal γgap βLong : ℝ) (hC : 0 ≤ C) (hz : 0 < z) (hc : 0 ≤ c)
    (hα : 0 < α) (hgap : 0 < γgap) (hβLong : 0 ≤ βLong) :
    ∃δ : ℝ,0 < δ ∧ ∀ᶠ L : ℝ in atTop,
      ∀n : Fin (scaleCount βGlobal γgap),0 < n.val →
      OriginalPrimePriorBound τ C z c d (lowerExponent α γgap)
        (shortExponent γgap n.val) (longExponent γgap n.val+scaleStep γgap) βLong δ L := by
  let ι := {n : Fin (scaleCount βGlobal γgap) // 0 < n.val}
  have hstep : 0 < scaleStep γgap := by unfold scaleStep; positivity
  have hlow : 0 < lowerExponent α γgap := by
    unfold lowerExponent
    exact lt_min hα (half_pos hstep)
  obtain ⟨δ,hδ,hbound⟩ := eventually_original_prime_priors_finite_grid (τ:=τ) (ι:=ι)
    C z c d (fun n=>shortExponent γgap n.val.val)
    (fun n=>longExponent γgap n.val.val)
    (fun n=>longExponent γgap n.val.val+scaleStep γgap) hC hz hc hlow
    (fun n=>(scale_exponents hα hgap n.property).2.1)
    (fun n=>(scale_exponents hα hgap n.property).2.2)
    (fun _=>lt_add_of_pos_right _ hstep) hβLong
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hbound] with L hL
  exact fun n hn=>hL ⟨n,hn⟩

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
