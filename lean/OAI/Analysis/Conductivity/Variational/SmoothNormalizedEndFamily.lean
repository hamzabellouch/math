import Mathlib
import OAI.Analysis.Conductivity.Variational.CompactParametricBounds
import OAI.Analysis.Conductivity.Fourier.CompactifiedFourierTail

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

lemma smooth_mul_of_support_in_open {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f ρ : E→ℝ} {S : Set E} (hS : IsOpen S)
    (hf : ContDiffOn ℝ (↑(⊤:ℕ∞)) f S) (hρ : ContDiff ℝ (↑(⊤:ℕ∞)) ρ)
    (hs : tsupport ρ⊆S) : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => ρ x*f x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x∈tsupport ρ
  · exact hρ.contDiffAt.mul (hf.contDiffAt (hS.mem_nhds (hs hx)))
  · have he : (fun y => ρ y*f y)=ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq he

lemma exists_normalized_end_cutoff {R T0 δ : ℝ} (hT : δ-T0 < -R) :
    ∃ ρ : (ℝ×Coord3)→ℝ,ContDiff ℝ (↑(⊤:ℕ∞)) ρ ∧
      tsupport ρ⊆Ioo (-1) 1 ×ˢ {x : Coord3 | δ-T0<x 0} ∧
      (∀ z,ρ z∈Icc 0 1) ∧
      (∀ p∈Icc (-(1:ℝ)/2) (1/2),∀ x : Coord3, x 0∈Icc (-R) R → ρ (p,x)=1) := by
  let K : Set (ℝ×ℝ) := Icc (-(1:ℝ)/2) (1/2) ×ˢ Icc (-R) R
  let Ω : Set (ℝ×ℝ) := Ioo (-1) 1 ×ˢ Ioo (δ-T0) (R+1)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hΩ : IsOpen Ω := isOpen_Ioo.prod isOpen_Ioo
  have hb : Bornology.IsBounded Ω :=
    ((isCompact_Icc : IsCompact (Icc (-1:ℝ) 1)).isBounded.subset Ioo_subset_Icc_self).prod
      ((isCompact_Icc : IsCompact (Icc (δ-T0) (R+1))).isBounded.subset Ioo_subset_Icc_self)
  have hsub : K⊆Ω := by
    intro z hz
    exact ⟨⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩,
      ⟨hT.trans_le hz.2.1,by linarith [hz.2.2]⟩⟩
  obtain ⟨χ,hχ,hχc,hχs,hχb,hχ1⟩ := exists_smooth_core_cutoff hK hΩ hb hsub
  let Q : (ℝ×Coord3)→(ℝ×ℝ) := fun z => (z.1,z.2 0)
  have hQ : ContDiff ℝ (↑(⊤:ℕ∞)) Q := by dsimp [Q]; fun_prop
  refine ⟨χ ∘ Q,hχ.comp hQ,?_,fun z => hχb _,?_⟩
  · intro z hz
    have he := hχs (tsupport_comp_subset_preimage χ hQ.continuous hz)
    exact ⟨he.1,he.2.1⟩
  · intro p hp x hx
    exact (hχ1 (p,x 0) ⟨hp,hx⟩).self_of_nhds

theorem exists_smooth_normalized_tail {s : Fin 3→ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {lam T0 gap B δ R : ℝ} {a phase : (Fin 2→ℤ)→ℝ}
    (hg : 0<gap) (hB : 0≤B) (ha : ∀ h,|a h|≤B) (hδ : 0<δ)
    (hr : ∀ h,a h≠0 → lam+gap≤torusRate s h) (hT : δ-T0 < -R) :
    ∃ f : (ℝ×Coord3)→ℝ,ContDiff ℝ (↑(⊤:ℕ∞)) f ∧
      (∀ p≤0,∀ x,f (p,x)=0) ∧
      (∀ p∈Ioc 0 (1/2),∀ x : Coord3,x 0∈Icc (-R) R →
        f (p,x)=exp (lam*(T0+1/p))*flatFourier s a phase (x+![T0+1/p,0,0])) := by
  obtain ⟨ρ,hρ,hρs,hρb,hρ1⟩ := exists_normalized_end_cutoff hT
  have hr' : ∀ h,a h≠0 → lam<torusRate s h := fun h hh => by linarith [hr h hh]
  refine ⟨fun z => ρ z*compactifiedFourierTail s lam T0 a phase z,
    smooth_mul_of_support_in_open (isOpen_Ioo.prod (axial_halfspace_open _))
      (compactifiedFourierTail_smooth hs hg hB ha hδ hr) hρ hρs,?_,?_⟩
  · intro p hp x
    dsimp only
    rw [compactifiedFourierTail_of_nonpos hr' hp,mul_zero]
  · intro p hp x hx
    dsimp only
    rw [hρ1 p ⟨by linarith [hp.1],hp.2⟩ x hx,one_mul,compactifiedFourierTail_of_pos hr' hp.1]

end ScalarConductivity

end
end

end OAI
