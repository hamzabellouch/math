import Mathlib
import OAI.Analysis.HardSphere.FormDomain.HilbertJet

namespace OAI

section

noncomputable section
open Set MeasureTheory Filter ContinuousLinearMap
open scoped Topology ComplexOrder InnerProductSpace
namespace HardSphere

def groundSpace (N : ℕ) (L : Length) (a : ℝ) : Submodule ℂ (ScalarL2 N L) :=
  @Submodule.span ℂ (ScalarL2 N L) Complex.instSemiring
    (scalarL2_normedAddCommGroup N L).toAddCommMonoid (scalarL2_module N L)
    {ψ | ∃u : Jet N L,IsGroundVector N L a u ∧ u.1=ψ}

lemma IsGroundVector.mem_groundSpace {N : ℕ} {L : Length} {a : ℝ}
    {u : Jet N L} (hu : IsGroundVector N L a u) : u.1∈groundSpace N L a :=
  Submodule.subset_span ⟨u,hu,rfl⟩

lemma IsGroundVector.energy_eq {N : ℕ} {L : Length} {a : ℝ} {u v : Jet N L}
    (hu : IsGroundVector N L a u) (hv : IsGroundVector N L a v) : energy u=energy v :=
  le_antisymm (hu.2.2.2 v hv.1 hv.2.1 hv.2.2.1) (hv.2.2.2 u hu.1 hu.2.1 hu.2.2.1)

lemma groundSpace_le_resolvent {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : IsGroundVector N L a u) :
    groundSpace N L a ≤
      Module.End.eigenspace (formResolvent N L a).toLinearMap ((1+(energy u:ℂ))⁻¹) ⊓
        bosonicSubmodule N L := by
  apply Submodule.span_le.mpr
  rintro ψ ⟨v,hv,rfl⟩
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_,mem_bosonicSubmodule.mpr hv.2.1⟩
  rw [hu.energy_eq hv]
  exact hv.resolvent_eigenvector

lemma ground_of_resolvent {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : IsGroundVector N L a u) {ψ : ScalarL2 N L} (hψ : ‖ψ‖=1)
    (hb : bosonic ψ)
    (he : formResolvent N L a ψ=((1+(energy u:ℂ))⁻¹) • ψ) :
    ∃v : Jet N L,v.1=ψ ∧ IsGroundVector N L a v := by
  let c : ℂ := 1+(energy u:ℂ)
  have hE : 0≤energy u := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hc : c≠0 := by
    dsimp only [c]
    exact_mod_cast (show (1:ℝ)+energy u≠0 by linarith)
  let J := scalarEmbedding N L a
  let w : hilbertDomain N L a := J.adjoint (c • ψ)
  let v : Jet N L := hilbertJetEquiv N L (w : HilbertJet N L)
  have hscalar : J w=ψ := by
    change formResolvent N L a (c • ψ)=ψ
    rw [map_smul,he,smul_smul,mul_inv_cancel₀ hc,one_smul]
  have hv : v.1=ψ := hscalar
  have hn : ‖(w : HilbertJet N L)‖^2=1+energy u := by
    have hi := J.adjoint_inner_left w (c • ψ)
    change inner ℂ w w=inner ℂ (c • ψ) (J w) at hi
    rw [hscalar,inner_smul_left,inner_self_eq_norm_sq_to_K,hψ] at hi
    simp only [RCLike.ofReal_one,one_pow,mul_one] at hi
    calc
      ‖(w : HilbertJet N L)‖^2=‖w‖^2 := rfl
      _ = (inner ℂ w w).re := norm_sq_eq_re_inner (𝕜:=ℂ) w
      _ = ((starRingEnd ℂ) c).re := congrArg Complex.re hi
      _ = 1+energy u := by simp [c]
  have henergy : energy v=energy u := by
    rw [hilbertJet_norm_sq] at hn
    change ‖v.1‖^2+energy v=1+energy u at hn
    rw [hv,hψ,one_pow] at hn
    linarith
  refine ⟨v,hv,w.property,?_,?_,?_⟩
  · rwa [hv]
  · rwa [hv]
  · intro z hz hzb hzn
    rw [henergy]
    exact hu.2.2.2 z hz hzb hzn

lemma groundSpace_normalized {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : IsGroundVector N L a u) {ψ : ScalarL2 N L}
    (hψ : ψ∈groundSpace N L a) (hn : ‖ψ‖=1) :
    ∃v : Jet N L,v.1=ψ ∧ IsGroundVector N L a v := by
  have hh := groundSpace_le_resolvent hu hψ
  exact ground_of_resolvent hu hn (mem_bosonicSubmodule.mp hh.2)
    (Module.End.mem_eigenspace_iff.mp hh.1)

lemma groundSpace_eq_bot_of_no_ground {N : ℕ} {L : Length} {a : ℝ}
    (h : ¬∃u : Jet N L,IsGroundVector N L a u) : groundSpace N L a=⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro ψ ⟨u,hu,_⟩
  exact (h ⟨u,hu⟩).elim

lemma groundSpace_normalized_iff {N : ℕ} {L : Length} {a : ℝ}
    {ψ : ScalarL2 N L} (hn : ‖ψ‖=1) :
    ψ∈groundSpace N L a ↔ ∃u : Jet N L,u.1=ψ ∧ IsGroundVector N L a u := by
  classical
  constructor
  · intro hψ
    have hex : ∃u : Jet N L,IsGroundVector N L a u := by
      by_contra h
      rw [groundSpace_eq_bot_of_no_ground h] at hψ
      have hz : ψ=0 := hψ
      rw [hz,norm_zero] at hn
      norm_num at hn
    obtain ⟨u,hu⟩ := hex
    exact groundSpace_normalized hu hψ hn
  · rintro ⟨u,rfl,hu⟩
    exact hu.mem_groundSpace

lemma groundSpace_nontrivial {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : IsGroundVector N L a u) : Nontrivial (groundSpace N L a) := by
  refine ⟨⟨(⟨u.1,hu.mem_groundSpace⟩ : groundSpace N L a),0,?_⟩⟩
  intro hh
  have hz : u.1=0 := congrArg Subtype.val hh
  have hn := hu.2.2.1
  rw [hz,norm_zero] at hn
  norm_num at hn

end HardSphere
end
end

end OAI
