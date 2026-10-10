import Mathlib
import OAI.Analysis.HardSphere.Geometry.FirstVariation
import OAI.Analysis.HardSphere.FormDomain.EnergyParallelogram

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
namespace HardSphere

lemma permutationPullback_comp {N : ℕ} {L : Length}
    (σ τ : Equiv.Perm (Fin N)) (ψ : ScalarL2 N L) :
    permutationPullback σ (permutationPullback τ ψ) = permutationPullback (σ * τ) ψ := by
  change Lp.compMeasurePreserving _ (measurePreserving_permute σ)
    (Lp.compMeasurePreserving _ (measurePreserving_permute τ) ψ) = _
  rw [← Lp.compMeasurePreserving_comp_apply]
  rfl

lemma inner_permutationPullback {N : ℕ} {L : Length} (σ : Equiv.Perm (Fin N))
    (ψ φ : ScalarL2 N L) :
    inner ℂ (permutationPullback σ ψ) (permutationPullback σ φ) = inner ℂ ψ φ :=
  (Lp.compMeasurePreservingₗᵢ ℂ _ (measurePreserving_permute σ)).inner_map_map ψ φ

lemma gradientPairing_permutationJet {N : ℕ} {L : Length}
    (σ : Equiv.Perm (Fin N)) (u v : Jet N L) :
    Variational.gradientPairing (permutationJet σ u) (permutationJet σ v) =
      Variational.gradientPairing u v := by
  change (∑ p : Direction N, inner ℂ (permutationPullback σ (u.2 (σ.symm p.1, p.2)))
    (permutationPullback σ (v.2 (σ.symm p.1, p.2)))) = _
  simp only [inner_permutationPullback]
  exact Equiv.sum_comp (Equiv.prodCongr σ.symm (Equiv.refl (Fin 3)))
    (fun p ↦ inner ℂ (u.2 p) (v.2 p))

theorem IsGroundVector.permutationInvariant {N : ℕ} {L : Length} {a : ℝ}
    {u : Jet N L} (hu : IsGroundVector N L a u) (σ : Equiv.Perm (Fin N)) :
    permutationJet σ u = u := by
  have hs : (permutationJet σ u).1 = u.1 := (bosonic_iff_pullback u.1).mp hu.2.1 σ
  have hv : permutationJet σ u ∈ groundFormSubmodule N L a := by
    rw [mem_groundFormSubmodule]
    exact ⟨permutationJet_mem_domain σ hu.1, hs ▸ hu.2.1⟩
  exact Variational.minimizer_eq_of_scalar_eq (groundFormSubmodule N L a) u
    (mem_groundFormSubmodule.mpr ⟨hu.1, hu.2.1⟩) hu.2.2.1
    (fun w hw hn ↦ hu.2.2.2 w (mem_groundFormSubmodule.mp hw).1
      (mem_groundFormSubmodule.mp hw).2 hn)
    (permutationJet σ u) hv hs (le_of_eq (energy_permutationJet σ u))

lemma bosonic_sum_permutationPullback {N : ℕ} {L : Length} (ψ : ScalarL2 N L) :
    bosonic (∑ σ : Equiv.Perm (Fin N), permutationPullback σ ψ) := by
  rw [bosonic_iff_pullback]
  intro τ
  simp only [map_sum, permutationPullback_comp]
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ ↦ permutationPullback σ ψ)

lemma gradientPairing_sum_right {N : ℕ} {L : Length} {I : Type*} [Fintype I]
    (u : Jet N L) (v : I → Jet N L) :
    Variational.gradientPairing u (∑ i, v i) =
      ∑ i, Variational.gradientPairing u (v i) := by
  simp only [Variational.gradientPairing, Prod.snd_sum, Finset.sum_apply, inner_sum]
  exact Finset.sum_comm

theorem IsGroundVector.full_first_variation {N : ℕ} {L : Length} {a : ℝ}
    {u : Jet N L} (hu : IsGroundVector N L a u) (v : Jet N L)
    (hv : v ∈ dirichletDomain N L a) :
    (∑ p : Direction N, inner ℂ (u.2 p) (v.2 p)) =
      (energy u : ℂ) * inner ℂ u.1 v.1 := by
  let w : Jet N L := ∑ σ : Equiv.Perm (Fin N), permutationJet σ v
  have hwd : w ∈ dirichletDomain N L a := by
    change w ∈ dirichletSubmodule N L a
    exact Submodule.sum_mem _ fun σ _ ↦ permutationJet_mem_domain σ hv
  have hwb : bosonic w.1 := by
    dsimp only [w]
    rw [Prod.fst_sum]
    exact bosonic_sum_permutationPullback v.1
  have hgp (σ : Equiv.Perm (Fin N)) :
      Variational.gradientPairing u (permutationJet σ v) = Variational.gradientPairing u v := by
    calc
      _ = Variational.gradientPairing (permutationJet σ u) (permutationJet σ v) := by
        rw [hu.permutationInvariant σ]
      _ = _ := gradientPairing_permutationJet σ u v
  have hip (σ : Equiv.Perm (Fin N)) :
      inner ℂ u.1 (permutationJet σ v).1 = inner ℂ u.1 v.1 := by
    calc
      _ = inner ℂ (permutationPullback σ u.1) (permutationPullback σ v.1) := by
        rw [(bosonic_iff_pullback u.1).mp hu.2.1 σ]; rfl
      _ = _ := inner_permutationPullback σ u.1 v.1
  have he := hu.first_variation w hwd hwb
  change Variational.gradientPairing u w = _ at he
  simp only [w, gradientPairing_sum_right, hgp, Prod.fst_sum, inner_sum, hip,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at he
  have hc : (Fintype.card (Equiv.Perm (Fin N)) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  apply mul_left_cancel₀ hc
  change (Fintype.card (Equiv.Perm (Fin N)) : ℂ) * Variational.gradientPairing u v = _
  rw [he]
  ring

end HardSphere

end
end
end
end

end OAI
