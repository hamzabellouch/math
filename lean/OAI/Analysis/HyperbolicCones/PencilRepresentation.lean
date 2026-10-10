import OAI.Analysis.HyperbolicCones.PencilCompression

namespace OAI

noncomputable section

open Set Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256

theorem zero_slice_proper (K : Set Ambient)
    (hzero : ∀ X Z : Sym 4, ((X, Z), (0 : Fin 3 → ℝ)) ∈ K ↔
      (X : Mat 4 ℝ).PosSemidef ∧ (Z : Mat 4 ℝ).PosSemidef) :
    (((-1, 1), 0) : Ambient) ∉ K := by
  intro h
  have hp := ((hzero (-1) 1).mp h).1
  have hd := hp.diag_nonneg (i := (0 : Fin 4))
  norm_num at hd

theorem representation_compression {n : ℕ} (K : Set Ambient)
    (L : Ambient →ₗ[ℝ] Sym n) (hL : K = {x | (L x : Mat n ℝ).PosSemidef})
    (he : basePoint ∈ interior K) (hproper : ∃ x : Ambient, x ∉ K) :
    ∃ m : ℕ, 0 < m ∧ ∃ C : Ambient →ₗ[ℝ] Sym m,
      (C basePoint : Mat m ℝ).PosDef ∧ K = {x | (C x : Mat m ℝ).PosSemidef} := by
  have hb : (L basePoint : Mat n ℝ).PosSemidef := by
    have h := interior_subset he
    rwa [hL] at h
  have hn : ∃ x : Ambient, ¬(L x : Mat n ℝ).PosSemidef := by
    simpa only [hL, mem_ofPred_eq] using hproper
  obtain ⟨m, hm, C, hC, hrep⟩ := pencil_compression_positive L basePoint hb
    (pencil_common_kernel K L hL he) hn
  refine ⟨m, hm, C, hC, ?_⟩
  ext x
  rw [hL]
  exact hrep x

theorem representation_compression_of_zero_slice {n : ℕ} (K : Set Ambient)
    (L : Ambient →ₗ[ℝ] Sym n) (hL : K = {x | (L x : Mat n ℝ).PosSemidef})
    (he : basePoint ∈ interior K)
    (hzero : ∀ X Z : Sym 4, ((X, Z), (0 : Fin 3 → ℝ)) ∈ K ↔
      (X : Mat 4 ℝ).PosSemidef ∧ (Z : Mat 4 ℝ).PosSemidef) :
    ∃ m : ℕ, 0 < m ∧ ∃ C : Ambient →ₗ[ℝ] Sym m,
      (C basePoint : Mat m ℝ).PosDef ∧ K = {x | (C x : Mat m ℝ).PosSemidef} :=
  representation_compression K L hL he ⟨(((-1, 1), 0) : Ambient), zero_slice_proper K hzero⟩

end Paper256

end

end OAI
