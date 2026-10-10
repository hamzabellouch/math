import OAI.Analysis.HyperbolicCones.CompressionBasic

namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

universe u v

namespace Paper256

theorem fromBlocks_quadratic {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (C : Matrix κ ι ℝ) (D : Matrix κ κ ℝ)
    (u : ι → ℝ) (v : κ → ℝ) :
    Sum.elim u v ⬝ᵥ (Matrix.fromBlocks A B C D *ᵥ Sum.elim u v) =
      u ⬝ᵥ (A *ᵥ u) + u ⬝ᵥ (B *ᵥ v) + v ⬝ᵥ (C *ᵥ u) + v ⬝ᵥ (D *ᵥ v) := by
  simp [Matrix.fromBlocks_mulVec, sumElim_dotProduct_sumElim,
    dotProduct_add, Function.comp_def]
  ring

theorem fromBlocks_add_lower_posDef {a c : ℕ} (A : Sym a) (E : Sym c)
    (B : Matrix (Fin a) (Fin c) ℝ) (hA : (A : Mat a ℝ).PosDef)
    (hM : (Matrix.fromBlocks (A : Mat a ℝ) B Bᵀ (E : Mat c ℝ)).PosSemidef)
    (δ : ℝ) (hδ : 0 < δ) :
    (Matrix.fromBlocks (A : Mat a ℝ) B Bᵀ ((E : Mat c ℝ) + δ • 1)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.IsHermitian.fromBlocks A.property (by simp)
      (E.property.add (Matrix.PosDef.one.smul hδ).isHermitian))
  intro w hw
  let u := w ∘ Sum.inl
  let v := w ∘ Sum.inr
  have hsplit : w = Sum.elim u v := by ext (i | i) <;> rfl
  have hbase := hM.dotProduct_mulVec_nonneg w
  rw [hsplit] at hbase ⊢
  simp only [star_trivial] at hbase ⊢
  by_cases hv : v = 0
  · have hu : u ≠ 0 := by
      intro hu
      apply hw
      rw [hsplit, hu, hv]
      ext (i | i) <;> rfl
    have hp := hA.dotProduct_mulVec_pos hu
    simpa only [fromBlocks_quadratic, hv, mulVec_zero, dotProduct_zero,
      zero_dotProduct, add_zero, star_trivial] using hp
  · have hp := (Matrix.PosDef.one.smul hδ : (δ • (1 : Mat c ℝ)).PosDef).dotProduct_mulVec_pos hv
    have hq :
        Sum.elim u v ⬝ᵥ
          (Matrix.fromBlocks (A : Mat a ℝ) B Bᵀ ((E : Mat c ℝ) + δ • 1) *ᵥ Sum.elim u v) =
        Sum.elim u v ⬝ᵥ (Matrix.fromBlocks (A : Mat a ℝ) B Bᵀ (E : Mat c ℝ) *ᵥ Sum.elim u v) +
          v ⬝ᵥ ((δ • (1 : Mat c ℝ)) *ᵥ v) := by
      rw [fromBlocks_quadratic, fromBlocks_quadratic, add_mulVec, dotProduct_add]
      ring
    rw [hq]
    exact add_pos_of_nonneg_of_pos hbase (by simpa only [star_trivial] using hp)

end Paper256

end

end OAI
