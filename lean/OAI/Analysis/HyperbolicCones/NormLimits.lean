import OAI.Analysis.HyperbolicCones.KernelLimit

namespace OAI

/-! The positive affine paths used in the norm identity and their matrix limits. -/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix Filter Topology
universe u

namespace Paper256

theorem matrix_mul_tendsto {m n k : ℕ} {T : Type u} {L : Filter T}
    {A : T → Matrix (Fin m) (Fin n) ℝ} {B : T → Matrix (Fin n) (Fin k) ℝ}
    {A₀ : Matrix (Fin m) (Fin n) ℝ} {B₀ : Matrix (Fin n) (Fin k) ℝ}
    (hA : Tendsto A L (𝓝 A₀)) (hB : Tendsto B L (𝓝 B₀)) :
    Tendsto (fun t => A t * B t) L (𝓝 (A₀ * B₀)) :=
  ((continuous_fst.matrix_mul continuous_snd).tendsto (A₀, B₀)).comp
    (hA.prodMk_nhds hB)

theorem affine_posDef {n : ℕ} (H : Sym n) (hH : (H : Mat n ℝ).PosSemidef)
    (t : ℝ) (ht : 1 ≤ t) :
    ((1 + (t - 1) • H : Sym n) : Mat n ℝ).PosDef := by
  change ((1 : Mat n ℝ) + (t - 1) • (H : Mat n ℝ)).PosDef
  exact Matrix.PosDef.one.add_posSemidef (hH.smul (sub_nonneg.mpr ht))

theorem positive_unital_map_affine_posDef {m n : ℕ} (D : Sym m →ₗ[ℝ] Sym n)
    (hD : ∀ H : Sym m, (H : Mat m ℝ).PosSemidef → (D H : Mat n ℝ).PosSemidef)
    (hI : D 1 = 1) (H : Sym m) (hH : (H : Mat m ℝ).PosSemidef)
    (t : ℝ) (ht : 1 ≤ t) :
    (D (1 + (t - 1) • H) : Mat n ℝ).PosDef := by
  simpa only [map_add, map_smul, hI] using affine_posDef (D H) (hD H hH) t ht

theorem positive_unital_map_inverseSquareRoot_tendsto {m n : ℕ}
    (D : Sym m →ₗ[ℝ] Sym n)
    (hD : ∀ H : Sym m, (H : Mat m ℝ).PosSemidef → (D H : Mat n ℝ).PosSemidef)
    (hI : D 1 = 1) (H : Sym m) (hH : (H : Mat m ℝ).PosSemidef) :
    Tendsto (fun t : ℝ => inverseSquareRoot (D (1 + (t - 1) • H))) atTop
      (𝓝 (kernelProjection (D H : Mat n ℝ))) := by
  simpa only [map_add, map_smul, hI] using
    inverseSquareRoot_affine_tendsto (D H) (hD H hH)

end Paper256

end

end OAI
