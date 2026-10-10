import OAI.Analysis.KadisonKastler.WeakRowEnergy
import OAI.Analysis.KadisonKastler.MinimalRowDynamics

namespace OAI

/-! Uniform row energy bounds on a minimal closed row family. -/

namespace KadisonKastler

noncomputable section

open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance minimalRowEnergyOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance minimalRowEnergyStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

def RowEnergyBound {M : VonNeumannAlgebra H}
    (F : Algebra M →ₗ[ℂ] Algebra M) (ξ : H) (d : ℝ) : Prop :=
  ∀ (n : ℕ) (r : Fin n → Algebra M), (∑ i, r i * star (r i) = 1) → rowEnergy F r ξ ≤ d

theorem rowEnergy_reindex {M : VonNeumannAlgebra H}
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (F : Algebra M →ₗ[ℂ] Algebra M) (r : κ → Algebra M) (ξ : H) :
    rowEnergy F (r ∘ e) ξ = rowEnergy F r ξ :=
  Equiv.sum_comp e (fun j => ‖(star (F (r j)) : H →L[ℂ] H) ξ‖ ^ 2)

theorem RowEnergyBound.finite {M : VonNeumannAlgebra H}
    {F : Algebra M →ₗ[ℂ] Algebra M} {ξ : H} {d : ℝ}
    (h : RowEnergyBound F ξ d) {ι : Type*} [Fintype ι]
    (r : ι → Algebra M) (hr : ∑ i, r i * star (r i) = 1) : rowEnergy F r ξ ≤ d := by
  classical
  let e := (Fintype.equivFin ι).symm
  have he : ∑ i, (r ∘ e) i * star ((r ∘ e) i) = 1 := by
    change (∑ i, r (e i) * star (r (e i))) = 1
    rw [Equiv.sum_comp e (fun j => r j * star (r j))]
    exact hr
  have hb := h (Fintype.card ι) (r ∘ e) he
  rwa [rowEnergy_reindex] at hb

theorem RowEnergyBound.average {M : VonNeumannAlgebra H}
    {F : Algebra M →ₗ[ℂ] Algebra M} {ξ : H} {d : ℝ}
    (h : RowEnergyBound F ξ d) {ι : Type*} [Fintype ι]
    (s : ι → Algebra M) (hs : ∑ i, s i * star (s i) = 1) :
    RowEnergyBound (finiteRightAverage s F) ξ d := by
  intro n r hr
  exact (rowEnergy_rightAverage_le F r s hs ξ).trans
    (h.finite _ (finiteRow_product_normalized r s hr hs))

theorem isClosed_rowEnergyBound {M : VonNeumannAlgebra H} {c d : ℝ}
    (hd : 0 ≤ d) (ξ : H) :
    IsClosed {F : BoundedWeakAlgebraMap M c | RowEnergyBound F.map ξ d} := by
  change IsClosed {F : BoundedWeakAlgebraMap M c | ∀ (n : ℕ) (r : Fin n → Algebra M),
    (∑ i, r i * star (r i) = 1) → rowEnergy F.map r ξ ≤ d}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun n => isClosed_iInter fun r =>
    isClosed_iInter fun _ => isClosed_rowEnergy_le hd r ξ

theorem minimal_row_family_energy_bound {M : VonNeumannAlgebra H} {c d : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (ξ : H)
    (K : Set (BoundedWeakAlgebraMap M c)) (hclosed : IsClosed K)
    (hinv : RowInvariant hc K)
    (hmin : ∀ L : Set (BoundedWeakAlgebraMap M c), L ⊆ K → L.Nonempty → IsClosed L →
      RowInvariant hc L → L = K)
    {F G : BoundedWeakAlgebraMap M c} (hF : F ∈ K) (hG : G ∈ K)
    (hbound : RowEnergyBound F.map ξ d) : RowEnergyBound G.map ξ d := by
  have hs : boundedWeakRowOrbit F ⊆
      {T : BoundedWeakAlgebraMap M c | RowEnergyBound T.map ξ d} := by
    intro T hT
    obtain ⟨n, r, hr, he⟩ := hT
    change RowEnergyBound T.map ξ d
    rw [he]
    exact hbound.average r hr
  have hcl := closure_minimal hs (isClosed_rowEnergyBound (M := M) hd ξ)
  rw [minimal_row_family_orbit_dense hc K hclosed hinv hmin hF] at hcl
  exact hcl hG

end

end KadisonKastler

end OAI
