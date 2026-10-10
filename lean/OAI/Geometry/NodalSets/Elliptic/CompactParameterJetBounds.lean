import OAI.Geometry.NodalSets.Elliptic.CompactParameterDerivativeBounds
import OAI.Geometry.NodalSets.Elliptic.RealFiniteJetSquare

namespace OAI

namespace Yau.Geometry
open Yau.Analysis
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]
variable {ι : Type*} [Fintype ι]

theorem compact_parameter_finite_jet_bound (n : ℕ)
    (f : ι → T → Yau.Jets.Coord → ℝ) {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (hf : ∀ i ds, ds.length ≤ n → Continuous (fun z : T × Q ↦ partialJet (f i z.1) ds z.2)) :
    ∃ B > 0, ∀ i t x, x ∈ Q → ∀ ds : List (Fin 4), ds.length ≤ n →
      |partialJet (f i t) ds x| ≤ B := by
  let I := ι × (Σ r : Fin (n+1), Fin r.val → Fin 4)
  obtain ⟨B,hB,hbound⟩ := compact_parameter_finite_scalar_bound
    (fun e : I ↦ fun t x ↦ partialJet (f e.1 t) (List.ofFn e.2.2) x)
    hQ (fun e ↦ hf e.1 _ (by simp only [List.length_ofFn]; exact Nat.le_of_lt_succ e.2.1.isLt))
  refine ⟨B,hB,?_⟩
  intro i t x hx ds hd
  have h := hbound (i,⟨⟨ds.length,by omega⟩,ds.get⟩) t x hx
  simpa only [List.ofFn_get] using h

end
end Yau.Geometry

end OAI
