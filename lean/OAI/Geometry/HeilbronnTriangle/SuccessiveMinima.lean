import OAI.Geometry.HeilbronnTriangle.SuccessiveVectors
import OAI.Geometry.HeilbronnTriangle.SuccessiveTransport

namespace OAI


namespace Problem355.SuccessiveMinima

open Module
open scoped BigOperators

theorem exists_basis_product_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hn : 0 < finrank ℝ E)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ b : Basis (Fin (finrank ℝ E)) ℝ E,
      SuccessiveVectors.IsSuccessive L b ∧
      (∏ i, ‖b i‖) ≤ Real.sqrt (finrank ℝ E) ^ finrank ℝ E * ZLattice.covolume L := by
  obtain ⟨b, hb⟩ := SuccessiveVectors.exists_successive_basis L
  refine ⟨b, hb, ?_⟩
  apply SuccessiveBox.successive_norm_product_le hn (by simp) L b
    hb.norm_pos hb.monotone_norm
  intro j x hx hxspan
  exact hb.minimal j x hx hxspan

theorem product_bound_of_successive
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} (hn : 0 < n)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin n) ℝ E) (hb : SuccessiveVectors.IsSuccessive L b) :
    (∏ i, ‖b i‖) ≤ Real.sqrt n ^ n * ZLattice.covolume L := by
  apply SuccessiveBox.successive_norm_product_le hn
    (finrank_eq_card_basis b) L b hb.norm_pos hb.monotone_norm
  intro j x hx hxspan
  exact hb.minimal j x hx hxspan

end Problem355.SuccessiveMinima

end OAI
