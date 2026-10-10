import OAI.Geometry.HeilbronnTriangle.SuccessiveMinima
import OAI.Geometry.HeilbronnTriangle.LatticePacking

namespace OAI


namespace Problem355.PlaneRadius

open Module

theorem exists_short_basis_of_minimum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : finrank ℝ E = 2)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {δ : ℝ} (hδ : 0 < δ)
    (hminimum : ∀ x ∈ L, x ≠ 0 → δ ≤ ‖x‖) :
    ∃ b : Basis (Fin 2) ℝ E,
      (∀ i, b i ∈ L) ∧ (∀ i, ‖b i‖ ≤ 2 * ZLattice.covolume L / δ) := by
  have hex := SuccessiveMinima.exists_basis_product_bound (L := L)
    (show 0 < finrank ℝ E by omega)
  rw [hdim] at hex
  obtain ⟨b, hb, hp⟩ := hex
  have hp' : ‖b 0‖ * ‖b 1‖ ≤ 2 * ZLattice.covolume L := by
    simpa only [Fin.prod_univ_two, Nat.cast_ofNat, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using hp
  have hzero : δ ≤ ‖b 0‖ := hminimum (b 0) (hb.mem_lattice 0) (b.ne_zero 0)
  have hmono : ‖b 0‖ ≤ ‖b 1‖ := hb.monotone_norm (by decide)
  have hone : ‖b 1‖ ≤ 2 * ZLattice.covolume L / δ := by
    apply (le_div_iff₀ hδ).mpr
    nlinarith [norm_nonneg (b 1)]
  refine ⟨b, hb.mem_lattice, ?_⟩
  intro i
  fin_cases i
  · exact hmono.trans hone
  · exact hone

theorem card_le_of_covolume_radius
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : finrank ℝ E = 2)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {δ R : ℝ} (hδ : 0 < δ)
    (hminimum : ∀ x ∈ L, x ≠ 0 → δ ≤ ‖x‖)
    (hR : 2 * ZLattice.covolume L / δ ≤ R)
    (A : Finset L) (c : E)
    (hA : ∀ x ∈ A, (x : E) ∈ Metric.closedBall c R) :
    (A.card : ℝ) ≤ 9 * Real.pi * R ^ 2 / ZLattice.covolume L := by
  obtain ⟨b, hbL, hb⟩ := exists_short_basis_of_minimum hdim L hδ hminimum
  have hR0 : 0 ≤ R := (norm_nonneg (b 0)).trans ((hb 0).trans hR)
  exact LatticePacking.plane_card_le_of_short_basis L b hbL A c R hR0 hA
    (fun i => (hb i).trans hR)

end Problem355.PlaneRadius

end OAI
