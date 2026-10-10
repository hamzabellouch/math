import OAI.MeasureTheory.Falconer.Recursion.ParentConeGeometry

namespace OAI

namespace PlanarFalconer
open Set

noncomputable def sourceCenteredCellDirection (X Y P Q : DyadicSquare) : UnitCircle :=
  sourceCircleRotate (-sourceParentAxis X Y) (sourceRadialUnit Q.center P.center)

theorem uniform_parent_cell_geometry {sig : ℝ} (hsig : 0 < sig) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a p : ℝ, ∀ X Y P Q : DyadicSquare,
    0 < X.side → 0 < Y.side → 0 < P.side → 0 < Q.side →
    X.side ≤ (2:ℝ)^(-a) → Y.side ≤ (2:ℝ)^(-a) →
    P.side ≤ (2:ℝ)^(-p) → Q.side ≤ (2:ℝ)^(-p) →
    P.carrier ⊆ X.carrier → Q.carrier ⊆ Y.carrier →
    100*(2:ℝ)^(-a) ≤ dist X.center Y.center →
    dist X.center Y.center ≤ 2000*(2:ℝ)^(-a) →
    ∀ x ∈ P.carrier, ∀ y ∈ Q.carrier, ∃ φ : ℝ,
      |φ| ≤ 1/20 ∧
      dist (sourceUnitDirection φ) (sourceCenteredCellDirection X Y P Q) ≤
        graphUncappedAngularScale N sig (p-a) ∧
      x-y = ‖x-y‖ • sourceDirection (φ+sourceParentAxis X Y) := by
  obtain ⟨N₀, hN₀⟩ := dyadic_direction_within_graph_scale (c := 96) (s := 1)
    hsig (by norm_num) (by norm_num)
  refine ⟨N₀, ?_⟩
  intro N hN a p X Y P Q hX hY hP hQ hXa hYa hPp hQp hPX hQY hlo hhi x hx y hy
  obtain ⟨φ,hφ,he,hΔ⟩ := strong_separation_parent_angle X Y hX hY hXa hYa hlo (hPX hx) (hQY hy)
  have hd := dyadic_strong_separation_endpoints X Y hX hY hXa hYa hlo hhi (hPX hx) (hQY hy)
  have hcent := dyadic_strong_separation_endpoints X Y hX hY hXa hYa hlo hhi
    (hPX (P.center_mem hP)) (hQY (Q.center_mem hQ))
  have hc : P.center ≠ Q.center := dist_pos.mp
    ((by positivity : 0 < 96*(2:ℝ)^(-a)).trans_le hcent.1)
  have hmove := hN₀ N hN a p Q P hQ hP
    (by simpa only [one_mul] using hQp) (by simpa only [one_mul] using hPp)
    y hy x hx (by simpa only [dist_comm] using hd.1) hc
  refine ⟨φ,hφ,?_,hΔ⟩
  rw [he, sourceCenteredCellDirection, sourceCircleRotate_dist]
  exact hmove

theorem uniform_parent_cell_geometry_frequency {sig : ℝ} (hsig : 0 < sig) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a p v : ℝ, ∀ X Y P Q : DyadicSquare,
    0 < X.side → 0 < Y.side → 0 < P.side → 0 < Q.side →
    X.side ≤ (2:ℝ)^(-a) → Y.side ≤ (2:ℝ)^(-a) →
    P.side ≤ (2:ℝ)^(-p) → Q.side ≤ (2:ℝ)^(-p) →
    P.carrier ⊆ X.carrier → Q.carrier ⊆ Y.carrier →
    100*(2:ℝ)^(-a) ≤ dist X.center Y.center →
    dist X.center Y.center ≤ 2000*(2:ℝ)^(-a) →
    ∀ Ψ : ℝ → ℝ, (∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4) →
    ∀ r : ℝ, Ψ (r/(2:ℝ)^v) ≠ 0 →
    ∀ x ∈ P.carrier, ∀ y ∈ Q.carrier, ∃ φ : ℝ,
      |φ| ≤ 1/20 ∧
      dist (sourceUnitDirection φ) (sourceCenteredCellDirection X Y P Q) ≤
        graphUncappedAngularScale N sig (p-a) ∧
      x-y = ‖x-y‖ • sourceDirection (φ+sourceParentAxis X Y) ∧
      24*(2:ℝ)^((p-a)+(v-p)) ≤ r*‖x-y‖ ∧
      r*‖x-y‖ ≤ 8016*(2:ℝ)^(v-a) := by
  obtain ⟨N₀,hN₀⟩ := uniform_parent_cell_geometry hsig
  refine ⟨N₀,?_⟩
  intro N hN a p v X Y P Q hX hY hP hQ hXa hYa hPp hQp hPX hQY hlo hhi Ψ hΨ r hr x hx y hy
  obtain ⟨φ,hφ,he,hΔ⟩ := hN₀ N hN a p X Y P Q hX hY hP hQ hXa hYa hPp hQp
    hPX hQY hlo hhi x hx y hy
  have hf := source_strong_separation_frequency X Y hX hY a v hXa hYa hlo hhi Ψ hΨ
    (hPX hx) (hQY hy) hr
  refine ⟨φ,hφ,he,hΔ,?_,hf.2.2.2⟩
  simpa only [show p-a+(v-p) = v-a by ring] using hf.2.2.1

end PlanarFalconer

end OAI
