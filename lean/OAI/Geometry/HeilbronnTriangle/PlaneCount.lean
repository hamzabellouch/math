import OAI.Geometry.HeilbronnTriangle.LatticePacking
import OAI.Geometry.HeilbronnTriangle.PrimitiveLine
import OAI.Geometry.HeilbronnTriangle.SuccessiveVectors
import OAI.Geometry.HeilbronnTriangle.SuccessiveEstimates

namespace OAI


noncomputable section

namespace Problem355.PlaneCount

open MeasureTheory

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem plane_lattice_count
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis (Fin 2) ℝ E) (hbL : ∀ i, b i ∈ L)
    (hfirst : ∀ u ∈ L, u ≠ 0 → ‖b 0‖ ≤ ‖u‖)
    (hsecond : ∀ u ∈ L, u ∉ Submodule.span ℝ {b 0} → ‖b 1‖ ≤ ‖u‖)
    (A : Finset L) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ a ∈ A, ‖(a : E)‖ ≤ R) :
    (‖b 1‖ ≤ R →
      (A.card : ℝ) ≤ 9 * Real.pi * R ^ 2 / ZLattice.covolume L) ∧
    (R < ‖b 1‖ →
      (∀ a ∈ A, ∃ z : ℤ, (a : E) = (z : ℝ) • b 0) ∧
      (A.card : ℝ) ≤ 1 + 2 * R / ‖b 0‖) := by
  classical
  have hv : b 0 ≠ 0 := b.ne_zero 0
  have horder : ‖b 0‖ ≤ ‖b 1‖ := hfirst (b 1) (hbL 1) (b.ne_zero 1)
  have hshort : ∀ u ∈ L.toAddSubgroup, u ≠ 0 → ‖b 0‖ ≤ ‖u‖ := hfirst
  constructor
  · intro hlarge
    apply LatticePacking.plane_card_le_of_short_basis L b hbL A 0 R hR
    · intro a ha
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hA a ha
    · intro i
      fin_cases i
      · exact horder.trans hlarge
      · exact hlarge
  · intro hsmall
    have hline (u : E) (hu : u ∈ L) (hnorm : ‖u‖ ≤ R) :
        ∃ r : ℝ, u = r • b 0 := by
      have hspan : u ∈ Submodule.span ℝ {b 0} := by
        by_contra hout
        exact (not_lt_of_ge (hsecond u hu hout)) (hnorm.trans_lt hsmall)
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hspan
      exact ⟨r, hr.symm⟩
    have hinteger (a : L) (ha : a ∈ A) :
        ∃ z : ℤ, (a : E) = (z : ℝ) • b 0 :=
      PrimitiveLine.integer_multiple_of_shortest L.toAddSubgroup hv (hbL 0)
        hshort a.property (hline a a.property (hA a ha))
    refine ⟨hinteger, ?_⟩
    let e : L ↪ E := ⟨Subtype.val, Subtype.val_injective⟩
    let S : Finset E := A.map e
    have hSmult : ∀ p ∈ S, ∃ z : ℤ, p = (z : ℝ) • b 0 := by
      intro p hp
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hp
      exact hinteger a ha
    have hSnorm : ∀ p ∈ S, ‖p‖ ≤ R := by
      intro p hp
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hp
      exact hA a ha
    have hcount := PrimitiveLine.card_integral_multiples_le
      (b 0) hv R hR S hSmult hSnorm
    simpa only [S, Finset.card_map] using hcount

theorem thin_plane_lattice_count
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis (Fin 2) ℝ E) (hbL : ∀ i, b i ∈ L)
    (hfirst : ∀ u ∈ L, u ≠ 0 → ‖b 0‖ ≤ ‖u‖)
    (hsecond : ∀ u ∈ L, u ∉ Submodule.span ℝ {b 0} → ‖b 1‖ ≤ ‖u‖)
    (A : Finset L) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ a ∈ A, ‖(a : E)‖ ≤ R)
    (hsmall : R < ‖b 1‖) (hone : ‖b 0‖ ≤ R) :
    (A.card : ℝ) ≤ 3 * R / ‖b 0‖ := by
  have h := ((plane_lattice_count L b hbL hfirst hsecond A R hR hA).2 hsmall).2
  have hpos : 0 < ‖b 0‖ := norm_pos_iff.mpr (b.ne_zero 0)
  have hratio : 1 ≤ R / ‖b 0‖ := (le_div_iff₀ hpos).mpr (by simpa using hone)
  calc
    (A.card : ℝ) ≤ 1 + 2 * R / ‖b 0‖ := h
    _ ≤ 3 * R / ‖b 0‖ := by
      simp only [mul_div_assoc]
      linarith

omit [MeasurableSpace E] [BorelSpace E] in

theorem exists_successive_plane_basis
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hdim : Module.finrank ℝ E = 2) :
    ∃ b : Module.Basis (Fin 2) ℝ E,
      (∀ i, b i ∈ L) ∧
      (∀ u ∈ L, u ≠ 0 → ‖b 0‖ ≤ ‖u‖) ∧
      (∀ u ∈ L, u ∉ Submodule.span ℝ {b 0} → ‖b 1‖ ≤ ‖u‖) := by
  obtain ⟨v, hv⟩ := SuccessiveVectors.exists_successive L 2 (by omega)
  let b := basisOfLinearIndependentOfCardEqFinrank' v hv.independent (by simp [hdim])
  have hb : (b : Fin 2 → E) = v := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  have hzero : SuccessiveVectors.earlier v 0 = ∅ := by
    simp [SuccessiveVectors.earlier]
  have hone : SuccessiveVectors.earlier v 1 = {v 0} := by
    simp [SuccessiveVectors.earlier]
  refine ⟨b, ?_, ?_, ?_⟩
  · simpa only [hb] using hv.mem_lattice
  · intro u hu hne
    rw [hb]
    apply hv.minimal 0 u hu
    simpa only [hzero, Submodule.span_empty, Submodule.mem_bot] using hne
  · intro u hu hout
    rw [hb] at hout ⊢
    apply hv.minimal 1 u hu
    simpa only [hone] using hout

theorem exists_plane_lattice_count
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hdim : Module.finrank ℝ E = 2) :
    ∃ b : Module.Basis (Fin 2) ℝ E,
      (∀ i, b i ∈ L) ∧ 0 < ‖b 0‖ ∧ ‖b 0‖ ≤ ‖b 1‖ ∧
      ∀ (A : Finset L) (R : ℝ), 0 ≤ R →
        (∀ a ∈ A, ‖(a : E)‖ ≤ R) →
        (‖b 1‖ ≤ R →
          (A.card : ℝ) ≤ 9 * Real.pi * R ^ 2 / ZLattice.covolume L) ∧
        (R < ‖b 1‖ →
          (∀ a ∈ A, ∃ z : ℤ, (a : E) = (z : ℝ) • b 0) ∧
          (A.card : ℝ) ≤ 1 + 2 * R / ‖b 0‖) := by
  obtain ⟨b, hbL, hfirst, hsecond⟩ := exists_successive_plane_basis L hdim
  refine ⟨b, hbL, norm_pos_iff.mpr (b.ne_zero 0),
    hfirst (b 1) (hbL 1) (b.ne_zero 1), ?_⟩
  intro A R hR hA
  exact plane_lattice_count L b hbL hfirst hsecond A R hR hA

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma isSuccessive_of_plane_minima
    (L : Submodule ℤ E) (b : Module.Basis (Fin 2) ℝ E)
    (hbL : ∀ i, b i ∈ L)
    (hfirst : ∀ u ∈ L, u ≠ 0 → ‖b 0‖ ≤ ‖u‖)
    (hsecond : ∀ u ∈ L, u ∉ Submodule.span ℝ {b 0} → ‖b 1‖ ≤ ‖u‖) :
    SuccessiveVectors.IsSuccessive L b := by
  refine ⟨hbL, b.linearIndependent, ?_⟩
  intro i u hu hout
  fin_cases i
  · apply hfirst u hu
    simpa [SuccessiveVectors.earlier] using hout
  · apply hsecond u hu
    simpa [SuccessiveVectors.earlier] using hout

theorem plane_covolume_bounds
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis (Fin 2) ℝ E) (hbL : ∀ i, b i ∈ L)
    (hfirst : ∀ u ∈ L, u ≠ 0 → ‖b 0‖ ≤ ‖u‖)
    (hsecond : ∀ u ∈ L, u ∉ Submodule.span ℝ {b 0} → ‖b 1‖ ≤ ‖u‖) :
    ZLattice.covolume L ≤ ‖b 0‖ * ‖b 1‖ ∧
      ‖b 0‖ * ‖b 1‖ ≤ 2 * ZLattice.covolume L ∧
      ((Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ≤ 2 := by
  have hs := isSuccessive_of_plane_minima L b hbL hfirst hsecond
  have h := SuccessiveEstimates.successive_basis_estimates (by decide : 0 < 2)
    L b hbL hs.minimal
  simpa only [Fin.prod_univ_two, Nat.cast_ofNat, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    using h

theorem exists_plane_lattice_estimates
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hdim : Module.finrank ℝ E = 2) :
    ∃ b : Module.Basis (Fin 2) ℝ E,
      SuccessiveVectors.IsSuccessive L b ∧
      ZLattice.covolume L ≤ ‖b 0‖ * ‖b 1‖ ∧
      ‖b 0‖ * ‖b 1‖ ≤ 2 * ZLattice.covolume L ∧
      ∀ (A : Finset L) (R : ℝ), 0 ≤ R →
        (∀ a ∈ A, ‖(a : E)‖ ≤ R) →
        (‖b 1‖ ≤ R →
          (A.card : ℝ) ≤ 9 * Real.pi * R ^ 2 / ZLattice.covolume L) ∧
        (R < ‖b 1‖ →
          (∀ a ∈ A, ∃ z : ℤ, (a : E) = (z : ℝ) • b 0) ∧
          (A.card : ℝ) ≤ 1 + 2 * R / ‖b 0‖) := by
  obtain ⟨b, hbL, hfirst, hsecond⟩ := exists_successive_plane_basis L hdim
  have hb := isSuccessive_of_plane_minima L b hbL hfirst hsecond
  obtain ⟨hlower, hupper, _⟩ := plane_covolume_bounds L b hbL hfirst hsecond
  refine ⟨b, hb, hlower, hupper, ?_⟩
  intro A R hR hA
  exact plane_lattice_count L b hbL hfirst hsecond A R hR hA

end Problem355.PlaneCount

end

end OAI
