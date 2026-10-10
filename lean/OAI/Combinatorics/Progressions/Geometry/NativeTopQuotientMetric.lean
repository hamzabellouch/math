import OAI.Combinatorics.Progressions.Linear.NativeRankQuotientOrbit

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis (Fin d) ℚ L) (w : Fin d → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
  (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
  (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ F.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ F.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ F.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (L ⧸ F.layerIdeal (s + 1)))]

local notation "V" => F.ofAdaptedBasis b w hF Γ N hN hin hout
local notation "Q" => F.topQuotientModel b w hF Γ N hN hin hout

theorem topQuotientModel_dist_le {p : ℝ} (hp : 0 ≤ p) (hgeom : (V).GeometryComplexityLE p)
    (u v : F.realification.Group) :
    letI := (V).metricSpace
    letI := (Q).metricSpace
    dist (QuotientGroup.mk (F.realQuotientStepHom (F.layerIdeal (s + 1)) le_rfl u) : (Q).Space)
      (QuotientGroup.mk (F.realQuotientStepHom (F.layerIdeal (s + 1)) le_rfl v)) ≤
        Real.exp ((p + 2) ^ 2) * dist (QuotientGroup.mk u : (V).Space) (QuotientGroup.mk v) := by
  let := (V).metricSpace
  let := (Q).metricSpace
  let := realificationQuotientMetricSpace b Γ N hN hout
  let := realificationQuotientMetricSpace (Q).basis (Q).lattice N hN (Q).outer_grid
  have hQ := F.topQuotientModel_geometry b w hF Γ N hN hin hout hp hgeom
  have hmap : Γ ≤ (Q).lattice.comap (mapOfSteps (lieQuotientMap (F.layerIdeal (s + 1)))) := by
    intro g hg
    exact ⟨g, hg, rfl⟩
  have hheight : ∀ i j, RationalHeightLE
      ((Q).basis.repr (lieQuotientMap (F.layerIdeal (s + 1)) (b j)) i) 1 := by
    intro i j
    exact quotientFinBasis_projection_height b (F.layerIdeal (s + 1))
      {i | s + 1 ≤ w i} (hF (s + 1)) j i
  obtain ⟨K, _, hK, hLip⟩ := exists_realificationMap_quotient_lipschitz_exp_bound
    b (Q).basis (lieQuotientMap (F.layerIdeal (s + 1))) Γ (Q).lattice hmap
    N N hN hN hout (Q).outer_grid 1 hp
    (by simpa only [Fintype.card_fin] using hgeom.1)
    (by simpa only [Fintype.card_fin] using hQ.1)
    (by simpa only [Nat.cast_one] using Real.one_le_exp hp) hheight
  have hd := hLip.dist_le_mul (QuotientGroup.mk u) (QuotientGroup.mk v)
  change dist (QuotientGroup.mk (F.realQuotientStepHom (F.layerIdeal (s + 1)) le_rfl u) : (Q).Space)
    (QuotientGroup.mk (F.realQuotientStepHom (F.layerIdeal (s + 1)) le_rfl v)) ≤
      (K : ℝ) * dist (QuotientGroup.mk u : (V).Space) (QuotientGroup.mk v) at hd
  exact hd.trans (mul_le_mul_of_nonneg_right hK dist_nonneg)

theorem topQuotientModel_orbit_dist_le {σ : Type*} {ω : σ → ℕ}
    {p : ℝ} (hp : 0 ≤ p) (hgeom : (V).GeometryComplexityLE p)
    (g : F.realification.PolynomialOrbit ω) (x y : σ → ℤ) :
    letI := (V).metricSpace
    letI := (Q).metricSpace
    dist (QuotientGroup.mk (F.quotientTop.realification.polynomialOrbitEval ω x
        (F.realQuotientPolynomialOrbit (F.layerIdeal (s + 1)) le_rfl g)) : (Q).Space)
      (QuotientGroup.mk (F.quotientTop.realification.polynomialOrbitEval ω y
        (F.realQuotientPolynomialOrbit (F.layerIdeal (s + 1)) le_rfl g))) ≤
      Real.exp ((p + 2) ^ 2) *
        dist (QuotientGroup.mk (F.realification.polynomialOrbitEval ω x g) : (V).Space)
          (QuotientGroup.mk (F.realification.polynomialOrbitEval ω y g)) := by
  let := (V).metricSpace
  let := (Q).metricSpace
  have heval (z : σ → ℤ) :
      (QuotientGroup.mk (F.quotientTop.realification.polynomialOrbitEval ω z
        (F.realQuotientPolynomialOrbit (F.layerIdeal (s + 1)) le_rfl g)) : (Q).Space) =
      QuotientGroup.mk (F.realQuotientStepHom (F.layerIdeal (s + 1)) le_rfl
        (F.realification.polynomialOrbitEval ω z g)) :=
    congrArg (fun a : (Q).RealGroup => (QuotientGroup.mk a : (Q).Space))
      (F.realQuotientPolynomialOrbit_eval (F.layerIdeal (s + 1)) (t := s) le_rfl g z)
  exact (congrArg₂ (fun a b : (Q).Space => dist a b) (heval x) (heval y)).trans_le
    (F.topQuotientModel_dist_le b w hF Γ N hN hin hout hp hgeom _ _)

end Erdos3.NilpotentLieFiltration

end

end OAI
