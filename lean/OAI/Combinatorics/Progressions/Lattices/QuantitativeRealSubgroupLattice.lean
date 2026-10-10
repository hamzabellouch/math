import OAI.Combinatorics.Progressions.Estimates.RationalRealSubgroup

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem exists_realification_subgroup_basis_and_lattice
    {ι η L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
    (e : Basis ι ℚ L) (K : LieSubalgebra ℚ L) (v : η → K)
    (hspan : Submodule.span ℚ (Set.range v) = ⊤)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) {H l : ℕ} (hHpos : 1 ≤ H) (hlpos : 0 < l)
    (hv : ∀ i j, RationalHeightLE (e.repr (v i : L) j) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    ∃ b : Basis (Fin (finrank ℚ K)) ℚ K, ∃ N : ℕ,
      0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      (∀ i j, RationalHeightLE (e.repr (b i : L) j) H) ∧
      (∀ i j k, ((lieStructureConstants b i j k).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 11) ∧
        ((lieStructureConstants b i j k).den : ℝ) ≤ Real.exp ((p + 2) ^ 11)) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates b
        (Γ.comap (NilpotentLieBCHGroup.map
          (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) K.incl)) ∧
      bchSubgroupCoordinates b
        (Γ.comap (NilpotentLieBCHGroup.map
          (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) K.incl)) ⊆ denominatorGrid N ∧
      CompactSpace (NilpotentLieBCHGroup.realificationSubgroup (hnil := hnil) K ⧸
        (Γ.map NilpotentLieBCHGroup.realificationHom).comap
          (NilpotentLieBCHGroup.realificationSubgroup (hnil := hnil) K).subtype) := by
  obtain ⟨b, N, hN, hNb, hb, hbr, hin, hout⟩ :=
    exists_subalgebra_basis_and_grid e K v hspan Γ hHpos hlpos hv hc hinner houter hp hd hH hl
  exact ⟨b, N, hN, hNb, hb, hbr, hin, hout,
    NilpotentLieBCHGroup.compactSpace_realificationSubgroup_quotient K b Γ N hN hin hout⟩

end Erdos3

end

end OAI
