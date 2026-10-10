import OAI.Probability.BenjaminiSchramm.HarmonicHeightAscent

namespace OAI

noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma height_harmonic_flat_or_fall (hl : G.LocallyFinite) (f : V → ℝ)
    (hf : ∀ x, (∑ y ∈ (G.finite_neighbors hl x).toFinset, Real.exp (f y-f x)) =
      G.modularWalkDegree x) (x : V) :
    (∃ y, G.fullGraph.Adj x y ∧ f y < f x) ∨
      (∀ y, G.fullGraph.Adj x y → f y=f x) := by
  by_cases hd : ∃ y, G.fullGraph.Adj x y ∧ f y < f x
  · exact Or.inl hd
  right
  have hle (y : V) (hy : y ∈ (G.finite_neighbors hl x).toFinset) :
      1 ≤ Real.exp (f y-f x) := by
    apply Real.one_le_exp_iff.mpr
    exact sub_nonneg.mpr (le_of_not_gt
      (fun h => hd ⟨y,(G.finite_neighbors hl x).mem_toFinset.mp hy,h⟩))
  have hs : (∑ _y ∈ (G.finite_neighbors hl x).toFinset, (1 : ℝ)) =
      ∑ y ∈ (G.finite_neighbors hl x).toFinset, Real.exp (f y-f x) := by
    rw [hf,Finset.sum_const,nsmul_eq_mul,mul_one]
    simp only [modularWalkDegree,Set.ncard_eq_toFinset_card _ (G.finite_neighbors hl x)]
  intro y hxy
  have he := (Finset.sum_eq_sum_iff_of_le hle).mp hs y
    ((G.finite_neighbors hl x).mem_toFinset.mpr hxy)
  exact sub_eq_zero.mp (Real.exp_injective (by simpa only [Real.exp_zero] using he.symm))

theorem stationaryOrbitHeight_descent [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : Percolation.BenjaminiSchramm.orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular) (x : V) :
    ∃ y, ∃ w : G.fullGraph.Walk x y,
      (∀ v ∈ w.support, G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ 0) ∧
        G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y < 0 := by
  let f := G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x
  have hself : f x=0 := G.orbitAdjustedHeight_self _ x
  obtain ⟨y,hy⟩ := G.orbitAdjustedHeight_nonconstant hc hl _ (G.stationaryOrbitWeight_aut μ) hu x
  have hhar (v : V) : (∑ y ∈ (G.finite_neighbors hl v).toFinset, Real.exp (f y-f v)) =
      G.modularWalkDegree v := by
    have he (y : V) : f y-f v=G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v y := by
      dsimp [f]
      rw [G.orbitAdjustedHeight_change_base hc hl _ x v y,add_sub_cancel_left]
    simp_rw [he]
    exact G.stationaryOrbitHeight_harmonic hc hl hq μ hμ hstat v
  have hfall (v : V) : (∃ z, G.fullGraph.Adj v z ∧ -f v < -f z) ∨
      (∀ z, G.fullGraph.Adj v z → -f z= -f v) := by
    rcases G.height_harmonic_flat_or_fall hl f hhar v with ⟨z,hvz,hz⟩ | hflat
    · exact Or.inl ⟨z,hvz,by linarith⟩
    · exact Or.inr fun z hz => congrArg Neg.neg (hflat z hz)
  have hy' : f y ≠ f x := by simpa only [hself] using hy
  obtain ⟨z,w,hw,hz⟩ := G.harmonic_ascent_walk (fun v => -f v) hfall
    (hc x y).some (fun he => hy' (neg_injective he))
  refine ⟨z,w,?_,?_⟩
  · intro v hv
    have hh := hw v hv
    rw [hself] at hh
    change f v ≤ 0
    linarith
  · rw [hself] at hz
    change f z < 0
    linarith

end CriticalPercolation.BondGraph

end

end OAI
