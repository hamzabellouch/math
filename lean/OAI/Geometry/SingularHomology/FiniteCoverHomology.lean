import OAI.Dynamics.EntropyCounterexample.CoordinateGoodCover
import OAI.Geometry.SingularHomology.SingularSmallChains
import OAI.Geometry.SingularHomology.SingularCoverChains
import OAI.Geometry.SingularHomology.HomologyEmpty
import OAI.Geometry.SingularHomology.FiniteGoodCoverHomology
import OAI.Dynamics.EntropyCounterexample.SpectralRadius
import OAI.Dynamics.EntropyCounterexample.FiniteSpectrumBound

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Problem340.FiniteCoverHomology

variable {ι X : Type} [TopologicalSpace X]

theorem goodCover_intersection_subsingleton
    (G : CoordinateGoodCover.GoodCover ι X) (s : Finset ι) (hs : s.Nonempty)
    (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (RealSingularHomology n ↥(⋂ i ∈ s, G.carrier i)) := by
  classical
  by_cases hne : (⋂ i ∈ s, G.carrier i).Nonempty
  · have := G.contractible s hs hne
    exact realSingularHomology_subsingleton_of_contractible n hn _
  · have : IsEmpty ↥(⋂ i ∈ s, G.carrier i) := by
      exact ⟨fun x => hne ⟨x.val, x.property⟩⟩
    exact realSingularHomology_subsingleton_of_totallyDisconnected n hn _

theorem finiteDimensional_inSubset_homology (s : Set X) (n : ℕ)
    [FiniteDimensional ℝ (RealSingularHomology n s)] :
    FiniteDimensional ℝ ((SingularSmallChains.inSubset s : SSet).homology
      (ModuleCat.of ℝ ℝ) n : ModuleCat ℝ) :=
  Module.Finite.equiv (SingularSmallChains.subspaceHomologyIso s n).toLinearEquiv

theorem isZero_inSubset_homology (s : Set X) (n : ℕ)
    [Subsingleton (RealSingularHomology n s)] :
    IsZero ((SingularSmallChains.inSubset s : SSet).homology
      (ModuleCat.of ℝ ℝ) n) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact (SingularSmallChains.subspaceHomologyIso s n).toLinearEquiv.symm.injective.subsingleton

theorem goodCover_intersection_inSubset_isZero
    (G : CoordinateGoodCover.GoodCover ι X) (s : Finset ι) (hs : s.Nonempty)
    (n : ℕ) (hn : n ≠ 0) :
    IsZero ((SingularSmallChains.inSubset (⋂ i ∈ s, G.carrier i) : SSet).homology
      (ModuleCat.of ℝ ℝ) n) := by
  have := goodCover_intersection_subsingleton G s hs n hn
  exact isZero_inSubset_homology _ n

theorem finiteHomology_goodCover_intersection
    (G : CoordinateGoodCover.GoodCover ι X) (s : Finset ι) (hs : s.Nonempty) :
    FiniteGoodCover.FiniteHomology
      ((SingularSmallChains.inSubset (⋂ i ∈ s, G.carrier i) : SSet).chainComplex
        (ModuleCat.of ℝ ℝ)) := by
  classical
  have hbase : IsEmpty ↥(⋂ i ∈ s, G.carrier i) ∨
      ContractibleSpace ↥(⋂ i ∈ s, G.carrier i) := by
    by_cases hne : (⋂ i ∈ s, G.carrier i).Nonempty
    · exact Or.inr (G.contractible s hs hne)
    · exact Or.inl ⟨fun x => hne ⟨x.val, x.property⟩⟩
  have h := realSingularHomology_finiteType_of_empty_or_contractible _ hbase
  constructor
  · intro n
    have := h.1 n
    exact finiteDimensional_inSubset_homology _ n
  · refine ⟨1, fun n hn => ?_⟩
    exact (h.2 n hn).of_iso
      (SingularSmallChains.subspaceHomologyIso (⋂ i ∈ s, G.carrier i) n).symm

theorem finiteHomology_subcomplex_bot (K : SSet.{0}) :
    FiniteGoodCover.FiniteHomology
      (((⊥ : K.Subcomplex) : SSet).chainComplex (ModuleCat.of ℝ ℝ)) := by
  have : ((⊥ : K.Subcomplex) : SSet).Finite :=
    SSet.finite_of_iso ((initialIsInitial (C := SSet)).uniqueUpToIso
      SSet.Subcomplex.isInitialBot)
  exact FiniteGoodCover.finiteHomology_of_finite_simplicial _

theorem finiteHomology_subcomplex_union {K : SSet.{0}} (A B : K.Subcomplex)
    (hA : FiniteGoodCover.FiniteHomology ((A : SSet).chainComplex (ModuleCat.of ℝ ℝ)))
    (hB : FiniteGoodCover.FiniteHomology ((B : SSet).chainComplex (ModuleCat.of ℝ ℝ)))
    (hAB : FiniteGoodCover.FiniteHomology
      (((A ⊓ B : K.Subcomplex) : SSet).chainComplex (ModuleCat.of ℝ ℝ))) :
    FiniteGoodCover.FiniteHomology
      (((A ⊔ B : K.Subcomplex) : SSet).chainComplex (ModuleCat.of ℝ ℝ)) := by
  exact FiniteGoodCover.finiteHomology_of_shortExact
    (SingularCover.unionShortComplex A B)
    (SingularCover.unionShortComplex_shortExact A B) hAB
    (FiniteGoodCover.finiteHomology_biprod hA hB)

theorem finiteHomology_subcomplex_finset_sup {K : SSet.{0}} (s : Finset ι)
    (A : ι → K.Subcomplex)
    (hinter : ∀ t : Finset ι, t ⊆ s → t.Nonempty →
      FiniteGoodCover.FiniteHomology (((t.inf A : K.Subcomplex) : SSet).chainComplex
        (ModuleCat.of ℝ ℝ))) :
    FiniteGoodCover.FiniteHomology (((s.sup A : K.Subcomplex) : SSet).chainComplex
      (ModuleCat.of ℝ ℝ)) := by
  let : DistribLattice K.Subcomplex := DistribLattice.ofInfSupLe (by
    intro B D E n σ h
    rcases h with ⟨hB, hD | hE⟩
    · exact Or.inl ⟨hB, hD⟩
    · exact Or.inr ⟨hB, hE⟩)
  refine FiniteGoodCover.property_sup_of_inf (L := K.Subcomplex)
    (fun B : K.Subcomplex => FiniteGoodCover.FiniteHomology
      ((B : SSet).chainComplex (ModuleCat.of ℝ ℝ))) ?_ ?_ s A hinter
  · exact finiteHomology_subcomplex_bot K
  · intro B D hB hD hBD
    exact finiteHomology_subcomplex_union B D hB hD hBD

private theorem finset_inf_inSubset (s : Finset ι) (U : ι → Set X) :
    s.inf (fun i => SingularSmallChains.inSubset (U i)) =
      SingularSmallChains.inSubset (⋂ i ∈ s, U i) := by
  ext n σ
  simp only [Finset.inf_eq_iInf, Subfunctor.iInf_obj,
    Set.mem_iInter, SingularSmallChains.inSubset]
  aesop

theorem finiteHomology_goodCover_small [Finite ι]
    (G : CoordinateGoodCover.GoodCover ι X) :
    FiniteGoodCover.FiniteHomology (SingularSmallChains.chains G.carrier) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have h := finiteHomology_subcomplex_finset_sup Finset.univ
    (fun i => SingularSmallChains.inSubset (G.carrier i)) (by
      intro t ht hne
      rw [finset_inf_inSubset]
      exact finiteHomology_goodCover_intersection G t hne)
  have heq : Finset.univ.sup (fun i => SingularSmallChains.inSubset (G.carrier i)) =
      SingularSmallChains.small G.carrier := by
    simp only [Finset.sup_eq_iSup, Finset.mem_univ, iSup_pos, SingularSmallChains.small]
  rw [heq] at h
  exact h

theorem finiteHomology_of_goodCover [Finite ι]
    (G : CoordinateGoodCover.GoodCover ι X)
    [QuasiIso (SingularSmallChains.inclusion G.carrier)] :
    FiniteGoodCover.FiniteHomology (realSingularChainComplex X) :=
  FiniteGoodCover.finiteHomology_of_quasiIso (SingularSmallChains.inclusion G.carrier)
    (finiteHomology_goodCover_small G)

theorem finiteDimensional_of_goodCover [Finite ι]
    (G : CoordinateGoodCover.GoodCover ι X)
    [QuasiIso (SingularSmallChains.inclusion G.carrier)] (n : ℕ) :
    FiniteDimensional ℝ (RealSingularHomology n X) :=
  (finiteHomology_of_goodCover G).1 n

theorem bddAbove_homologyEigenvalueRadii_of_goodCover [Finite ι]
    (G : CoordinateGoodCover.GoodCover ι X)
    [QuasiIso (SingularSmallChains.inclusion G.carrier)]
    (f : X → X) (hf : Continuous f) :
    BddAbove (homologyEigenvalueRadii f hf) := by
  let (n : ℕ) := finiteDimensional_of_goodCover G n
  obtain ⟨N, hN⟩ := (finiteHomology_of_goodCover G).2
  exact bddAbove_homologyEigenvalueRadii_of_finiteDimensional f hf N
    (fun n hn => ModuleCat.isZero_iff_subsingleton.mp (hN n hn.le))

theorem counterexampleManifold_finiteHomology (q : ℕ)
    [QuasiIso (SingularSmallChains.inclusion
      (CoordinateGoodCover.counterexampleGoodCover q).carrier)] :
    FiniteGoodCover.FiniteHomology (realSingularChainComplex (CounterexampleManifold q)) :=
  finiteHomology_of_goodCover (CoordinateGoodCover.counterexampleGoodCover q)

end Problem340.FiniteCoverHomology

end

end OAI
