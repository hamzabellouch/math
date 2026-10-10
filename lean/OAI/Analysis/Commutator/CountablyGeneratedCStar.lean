import Mathlib
import OAI.Analysis.Commutator.CountableStrongTests
import OAI.Analysis.Commutator.DenseCommutes
import OAI.Analysis.Commutator.MatrixTowerGNS

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

namespace Kadison

lemma countable_submonoidClosure {A : Type*} [Monoid A] {s : Set A} (hs : s.Countable) :
    (Submonoid.closure s : Set A).Countable := by
  let := hs.to_subtype
  rw [Submonoid.closure_eq_mrange,MonoidHom.coe_mrange]
  exact Set.countable_range _

lemma separable_starAdjoin {A : Type*} [CStarAlgebra A] {s : Set A} (hs : s.Countable) :
    TopologicalSpace.IsSeparable (StarAlgebra.adjoin ℂ s : Set A) := by
  have hss : (s ∪ star s).Countable := hs.union (by simpa only [Set.image_star] using hs.image star)
  have hh := ((countable_submonoidClosure hss).isSeparable.span (R:=ℂ))
  have he : (StarAlgebra.adjoin ℂ s : Set A)=
      (Submodule.span ℂ (Submonoid.closure (s∪star s) : Set A) : Set A) :=
    congrArg (fun M : Submodule ℂ A => (M:Set A)) (StarAlgebra.adjoin_eq_span (R:=ℂ) s)
  rwa [he]

theorem exists_separable_cstar_bicommutant
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P : VonNeumannAlgebra H) :
    ∃ S : StarSubalgebra ℂ (H →L[ℂ] H),IsClosed (S:Set (H →L[ℂ] H)) ∧
      TopologicalSpace.SeparableSpace S ∧ S≤P.toStarSubalgebra ∧ NormalGNS.bicommutant S=P := by
  obtain ⟨test,ht,hd⟩ := exists_countable_strong_contraction_tests P
  let S := (StarAlgebra.adjoin ℂ (Set.range test)).topologicalClosure
  have hclosed : IsClosed (S:Set (H →L[ℂ] H)) := StarSubalgebra.isClosed_topologicalClosure _
  have hsep : TopologicalSpace.SeparableSpace S := by
    apply TopologicalSpace.IsSeparable.separableSpace
    exact (separable_starAdjoin (Set.countable_range test)).closure
  have hSP : S≤P.toStarSubalgebra := StarSubalgebra.topologicalClosure_minimal
    (StarAlgebra.adjoin_le (by rintro _ ⟨n,rfl⟩; exact (ht n).1)) (VonNeumannCStar.isClosed P)
  have htt (n : ℕ) : test n∈S := StarSubalgebra.le_topologicalClosure _
    (StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self n))
  refine ⟨S,hclosed,hsep,hSP,?_⟩
  apply SetLike.ext
  intro A
  rw [NormalGNS.mem_bicommutant]
  constructor
  · intro ha
    have hc := Set.centralizer_subset (Set.centralizer_subset hSP) ha
    change A∈Set.centralizer (Set.centralizer (P : Set (H →L[ℂ] H))) at hc
    change A∈(P : Set (H →L[ℂ] H))
    rwa [VonNeumannAlgebra.centralizer_centralizer] at hc
  · intro hA B hB
    exact (commutes_of_dense_contraction_tests P test hd B
      (fun n => hB _ (htt n)) A hA).eq.symm

end Kadison

end

end
end

end OAI
