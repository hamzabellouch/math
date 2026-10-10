import OAI.Probability.InvariantIsing.Cavity.CavityGroupedGram
import OAI.Probability.InvariantIsing.Cavity.CavityBaseGroups

namespace OAI

/-! The canonical spectral labels form the actual finite partition with
exact prescribed block dimensions. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma cavitySpectralGroup_pairwiseDisjoint {N m : ℕ} (g : Fin N → Fin m) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (cavitySpectralGroup g) := by
  intro a _ b _ hab
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hi' : g i=a := (Finset.mem_filter.mp hi).2
  have hj' : g i=b := (Finset.mem_filter.mp hj).2
  exact hab (hi'.symm.trans hj')

lemma cavitySpectralGroup_cover {N m : ℕ} (g : Fin N → Fin m) :
    Finset.univ.biUnion (cavitySpectralGroup g)=Finset.univ := by
  classical
  ext i
  simp [cavitySpectralGroup]

lemma cavity_group_dimension_card {N m : ℕ} (dims : Fin m → ℕ)
    (E : ((a : Fin m) × Fin (dims a)) ≃ Fin N) (a : Fin m) :
    (cavitySpectralGroup (fun i => (E.symm i).1) a).card=dims a := by
  have he := Fintype.card_congr (cavityGroupSetEquiv dims E a)
  simpa only [Fintype.card_fin, Fintype.card_coe] using he.symm

end InvariantIsing

end

end OAI
