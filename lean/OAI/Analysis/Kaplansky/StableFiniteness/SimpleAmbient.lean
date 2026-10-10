import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Ultrapower.Construction
import OAI.Analysis.Kaplansky.Ultrapower.Unitary
import OAI.Analysis.Kaplansky.Ultrapower.DenseUnits
import OAI.Analysis.Kaplansky.Ultrapower.MatrixDenseUnits
import OAI.Analysis.Kaplansky.Quotient.MaximalClosedIdeal
import OAI.Analysis.Kaplansky.StableFiniteness.TraceFree

namespace OAI

noncomputable section

namespace KaplanskyConsequences

open Filter Topology
open Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

universe u

lemma simple_stablyFinite_quotient {A : Type u} [CStarAlgebra A] [Nontrivial A]
    (V : QuasiValue A) (ht : IsEmpty (TracialState A)) :
    ∃ (M : Type u) (inst : CStarAlgebra M),
      letI := inst
      Nontrivial M ∧ CStarSimple M ∧ StablyFinite M ∧ IsEmpty (TracialState M) := by
  let u : Ultrafilter ℕ := Ultrafilter.of atTop
  have hu : (u : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  let B := V.UltraQuotient u
  let : Nontrivial B := (V.ultra u).faithfulQuotient_nontrivial
  have hB : DenseUnits B := denseUnits_of_unitary_polar (V.ultra_unitary_polar u hu)
  obtain ⟨I,hI,hmax⟩ := maximal_closedStarIdeal_exists (A:=B)
  let : Nontrivial I.Quotient := I.quotient_nontrivial hI
  have hd := hB.map I.mkStarAlgHom I.mk_surjective
  have hmap : A →⋆ₐ[ℂ] I.Quotient :=
    I.mkStarAlgHom.comp ((V.ultraHom u).comp (QuasiValue.constHom (A:=A) (ι:=ℕ)))
  exact ⟨I.Quotient,inferInstance,inferInstance,I.quotient_simple hmax,hd.stablyFinite,
    no_tracialState_of_map hmap ht⟩

theorem simple_stablyFinite_traceless_exists :
    ∃ (M : Type) (inst : CStarAlgebra M),
      letI := inst
      Nontrivial M ∧ CStarSimple M ∧ StablyFinite M ∧ IsEmpty (TracialState M) := by
  let d : CuntzDimensionState ActualAlgebra := Classical.choice
    (cuntzDimensionState_nonempty fun k hk => actualAlgebra_matrix_not_properlyInfinite hk)
  let := actualAlgebra_nontrivial_separable.1
  exact simple_stablyFinite_quotient (QuasiValue.ofDimensionState d) actualAlgebra_no_tracialState


end KaplanskyConsequences

end

end OAI
