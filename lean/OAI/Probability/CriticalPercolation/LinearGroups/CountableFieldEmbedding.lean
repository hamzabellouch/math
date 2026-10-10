import Mathlib

namespace OAI

section
noncomputable section
open Set Function Cardinal
open scoped Classical

namespace CriticalPercolation.Arithmetic

lemma exists_algHom_of_countable {k K F : Type} [Field k] [Field K] [Field F]
    [Algebra k K] [Algebra k F] [Countable k] [Countable K] [IsAlgClosed F] [Uncountable F] :
    Nonempty (K →ₐ[k] F) := by
  obtain ⟨S,hS⟩ := exists_isTranscendenceBasis k K
  obtain ⟨T,hT⟩ := exists_isTranscendenceBasis k F
  have hcard : #F=#T := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'
    _ hT mk_le_aleph0 aleph0_lt_mk
  have hle : #S≤#T := by
    rw [←hcard]
    exact mk_le_aleph0.trans aleph0_lt_mk.le
  obtain ⟨e⟩ := (Cardinal.le_def S T).mp hle
  let y : S → F := fun s => (e s: F)
  have hy : AlgebraicIndependent k y := hT.1.comp e e.injective
  let A := IntermediateField.adjoin k (Set.range (Subtype.val : S → K))
  let φ : A →ₐ[k] F := (IsFractionRing.liftAlgHom
    (algebraicIndependent_iff_injective_aeval.mp hy)).comp hS.1.reprField
  let : Algebra A F := φ.toRingHom.toAlgebra
  let : IsScalarTower k A F := IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)
  let : Algebra.IsAlgebraic A K := hS.isAlgebraic_field
  exact ⟨(IsAlgClosed.lift (R:=A) (S:=K) (M:=F)).restrictScalars k⟩

lemma exists_extension_of_countable {k K F : Type} [Field k] [Field K] [Field F]
    [Algebra k K] [Countable k] [Countable K] [IsAlgClosed F] [Uncountable F]
    (f : k →+* F) : ∃ g : K →+* F, g.comp (algebraMap k K)=f := by
  let : Algebra k F := f.toAlgebra
  obtain ⟨g⟩ := exists_algHom_of_countable (k:=k) (K:=K) (F:=F)
  exact ⟨g.toRingHom,g.comp_algebraMap⟩

lemma uncountable_complete_normed_field (F : Type*) [NontriviallyNormedField F] [CompleteSpace F] :
    Uncountable F := by
  obtain ⟨f,_,_,hf⟩ := (PerfectSpace.univ_perfect (α:=F)).exists_nat_bool_injection Set.univ_nonempty
  let : Uncountable (ℕ → Bool) := Cardinal.aleph0_lt_mk_iff.mp (by
    simpa only [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.lift_id, Cardinal.two_power_aleph0]
      using Cardinal.aleph0_lt_continuum)
  exact hf.uncountable

end CriticalPercolation.Arithmetic
end
end

end OAI
