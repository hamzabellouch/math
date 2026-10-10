import OAI.AlgebraicGeometry.CharacterVarieties.Frames.Graded
import OAI.AlgebraicGeometry.CharacterVarieties.Cutting.AtomicGallery

namespace OAI

namespace IntegralCharacterVarieties.NamedBandGrades
open scoped Classical
open TwoFlagBand OccurrenceIncidence.VertexTable
variable {K V α β : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {n m : ℕ}

/-- A framed flag pair determines a finite atom-conservative band, with frames at every split, swap
and merge vertex and the original named endpoint quotient projections. -/
theorem actual_named_atomic_band
    (a : α → Fin n) (b : β → Fin m)
    (f : (α → K) ≃ₗ[K] V) (h : (β → K) ≃ₗ[K] V) :
    ∃ (d : RankShape n m (Module.finrank K V)) (e : (Atoms d → K) ≃ₗ[K] V)
      (row : (k : ℕ) → ({i // rowGrade d i=k} → K) ≃ₗ[K] ({i // (a i).val=k} → K))
      (col : (k : ℕ) → ({i // colGrade d i=k} → K) ≃ₗ[K] ({i // (b i).val=k} → K)),
      (∀ k,framedPrefix (rowGrade d) e k=framedPrefix (fun i => (a i).val) f k) ∧
      (∀ k,framedPrefix (colGrade d) e k=framedPrefix (fun i => (b i).val) h k) ∧
      (∀ k v,v∈framedPrefix (rowGrade d) e (k+1) →
        row k (framedGrade (rowGrade d) e k v)=framedGrade (fun i => (a i).val) f k v) ∧
      (∀ k v,v∈framedPrefix (colGrade d) e (k+1) →
        col k (framedGrade (colGrade d) e k v)=framedGrade (fun i => (b i).val) h k v) ∧
      d.atomicBand.crossings.Nodup ∧
      (∀ v,∃ s : (d.atomicBand.kind v).SecondaryNames (Secondary n m),
        d.atomicBand.decoration v=(d.atomicBand.kind v).freshDecoration s) ∧
      (∀ v,(d.atomicBand.decoration v).AtomConservative d.facetAtoms) ∧
      (∀ v z,(d.vertexAtoms v).rank z=
        freshRank (Module.finrank K V) d.secondaryRank ((d.atomicBand.decoration v).color z)) ∧
      (∀ v,(LocalRanks.comparison (d.atomicBand.kind v) (d.vertexAtoms v).localRanks
        ((d.vertexAtoms v).frame (R:=K))).Holds) := by
  obtain ⟨d,e,row,col,hr,hc,hnr,hnc⟩ := actual_named_band_grades a b f h
  exact ⟨d,e,row,col,hr,hc,hnr,hnc,d.atomicBand_nodup,d.atomicBand_fresh,
    d.atomicBand_atoms,d.vertexAtoms_rank,d.atomicBand_comparison⟩

end IntegralCharacterVarieties.NamedBandGrades

end OAI
