import Mathlib
import OAI.Computability.VertexCover.Machines.ExpanderBound

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                   
section

namespace VertexCover.Machine
open UniqueGames.Foundations.PCP

theorem iterate_fixed {α : Type} (f : α → α) (a : α) (h : f a = a) (n : ℕ) :
    Iterate.run f n a = a := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Iterate.run,h] using ih

namespace ExpandMachine

def family {d : ℕ} (H : ExpanderTables.Table ((d*d)*(d*d)) d) (e : ℕ) : Input (d*d) :=
  ⟨ExpanderTables.vertexCount (d*d) e,ExpanderTables.family H e⟩

 theorem capped_family {d : ℕ} (H : ExpanderTables.Table ((d*d)*(d*d)) d)
    (fuel k e : ℕ) :
    Iterate.run (capped H) fuel (k,family H e) =
      (k,family H (PreprocessingLevels.levelLoop ((d*d)*(d*d)) k fuel e
        (ExpanderTables.vertexCount (d*d) e)).1) := by
  induction fuel generalizing e with
  | zero => rfl
  | succ fuel ih =>
    by_cases hh : k ≤ ExpanderTables.vertexCount (d*d) e
    · rw [PreprocessingLevels.levelLoop,ite_eq_left hh]
      exact iterate_fixed (capped H) _ (by simp [capped,family,hh]) _
    · rw [PreprocessingLevels.levelLoop,ite_eq_right hh]
      change Iterate.run (capped H) fuel (capped H (k,family H e)) = _
      have hc : capped H (k,family H e) = (k,family H (e+1)) := by
        dsimp only [capped,family]
        rw [ite_eq_right hh]
        rfl
      rw [hc,ih]
      rfl

 theorem growth_eq : ExpanderFamily.growth =
    (Expanders.baseDegree*Expanders.baseDegree)*(Expanders.baseDegree*Expanders.baseDegree) := by
  unfold ExpanderFamily.growth
  ring

def paddedFamily (H : PreprocessingRegularTables.BaseTable) (k : ℕ) :
    Input PreprocessingRegularTables.internalDegree :=
  family H (PreprocessingLevels.boundedLevel k)

 theorem paddedFamily_run (H : PreprocessingRegularTables.BaseTable) (k : ℕ) :
    Iterate.run (capped H) k (k,family H 0) = (k,paddedFamily H k) := by
  rw [capped_family]
  unfold paddedFamily PreprocessingLevels.boundedLevel PreprocessingLevels.searchResult
  rw [growth_eq]
  rfl

noncomputable def paddedFamilyPoly (H : PreprocessingRegularTables.BaseTable) :
    Poly natBits code (paddedFamily H) := by
  let Q := Expanders.baseDegree*Expanders.baseDegree
  let start := (Poly.identity natBits).pair
    ((Poly.identity natBits).pair (Poly.const natBits (code (q := Q)) (family H 0)))
  exact (((start.comp (cappedIteratePoly H)).comp (Poly.snd natBits code))).congr
    (fun k => congrArg Prod.snd (paddedFamily_run H k))

 theorem paddedFamily_vertices (H : PreprocessingRegularTables.BaseTable) (k : ℕ) :
    (paddedFamily H k).1 = PreprocessingLevels.paddedSize k :=
  PreprocessingLevels.table_vertexCount_eq_paddedSize k

noncomputable def paddedSizePoly : Poly natBits natBits PreprocessingLevels.paddedSize := by
  let H := Classical.choose ExpanderTables.exists_base_table
  exact ((paddedFamilyPoly H).comp verticesPoly).congr (paddedFamily_vertices H)

noncomputable def cloudPaddedPoly : Poly natBits natBits PreprocessingLevels.cloudPaddedSize :=
  (Poly.natZero.ite (Poly.const natBits natBits 0) paddedSizePoly).congr (fun k => by
    simp [PreprocessingLevels.cloudPaddedSize])

end ExpandMachine
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
