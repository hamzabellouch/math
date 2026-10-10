import OAI.MeasureTheory.Falconer.Radial.TubeCoverChoice
import OAI.MeasureTheory.Falconer.Geometry.TubeAnchorNet

namespace OAI

/-! # Enumerating the admissible finite lists from a bounded anchor net -/

namespace Falconer
open Set
variable {X : Type*}

theorem bounded_finset_enumeration (G : Finset X) (N : ℕ) :
    ∃ C : ℕ → Finset X, (∀ n, C n ⊆ G ∧ (C n).card ≤ N) ∧
      ∀ J : Finset X, J ⊆ G → J.card ≤ N → ∃ n, C n = J := by
  classical
  let S := G.powerset.filter (fun J => J.card ≤ N)
  have hs : (∅ : Finset X) ∈ S := by simp [S]
  have : Nonempty {J : Finset X // J ∈ S} := ⟨⟨∅,hs⟩⟩
  obtain ⟨f,hf⟩ := exists_surjective_nat {J : Finset X // J ∈ S}
  refine ⟨fun n => (f n).val,?_,?_⟩
  · intro n
    have hp := Finset.mem_filter.mp (f n).property
    exact ⟨Finset.mem_powerset.mp hp.1,hp.2⟩
  · intro J hJG hJN
    have hJS : J ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hJG,hJN⟩
    obtain ⟨n,hn⟩ := hf ⟨J,hJS⟩
    exact ⟨n,congrArg Subtype.val hn⟩

end Falconer

end OAI
