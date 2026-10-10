import OAI.NumberTheory.DirichletL.Descent.Dyadic

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

section FiniteGrid
variable {M H C A : Type*} [DecidableEq M] [DecidableEq H] [DecidableEq C] [AddCommMonoid A]

def gridCommonSupport (T : Finset ((M × H) × C)) (m : M) : Finset C :=
  (T.filter fun u => u.1.1 = m).image Prod.snd

theorem finite_triple_support_reindex (T : Finset ((M × H) × C))
    (f : (M × H) × C → A) :
    (∑ u ∈ T, f u) = ∑ p ∈ T.image Prod.fst,
      ∑ c ∈ gridCommonSupport T p.1, if (p, c) ∈ T then f (p, c) else 0 := by
  have hp := Finset.sum_fiberwise_of_maps_to
    (s := T) (t := T.image Prod.fst) (g := Prod.fst)
    (fun u hu => Finset.mem_image.mpr ⟨u, hu, rfl⟩) f
  rw [← hp]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun u _ => u.2)
  · intro u hu
    obtain ⟨huT, hup⟩ := Finset.mem_filter.mp hu
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨huT, congrArg Prod.fst hup⟩, rfl⟩
    · simpa only [← hup, Prod.eta] using huT
  · intro u hu v hv he
    apply Prod.ext
    · exact (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm
    · exact he
  · intro c hc
    have hpc := (Finset.mem_filter.mp hc).2
    exact ⟨(p, c), Finset.mem_filter.mpr ⟨hpc, rfl⟩, rfl⟩
  · intro u hu
    have hup := (Finset.mem_filter.mp hu).2
    simp only [← hup, Prod.eta]

end FiniteGrid

def HybridColumnData.gridIndex (d : HybridColumnData) :
    (Ideal Eis × Ideal Eis) × Ideal Eis := ((d.residualN, d.residualB), d.common)

theorem HybridColumnData.gridIndex_injective_on_square (t : Ideal Eis) :
    Set.InjOn HybridColumnData.gridIndex {d | d.square = t} := by
  intro d hd e he hg
  have hm : d.residualN = e.residualN := congrArg (fun u => u.1.1) hg
  have hh : d.residualB = e.residualB := congrArg (fun u => u.1.2) hg
  have hc : d.common = e.common := congrArg Prod.snd hg
  have ht : d.square = e.square := hd.trans he.symm
  cases d
  cases e
  cases hc
  cases hm
  cases hh
  cases ht
  rfl

def hybridGridSupport (D : Finset HybridColumnData) :
    Finset ((Ideal Eis × Ideal Eis) × Ideal Eis) := D.image HybridColumnData.gridIndex

theorem hybrid_grid_reindex (D : Finset HybridColumnData) (t : Ideal Eis)
    (hD : ∀ d ∈ D, d.square = t) (f : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) :
    (∑ d ∈ D, f d.common d.residualN d.residualB) =
      ∑ p ∈ (hybridGridSupport D).image Prod.fst,
        ∑ c ∈ gridCommonSupport (hybridGridSupport D) p.1,
          if (p, c) ∈ hybridGridSupport D then f c p.1 p.2 else 0 := by
  have he : (∑ d ∈ D, f d.common d.residualN d.residualB) =
      ∑ u ∈ hybridGridSupport D, f u.2 u.1.1 u.1.2 := by
    symm
    apply Finset.sum_image
    intro d hd e he hg
    exact HybridColumnData.gridIndex_injective_on_square t (hD d hd) (hD e he) hg
  rw [he]
  exact finite_triple_support_reindex (hybridGridSupport D) _

theorem gridCommonSupport_origin (D : Finset HybridColumnData) (m c : Ideal Eis)
    (hc : c ∈ gridCommonSupport (hybridGridSupport D) m) :
    ∃ d ∈ D, d.residualN = m ∧ d.common = c := by
  obtain ⟨u, hu, huc⟩ := Finset.mem_image.mp hc
  obtain ⟨huT, hum⟩ := Finset.mem_filter.mp hu
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp huT
  exact ⟨d, hd, hum, huc⟩

end
end SevenEighths.InverseMoment

end OAI
