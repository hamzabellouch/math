import OAI.Combinatorics.Crossing.ParameterNeighborhoods
import OAI.Combinatorics.Crossing.MarkedCurveDisks

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem finite_injective_curve_disk_isolation {E M : Type*}
    [Fintype E] [Fintype M] [DecidableEq M]
    (γ : E → unitInterval → Plane) (hc : ∀ e, Continuous (γ e))
    (hi : ∀ e, Function.Injective (γ e)) (mark : M → Plane) (hm : Function.Injective mark) :
    ∃ δ : E → ℝ, ∃ r : ℝ, (∀ e, 0 < δ e) ∧ 0 < r ∧
      (∀ k l, k ≠ l → Disjoint (closedRoundDisk (mark k) r) (closedRoundDisk (mark l) r)) ∧
      (∀ e k t, γ e t ∈ closedRoundDisk (mark k) r →
        ∃ u : unitInterval, γ e u=mark k ∧ t ∈ parameterNeighborhood u (δ e)) ∧
      (∀ e u v, γ e u ∈ Set.range mark → γ e v ∈ Set.range mark → u ≠ v →
        Disjoint (closure (parameterNeighborhood u (δ e)))
          (closure (parameterNeighborhood v (δ e)))) := by
  have hfinite (e : E) : ((γ e) ⁻¹' Set.range mark).Finite :=
    Set.Finite.preimage (hi e).injOn (Set.finite_range mark)
  have hex (e : E) : ∃ δ : ℝ, 0 < δ ∧
      ∀ u v, γ e u ∈ Set.range mark → γ e v ∈ Set.range mark → u ≠ v →
        Disjoint (closure (parameterNeighborhood u δ)) (closure (parameterNeighborhood v δ)) := by
    let S := (γ e) ⁻¹' Set.range mark
    let : Fintype S := (hfinite e).fintype
    let : DecidableEq S := Classical.decEq _
    obtain ⟨δ,hδ,_,hd⟩ := finite_parameter_neighborhoods (fun t : S => t.val) Subtype.val_injective
    refine ⟨δ,hδ,?_⟩
    intro u v hu hv huv
    exact hd ⟨u,hu⟩ ⟨v,hv⟩ (fun he => huv (congrArg Subtype.val he))
  choose δ hδ hseparate using hex
  let O : E → M → Set unitInterval := fun e k =>
    {t | ∃ u, γ e u=mark k ∧ t ∈ parameterNeighborhood u (δ e)}
  have hO (e : E) (k : M) : IsOpen (O e k) := by
    apply isOpen_iff_mem_nhds.mpr
    rintro t ⟨u,hu,ht⟩
    exact Filter.mem_of_superset ((parameterNeighborhood_open u (δ e)).mem_nhds ht)
      (fun s hs => ⟨u,hu,hs⟩)
  obtain ⟨r,hr,hdisks,hvisits⟩ := finite_curve_mark_isolation γ hc mark hm O hO (by
    intro e k t ht
    exact ⟨t,ht,by simpa [parameterNeighborhood] using hδ e⟩)
  exact ⟨δ,r,hδ,hr,hdisks,hvisits,hseparate⟩

end Zarankiewicz

end

end OAI
