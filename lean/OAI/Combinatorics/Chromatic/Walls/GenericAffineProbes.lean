import Mathlib
import OAI.Combinatorics.Chromatic.Walls.MutatedPathIndependent

namespace OAI

section
namespace ElementaryPositivity.FiniteRayGeometry
noncomputable section
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
lemma generic_for_two_directions_with_probes (T : ℕ → Finset E) (a b k : Module.Dual ℝ E)
    (P : Finset (ℝ×E)) (v:Module.Dual ℝ E) :
    ∃h : Module.Dual ℝ E,(∀N,GenericOffset (T N) 0 a h) ∧
      (∀N,GenericOffset (T N) 0 b h) ∧
      ∀s∈P,(0<(k+s.1 • v) s.2 → 0<(h+s.1 • v) s.2) ∧
        ((k+s.1 • v) s.2<0 → (h+s.1 • v) s.2<0) := by
  classical
  let W : Set E:=⋃N,↑(forbidden (T N) 0 a∪forbidden (T N) 0 b)
  have hc : W.Countable:=Set.countable_iUnion (fun N=>(forbidden (T N) 0 a∪forbidden (T N) 0 b).countable_toSet)
  have hp : ∀w∈W,w∉Submodule.span ℝ {(0:E)}:=by
    intro w hw
    obtain ⟨N,hN⟩:=Set.mem_iUnion.mp hw
    rcases Finset.mem_union.mp hN with hh|hh
    · exact (Finset.mem_filter.mp hh).2
    · exact (Finset.mem_filter.mp hh).2
  obtain ⟨h,h0,havoid,hprobe⟩:=countable_avoid_with_probes W hc 0 hp
    P v k (map_zero k)
  have hGa : ∀N,GenericOffset (T N) 0 a h:=by
    intro N
    refine ⟨h0,?_,?_⟩
    · intro s hs hn
      exact havoid s (Set.mem_iUnion.mpr ⟨N,Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hs,hn⟩)⟩)
    · intro s hs t ht hn
      exact havoid _ (Set.mem_iUnion.mpr ⟨N,Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨(s,t),Finset.mem_product.mpr ⟨hs,ht⟩,rfl⟩),hn⟩)⟩)
  have hGb : ∀N,GenericOffset (T N) 0 b h:=by
    intro N
    refine ⟨h0,?_,?_⟩
    · intro s hs hn
      exact havoid s (Set.mem_iUnion.mpr ⟨N,Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hs,hn⟩)⟩)
    · intro s hs t ht hn
      exact havoid _ (Set.mem_iUnion.mpr ⟨N,Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨(s,t),Finset.mem_product.mpr ⟨hs,ht⟩,rfl⟩),hn⟩)⟩)
  exact ⟨h,hGa,hGb,hprobe⟩
end
end ElementaryPositivity.FiniteRayGeometry
namespace ElementaryPositivity.QuantumTorus
open FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I]
variable (C:(I → ℤ) →+ M) (e:M →+ E)
lemma generic_region_path_via_probes (a b k : Module.Dual ℝ E) (P : Finset (ℝ×E)) (v:Module.Dual ℝ E)
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (U : Set (Module.Dual ℝ E))
    (hU : ∀h : Module.Dual ℝ E,
      (∀x∈P,(0<(k+x.1 • v) x.2 → 0<(h+x.1 • v) x.2) ∧
        ((k+x.1 • v) x.2<0 → (h+x.1 • v) x.2<0)) →
      (∀t:ℝ,0≤t → t≤1 → (1-t) • a+t • h∈U) ∧
      (∀t:ℝ,0≤t → t≤1 → (1-t) • h+t • b∈U)) :
    ∃p : GenericLinePath C e a b,p.InRegion C e U := by
  obtain ⟨h,Ha,Hb,HP⟩:=generic_for_two_directions_with_probes (realRootsThrough e C) a b k P v
  have HH : RegularCovector C e h:=by
    intro N s hs hn
    exact (Ha N).avoid s hs (by simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using hn)
  let s:=segmentBetween C e a h HA HH (fun N=>(Ha N).join (HA N))
  let t:=segmentBetween C e h b HH HB (fun N=>(Hb N).join_reverse (HB N))
  let p:=(GenericLinePath.single C e s).castEnds C e
    (segmentBetween_start C e a h HA HH _) (segmentBetween_finish C e a h HA HH _)
  let q:=(GenericLinePath.single C e t).castEnds C e
    (segmentBetween_start C e h b HH HB _) (segmentBetween_finish C e h b HH HB _)
  have hp : p.InRegion C e U :=
    (segmentBetween_inRegion C e a h HA HH _ (hU h HP).1).castEnds C e _ _
  have hq : q.InRegion C e U :=
    (segmentBetween_inRegion C e h b HH HB _ (hU h HP).2).castEnds C e _ _
  exact ⟨p.trans C e q,hp.trans C e hq⟩
end
end ElementaryPositivity.QuantumTorus

end

end OAI
