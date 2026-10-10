import Mathlib
import OAI.Combinatorics.Chromatic.Walls.LineOldTransport

namespace OAI

section
namespace ElementaryPositivity.FiniteRayGeometry
open Module
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma wedge_ne_of_difference_ne (a h : Module.Dual ℝ E) (s t : E)
    (ha : s≠0 → a s≠0) (hw : (h-a) s • t-(h-a) t • s≠0) :
    a s • t-a t • s≠0 := by
  intro hz
  by_cases hs : s=0
  · apply hw
    simp only [hs,map_zero,zero_smul,smul_zero,sub_self]
  · have has:=ha hs
    have ht : t=(a t/a s) • s:=by
      calc
        t=(a s)⁻¹ • (a s • t):=(inv_smul_smul₀ has t).symm
        _=(a t/a s) • s:=by rw [sub_eq_zero.mp hz,smul_smul]; congr 1; ring
    apply hw
    rw [ht]
    simp only [map_smul,smul_smul,smul_eq_mul,mul_comm,sub_self]

lemma GenericOffset.join {T : Finset E} {a h : Module.Dual ℝ E}
    (H : GenericOffset T 0 a h) (ha : ∀s∈T,s≠0 → a s≠0) :
    GenericOffset T 0 (h-a) a := by
  refine ⟨map_zero _,?_,?_⟩
  · intro s hs hn
    exact ha s hs (by simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using hn)
  · intro s hs t ht hn
    have hw : (h-a) s • t-(h-a) t • s≠0:=by
      simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using hn
    have hz:=H.distinct s hs t ht (by
      simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using
        wedge_ne_of_difference_ne a h s t (ha s hs) hw)
    intro hh
    apply hz
    simp only [map_sub,map_smul,smul_eq_mul,LinearMap.sub_apply] at hh ⊢
    nlinarith

lemma GenericOffset.join_reverse {T : Finset E} {a h : Module.Dual ℝ E}
    (H : GenericOffset T 0 a h) (ha : ∀s∈T,s≠0 → a s≠0) :
    GenericOffset T 0 (a-h) h := by
  refine ⟨map_zero _,H.avoid,?_⟩
  intro s hs t ht hn
  have hw : (h-a) s • t-(h-a) t • s≠0:=by
    intro hz
    apply hn
    have he : (a-h) s • t-(a-h) t • s= -((h-a) s • t-(h-a) t • s):=by
      simp only [LinearMap.sub_apply,neg_sub,sub_smul]
      abel
    rw [he,hz,neg_zero]
    exact (Submodule.span ℝ {(0:E)}).zero_mem
  have hz:=H.distinct s hs t ht (by
    simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using
      wedge_ne_of_difference_ne a h s t (ha s hs) hw)
  intro hh
  apply hz
  simp only [map_sub,map_smul,smul_eq_mul,LinearMap.sub_apply] at hh ⊢
  nlinarith
end

section Simultaneous
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
noncomputable section
lemma generic_for_two_directions (T : ℕ → Finset E) (a b k : Module.Dual ℝ E)
    (P : Finset E) :
    ∃h : Module.Dual ℝ E,(∀N,GenericOffset (T N) 0 a h) ∧
      (∀N,GenericOffset (T N) 0 b h) ∧
      ∀s∈P,(0<k s → 0<h s) ∧ (k s<0 → h s<0) := by
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
    (P.image (fun s=>((0:ℝ),s))) 0 k (map_zero k)
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
  refine ⟨h,hGa,hGb,?_⟩
  intro s hs
  simpa only [zero_smul,add_zero] using hprobe (0,s) (Finset.mem_image.mpr ⟨s,hs,rfl⟩)
end
end Simultaneous
end ElementaryPositivity.FiniteRayGeometry

end
section
namespace ElementaryPositivity.QuantumTorus
open FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E)
def RegularCovector (a : Module.Dual ℝ E) : Prop :=
  ∀N,∀s∈realRootsThrough e C N,s≠0 → a s≠0

def segmentBetween (a b : Module.Dual ℝ E)
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (H : ∀N,GenericOffset (realRootsThrough e C N) 0 (b-a) a) :
    GenericLineSegment C e where
  direction:=b-a
  offset:=a
  lo:=0
  hi:=1
  ordered:=zero_lt_one
  generic:=H
  start_regular:=by
    intro N hh
    obtain ⟨s,hs,hv,hsa⟩:=(mem_lineEvents_iff _ _ _ _).mp hh
    exact HA N s hs (fun hz=>hv (by rw [hz,map_zero])) (by simpa only [zero_smul,add_zero] using hsa)
  finish_regular:=by
    intro N hh
    obtain ⟨s,hs,hv,hsa⟩:=(mem_lineEvents_iff _ _ _ _).mp hh
    exact HB N s hs (fun hz=>hv (by rw [hz,map_zero])) (by simpa only [one_smul,add_sub_cancel] using hsa)

@[simp] lemma segmentBetween_start (a b : Module.Dual ℝ E)
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (H : ∀N,GenericOffset (realRootsThrough e C N) 0 (b-a) a) :
    (segmentBetween C e a b HA HB H).start C e=a := by
  simp only [segmentBetween,GenericLineSegment.start,zero_smul,add_zero]
@[simp] lemma segmentBetween_finish (a b : Module.Dual ℝ E)
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (H : ∀N,GenericOffset (realRootsThrough e C N) 0 (b-a) a) :
    (segmentBetween C e a b HA HB H).finish C e=b := by
  simp only [segmentBetween,GenericLineSegment.finish,one_smul,add_sub_cancel]

def GenericLinePath.single (s : GenericLineSegment C e) :
    GenericLinePath C e (s.start C e) (s.finish C e) :=
  .append s (.nil _)

def GenericLinePath.trans {a b c : Module.Dual ℝ E}
    (p : GenericLinePath C e a b) (q : GenericLinePath C e b c) :
    GenericLinePath C e a c :=
  match q with
  | .nil _=>p
  | .append s q=>.append s (p.trans q)
end

section Existence
open FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E)
lemma regularCovector_exists (P : Finset E) (k : Module.Dual ℝ E) :
    ∃h : Module.Dual ℝ E,RegularCovector C e h ∧
      ∀s∈P,(0<k s → 0<h s) ∧ (k s<0 → h s<0) := by
  obtain ⟨h,Ha,Hb,HP⟩:=generic_for_two_directions (realRootsThrough e C) 0 0 k P
  refine ⟨h,?_,HP⟩
  intro N s hs hn
  exact (Ha N).avoid s hs (by simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using hn)

lemma generic_paths_via_intermediate (a b k : Module.Dual ℝ E) (P : Finset E)
    (HA : RegularCovector C e a) (HB : RegularCovector C e b) :
    ∃h : Module.Dual ℝ E,RegularCovector C e h ∧
      (∀s∈P,(0<k s → 0<h s) ∧ (k s<0 → h s<0)) ∧
      Nonempty (GenericLinePath C e a h) ∧ Nonempty (GenericLinePath C e h b) := by
  obtain ⟨h,Ha,Hb,HP⟩:=generic_for_two_directions (realRootsThrough e C) a b k P
  have HH : RegularCovector C e h:=by
    intro N s hs hn
    exact (Ha N).avoid s hs (by simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using hn)
  refine ⟨h,HH,HP,?_,?_⟩
  · let s:=segmentBetween C e a h HA HH (fun N=>(Ha N).join (HA N))
    have p:=GenericLinePath.single C e s
    exact ⟨by simpa only [s,segmentBetween_start,segmentBetween_finish] using p⟩
  · let s:=segmentBetween C e h b HH HB (fun N=>(Hb N).join_reverse (HB N))
    have p:=GenericLinePath.single C e s
    exact ⟨by simpa only [s,segmentBetween_start,segmentBetween_finish] using p⟩

theorem generic_path_exists (a b : Module.Dual ℝ E)
    (HA : RegularCovector C e a) (HB : RegularCovector C e b) :
    Nonempty (GenericLinePath C e a b) := by
  obtain ⟨h,_,_,⟨p⟩,⟨q⟩⟩:=generic_paths_via_intermediate C e a b 0 ∅ HA HB
  exact ⟨p.trans C e q⟩
end
end Existence
end ElementaryPositivity.QuantumTorus

end

end OAI
