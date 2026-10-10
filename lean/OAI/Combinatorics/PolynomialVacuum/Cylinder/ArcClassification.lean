import OAI.Combinatorics.PolynomialVacuum.Cylinder.ArcIsometries

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M H : ℕ} [NeZero M]
namespace BoundaryArc
noncomputable def mapBand (A : BoundaryArc (bandSites M H))
    (f : Vertex M → Vertex M) (hf : Function.Injective f)
    (hn : ∀v k,f (neighbor v k)=neighbor (f v) k)
    (hb : ∀v,InBand H (f v) ↔ InBand H v) : BoundaryArc (bandSites M H) where
  start := mapGerm f A.start
  word := A.word
  nonempty := A.nonempty
  startInside := (mem_bandSites H _).mpr ((hb _).mpr ((mem_bandSites H _).mp A.startInside))
  startOutside := by
    change neighbor (f A.start.1) A.start.2∉bandSites M H
    rw [← hn,mem_bandSites,hb]
    exact fun h => A.startOutside ((mem_bandSites H _).mpr h)
  distinct := by rw [← map_traced f hn]; exact A.distinct.map hf
  inside := by
    intro v hv
    rw [← map_traced f hn] at hv
    obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hv
    exact (mem_bandSites H _).mpr ((hb _).mpr ((mem_bandSites H _).mp (A.inside w hw)))
  endOutside := by
    rw [← map_terminal f hn]
    change f (terminalGerm A.start A.word).1∉bandSites M H
    rw [mem_bandSites,hb]
    exact fun h => A.endOutside ((mem_bandSites H _).mpr h)
  endInside := by
    rw [← map_terminal f hn]
    change neighbor (f (terminalGerm A.start A.word).1) (terminalGerm A.start A.word).2∈bandSites M H
    rw [← hn,mem_bandSites,hb]
    exact (mem_bandSites H _).mp A.endInside

def port (A : BoundaryArc (bandSites M H)) : Bool × ZMod M :=
  match A.start.1 with
  | .up i _ => (false,i)
  | .down i _ => (true,i)

theorem start_port (A : BoundaryArc (bandSites M H)) :
    A.start=(if A.port.1 then (.down A.port.2 ((H : ℤ)-1),0) else (.up A.port.2 0,0)) := by
  have hb:=band_boundary H A.start.1 A.start.2 ((mem_bandSites H _).mp A.startInside)
    (by simpa only [reverseGerm,mem_bandSites] using A.startOutside)
  rcases hb with ⟨i,hv,hk⟩ | ⟨i,hv,hk⟩
  · have he : A.start=(.up i 0,0) := Prod.ext hv hk
    simp [port,he]
  · have he : A.start=(.down i ((H : ℤ)-1),0) := Prod.ext hv hk
    simp [port,he]

theorem terminal_ports (A : BoundaryArc (bandSites M H)) :
    (∃i,terminalGerm A.start A.word=(.down i (-1),0)) ∨
    (∃i,terminalGerm A.start A.word=(.up i H,0)) := by
  let g:=terminalGerm A.start A.word
  have hb:=band_boundary H (reverseGerm g).1 g.2 ((mem_bandSites H _).mp A.endInside)
    (by simpa only [reverseGerm,neighbor_neighbor,mem_bandSites] using A.endOutside)
  have he : g=reverseGerm (reverseGerm g) := by simp [reverseGerm,neighbor_neighbor]
  rcases hb with ⟨i,hv,hk⟩ | ⟨i,hv,hk⟩
  · left
    refine ⟨i,?_⟩
    change g=_
    rw [he]
    change (neighbor (reverseGerm g).1 g.2,g.2)=_
    rw [hv,hk]
    simp [neighbor]
  · right
    refine ⟨i,?_⟩
    change g=_
    rw [he]
    change (neighbor (reverseGerm g).1 g.2,g.2)=_
    rw [hv,hk]
    simp [neighbor]

noncomputable def normalized (A : BoundaryArc (bandSites M H)) : BoundaryArc (bandSites M H) :=
  if A.port.1 then
    (A.mapBand (rotate H) (Function.LeftInverse.injective (rotate_invol H)) (rotate_neighbor H) (rotate_band H)).mapBand
      (translate A.port.2 0) (translate_injective _ _) (translate_neighbor_cyl _ _) (translate_band _ H)
  else A.mapBand (translate (-A.port.2) 0) (translate_injective _ _) (translate_neighbor_cyl _ _) (translate_band _ H)

@[simp] theorem normalized_word (A : BoundaryArc (bandSites M H)) : A.normalized.word=A.word := by
  unfold normalized
  split <;> rfl
@[simp] theorem normalized_start (A : BoundaryArc (bandSites M H)) : A.normalized.start=(.up 0 0,0) := by
  have hs:=A.start_port
  unfold normalized
  split <;> simp_all [mapBand,mapGerm,rotate,translate]

theorem word_shape (A : BoundaryArc (bandSites M H)) :
    (∃B : PolynomialVacuumBridge.Corridor.ArchWord.CylinderArch M,B.val.word=A.word) ∨
    (∃B : PolynomialVacuumBridge.Corridor.BridgeWord.CylinderBridge M,B.val.word=A.word ∧ B.val.height=H) := by
  have hn : (traced (.up (0 : ZMod M) 0,0) A.word).Nodup := by simpa using A.normalized.distinct
  have hi : ∀v∈traced (.up (0 : ZMod M) 0,0) A.word,InBand H v := by
    intro v hv
    apply (mem_bandSites H v).mp
    apply A.normalized.inside
    simpa using hv
  rcases A.normalized.terminal_ports with hb | ht
  · left
    apply word_is_cylinder_arch A.word hn (by simpa using hb)
    exact fun v hv => (hi v hv).1
  · right
    exact word_is_cylinder_bridge H A.word hn (by simpa using ht) hi
end BoundaryArc
end PolynomialVacuumCylinder

end OAI
