import OAI.Combinatorics.PolynomialVacuum.Cylinder.ArcLength

namespace OAI

namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumBridge.Corridor
variable {M H : ℕ} [NeZero M]

 

noncomputable def halfArchToBand (A : ArchWord.CylinderArch M)
    (hH : A.val.height≤H) : BoundaryArc (bandSites M H) where
  start := (.up 0 0,0)
  word := A.val.word
  nonempty := A.val.nonempty
  startInside := by
    rw [mem_bandSites]
    have hp : 0<A.val.height := Nat.succ_pos _
    simp only [InBand,vertexLayer]
    omega
  startOutside := by simp [mem_bandSites,reverseGerm,neighbor,InBand,vertexLayer]
  distinct := by
    have hp : projectGerm M bottomSource=(.up (0 : ZMod M) 0,0) := by simp [projectGerm,projectVertex,bottomSource]
    simpa only [ArchWord.CylinderSafe,project_traced,hp] using A.property
  inside := by
    intro v hv
    have hp : projectGerm M bottomSource=(.up (0 : ZMod M) 0,0) := by simp [projectGerm,projectVertex,bottomSource]
    rw [← hp,← project_traced] at hv
    obtain ⟨u,hu,rfl⟩:=List.mem_map.mp hv
    rw [mem_bandSites]
    have hl:=A.val.layer_lt_height u hu
    have hn:=A.val.inHalfPlane u hu
    change 0≤vertexLayer (projectVertex M u) ∧ vertexLayer (projectVertex M u)<(H : ℤ)
    have he : vertexLayer (projectVertex M u)=boxIndex u 0 := by cases u <;> rfl
    rw [he]
    omega
  endOutside := by
    have hp : projectGerm M bottomSource=(.up (0 : ZMod M) 0,0) := by simp [projectGerm,projectVertex,bottomSource]
    rw [← hp,← project_terminal,A.val.terminal]
    simp [projectGerm,projectVertex,mem_bandSites,InBand,vertexLayer]
  endInside := by
    have hp : projectGerm M bottomSource=(.up (0 : ZMod M) 0,0) := by simp [projectGerm,projectVertex,bottomSource]
    rw [← hp,← project_terminal,A.val.terminal]
    have hh : 0<A.val.height := Nat.succ_pos _
    simp [projectGerm,projectVertex,mem_bandSites,InBand,vertexLayer,reverseGerm,neighbor]
    omega

 
noncomputable def atPort (A : ArchWord.CylinderArch M) (hH : A.val.height≤H)
    (p : Bool × ZMod M) : BoundaryArc (bandSites M H) :=
  if p.1 then
    ((halfArchToBand A hH).mapBand (rotate H) (Function.LeftInverse.injective (rotate_invol H))
      (rotate_neighbor H) (rotate_band H)).mapBand (translate p.2 0) (translate_injective _ _)
        (translate_neighbor_cyl _ _) (translate_band _ H)
  else (halfArchToBand A hH).mapBand (translate p.2 0) (translate_injective _ _)
        (translate_neighbor_cyl _ _) (translate_band _ H)

@[simp] theorem atPort_word (A : ArchWord.CylinderArch M) (hH : A.val.height≤H) (p : Bool × ZMod M) :
    (atPort A hH p).word=A.val.word := by unfold atPort; split <;> rfl
@[simp] theorem atPort_start (A : ArchWord.CylinderArch M) (hH : A.val.height≤H) (p : Bool × ZMod M) :
    (atPort A hH p).start=(if p.1 then (.down p.2 ((H : ℤ)-1),0) else (.up p.2 0,0)) := by
  unfold atPort
  split <;> simp_all [BoundaryArc.mapBand,halfArchToBand,mapGerm,rotate,translate]
@[simp] theorem atPort_port (A : ArchWord.CylinderArch M) (hH : A.val.height≤H) (p : Bool × ZMod M) :
    (atPort A hH p).port=p := by
  unfold BoundaryArc.port
  rw [atPort_start]
  cases p with
  | mk b i => cases b <;> rfl
@[simp] theorem atPort_shape (A : ArchWord.CylinderArch M) (hH : A.val.height≤H) (p : Bool × ZMod M) :
    (atPort A hH p).shape=.inl A := by
  apply ArcShape.word_injective
  rw [BoundaryArc.shape_word,atPort_word]
  rfl

theorem eq_atPort_of_shape (B : BoundaryArc (bandSites M H)) (A : ArchWord.CylinderArch M)
    (hA : B.shape=.inl A) (hH : A.val.height≤H) : B=atPort A hH B.port := by
  apply B.eq_of_port_shape
  · simp
  · simp [hA]

end PolynomialVacuumCylinder

end OAI
