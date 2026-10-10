import OAI.Combinatorics.PolynomialVacuum.Cylinder.OpenCurrent
import OAI.Combinatorics.PolynomialVacuum.Cylinder.ArcDecay

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ}

def vertexLayer : Vertex M → ℤ
  | .up _ j => j
  | .down _ j => j

def InBand (H : ℕ) (v : Vertex M) : Prop := 0≤vertexLayer v ∧ vertexLayer v<(H : ℤ)

noncomputable def bandSites (M H : ℕ) [NeZero M] : Finset (Vertex M) :=
  ((Finset.univ ×ˢ Finset.Ico (0 : ℤ) H).image (fun p : ZMod M × ℤ => Vertex.up p.1 p.2)) ∪
  ((Finset.univ ×ˢ Finset.Ico (0 : ℤ) H).image (fun p : ZMod M × ℤ => Vertex.down p.1 p.2))

theorem mem_bandSites [NeZero M] (H : ℕ) (v : Vertex M) : v∈bandSites M H ↔ InBand H v := by
  cases v <;> simp [bandSites,InBand,vertexLayer,Finset.mem_image,Prod.exists]

 

theorem band_boundary (H : ℕ) (v : Vertex M) (k : Fin 3) (hv : InBand H v)
    (ho : ¬InBand H (neighbor v k)) :
    (∃i,v=.up i 0 ∧ k=0) ∨ (∃i,v=.down i ((H : ℤ)-1) ∧ k=0) := by
  cases v with
  | up i j =>
    left
    refine ⟨i,?_,?_⟩
    · have hj : j=0 := by
        fin_cases k <;> simp [InBand,vertexLayer,neighbor] at hv ho <;> omega
      simp [hj]
    · fin_cases k <;> simp_all [InBand,vertexLayer,neighbor]
  | down i j =>
    right
    refine ⟨i,?_,?_⟩
    · have hj : j=(H : ℤ)-1 := by
        fin_cases k <;> simp [InBand,vertexLayer,neighbor] at hv ho <;> omega
      simp [hj]
    · fin_cases k <;> simp_all [InBand,vertexLayer,neighbor]

@[simp] theorem layer_project (v : PolynomialVacuumBridge.Corridor.Vertex) :
    vertexLayer (projectVertex M v)=PolynomialVacuumBridge.Corridor.layer v := by cases v <;> rfl

private theorem plane_top_of_project (g : PolynomialVacuumBridge.Corridor.Germ) (h : ℤ)
    (hg : ∃i,projectGerm M g=(.up i h,0)) : ∃x,g=(.up x h,0) := by
  rcases g with ⟨v,k⟩
  rcases hg with ⟨i,hi⟩
  cases v with
  | up x y =>
    simp only [projectGerm,projectVertex,Prod.mk.injEq,Vertex.up.injEq] at hi
    exact ⟨x,by rw [hi.1.2,hi.2]⟩
  | down x y => cases hi

private theorem plane_bottom_of_project (g : PolynomialVacuumBridge.Corridor.Germ)
    (hg : ∃i,projectGerm M g=(.down i (-1),0)) : ∃x,g=(.down x (-1),0) := by
  rcases g with ⟨v,k⟩
  rcases hg with ⟨i,hi⟩
  cases v with
  | up x y => cases hi
  | down x y =>
    simp only [projectGerm,projectVertex,Prod.mk.injEq,Vertex.down.injEq] at hi
    exact ⟨x,by rw [hi.1.2,hi.2]⟩

 

theorem word_is_cylinder_bridge (H : ℕ) (w : List Bool)
    (hN : (traced (.up (0 : ZMod M) 0,0) w).Nodup)
    (ht : ∃i,terminalGerm (.up (0 : ZMod M) 0,0) w=(.up i H,0))
    (hi : ∀v∈traced (.up (0 : ZMod M) 0,0) w,InBand H v) :
    ∃A : PolynomialVacuumBridge.Corridor.BridgeWord.CylinderBridge M,A.val.word=w ∧ A.val.height=H := by
  have hp : projectGerm M PolynomialVacuumBridge.Corridor.bottomSource=(.up (0 : ZMod M) 0,0) := by
    simp [projectGerm,projectVertex,PolynomialVacuumBridge.Corridor.bottomSource]
  have he : ∃x,PolynomialVacuumBridge.Corridor.terminalGerm PolynomialVacuumBridge.Corridor.bottomSource w=(.up x H,0) := by
    apply plane_top_of_project (M:=M)
    simpa only [project_terminal,hp] using ht
  obtain ⟨x,hx⟩:=he
  have hn : ((PolynomialVacuumBridge.Corridor.traced PolynomialVacuumBridge.Corridor.bottomSource w).map
      (projectVertex M)).Nodup := by simpa only [project_traced,hp] using hN
  let A : PolynomialVacuumBridge.Corridor.BridgeWord :=
    ⟨w,H,x,List.Nodup.of_map (projectVertex M) hn,hx,by
      intro v hv
      have hh:=hi (projectVertex M v) (by rw [← hp,← project_traced]; exact List.mem_map.mpr ⟨v,hv,rfl⟩)
      simpa only [InBand,layer_project] using hh⟩
  exact ⟨⟨A,hn⟩,rfl,rfl⟩

 

theorem word_is_cylinder_arch (w : List Bool)
    (hN : (traced (.up (0 : ZMod M) 0,0) w).Nodup)
    (ht : ∃i,terminalGerm (.up (0 : ZMod M) 0,0) w=(.down i (-1),0))
    (hi : ∀v∈traced (.up (0 : ZMod M) 0,0) w,0≤vertexLayer v) :
    ∃A : PolynomialVacuumBridge.Corridor.ArchWord.CylinderArch M,A.val.word=w := by
  have hp : projectGerm M PolynomialVacuumBridge.Corridor.bottomSource=(.up (0 : ZMod M) 0,0) := by
    simp [projectGerm,projectVertex,PolynomialVacuumBridge.Corridor.bottomSource]
  have he : ∃x,PolynomialVacuumBridge.Corridor.terminalGerm PolynomialVacuumBridge.Corridor.bottomSource w=(.down x (-1),0) := by
    apply plane_bottom_of_project (M:=M)
    simpa only [project_terminal,hp] using ht
  obtain ⟨x,hx⟩:=he
  have hn : ((PolynomialVacuumBridge.Corridor.traced PolynomialVacuumBridge.Corridor.bottomSource w).map
      (projectVertex M)).Nodup := by simpa only [project_traced,hp] using hN
  let A : PolynomialVacuumBridge.Corridor.ArchWord :=
    ⟨w,x,List.Nodup.of_map (projectVertex M) hn,hx,by
      intro v hv
      have hh:=hi (projectVertex M v) (by rw [← hp,← project_traced]; exact List.mem_map.mpr ⟨v,hv,rfl⟩)
      simpa only [layer_project,PolynomialVacuumBridge.Corridor.layer_boxIndex] using hh⟩
  exact ⟨⟨A,hn⟩,rfl⟩

end PolynomialVacuumCylinder

end OAI
