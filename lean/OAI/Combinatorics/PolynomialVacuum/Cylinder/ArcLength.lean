import OAI.Combinatorics.PolynomialVacuum.Cylinder.ArcEncoding

namespace OAI

namespace PolynomialVacuumCylinder
variable {M : ℕ}

theorem neighbor_layer_bound (v : Vertex M) (k : Fin 3) :
    vertexLayer v-1≤vertexLayer (neighbor v k) ∧ vertexLayer (neighbor v k)≤vertexLayer v+1 := by
  cases v <;> fin_cases k <;> simp [neighbor,vertexLayer] <;> omega

theorem terminal_layer_bound (g : Germ M) (w : List Bool) :
    vertexLayer g.1-(w.length : ℤ)≤vertexLayer (terminalGerm g w).1 ∧
    vertexLayer (terminalGerm g w).1≤vertexLayer g.1+(w.length : ℤ) := by
  induction w generalizing g with
  | nil => simp [terminalGerm]
  | cons b w ih =>
    have hn:=neighbor_layer_bound g.1 (outgoingSlot g b)
    have ht:=ih (advance g b)
    simp only [terminalGerm,List.length_cons,Nat.cast_add,Nat.cast_one,advance]
    simp only [advance] at ht
    omega

theorem traced_layer_bound (g : Germ M) (w : List Bool) (v : Vertex M) (hv : v∈traced g w) :
    vertexLayer g.1-(w.length : ℤ)<vertexLayer v ∧ vertexLayer v<vertexLayer g.1+(w.length : ℤ) := by
  induction w generalizing g with
  | nil => simp [traced] at hv
  | cons b w ih =>
    simp only [traced,List.mem_cons] at hv
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    rcases hv with rfl | hv
    · omega
    · have hn:=neighbor_layer_bound g.1 (outgoingSlot g b)
      have ht:=ih (advance g b) hv
      simp only [advance] at ht
      omega
end PolynomialVacuumCylinder
namespace PolynomialVacuumBridge.Corridor
open PolynomialVacuumCylinder
namespace BridgeWord

theorem height_le_length (A : BridgeWord) : A.height≤A.word.length := by
  have hp : projectGerm 1 bottomSource=(.up (0 : ZMod 1) 0,0) := by simp [projectGerm,projectVertex,bottomSource]
  have ht:= (terminal_layer_bound (M:=1) (projectGerm 1 bottomSource) A.word).2
  rw [← project_terminal,A.terminal] at ht
  simpa [projectGerm,projectVertex,vertexLayer,bottomSource] using ht
end BridgeWord
namespace ArchWord

theorem nonempty (A : ArchWord) : A.word≠[] := by
  intro he
  have ht:=A.terminal
  simp [he,terminalGerm,bottomSource] at ht

theorem height_le_length (A : ArchWord) : A.height≤A.word.length := by
  have hp : 0<A.word.length := List.length_pos_iff.mpr A.nonempty
  have hb (v : PolynomialVacuumBridge.Corridor.Vertex) (hv : v∈traced bottomSource A.word) :
      (boxIndex v 0).toNat≤A.word.length-1 := by
    have hmem : projectVertex 1 v∈PolynomialVacuumCylinder.traced (projectGerm 1 bottomSource) A.word := by
      rw [← project_traced]
      exact List.mem_map.mpr ⟨v,hv,rfl⟩
    have ht:=(traced_layer_bound _ _ _ hmem).2
    have he : vertexLayer (projectVertex 1 v)=boxIndex v 0 := by cases v <;> rfl
    have hs : vertexLayer (projectGerm 1 bottomSource).1=0 := rfl
    rw [hs,zero_add,he] at ht
    omega
  unfold height
  have hs : (traced bottomSource A.word).toFinset.sup (fun v => (boxIndex v 0).toNat)≤A.word.length-1 :=
    Finset.sup_le (fun v hv => hb v (List.mem_toFinset.mp hv))
  omega
end ArchWord
end PolynomialVacuumBridge.Corridor
namespace PolynomialVacuumCylinder
open Classical
variable {M H : ℕ} [NeZero M]
namespace BoundaryArc

theorem shape_arch_of_length_lt (A : BoundaryArc (bandSites M H)) (h : A.word.length<H) :
    ∃B : PolynomialVacuumBridge.Corridor.ArchWord.CylinderArch M,A.shape=.inl B := by
  unfold shape
  split_ifs with he
  · exact ⟨he.choose,rfl⟩
  · obtain ⟨B,hB,hH⟩:=A.word_shape.resolve_left he
    have hl:=B.val.height_le_length
    rw [hB,hH] at hl
    omega
end BoundaryArc
end PolynomialVacuumCylinder

end OAI
