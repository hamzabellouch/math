import Mathlib
import OAI.Combinatorics.HoneycombCorridor.ConvexCuts

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def mirrorVertex : Vertex → Vertex
  | .up i j => .up (-i-j) j
  | .down i j => .down (-i-j-1) j

def mirrorSlot (k : Fin 3) : Fin 3 := if k = 0 then 0 else if k = 1 then 2 else 1

def mirrorGerm (g : Germ) : Germ := (mirrorVertex g.1,mirrorSlot g.2)
def mirrorWord (w : List Bool) : List Bool := w.map Bool.not

@[simp] theorem mirrorVertex_invol (v : Vertex) : mirrorVertex (mirrorVertex v) = v := by
  cases v <;> simp [mirrorVertex]
  omega

@[simp] theorem mirrorSlot_invol (k : Fin 3) : mirrorSlot (mirrorSlot k) = k := by
  fin_cases k <;> rfl

@[simp] theorem mirrorGerm_invol (g : Germ) : mirrorGerm (mirrorGerm g) = g := by
  simp [mirrorGerm]

@[simp] theorem mirrorWord_invol (w : List Bool) : mirrorWord (mirrorWord w) = w := by
  simp [mirrorWord,List.map_map,Function.comp_def]

theorem mirrorVertex_injective : Function.Injective mirrorVertex :=
  Function.Involutive.injective mirrorVertex_invol

theorem mirrorWord_injective : Function.Injective mirrorWord :=
  Function.Involutive.injective mirrorWord_invol

@[simp] theorem mirrorWord_length (w : List Bool) : (mirrorWord w).length = w.length := by
  simp [mirrorWord]

@[simp] theorem mirror_position (v : Vertex) : (position (mirrorVertex v)).1 = -(position v).1 := by
  cases v <;> simp [mirrorVertex,position] <;> ring

@[simp] theorem mirror_neighbor (v : Vertex) (k : Fin 3) :
    mirrorVertex (neighbor v k) = neighbor (mirrorVertex v) (mirrorSlot k) := by
  cases v <;> fin_cases k <;> simp [mirrorVertex,mirrorSlot,neighbor] <;> omega

@[simp] theorem mirror_advance (g : Germ) (b : Bool) :
    mirrorGerm (advance g b) = advance (mirrorGerm g) (!b) := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;> cases b <;>
    simp [mirrorGerm,mirrorVertex,mirrorSlot,advance,outgoingSlot,neighbor,
      Fin.reduceAdd,Fin.reduceEq,Fin.isValue] <;> omega

@[simp] theorem mirror_terminal (g : Germ) (w : List Bool) :
    terminalGerm (mirrorGerm g) (mirrorWord w) = mirrorGerm (terminalGerm g w) := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
    simp only [mirrorWord,List.map_cons,terminalGerm,← mirror_advance]
    exact ih _

@[simp] theorem mirror_traced (g : Germ) (w : List Bool) :
    traced (mirrorGerm g) (mirrorWord w) = (traced g w).map mirrorVertex := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
    change mirrorVertex g.1 :: traced (advance (mirrorGerm g) (!b)) (mirrorWord w) =
      mirrorVertex g.1 :: (traced (advance g b) w).map mirrorVertex
    rw [← mirror_advance,ih]

@[simp] theorem mirror_bottomSource : mirrorGerm bottomSource = bottomSource := by rfl

noncomputable def mirrorDomain (D : Finset Vertex) : Finset Vertex := D.image mirrorVertex

@[simp] theorem mem_mirrorDomain (D : Finset Vertex) (v : Vertex) :
    v ∈ mirrorDomain D ↔ mirrorVertex v ∈ D := by
  constructor
  · intro hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    simpa using hu
  · intro hv
    exact Finset.mem_image.mpr ⟨mirrorVertex v,hv,mirrorVertex_invol v⟩

@[simp] theorem mirrorDomain_invol (D : Finset Vertex) : mirrorDomain (mirrorDomain D) = D := by
  ext v
  simp

@[simp] theorem mirror_indices (v : Vertex) :
    boxIndex (mirrorVertex v) 0 = boxIndex v 0 ∧
    boxIndex (mirrorVertex v) 1 = -boxIndex v 2 ∧
    boxIndex (mirrorVertex v) 2 = -boxIndex v 1 := by
  cases v <;> simp [mirrorVertex,boxIndex] <;> omega

theorem mirrorDomain_convex (D : Finset Vertex) (hD : AdmissiblyConvex D) :
    AdmissiblyConvex (mirrorDomain D) := by
  obtain ⟨lo,hi,hbox⟩ := admissiblyConvex_box D hD
  let lo' : Fin 3 → ℤ := fun k => if k = 0 then lo 0 else if k = 1 then 1-hi 2 else 1-hi 1
  let hi' : Fin 3 → ℤ := fun k => if k = 0 then hi 0 else if k = 1 then 1-lo 2 else 1-lo 1
  apply admissiblyConvex_of_box _ lo' hi'
  intro v
  rw [mem_mirrorDomain,hbox]
  have hm := mirror_indices v
  constructor
  · intro hv k
    have h0 := hv 0
    have h1 := hv 1
    have h2 := hv 2
    rw [hm.1] at h0
    rw [hm.2.1] at h1
    rw [hm.2.2] at h2
    fin_cases k <;> simp [lo',hi'] <;> omega
  · intro hv k
    have h0 := hv 0
    have h1 := hv 1
    have h2 := hv 2
    simp only [lo',hi',Fin.isValue,Fin.reduceEq,ite_true,ite_false] at h0 h1 h2
    fin_cases k
    · change lo 0 ≤ boxIndex (mirrorVertex v) 0 ∧ boxIndex (mirrorVertex v) 0 < hi 0
      rw [hm.1]; omega
    · change lo 1 ≤ boxIndex (mirrorVertex v) 1 ∧ boxIndex (mirrorVertex v) 1 < hi 1
      rw [hm.2.1]; omega
    · change lo 2 ≤ boxIndex (mirrorVertex v) 2 ∧ boxIndex (mirrorVertex v) 2 < hi 2
      rw [hm.2.2]; omega

theorem mirrorDomain_strip (h : ℕ) (D : Finset Vertex) (hstrip : ∀ v ∈ D, InStrip h v) :
    ∀ v ∈ mirrorDomain D, InStrip h v := by
  intro v hv
  have hh := hstrip _ ((mem_mirrorDomain D v).mp hv)
  simpa only [InStrip,(mirror_indices v).1] using hh

theorem mirror_sourceExits (D : Finset Vertex) (g : Germ) (w : List Bool)
    (hw : w ∈ sourceExits D g) : mirrorWord w ∈ sourceExits (mirrorDomain D) (mirrorGerm g) := by
  obtain ⟨hs,ht⟩ := (mem_sourceExits D g w).mp hw
  obtain ⟨hn,hm⟩ := stopped_traced D g w hs
  have ht' : (terminalGerm (mirrorGerm g) (mirrorWord w)).1 ∉ mirrorDomain D := by
    rw [mirror_terminal]
    change mirrorVertex (terminalGerm g w).1 ∉ mirrorDomain D
    rwa [mem_mirrorDomain,mirrorVertex_invol]
  apply (mem_sourceExits _ _ _).mpr
  refine ⟨stopped_of_trace _ _ _ ?_ ?_ ht',ht'⟩
  · rw [mirror_traced]
    exact hn.map mirrorVertex_injective
  · intro v hv
    rw [mirror_traced,List.mem_map] at hv
    obtain ⟨u,hu,rfl⟩ := hv
    simpa only [mem_mirrorDomain,mirrorVertex_invol] using hm u hu

theorem mirror_sourceExits_eq (D : Finset Vertex) :
    sourceExits (mirrorDomain D) bottomSource = (sourceExits D bottomSource).image mirrorWord := by
  ext w
  constructor
  · intro hw
    refine Finset.mem_image.mpr ⟨mirrorWord w,?_,mirrorWord_invol w⟩
    simpa only [mirrorDomain_invol,mirror_bottomSource] using
      mirror_sourceExits (mirrorDomain D) bottomSource w hw
  · intro hw
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hw
    simpa only [mirror_bottomSource] using mirror_sourceExits D bottomSource u hu

end PolynomialVacuumBridge.Corridor

end

end OAI
