import OAI.Probability.DilutedSpin.RootProjectionShiftError

namespace OAI

section
section
namespace DilutedSpinGlass

/-- Transport along equality of total depths only; no change to a kernel. -/
def kernelHeightCast {Ω : Type} [Fintype Ω] {n m : ℕ} (h : n=m)
    (T : KernelTower Ω n) : KernelTower Ω m := h ▸ T

def pathHeightCast {Ω : Type} {n m : ℕ} (h : n=m)
    (x : FinitePath Ω n) : FinitePath Ω m := h ▸ x

def vectorHeightCast {Ω : Type} {n m N : ℕ} (h : n=m)
    (f : FinitePath Ω n → Fin N → ℝ) : FinitePath Ω m → Fin N → ℝ :=
  fun x => f (pathHeightCast h.symm x)

@[simp] theorem kernelHeightCast_inv {Ω : Type} [Fintype Ω] {n m : ℕ} (h : n=m)
    (T : KernelTower Ω m) : kernelHeightCast h (kernelHeightCast h.symm T)=T := by cases h; rfl
@[simp] theorem vectorHeightCast_inv {Ω : Type} {n m N : ℕ} (h : n=m)
    (f : FinitePath Ω m → Fin N → ℝ) : vectorHeightCast h (vectorHeightCast h.symm f)=f := by cases h; rfl

namespace PrescribedTree
variable {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I] {n m N : ℕ}

def heightCast (h : n=m) (S : PrescribedTree n) : PrescribedTree m := h ▸ S

def leafHeightCast (h : n=m) (S : PrescribedTree n) (a : S.Leaf) : (heightCast h S).Leaf := by
  cases h; exact a

lemma leafHeightCast_bijective (h : n=m) (S : PrescribedTree n) :
    Function.Bijective (leafHeightCast h S) := by cases h; exact Function.bijective_id

@[simp] theorem splitDepth_heightCast (h : n=m) (S : PrescribedTree n) (a b : S.Leaf) :
    splitDepth (heightCast h S) (leafHeightCast h S a) (leafHeightCast h S b)=splitDepth S a b := by
  cases h; rfl

omit [DecidableEq I] in
@[simp] theorem matrixProjectionError_heightCast (h : n=m) (S : PrescribedTree n)
    (q : I → S.Leaf) (T : KernelTower Ω n) (a c : I)
    (f X : FinitePath Ω n → Fin N → ℝ) :
    matrixProjectionError (heightCast h S) (fun j => leafHeightCast h S (q j))
      (kernelHeightCast h T) a c (spatialProduct (fun _ : I => vectorHeightCast h f))
      (vectorHeightCast h X)=
    matrixProjectionError S q T a c (spatialProduct (fun _ : I => f)) X := by cases h; rfl

end PrescribedTree
namespace ReducedTopology
variable {Ω ι : Type} [Fintype Ω] [Fintype ι] {n m N : ℕ}

@[simp] theorem conditionalScheduledProduct_heightCast (h : n=m) (d p : ℕ)
    (C : ι → ReducedTopology) (q : (j : ι) → (C j).Vertex → ℕ) (T : KernelTower Ω n)
    (f : FinitePath Ω n → Fin N → ℝ) :
    vectorHeightCast h (conditionalScheduledProduct n d p C q T f)=
      conditionalScheduledProduct m d p C q (kernelHeightCast h T) (vectorHeightCast h f) := by
  cases h; rfl

@[simp] theorem projectionShiftError_heightCast {α : Type} [Fintype α] [DecidableEq α]
    (h : n=m) (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a})
    (T : KernelTower Ω n) (f : FinitePath Ω n → Fin N → ℝ) (Q : α → Fin n) :
    projectionShiftError a C e (kernelHeightCast h T) (vectorHeightCast h f) (fun j => Fin.cast h (Q j))=
      projectionShiftError a C e T f Q := by cases h; rfl

end ReducedTopology
end DilutedSpinGlass
end

end

end OAI
