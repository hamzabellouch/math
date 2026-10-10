import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.Grid
import OAI.Combinatorics.ThinTrees.Flow.Interior
import OAI.Combinatorics.ThinTrees.Flow.RootedRelaxation

namespace OAI

/-! Continuation coordinates. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Orientations

abbrev Triple (n : ℕ) := Fin n × (Fin n × Fin n)
abbrev Var (n m : ℕ) :=
  (Fin n × Fin n) ⊕ (Triple n ⊕ ((Fin 3 × Fin m) ⊕ (Fin 2 × (Fin n × Fin m))))

def dimension (n m : ℕ) := n*n+(n*(n*n)+(3*m+2*(n*m)))

def index (n m : ℕ) : Var n m ≃ Fin (dimension n m) :=
  let et : Triple n ≃ Fin (n*(n*n)) :=
    ((Equiv.refl (Fin n)).prodCongr finProdFinEquiv).trans finProdFinEquiv
  let ef : (Fin 2 × (Fin n × Fin m)) ≃ Fin (2*(n*m)) :=
    ((Equiv.refl (Fin 2)).prodCongr finProdFinEquiv).trans finProdFinEquiv
  let ee := (finProdFinEquiv.sumCongr ef).trans finSumFinEquiv
  (finProdFinEquiv.sumCongr ((et.sumCongr ee).trans finSumFinEquiv)).trans finSumFinEquiv

variable {n m : ℕ}

def matIndex (i j : Fin n) : Fin (dimension n m) := index n m (.inl (i,j))
def mulIndex (ijk : Triple n) : Fin (dimension n m) := index n m (.inr (.inl ijk))
def edgeIndex (p : Fin 3) (e : Fin m) : Fin (dimension n m) := index n m (.inr (.inr (.inl (p,e))))
def flowIndex (p : Fin 2) (r : Fin n) (e : Fin m) : Fin (dimension n m) :=
  index n m (.inr (.inr (.inr (p,(r,e)))))

def rawMatrix {R : Type*} (v : Fin (dimension n m) → R) : Matrix (Fin n) (Fin n) R :=
  fun i j => v (matIndex i j)
def multiplier {R : Type*} (v : Fin (dimension n m) → R) : DistinctTriple n → R :=
  fun ijk => v (mulIndex ijk.val)
def y {R : Type*} (v : Fin (dimension n m) → R) : Fin m → R :=fun e => v (edgeIndex 0 e)
def z {R : Type*} (v : Fin (dimension n m) → R) : Fin m → R :=fun e => v (edgeIndex 1 e)
def flowX {R : Type*} (v : Fin (dimension n m) → R) : Fin m → R :=fun e => v (edgeIndex 2 e)
def flowA {R : Type*} (v : Fin (dimension n m) → R) : Fin n → Fin m → R :=fun r e => v (flowIndex 0 r e)
def flowB {R : Type*} (v : Fin (dimension n m) → R) : Fin n → Fin m → R :=fun r e => v (flowIndex 1 r e)

def step (v : Fin (dimension n m) → ℝ) : StepFree n m :=
  (rawMatrix v,multiplier v,y v,z v)
def flow (v : Fin (dimension n m) → ℝ) : FlowPoint n m :=
  ⟨flowX v,flowA v,flowB v⟩

def rational (v : Fin (dimension n m) → ℚ) : StepRational n m :=
  (rawMatrix v,multiplier v,y v,z v)

lemma rational_real (v : Fin (dimension n m) → ℚ) :
    (rational v).real=step (fun i => (v i:ℝ)) := rfl

noncomputable def encode (c : StepFree n m) (F : FlowPoint n m) : Fin (dimension n m) → ℝ :=
  fun k => match (index n m).symm k with
  | .inl (i,j) => c.1 i j
  | .inr (.inl ijk) =>
      if h : ijk.1 ≠ ijk.2.1 ∧ ijk.2.1 ≠ ijk.2.2 ∧ ijk.1 ≠ ijk.2.2 then c.multiplier ⟨ijk,h⟩ else 0
  | .inr (.inr (.inl (p,e))) => if p=0 then c.y e else if p=1 then c.z e else F.x e
  | .inr (.inr (.inr (p,(r,e)))) => if p=0 then F.a r e else F.b r e

@[simp] lemma encode_mat (c : StepFree n m) (F : FlowPoint n m) (i j : Fin n) :
    encode c F (matIndex i j)=c.1 i j := by simp [encode,matIndex]
@[simp] lemma encode_mul (c : StepFree n m) (F : FlowPoint n m) (ijk : DistinctTriple n) :
    encode c F (mulIndex ijk.val)=c.multiplier ijk := by simp [encode,mulIndex,ijk.property]
@[simp] lemma encode_y (c : StepFree n m) (F : FlowPoint n m) (e : Fin m) :
    encode c F (edgeIndex 0 e)=c.y e := by simp [encode,edgeIndex]
@[simp] lemma encode_z (c : StepFree n m) (F : FlowPoint n m) (e : Fin m) :
    encode c F (edgeIndex 1 e)=c.z e := by simp [encode,edgeIndex]
@[simp] lemma encode_x (c : StepFree n m) (F : FlowPoint n m) (e : Fin m) :
    encode c F (edgeIndex 2 e)=F.x e := by simp [encode,edgeIndex]
@[simp] lemma encode_a (c : StepFree n m) (F : FlowPoint n m) (r : Fin n) (e : Fin m) :
    encode c F (flowIndex 0 r e)=F.a r e := by simp [encode,flowIndex]
@[simp] lemma encode_b (c : StepFree n m) (F : FlowPoint n m) (r : Fin n) (e : Fin m) :
    encode c F (flowIndex 1 r e)=F.b r e := by simp [encode,flowIndex]

lemma encode_step (c : StepFree n m) (F : FlowPoint n m) : step (encode c F)=c := by
  apply Prod.ext
  · funext i j
    exact encode_mat c F i j
  · apply Prod.ext
    · funext ijk
      exact encode_mul c F ijk
    · apply Prod.ext
      · funext e
        exact encode_y c F e
      · funext e
        exact encode_z c F e
lemma encode_flow (c : StepFree n m) (F : FlowPoint n m) : flow (encode c F)=F := by
  have hx : flowX (encode c F)=F.x := funext (encode_x c F)
  have ha : flowA (encode c F)=F.a := funext (fun r => funext (encode_a c F r))
  have hb : flowB (encode c F)=F.b := funext (fun r => funext (encode_b c F r))
  simp only [flow,hx,ha,hb]

lemma close_step_flow (c : StepFree n m) (F : FlowPoint n m)
    (v : Fin (dimension n m) → ℝ) {ρ : ℝ}
    (h : ∀i, |v i-encode c F i| ≤ ρ) :
    (step v).Close c ρ ∧ (flow v).Close F ρ := by
  refine ⟨⟨?_,?_,?_,?_⟩,⟨?_,?_,?_⟩⟩
  · intro i j
    simpa only [step,flow,StepFree.multiplier,StepFree.y,StepFree.z,rawMatrix,multiplier,y,z,flowX,flowA,flowB,encode_mat] using h (matIndex i j)
  · intro ijk
    simpa only [step,flow,StepFree.multiplier,StepFree.y,StepFree.z,rawMatrix,multiplier,y,z,flowX,flowA,flowB,encode_mul] using h (mulIndex ijk.val)
  · intro e
    simpa only [step,flow,StepFree.multiplier,StepFree.y,StepFree.z,rawMatrix,multiplier,y,z,flowX,flowA,flowB,encode_y] using h (edgeIndex 0 e)
  · intro e
    simpa only [step,flow,StepFree.multiplier,StepFree.y,StepFree.z,rawMatrix,multiplier,y,z,flowX,flowA,flowB,encode_z] using h (edgeIndex 1 e)
  · intro e
    simpa only [step,flow,StepFree.multiplier,StepFree.y,StepFree.z,rawMatrix,multiplier,y,z,flowX,flowA,flowB,encode_x] using h (edgeIndex 2 e)
  · intro r e
    simpa only [step,flow,StepFree.multiplier,StepFree.y,StepFree.z,rawMatrix,multiplier,y,z,flowX,flowA,flowB,encode_a] using h (flowIndex 0 r e)
  · intro r e
    simpa only [step,flow,StepFree.multiplier,StepFree.y,StepFree.z,rawMatrix,multiplier,y,z,flowX,flowA,flowB,encode_b] using h (flowIndex 1 r e)

lemma encode_bound (c : StepFree n m) (F : FlowPoint n m) {R : ℝ}
    (hR : 0 ≤ R) (hc : c.Bounded R) (hF : F.Bounded R) : ∀i, |encode c F i| ≤ R := by
  intro i
  unfold encode
  cases h : (index n m).symm i with
  | inl ij => exact hc.1 ij.1 ij.2
  | inr w =>
    cases w with
    | inl ijk => dsimp only; split_ifs <;> first | exact hc.2.1 _ | simpa using hR
    | inr w =>
      cases w with
      | inl pe => dsimp only; split_ifs <;> first | exact hc.2.2.1 _ | exact hc.2.2.2 _ | exact hF.1 _
      | inr pre => dsimp only; split_ifs <;> first | exact hF.2.1 _ _ | exact hF.2.2 _ _

lemma dimension_bound (n m : ℕ) : dimension n m ≤ (n+m+2)^3 := by
  unfold dimension
  nlinarith [Nat.zero_le (n*n*m),Nat.zero_le (n*m*m),Nat.zero_le (m*m*m)]

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
