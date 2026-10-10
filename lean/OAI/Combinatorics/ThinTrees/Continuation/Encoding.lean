import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.Domain
import OAI.Combinatorics.ThinTrees.Metric.ConeRepresentation

namespace OAI

/-! Continuation encoding. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n m : ℕ}

def responseMatrix (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  centered ((1/2 : ℝ) • (A+Aᵀ))

lemma responseMatrix_hermitian (A : Matrix (Fin n) (Fin n) ℝ) :
    (responseMatrix A).IsHermitian := by
  apply isHermitian_iff_isSymm.mpr
  simp only [responseMatrix,centered,IsSymm,transpose_mul,transpose_smul,transpose_add,
    transpose_transpose,centering_symmetric]
  rw [add_comm Aᵀ A,mul_assoc]

lemma responseMatrix_ones (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) :
    responseMatrix A *ᵥ ones n=0 := centered_ones hn _

lemma responseMatrix_fixed {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hA0 : A *ᵥ ones n=0) : responseMatrix A=A := by
  rw [responseMatrix,(isHermitian_iff_isSymm.mp hA).eq,
    show (1/2 : ℝ) • (A+A)=A by module,centered_eq hA hA0]

lemma responseMatrix_add (A B : Matrix (Fin n) (Fin n) ℝ) :
    responseMatrix (A+B)=responseMatrix A+responseMatrix B := by
  simp only [responseMatrix,transpose_add,centered,smul_add,mul_add,add_mul]
  abel

lemma responseMatrix_smul (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    responseMatrix (c • A)=c • responseMatrix A := by
  simp only [responseMatrix,transpose_smul,←smul_add,smul_comm (1/2:ℝ) c,
    centered,mul_smul_comm,smul_mul_assoc]

lemma responseMatrix_sub (A B : Matrix (Fin n) (Fin n) ℝ) :
    responseMatrix (A-B)=responseMatrix A-responseMatrix B := by
  simp only [responseMatrix,transpose_sub,centered,smul_sub,mul_sub,sub_mul,smul_add,mul_add,add_mul]
  abel

abbrev StepFree (n m : ℕ) :=
  Matrix (Fin n) (Fin n) ℝ × (DistinctTriple n → ℝ) × (Fin m → ℝ) × (Fin m → ℝ)

namespace StepFree

def matrix (x : StepFree n m) : Matrix (Fin n) (Fin n) ℝ := responseMatrix x.1
def multiplier (x : StepFree n m) : DistinctTriple n → ℝ := x.2.1
def y (x : StepFree n m) : Fin m → ℝ := x.2.2.1
def z (x : StepFree n m) : Fin m → ℝ := x.2.2.2

def capacities (κ : ℝ) (u : Fin m → ℝ) (x : StepFree n m) : Fin m → ℝ :=
  fun e => if 0 < u e then x.z e else κ

def lowerPencil (H : MultiGraph n m) (x : StepFree n m) := x.matrix-H.laplacian univ
def upperPencil (H : MultiGraph n m) (x : StepFree n m) :=
  (3 : ℝ) • H.laplacian univ-x.matrix-∑ijk, x.multiplier ijk • triangleGenerator ijk

def edgePencil (H : MultiGraph n m) (s : ℝ) (x : StepFree n m) (e : Fin m) :=
  x.matrix-(6*s*x.y e) • vecMulVec (H.incidence e) (H.incidence e)

lemma matrix_combo (a b : ℝ) (x w : StepFree n m) :
    (a • x+b • w).matrix=a • x.matrix+b • w.matrix := by
  change responseMatrix (a • x.1+b • w.1)=_
  rw [responseMatrix_add,responseMatrix_smul,responseMatrix_smul]
  rfl

lemma lowerPencil_combo (H : MultiGraph n m) (a b : ℝ) (hab : a+b=1) (x w : StepFree n m) :
    lowerPencil H (a • x+b • w)=a • lowerPencil H x+b • lowerPencil H w := by
  rw [lowerPencil,matrix_combo,lowerPencil,lowerPencil]
  have he : a • H.laplacian univ+b • H.laplacian univ=H.laplacian univ := by rw [←add_smul,hab,one_smul]
  simp only [smul_sub]
  conv_lhs => rw [←he]
  abel

lemma upperPencil_combo (H : MultiGraph n m) (a b : ℝ) (hab : a+b=1) (x w : StepFree n m) :
    upperPencil H (a • x+b • w)=a • upperPencil H x+b • upperPencil H w := by
  have he : a • H.laplacian univ+b • H.laplacian univ=H.laplacian univ := by rw [←add_smul,hab,one_smul]
  simp only [upperPencil,matrix_combo,multiplier,Prod.fst_add,Prod.smul_fst,
    Prod.snd_add,Prod.smul_snd,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    add_smul,mul_smul,sum_add_distrib,←smul_sum,smul_sub]
  have h3 : (3 : ℝ) • H.laplacian univ =
      a • (3 : ℝ) • H.laplacian univ+b • (3 : ℝ) • H.laplacian univ := by
    rw [←add_smul,hab,one_smul]
  conv_lhs => rw [h3]
  module

lemma edgePencil_combo (H : MultiGraph n m) (s a b : ℝ) (x w : StepFree n m) (e : Fin m) :
    edgePencil H s (a • x+b • w) e=a • edgePencil H s x e+b • edgePencil H s w e := by
  simp only [edgePencil,matrix_combo,y,Prod.fst_add,Prod.smul_fst,Prod.snd_add,
    Prod.smul_snd,Pi.add_apply,Pi.smul_apply,smul_eq_mul,smul_sub,smul_smul]
  module

lemma capacities_combo (κ a b : ℝ) (hab : a+b=1) (u : Fin m → ℝ) (x w : StepFree n m) :
    capacities κ u (a • x+b • w)=a • capacities κ u x+b • capacities κ u w := by
  ext e
  simp only [capacities,z,Prod.snd_add,Prod.smul_snd,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  split_ifs
  · rfl
  · rw [←add_mul,hab,one_mul]

end StepFree

def stepCore (H : MultiGraph n m) (s κ t : ℝ) (u : Fin m → ℝ) : Set (StepFree n m) :=
  {x | (x.lowerPencil H).PosSemidef ∧ (x.upperPencil H).PosSemidef ∧
    (∀ijk, 0 ≤ x.multiplier ijk) ∧ (∀e, x.y e ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀e, x.z e ∈ Set.Icc 0 (κ+1)) ∧
    (∀e, 0 < u e → (x.edgePencil H s e).PosSemidef ∧
      x.z e ≤ κ+u e+t*(5*x.y e-4))}

def stepFeasible (H : MultiGraph n m) (s κ t q : ℝ) (u : Fin m → ℝ) : Set (StepFree n m) :=
  {x | x ∈ stepCore H s κ t u ∧ ∀p, 0 ≤ slack H.left H.right (x.capacities κ u) q p}

lemma stepCore_domain (H : MultiGraph n m) (hn : 0 < n)
    {s κ t : ℝ} {u : Fin m → ℝ} {x : StepFree n m} (hx : x ∈ stepCore H s κ t u) :
    x.matrix ∈ metricDomain H := by
  apply (metricDomain_iff_lmi H hn (responseMatrix_hermitian x.1) (responseMatrix_ones hn x.1)).mpr
  exact ⟨Matrix.le_iff.mpr hx.1,x.multiplier,hx.2.2.1,hx.2.1⟩

lemma stepCore_admissible (H : MultiGraph n m) (hn : 0 < n)
    {s κ t : ℝ} {u : Fin m → ℝ} {x : StepFree n m} (hx : x ∈ stepCore H s κ t u) :
    (x.matrix,x.y) ∈ admissible H s u :=
  ⟨stepCore_domain H hn hx,hx.2.2.2.1,fun e he => Matrix.le_iff.mpr ((hx.2.2.2.2.2 e he).1)⟩

lemma stepCore_capacity_le (H : MultiGraph n m)
    {s κ t : ℝ} {u : Fin m → ℝ} {x : StepFree n m} (hx : x ∈ stepCore H s κ t u) (e : Fin m) :
    x.capacities κ u e ≤ lowerCapacity κ t (u e) (x.y e) := by
  unfold StepFree.capacities lowerCapacity
  split_ifs with he
  · rw [add_min]
    exact le_min (hx.2.2.2.2.1 e).2 (by simpa only [add_assoc] using (hx.2.2.2.2.2 e he).2)
  · exact le_rfl

lemma stepFeasible_response (H : MultiGraph n m) (hn : 0 < n)
    {s κ t q : ℝ} {u : Fin m → ℝ} {x : StepFree n m} (hx : x ∈ stepFeasible H s κ t q u) :
    (x.matrix,x.y) ∈ admissible H s u ∧
      ∀p, 0 ≤ responseSlack H κ t q u p (x.matrix,x.y) := by
  refine ⟨stepCore_admissible H hn hx.1,fun p => (hx.2 p).trans ?_⟩
  unfold responseSlack slack capacity
  apply sub_le_sub_right
  exact sum_le_sum (fun e _ => mul_le_mul_of_nonneg_right
    (stepCore_capacity_le H hx.1 e) (crossingIndicator_nonneg _ _ _))

lemma response_to_stepFeasible (H : MultiGraph n m) (hn : 0 < n)
    {s κ t q : ℝ} {u : Fin m → ℝ} (ht : 0 ≤ t) (hκt : 4*t ≤ κ)
    {w : ResponseSpace n m} (hw : w ∈ admissible H s u)
    (hp : ∀p, 0 ≤ responseSlack H κ t q u p w) :
    ∃x ∈ stepFeasible H s κ t q u, x.matrix=w.1 ∧ x.y=w.2 := by
  obtain ⟨_,lam,hlam,hP⟩ := (metricDomain_iff_lmi H hn hw.1.1 hw.1.2.1).mp hw.1
  let z : Fin m → ℝ := fun e => lowerCapacity κ t (u e) (w.2 e)
  let x : StepFree n m := (w.1,lam,w.2,z)
  have hmat : x.matrix=w.1 := responseMatrix_fixed hw.1.1 hw.1.2.1
  have hcap : x.capacities κ u=z := by
    ext e
    simp only [StepFree.capacities,StepFree.z,x]
    split_ifs with he
    · rfl
    · simp only [z,lowerCapacity,ite_eq_right he]
  refine ⟨x,⟨?_,?_⟩,hmat,rfl⟩
  · refine ⟨?_,?_,hlam,hw.2.1,?_,?_⟩
    · simpa only [StepFree.lowerPencil,hmat] using Matrix.le_iff.mp hw.1.2.2.1
    · simpa only [StepFree.upperPencil,hmat,StepFree.multiplier,x] using hP
    · intro e
      exact ⟨lowerCapacity_nonneg ht (hw.2.1 e).1 hκt,lowerCapacity_le⟩
    · intro e he
      refine ⟨?_,?_⟩
      · simpa only [StepFree.edgePencil,hmat,StepFree.y,x] using Matrix.le_iff.mp (hw.2.2 e he)
      · change lowerCapacity κ t (u e) (w.2 e) ≤ _
        rw [lowerCapacity,ite_eq_left he]
        change κ+min 1 (u e+t*(5*w.2 e-4)) ≤ κ+u e+t*(5*w.2 e-4)
        linarith only [min_le_right (1 : ℝ) (u e+t*(5*w.2 e-4))]
  · intro p
    rw [hcap]
    exact hp p

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
