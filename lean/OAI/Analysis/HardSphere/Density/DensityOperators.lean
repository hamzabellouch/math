import OAI.Analysis.HardSphere.CondensationDefinitions

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace NNReal ENNReal
namespace HardSphere.Density

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H}

def Operator.root (T : Operator H) : H →L[ℂ] H := CFC.sqrt T.toCLM

lemma Operator.root_positive (T : Operator H) : T.root.IsPositive :=
  ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg _)

lemma Operator.root_sq (T : Operator H) : T.root*T.root=T.toCLM :=
  CFC.sqrt_mul_sqrt_self _ T.positive

lemma Operator.root_norm_sq (T : Operator H) (x : H) :
    ‖T.root x‖^2=(inner ℂ x (T.toCLM x)).re := by
  calc
    _ = (inner ℂ (T.root x) (T.root x)).re := by exact norm_sq_eq_re_inner (𝕜:=ℂ) _
    _ = (inner ℂ x (T.root (T.root x))).re := congrArg Complex.re (T.root_positive.isSymmetric x (T.root x))
    _ = _ := by rw [←mul_apply_eq_comp,T.root_sq]

lemma Operator.root_hasSum (T : Operator H) :
    HasSum (fun i : basisSet H ↦ ‖T.root (basis H i)‖^2) 1 := by
  simpa only [T.root_norm_sq] using T.trace_one

lemma Operator.root_mem_support (T : Operator H) (x : H) :
    T.root x∈T.toCLM.kerᗮ := by
  rw [Submodule.mem_orthogonal']
  intro y hy
  have hy0 : T.toCLM y=0 := hy
  have hr : T.root y=0 := by
    have hh := T.root_norm_sq y
    rw [hy0,inner_zero_right,Complex.zero_re] at hh
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hh)
  have hs : inner ℂ (T.root x) y=inner ℂ x (T.root y) := T.root_positive.isSymmetric x y
  rw [hs,hr,inner_zero_right]

end HardSphere.Density

namespace HardSphere.Density
open ContinuousLinearMap

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] in
lemma parseval {ι : Type*} (b : HilbertBasis ι ℂ H) (x : H) :
    HasSum (fun i ↦ ‖inner ℂ (b i) x‖^2) (‖x‖^2) := by
  simpa [HilbertBasis.repr_apply_apply] using lp.hasSum_norm (p:=2) (by norm_num) (b.repr x)

omit [CompleteSpace K] in
lemma Operator.image_summable (T : Operator H) (A : H →L[ℂ] K) :
    Summable (fun i : basisSet H ↦ ‖A (T.root (basis H i))‖^2) := by
  apply Summable.of_nonneg_of_le (fun _ ↦ sq_nonneg _)
    (fun i ↦ ?_) (T.root_hasSum.summable.mul_left (‖A‖^2))
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm (T.root (basis H i))) 2


lemma Operator.compression_diagonal (T : Operator H) (A : H →L[ℂ] K) (x : K) :
    (inner ℂ x ((A ∘L T.toCLM ∘L A.adjoint) x)).re=
      (inner ℂ (A.adjoint x) (T.toCLM (A.adjoint x))).re := by
  rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,←A.adjoint_inner_left]

def Operator.entry {ι : Type*} (T : Operator H) (A : H →L[ℂ] K)
    (b : HilbertBasis ι ℂ K) (i : basisSet H) (j : ι) : ℝ :=
  ‖inner ℂ (b j) (A (T.root (basis H i)))‖^2

omit [CompleteSpace K] in
lemma Operator.entry_row {ι : Type*} (T : Operator H) (A : H →L[ℂ] K)
    (b : HilbertBasis ι ℂ K) (i : basisSet H) :
    HasSum (T.entry A b i) (‖A (T.root (basis H i))‖^2) :=
  parseval (H:=K) b (A (T.root (basis H i)))

lemma Operator.entry_col {ι : Type*} (T : Operator H) (A : H →L[ℂ] K)
    (b : HilbertBasis ι ℂ K) (j : ι) :
    HasSum (fun i ↦ T.entry A b i j) (‖T.root (A.adjoint (b j))‖^2) := by
  have hh := parseval (basis H) (T.root (A.adjoint (b j)))
  convert hh using 1
  funext i
  dsimp only [Operator.entry]
  have ha : inner ℂ (b j) (A (T.root (basis H i)))=
      inner ℂ (A.adjoint (b j)) (T.root (basis H i)) := (A.adjoint_inner_left _ _).symm
  have ht : inner ℂ (A.adjoint (b j)) (T.root (basis H i))=
      inner ℂ (T.root (A.adjoint (b j))) (basis H i) := (T.root_positive.isSymmetric _ _).symm
  rw [ha,ht,norm_inner_symm]

omit [CompleteSpace K] in
lemma Operator.entry_summable {ι : Type*} (T : Operator H) (A : H →L[ℂ] K)
    (b : HilbertBasis ι ℂ K) : Summable (Function.uncurry (T.entry A b)) := by
  apply (summable_prod_of_nonneg (fun p ↦ sq_nonneg _)).mpr
  refine ⟨fun i ↦ (T.entry_row A b i).summable,?_⟩
  convert T.image_summable A using 1
  funext i
  exact (T.entry_row A b i).tsum_eq

lemma Operator.trace_basis_identity {ι : Type*} (T : Operator H) (A : H →L[ℂ] K)
    (b : HilbertBasis ι ℂ K) :
    (∑' i : basisSet H,‖A (T.root (basis H i))‖^2)=
      ∑' j : ι,(inner ℂ (A.adjoint (b j)) (T.toCLM (A.adjoint (b j)))).re := by
  calc
    _ = ∑' i : basisSet H,∑' j : ι,T.entry A b i j :=
      tsum_congr fun i ↦ (T.entry_row A b i).tsum_eq.symm
    _ = ∑' j : ι,∑' i : basisSet H,T.entry A b i j := (T.entry_summable A b).tsum_comm.symm
    _ = ∑' j : ι,‖T.root (A.adjoint (b j))‖^2 :=
      tsum_congr fun j ↦ (T.entry_col A b j).tsum_eq
    _ = _ := by simp only [T.root_norm_sq]

lemma Operator.compressionTrace_eq (T : Operator H) (A : H →L[ℂ] K) :
    T.compressionTrace A=∑' i : basisSet H,‖A (T.root (basis H i))‖^2 :=
  (T.trace_basis_identity A (basis K)).symm

lemma Operator.trace_independent {ι : Type*} (T : Operator H) (b : HilbertBasis ι ℂ H) :
    (∑' j : ι,(inner ℂ (b j) (T.toCLM (b j))).re)=1 := by
  have hh := T.trace_basis_identity (ContinuousLinearMap.id ℂ H) b
  simpa only [ContinuousLinearMap.adjoint_id,ContinuousLinearMap.id_apply,T.root_hasSum.tsum_eq] using hh.symm

end HardSphere.Density
end

end OAI
