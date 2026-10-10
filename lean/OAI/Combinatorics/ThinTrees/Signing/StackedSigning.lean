import Mathlib
import OAI.Combinatorics.ThinTrees.Signing.RationalSigning

namespace OAI

/-! Stacked signing. -/

section

namespace AlgorithmicThinTrees.StackedSigning
open Matrix Finset
open scoped MatrixOrder
variable {a b m : ℕ}

def stack {K : Type*} (u : Fin a → K) (v : Fin b → K) : Fin (a+b) → K :=
  Fin.addCases u v

@[simp] lemma stack_left {K : Type*} (u : Fin a → K) (v : Fin b → K) (i : Fin a) :
    stack u v (Fin.castAdd b i)=u i := Fin.addCases_left i

@[simp] lemma stack_right {K : Type*} (u : Fin a → K) (v : Fin b → K) (i : Fin b) :
    stack u v (Fin.natAdd a i)=v i := Fin.addCases_right i

lemma dot_stack (x : Fin (a+b) → ℝ) (u : Fin a → ℝ) (v : Fin b → ℝ) :
    x ⬝ᵥ stack u v = (fun i => x (Fin.castAdd b i)) ⬝ᵥ u +
      (fun i => x (Fin.natAdd a i)) ⬝ᵥ v := by
  simp only [dotProduct,Fin.sum_univ_add,stack_left,stack_right]

lemma stack_norm (u : Fin a → ℝ) (v : Fin b → ℝ) :
    stack u v ⬝ᵥ stack u v=u ⬝ᵥ u+v ⬝ᵥ v := by
  simp only [dot_stack,stack_left,stack_right]

def gram {d : ℕ} (v : Fin m → Fin d → ℝ) (A : Finset (Fin m)) : Matrix (Fin d) (Fin d) ℝ :=
  ∑e∈A, vecMulVec (v e) (v e)

lemma gram_psd {d : ℕ} (v : Fin m → Fin d → ℝ) (A : Finset (Fin m)) :
    (gram v A).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro e _
  simpa only [star_trivial] using posSemidef_vecMulVec_self_star (v e)

lemma gram_eval {d : ℕ} (v : Fin m → Fin d → ℝ) (A : Finset (Fin m)) (x : Fin d → ℝ) :
    x ⬝ᵥ (gram v A*ᵥx)=∑e∈A,(x ⬝ᵥ v e)^2 := by
  simp only [gram,Matrix.sum_mulVec,dotProduct_sum,vecMulVec_mulVec,dotProduct_smul]
  apply sum_congr rfl
  intro e _
  rw [dotProduct_comm (v e) x,pow_two]
  rfl

lemma gram_eval_le {d : ℕ} (v : Fin m → Fin d → ℝ) (A : Finset (Fin m))
    {c : ℝ} (h : gram v A ≤ c • (1 : Matrix (Fin d) (Fin d) ℝ)) (x : Fin d → ℝ) :
    (∑e∈A,(x ⬝ᵥ v e)^2) ≤ c*(x ⬝ᵥ x) := by
  have hh := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg x
  simp only [star_trivial,Matrix.sub_mulVec,dotProduct_sub,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_smul,smul_eq_mul,gram_eval] at hh
  linarith only [hh]

lemma stack_covariance (u : Fin m → Fin a → ℝ) (v : Fin m → Fin b → ℝ)
    (hu : gram u univ ≤ 1) (hv : gram v univ ≤ 1) :
    gram (fun e => stack (u e) (v e)) univ ≤ (2:ℝ) • 1 := by
  rw [Matrix.le_iff]
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (Matrix.PosSemidef.one.smul (by norm_num : (0:ℝ) ≤ 2)).isHermitian.sub
      (gram_psd _ _).isHermitian
  intro x
  simp only [star_trivial,Matrix.sub_mulVec,dotProduct_sub,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_smul,smul_eq_mul,gram_eval]
  have h1 := gram_eval_le u univ (c:=1) (by simpa only [one_smul] using hu)
    (fun i => x (Fin.castAdd b i))
  have h2 := gram_eval_le v univ (c:=1) (by simpa only [one_smul] using hv)
    (fun i => x (Fin.natAdd a i))
  have hs : (∑e : Fin m, (x ⬝ᵥ stack (u e) (v e))^2) ≤
      2*(∑e : Fin m, ((fun i => x (Fin.castAdd b i)) ⬝ᵥ u e)^2)+
        2*(∑e : Fin m, ((fun i => x (Fin.natAdd a i)) ⬝ᵥ v e)^2) := by
    rw [mul_sum,mul_sum,←sum_add_distrib]
    apply sum_le_sum
    intro e _
    rw [dot_stack]
    nlinarith only [sq_nonneg (((fun i => x (Fin.castAdd b i)) ⬝ᵥ u e)-
      ((fun i => x (Fin.natAdd a i)) ⬝ᵥ v e))]
  have hx : x ⬝ᵥ x=(fun i => x (Fin.castAdd b i)) ⬝ᵥ (fun i => x (Fin.castAdd b i))+
      (fun i => x (Fin.natAdd a i)) ⬝ᵥ (fun i => x (Fin.natAdd a i)) := by
    exact Fin.sum_univ_add _
  nlinarith only [h1,h2,hs,hx]

lemma submatrix_mono {d e : ℕ} {A B : Matrix (Fin d) (Fin d) ℝ} (h : A ≤ B)
    (f : Fin e → Fin d) : A.submatrix f f ≤ B.submatrix f f := by
  rw [Matrix.le_iff]
  exact (Matrix.le_iff.mp h).submatrix f

lemma gram_submatrix {d e : ℕ} (v : Fin m → Fin d → ℝ) (A : Finset (Fin m))
    (f : Fin e → Fin d) :
    (gram v A).submatrix f f=gram (fun j i => v j (f i)) A := by
  ext i j
  simp only [gram,submatrix_apply,Matrix.sum_apply,vecMulVec_apply]

lemma compress_half {d e : ℕ} (v : Fin m → Fin d → ℝ) (A : Finset (Fin m))
    (f : Fin e → Fin d) (hf : Function.Injective f) {ε : ℝ}
    (h : -(ε • (1 : Matrix (Fin d) (Fin d) ℝ)) ≤ gram v A-(1/2:ℝ) • gram v univ ∧
      gram v A-(1/2:ℝ) • gram v univ ≤ ε • 1) :
    -(ε • (1 : Matrix (Fin e) (Fin e) ℝ)) ≤
        gram (fun j i => v j (f i)) A-(1/2:ℝ) • gram (fun j i => v j (f i)) univ ∧
      gram (fun j i => v j (f i)) A-(1/2:ℝ) • gram (fun j i => v j (f i)) univ ≤ ε • 1 := by
  have h1 := submatrix_mono h.1 f
  have h2 := submatrix_mono h.2 f
  change -(ε • (1 : Matrix (Fin d) (Fin d) ℝ).submatrix f f) ≤
    (gram v A).submatrix f f-(1/2:ℝ) • (gram v univ).submatrix f f at h1
  change (gram v A).submatrix f f-(1/2:ℝ) • (gram v univ).submatrix f f ≤
    ε • (1 : Matrix (Fin d) (Fin d) ℝ).submatrix f f at h2
  simpa only [submatrix_one f hf,gram_submatrix] using And.intro h1 h2

def selected (u : Fin m → Fin a → ℚ) (v : Fin m → Fin b → ℚ) : Finset (Fin m) :=
  RationalSigning.selected (fun e => stack (u e) (v e))

lemma real_stack (u : Fin m → Fin a → ℚ) (v : Fin m → Fin b → ℚ) (e : Fin m) :
    RationalSigning.realVec (fun e => stack (u e) (v e)) e=
      stack (RationalSigning.realVec u e) (RationalSigning.realVec v e) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [RationalSigning.realVec,stack_left,stack_right]

theorem simultaneous (u : Fin m → Fin a → ℚ) (v : Fin m → Fin b → ℚ) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hu : gram (RationalSigning.realVec u) univ ≤ 1)
    (hv : gram (RationalSigning.realVec v) univ ≤ 1)
    (hnorm : ∀e, RationalSigning.realVec u e ⬝ᵥ RationalSigning.realVec u e+
      RationalSigning.realVec v e ⬝ᵥ RationalSigning.realVec v e ≤ δ) :
    let A := selected u v
    let ε := 20*Real.sqrt (2*δ)
    (-(ε • (1 : Matrix (Fin a) (Fin a) ℝ)) ≤
        gram (RationalSigning.realVec u) A-(1/2:ℝ) • gram (RationalSigning.realVec u) univ ∧
      gram (RationalSigning.realVec u) A-(1/2:ℝ) • gram (RationalSigning.realVec u) univ ≤ ε • 1) ∧
    (-(ε • (1 : Matrix (Fin b) (Fin b) ℝ)) ≤
        gram (RationalSigning.realVec v) A-(1/2:ℝ) • gram (RationalSigning.realVec v) univ ∧
      gram (RationalSigning.realVec v) A-(1/2:ℝ) • gram (RationalSigning.realVec v) univ ≤ ε • 1) := by
  have hcov := stack_covariance (RationalSigning.realVec u) (RationalSigning.realVec v) hu hv
  have hs := RationalSigning.half_bounds (fun e => stack (u e) (v e)) hδ (by norm_num : (0:ℝ) ≤ 2)
    (by simpa only [RationalSigning.outer,real_stack,gram] using hcov)
    (fun e => by simpa only [real_stack,stack_norm] using hnorm e)
  change (-(20*Real.sqrt (2*δ))) • (1 : Matrix (Fin (a+b)) (Fin (a+b)) ℝ) ≤ _ ∧ _ at hs
  simp only [neg_smul] at hs
  have hl := compress_half _ (selected u v) (Fin.castAdd b) (Fin.castAdd_injective a b) hs
  have hr := compress_half _ (selected u v) (Fin.natAdd a) (Fin.natAdd_injective b a) hs
  simpa only [real_stack,stack_left,stack_right] using And.intro hl hr

end AlgorithmicThinTrees.StackedSigning
end

end OAI
