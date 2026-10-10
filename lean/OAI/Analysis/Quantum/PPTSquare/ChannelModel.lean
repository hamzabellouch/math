import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import OAI.Analysis.Quantum.PPTSquare.SplittingField
import OAI.Analysis.Quantum.PPTSquare.Directions

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
namespace ChannelCompletion

abbrev Mat (n : Type) := Matrix n n ℂ
abbrev Map (n m : Type) := Mat n →ₗ[ℂ] Mat m

variable {n m p : Type} [Fintype n] [Fintype m] [Fintype p]

def amplify (F : Map n m) {k : Type} (X : Mat (k × n)) : Mat (k × m) :=
  fun a b => F (fun i j => X (a.1, i) (b.1, j)) a.2 b.2

def choi [DecidableEq n] (F : Map n m) : Mat (n × m) :=
  fun a b => F (Matrix.single a.1 b.1 1) a.2 b.2

def CP (F : Map n m) : Prop :=
  ∀ (k : Type) [Fintype k] (X : Mat (k × n)), X.PosSemidef → (amplify F X).PosSemidef

def transposeMap : Map n n where
  toFun := Matrix.transpose
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def PPT (F : Map n m) : Prop := CP F ∧ CP (transposeMap.comp F)

def TracePreserving (F : Map n m) : Prop := ∀ X, Matrix.trace (F X) = Matrix.trace X

def Separable (Z : Mat (n × m)) : Prop :=
  ∃ (r : ℕ) (A : Fin r → Mat n) (B : Fin r → Mat m),
    (∀ i, (A i).PosSemidef) ∧ (∀ i, (B i).PosSemidef) ∧
    Z = ∑ i, A i ⊗ₖ B i

def EntanglementBreaking (F : Map n m) : Prop :=
  CP F ∧ ∀ (k : Type) [Fintype k] (X : Mat (k × n)),
    X.PosSemidef → Separable (amplify F X)

def ad (V : Matrix m n ℂ) : Map n m where
  toFun X := V * X * Vᴴ
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

def effect [DecidableEq n] (F : Map n m) : Mat n :=
  fun i j => Matrix.trace (F (Matrix.single j i 1))

def coefficient [DecidableEq n] (F : Map n m) : ℝ :=
  1 / (1 + (Matrix.trace (effect F)).re)

def defect [DecidableEq n] (F : Map n m) : Mat n :=
  1 - (coefficient F : ℂ) • effect F

abbrev Space (d : ℕ) := (Fin d ⊕ Fin d) ⊕ Unit

def first (d : ℕ) (i : Fin d) : Space d := Sum.inl (Sum.inl i)
def second (d : ℕ) (i : Fin d) : Space d := Sum.inl (Sum.inr i)
def flag (d : ℕ) : Space d := Sum.inr ()

def coord {a b : Type} [DecidableEq b] (e : a → b) : Matrix b a ℂ :=
  fun x i => if x = e i then 1 else 0

def W0 (d : ℕ) : Matrix (Space d) (Fin d) ℂ := coord (first d)
def W1 (d : ℕ) : Matrix (Space d) (Fin d) ℂ := coord (second d)
def flagProjection (d : ℕ) : Mat (Space d) := Matrix.single (flag d) (flag d) 1

def theta (d : ℕ) (F G : Map (Fin d) (Fin d)) : Map (Space d) (Space d) where
  toFun X :=
    (coefficient G : ℂ) • (ad (W0 d) (G (W1 d |> fun W => Wᴴ * X * W))) +
    (coefficient F : ℂ) • (ad (W1 d) (F (W0 d |> fun W => Wᴴ * X * W))) +
    (Matrix.trace (defect F * ((W0 d)ᴴ * X * W0 d)) +
     Matrix.trace (defect G * ((W1 d)ᴴ * X * W1 d)) +
     X (flag d) (flag d)) • flagProjection d
  map_add' X Y := by
    simp only [Matrix.mul_add, Matrix.add_mul, map_add, Matrix.trace_add,
      Matrix.add_apply, smul_add, add_smul]
    abel
  map_smul' c X := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, map_smul, Matrix.trace_smul,
      Matrix.smul_apply, smul_eq_mul, smul_add, smul_smul, RingHom.id_apply]
    congr 1
    · module
    · module

end ChannelCompletion

namespace ChannelCompletion
variable {n m p : Type} [Fintype n] [Fintype m] [Fintype p]

omit [Fintype m] in
@[simp] theorem ad_apply (V : Matrix m n ℂ) (X : Mat n) : ad V X = V * X * Vᴴ := rfl
omit [Fintype n] in
@[simp] theorem transposeMap_apply (X : Mat n) : transposeMap X = Xᵀ := rfl

omit [Fintype m] in
lemma amplify_ad {k : Type} [Fintype k] [DecidableEq k]
    (V : Matrix m n ℂ) (X : Mat (k × n)) :
    amplify (ad V) X = ((1 : Mat k) ⊗ₖ V) * X * ((1 : Mat k) ⊗ₖ V)ᴴ := by
  ext a b
  rcases a with ⟨a,i⟩
  rcases b with ⟨b,j⟩
  change (∑ r : n, (∑ s : n, V i s * X (a,s) (b,r)) * star (V j r)) =
    ∑ r : k × n, (∑ s : k × n, ((1 : Mat k) a s.1 * V i s.2) * X s r) *
      star ((1 : Mat k) b r.1 * V j r.2)
  simp [Fintype.sum_prod_type, Matrix.one_apply, ite_mul, apply_ite,
    Finset.sum_mul]

lemma cp_ad (V : Matrix m n ℂ) : CP (ad V) := by
  intro k _ X hX
  classical
  rw [amplify_ad]
  exact hX.mul_mul_conjTranspose_same _

omit [Fintype n] [Fintype m] [Fintype p] in
lemma cp_comp {F : Map n m} {G : Map m p} (hG : CP G) (hF : CP F) : CP (G.comp F) := by
  intro k _ X hX
  exact hG k (amplify F X) (hF k X hX)

omit [Fintype n] [Fintype m] in
lemma cp_add {F G : Map n m} (hF : CP F) (hG : CP G) : CP (F + G) := by
  intro k _ X hX
  exact (hF k X hX).add (hG k X hX)

omit [Fintype n] [Fintype m] in
lemma cp_smul {F : Map n m} (hF : CP F) {c : ℝ} (hc : 0 ≤ c) :
    CP ((c : ℂ) • F) := by
  intro k _ X hX
  exact (hF k X hX).smul (show (0 : ℂ) ≤ c by exact_mod_cast hc)

def omega [DecidableEq n] : n × n → ℂ := fun a => if a.1 = a.2 then 1 else 0

omit [Fintype n] [Fintype m] in
lemma amplify_omega [DecidableEq n] (F : Map n m) :
    amplify F (Matrix.vecMulVec (omega (n := n)) (star omega)) = choi F := by
  ext ⟨i,a⟩ ⟨j,b⟩
  change F _ a b = F _ a b
  apply congrArg (fun X : Mat n => F X a b)
  ext x y
  simp only [Matrix.vecMulVec_apply, omega, Pi.star_apply, Matrix.single_apply]
  by_cases hix : i = x <;> by_cases hjy : j = y <;> simp [hix, hjy]

omit [Fintype m] in
lemma cp_choi [DecidableEq n] {F : Map n m} (hF : CP F) : (choi F).PosSemidef := by
  rw [← amplify_omega]
  exact hF n _ (Matrix.posSemidef_vecMulVec_self_star _)

omit [Fintype m] in
lemma eb_choi [DecidableEq n] {F : Map n m} (hF : EntanglementBreaking F) :
    Separable (choi F) := by
  rw [← amplify_omega]
  exact hF.2 n _ (Matrix.posSemidef_vecMulVec_self_star _)

omit [Fintype n] in
lemma effect_eq_sum [DecidableEq n] (F : Map n m) :
    effect F = ∑ a : m, (choi F)ᵀ.submatrix (fun i => (i,a)) (fun i => (i,a)) := by
  ext i j
  simp [effect, choi, Matrix.trace, Matrix.sum_apply]

lemma effect_psd [DecidableEq n] {F : Map n m} (hF : CP F) : (effect F).PosSemidef := by
  rw [effect_eq_sum]
  exact Matrix.posSemidef_sum _ (fun a _ => (cp_choi hF).transpose.submatrix _)

lemma effect_trace [DecidableEq n] (F : Map n m) (X : Mat n) :
    Matrix.trace (effect F * X) = Matrix.trace (F X) := by
  induction X using Matrix.induction_on' with
  | h_zero => simp
  | h_add X Y hX hY => simp [Matrix.mul_add, hX, hY]
  | h_std_basis i j c =>
    rw [Matrix.trace_mul_single]
    have he : Matrix.single i j c = c • Matrix.single i j (1 : ℂ) := by
      simp [Matrix.smul_single]
    rw [he, map_smul, Matrix.trace_smul]
    change Matrix.trace (F (Matrix.single i j 1)) * c =
      c * Matrix.trace (F (Matrix.single i j 1))
    exact mul_comm _ _

lemma coefficient_pos [DecidableEq n] {F : Map n m} (hF : CP F) :
    0 < coefficient F := by
  have h := Complex.nonneg_iff.mp (effect_psd hF).trace_nonneg
  exact one_div_pos.mpr (by linarith [h.1])

end ChannelCompletion

end

end OAI
