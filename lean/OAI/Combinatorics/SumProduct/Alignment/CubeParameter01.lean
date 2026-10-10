import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.BooleanRough02
import OAI.Combinatorics.SumProduct.Alignment.RoughRational01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
noncomputable section
open Finset
open scoped BigOperators
end

end
 

section
 
 

noncomputable section
open Finset
open scoped BigOperators
namespace CubeParameter
open RealPolynomialDegree RoughPolynomialDegree Combinatorics

def realVertex {n : ℕ} (z : Fin n → Bool) : Fin n → ℝ := fun i => if z i then 1 else 0

def vertexSet {n : ℕ} (z : Fin n → Bool) : Finset (Fin n) := univ.filter (fun i => z i)

lemma mem_vertexSet {n : ℕ} (z : Fin n → Bool) (i : Fin n) : i ∈ vertexSet z ↔ z i := by
  simp [vertexSet]

lemma vertex_to_set {n : ℕ} (z : Fin n → Bool) :
    realVertex z = fun i => if i ∈ vertexSet z then 1 else 0 := by
  ext i
  simp [realVertex, mem_vertexSet]

lemma realVertex_set {n : ℕ} (S : Finset (Fin n)) :
    realVertex (fun i => decide (i ∈ S)) = fun i => if i ∈ S then 1 else 0 := by
  ext i
  simp [realVertex]

lemma realVertex_degree {n : ℕ} (f : (Fin n → ℝ) → ℝ) (q : ℕ) (hf : HasDegree f q) :
    ∃ θ : Finset (Fin n) → ℝ, BooleanRough.DegreeLE q θ ∧
      ∀ z, BooleanRough.Eval θ (vertexSet z) = f (realVertex z) := by
  obtain ⟨p, hp, he⟩ := hf
  refine ⟨BooleanRough.BoolCoeffs p, ?_, ?_⟩
  · intro S hS
    exact BooleanRough.degree_boolCoeffs p S (by omega)
  · intro z
    rw [BooleanRough.eval_boolCoeffs, ← vertex_to_set, ← he]

lemma degree_append {n v : ℕ} (x : Fin v → ℝ) (i : Fin (n+v)) :
    HasDegree (fun z : Fin n → ℝ => Fin.append z x i) 1 := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa using coordinate j
  · intro j
    simpa using RealPolynomialDegree.const (σ:=Fin n) (x j) 1

lemma degree_parameter_restrict {n v q : ℕ} {f : (Fin (n+v) → ℝ) → ℝ}
    (hf : HasDegree f q) (x : Fin v → ℝ) :
    HasDegree (fun z : Fin n → ℝ => f (Fin.append z x)) q := by
  simpa using compose hf (fun i z => Fin.append z x i) (degree_append x)

lemma degree_space_restrict {n v q : ℕ} {f : (Fin (n+v) → ℝ) → ℝ}
    (hf : HasDegree f q) (z : Fin n → ℝ) :
    HasDegree (fun x : Fin v → ℝ => f (Fin.append z x)) q := by
  have hh := compose hf (fun i (x : Fin v → ℝ) => Fin.append z x i) (e:=1) (by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa using RealPolynomialDegree.const (σ:=Fin v) (z j) 1
    · intro j
      simpa using coordinate j)
  simpa using hh

def lift {n N v : ℕ} (l : Subspace (Fin n) Bool (Fin N))
    (y : Fin (n+v) → ℝ) : Fin (N+v) → ℝ :=
  Fin.append (fun i => match l.idxFun i with
    | Sum.inl b => if b then 1 else 0
    | Sum.inr j => y (j.castAdd v)) (fun i => y (i.natAdd n))

lemma lift_degree {n N v : ℕ} (l : Subspace (Fin n) Bool (Fin N)) (i : Fin (N+v)) :
    HasDegree (fun y => lift (v:=v) l y i) 1 := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [lift, Fin.append_left]
    cases hj : l.idxFun j with
    | inl b => exact RealPolynomialDegree.const _ _
    | inr k => exact coordinate _
  · intro j
    simpa [lift] using coordinate (j.natAdd n)

lemma lift_vertex {n N v : ℕ} (l : Subspace (Fin n) Bool (Fin N))
    (z : Fin n → Bool) (x : Fin v → ℝ) :
    lift l (Fin.append (realVertex z) x) = Fin.append (realVertex (l z)) x := by
  ext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [lift, Fin.append_left, Fin.append_right, realVertex, Subspace.coe_apply]
    split <;> rename_i h <;> simp [h]
  · intro j
    simp [lift]

lemma degree_lift {n N v q : ℕ} (l : Subspace (Fin n) Bool (Fin N))
    {f : (Fin (N+v) → ℝ) → ℝ} (hf : HasDegree f q) :
    HasDegree (fun y : Fin (n+v) → ℝ => f (lift l y)) q := by
  simpa using compose hf (fun i y => lift l y i) (lift_degree l)

lemma vertexSet_decide {n : ℕ} (S : Finset (Fin n)) :
    vertexSet (fun i => decide (i ∈ S)) = S := by
  ext i
  simp [vertexSet]

def parameterLift {n N : ℕ} (l : Subspace (Fin n) Bool (Fin N))
    (z : Fin n → ℝ) (i : Fin N) : ℝ :=
  (l.idxFun i).elim (fun b => if b then 1 else 0) z

lemma parameterLift_degree {n N : ℕ} (l : Subspace (Fin n) Bool (Fin N)) (i : Fin N) :
    HasDegree (fun z => parameterLift l z i) 1 := by
  unfold parameterLift
  cases l.idxFun i with
  | inl b => exact RealPolynomialDegree.const _ _
  | inr j => exact coordinate _

lemma parameterLift_vertex {n N : ℕ} (l : Subspace (Fin n) Bool (Fin N)) (z : Fin n → Bool) :
    parameterLift l (realVertex z) = realVertex (l z) := by
  ext i
  change (l.idxFun i).elim (fun b => if b then (1 : ℝ) else 0) (fun i => if z i then 1 else 0) =
    if (l.idxFun i).elim id z then 1 else 0
  rcases hi : l.idxFun i with b | j <;> rfl

lemma degree_parameterLift {n N q : ℕ} (l : Subspace (Fin n) Bool (Fin N))
    {f : (Fin N → ℝ) → ℝ} (hf : HasDegree f q) :
    HasDegree (fun z => f (parameterLift l z)) q := by
  simpa using compose hf (fun i z => parameterLift l z i) (parameterLift_degree l)

lemma lift_append {n N v : ℕ} (l : Subspace (Fin n) Bool (Fin N))
    (z : Fin n → ℝ) (x : Fin v → ℝ) :
    lift l (Fin.append z x) = Fin.append (parameterLift l z) x := by
  ext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [lift, Fin.append_left, parameterLift]
    cases l.idxFun j <;> rfl
  · intro j
    simp [lift]

end CubeParameter

end

end
 

section
 
 

noncomputable section
open Finset
open scoped BigOperators
namespace CubeCoefficients
open CubeParameter RealPolynomialDegree RoughPolynomialDegree
open PolynomialLineCoefficients CorrectedBoxLeibman RoughRealCharacterIdentity

 
def coefficients {n v s : ℕ} (f : (Fin (n+v) → ℝ) → ℝ)
    (I : PolynomialLineCoefficients.Grid v s) (z : Fin n → ℝ) : ℝ :=
  ∑ t : PolynomialLineCoefficients.Grid v s, f (Fin.append z (fun i => ((t i).val : ℝ))) *
    ∏ i, (realBasis s (t i)).coeff (I i).val

lemma coefficients_degree {n v s q : ℕ} {f : (Fin (n+v) → ℝ) → ℝ}
    (hf : HasDegree f q) (I : PolynomialLineCoefficients.Grid v s) : HasDegree (coefficients (s:=s) f I) q := by
  apply finite_sum
  intro t _
  simpa only [mul_comm] using RealPolynomialDegree.scale
    (degree_parameter_restrict hf (fun i => ((t i).val : ℝ)))
    (∏ i, (realBasis s (t i)).coeff (I i).val)

lemma coefficients_grid_integer {n v s : ℕ} (f : (Fin (n+v) → ℝ) → ℝ)
    (z : Fin n → ℝ)
    (hf : LinePolynomial v s (fun x => f (Fin.append z (fun i => (x i : ℝ)))))
    (x : Fin v → ℤ) :
    gridEval (fun I => coefficients (s:=s) f I z) (fun i => (x i : ℝ)) =
      f (Fin.append z (fun i => (x i : ℝ))) := by
  rw [tensor_interpolation v s _ hf x]
  have hexp (t : Fin (s+1)) (y : ℝ) :
      (realBasis s t).eval y = ∑ j : Fin (s+1), (realBasis s t).coeff j.val*y^j.val := by
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (realBasis_degree s t))]
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  simp_rw [hexp, Fintype.prod_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold gridEval coefficients
  apply Finset.sum_congr rfl
  intro I _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_mul_distrib]
  push_cast
  ring

lemma coefficients_grid_real {n v s q : ℕ} (f : (Fin (n+v) → ℝ) → ℝ)
    (hf : HasDegree f q) (z : Fin n → ℝ)
    (hline : LinePolynomial v s (fun x => f (Fin.append z (fun i => (x i : ℝ)))))
    (x : Fin v → ℝ) : gridEval (fun I => coefficients (s:=s) f I z) x = f (Fin.append z x) := by
  have hleft : HasDegree (fun x => gridEval (fun I => coefficients (s:=s) f I z) x)
      (gridMv (fun I => coefficients (s:=s) f I z)).totalDegree :=
    ⟨gridMv (fun I => coefficients (s:=s) f I z), le_rfl, fun x => (eval_gridMv _ x).symm⟩
  have he := eq_of_integer_agree hleft (degree_space_restrict hf z)
    (coefficients_grid_integer f z hline)
  exact congrFun he x

def value {n v s : ℕ} (θ : PolynomialLineCoefficients.Grid v s → (Fin n → ℝ) → ℝ) (y : Fin (n+v) → ℝ) : ℝ :=
  gridEval (fun I => θ I (fun i => y (i.castAdd v))) (fun i => y (i.natAdd n))

lemma value_degree {n v s q : ℕ} (θ : PolynomialLineCoefficients.Grid v s → (Fin n → ℝ) → ℝ)
    (hθ : ∀ I, HasDegree (θ I) q) : HasDegree (value θ) (q+v*s) := by
  unfold value gridEval
  apply finite_sum
  intro I _
  have ht : HasDegree (fun y : Fin (n+v) → ℝ => θ I (fun i => y (i.castAdd v))) q := by
    simpa using compose (hθ I) (fun i (y : Fin (n+v) → ℝ) => y (i.castAdd v)) (fun i => coordinate _)
  have hx : HasDegree (fun y : Fin (n+v) → ℝ => ∏ i, y (i.natAdd n)^(I i).val)
      (totalDegree I) := by
    simpa only [one_mul, totalDegree] using finite_prod univ
      (fun i (y : Fin (n+v) → ℝ) => y (i.natAdd n)^(I i).val) (fun i => 1*(I i).val)
      (fun i _ => power (coordinate _) _)
  exact RealPolynomialDegree.mono (RealPolynomialDegree.mul ht hx)
    (Nat.add_le_add_left (PolynomialLineCoefficients.totalDegree_le I) q)

lemma value_append {n v s : ℕ} (θ : PolynomialLineCoefficients.Grid v s → (Fin n → ℝ) → ℝ)
    (z : Fin n → ℝ) (x : Fin v → ℝ) : value θ (Fin.append z x) = gridEval (fun I => θ I z) x := by
  simp [value]

lemma realize_boolean_rational {n q : ℕ} (f : Finset (Fin n) → ℚ)
    (hf : BooleanRough.DegreeLE q f) :
    ∃ m : (Fin n → ℝ) → ℝ, HasDegree m q ∧
      ∀ z, m (realVertex z) = ((BooleanRough.Eval f (vertexSet z) : ℚ) : ℝ) := by
  let p := BooleanRough.AsPoly (fun S => (f S : ℝ))
  have hp : p.totalDegree ≤ q := BooleanRough.asPoly_degree q _ (by
    intro S hS
    simp only [hf S hS, Rat.cast_zero])
  refine ⟨fun z => MvPolynomial.eval z p, ⟨p, hp, fun _ => rfl⟩, ?_⟩
  intro z
  rw [vertex_to_set]
  change MvPolynomial.eval _ (BooleanRough.AsPoly (fun T => (f T : ℝ))) = _
  rw [BooleanRough.eval_asPoly]
  simp only [BooleanRough.Eval, Rat.cast_sum]

end CubeCoefficients

end

end
 


end OAI
