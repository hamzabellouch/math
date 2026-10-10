import Mathlib
import OAI.Analysis.MatrixSigning.Potential.TightComplementarity
import OAI.Analysis.MatrixSigning.Potential.DiagBlock
import OAI.Analysis.MatrixSigning.Arithmetic.Alpha2

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Interaction
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

structure LightPoint (d N : ℕ) where
  A : Fin N → H d
  x : Coordinates N
  fixedPart : H d
  ε : ℝ
  ε_pos : 0 < ε
  ε_le_one : ε ≤ 1
  A_pos : ∀ i, A i ∈ psdCone d
  A_ne_zero : ∀ i, A i ≠ 0
  A_rank : ∀ i, (A i : Hermitian.Mat d).rank ≤ 1
  interior : ∀ i, |x i| < 1
  lower : -(100 : ℝ) • (Hermitian.one : H d) ≤ fixedPart+S A x
  upper : fixedPart+S A x ≤ (100 : ℝ) • (Hermitian.one : H d)
  primal : Point d
  feasible : primal ∈ Variational.feasible (fixedPart+S A x) (eta 384 A x)
  sublevel : objective ε primal ≤ 100
  minimal : ∀ w ∈ Variational.feasible (fixedPart+S A x) (eta 384 A x),
    objective ε primal ≤ objective ε w
  P : H d
  Q : H d
  P_pos : P ∈ pd d
  Q_pos : Q ∈ pd d
  P_le : P ≤ (Hermitian.one : H d)
  Q_le : Q ≤ (Hermitian.one : H d)
  trace_eq : Hermitian.realTrace P+Hermitian.realTrace Q = 1
  tight : residual (fixedPart+S A x) (eta 384 A x) primal = 0
  stationary_X : sandwich (invH primal.2.1) P = eta 384 A x Q+ε • (Hermitian.one : H d)
  stationary_Y : sandwich (invH primal.2.2) Q = eta 384 A x P+ε • (Hermitian.one : H d)
  lightA : ∀ i, 384*psi (x i)*inner ℝ (A i) primal.2.1 < 1+x i
  lightB : ∀ i, 384*psi (x i)*inner ℝ (A i) primal.2.2 < 1-x i

variable {d N : ℕ}

lemma lightPoint_of_optimizer [NeZero d] (A : Fin N → H d) (x : Coordinates N) (S₀ : H d)
    {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hA : ∀ i, A i ∈ psdCone d) (hA0 : ∀ i, A i ≠ 0)
    (hrank : ∀ i, (A i : Hermitian.Mat d).rank ≤ 1) (hx : ∀ i, |x i| < 1)
    (hlo : -(100 : ℝ) • (Hermitian.one : H d) ≤ S₀+S A x)
    (hhi : S₀+S A x ≤ (100 : ℝ) • (Hermitian.one : H d))
    (z : Point d) (hz : z ∈ Variational.feasible (S₀+S A x) (eta 384 A x))
    (hsub : objective ε z ≤ 100)
    (hmin : ∀ w ∈ Variational.feasible (S₀+S A x) (eta 384 A x), objective ε z ≤ objective ε w)
    (hlightA : ∀ i, 384*psi (x i)*inner ℝ (A i) z.2.1 < 1+x i)
    (hlightB : ∀ i, 384*psi (x i)*inner ℝ (A i) z.2.2 < 1-x i) :
    ∃ p : LightPoint d N, p.A = A ∧ p.x = x ∧ p.fixedPart = S₀ ∧ p.ε = ε ∧ p.primal = z := by
  obtain ⟨P,Q,hP,hQ,hPle,hQle,htr,_,_,ht,hX,hY⟩ := kkt (S₀+S A x) (eta 384 A x)
    (eta_positive (by norm_num) A (fun i => (hx i).le)) (eta_symmetric 384 A x) hε hlo hhi z hz hmin
  exact ⟨⟨A,x,S₀,ε,hε,hε₁,hA,hA0,hrank,hx,hlo,hhi,z,hz,hsub,hmin,P,Q,hP,hQ,hPle,hQle,htr,
    ht,hX,hY,hlightA,hlightB⟩,rfl,rfl,rfl,rfl,rfl⟩

lemma inner_smul_right_fixed (A B : H d) (r : ℝ) :
    inner ℝ A (r • B) = r*inner ℝ A B := real_inner_smul_right A B r

namespace LightPoint
variable (p : LightPoint d N)

def X : H d := p.primal.2.1
def Y : H d := p.primal.2.2
def a (i : Fin N) : ℝ := inner ℝ (p.A i) p.X
def b (i : Fin N) : ℝ := inner ℝ (p.A i) p.Y
def pp (i : Fin N) : ℝ := inner ℝ (p.A i) p.P
def qq (i : Fin N) : ℝ := inner ℝ (p.A i) p.Q
def T (i : Fin N) : ℝ := scaleT 384 (p.x i) (p.a i) (p.b i)
def l (i : Fin N) : ℝ := scaleL 384 (p.x i) (p.a i) (p.b i)
def m (i : Fin N) : ℝ := scaleM 384 (p.x i) (p.a i) (p.b i)
lemma X_pos : p.X ∈ pd d := p.feasible.1.1
lemma Y_pos : p.Y ∈ pd d := p.feasible.1.2
lemma a_pos [NeZero d] (i : Fin N) : 0 < p.a i :=
  coordinate_pos (p.A i) p.X (p.A_pos i) (p.A_ne_zero i) p.X_pos
lemma b_pos [NeZero d] (i : Fin N) : 0 < p.b i :=
  coordinate_pos (p.A i) p.Y (p.A_pos i) (p.A_ne_zero i) p.Y_pos
lemma pp_pos [NeZero d] (i : Fin N) : 0 < p.pp i :=
  coordinate_pos (p.A i) p.P (p.A_pos i) (p.A_ne_zero i) p.P_pos
lemma qq_pos [NeZero d] (i : Fin N) : 0 < p.qq i :=
  coordinate_pos (p.A i) p.Q (p.A_pos i) (p.A_ne_zero i) p.Q_pos
lemma scales_pos [NeZero d] (i : Fin N) : 0 < p.T i ∧ 0 < p.l i ∧ 0 < p.m i :=
  (light_rescaling_pos (by norm_num) (p.interior i) (p.a_pos i) (p.b_pos i) (p.lightA i) (p.lightB i)).2.2
lemma lm_eq [NeZero d] (i : Fin N) : p.l i*p.m i = psi (p.x i) :=
  scaleL_mul_scaleM (by norm_num) (p.interior i) (p.a_pos i) (p.b_pos i) (p.lightA i) (p.lightB i)
lemma lT_eq [NeZero d] (i : Fin N) : p.l i*p.T i = 1+384*psi₁ (p.x i)*p.b i := by
  change Alpha 384 (p.x i) (p.a i) (p.b i)/p.T i*p.T i = _
  rw [div_mul_cancel₀ _ (p.scales_pos i).1.ne',Alpha_eq (p.interior i)]
lemma mT_eq [NeZero d] (i : Fin N) : p.m i*p.T i = 1-384*psi₁ (p.x i)*p.a i := by
  change Beta 384 (p.x i) (p.a i) (p.b i)/p.T i*p.T i = _
  rw [div_mul_cancel₀ _ (p.scales_pos i).1.ne',Beta_eq (p.interior i)]
lemma product_bound [NeZero d] (i : Fin N) : (p.l i*p.a i)*(p.m i*p.b i) ≤ (384 : ℝ)⁻¹^2 :=
  rescaled_product_bound (by norm_num) (p.interior i) (p.a_pos i) (p.b_pos i) (p.lightA i) (p.lightB i)
lemma square_bounds [NeZero d] (i : Fin N) :
    (p.l i*p.a i)^2 ≤ 3*(384 : ℝ)⁻¹^2 ∧ (p.m i*p.b i)^2 ≤ 3*(384 : ℝ)⁻¹^2 :=
  rescaled_square_bounds (by norm_num) (p.interior i) (p.a_pos i) (p.b_pos i) (p.lightA i) (p.lightB i)
lemma drift_bounds [NeZero d] (i : Fin N) :
    p.T i*(p.l i*p.a i+p.m i*p.b i) ≤ 2/(384*psi (p.x i)) ∧
    (p.l i*p.a i+p.m i*p.b i)/p.T i ≤ (3/384 : ℝ) :=
  rescaled_drift_bounds (by norm_num) (p.interior i) (p.a_pos i) (p.b_pos i) (p.lightA i) (p.lightB i)
lemma kappa_bounds [NeZero d] (i : Fin N) :
    (1/3 : ℝ) ≤ kappa (p.x i)/p.T i^2 ∧ (p.T i^2)⁻¹ ≤ (3/2 : ℝ) :=
  (rescaled_kappa_bounds (by norm_num) (p.interior i) (p.a_pos i) (p.b_pos i) (p.lightA i) (p.lightB i)).2

end LightPoint
end
end CurrentKS.State

end OAI
