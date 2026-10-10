import Mathlib
import OAI.Analysis.MatrixSigning.Calculus.NormSmulRightId
import OAI.Analysis.MatrixSigning.Potential.Line
import OAI.Analysis.MatrixSigning.Potential.Energy
import OAI.Analysis.MatrixSigning.Arithmetic.MixedYoungBound

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

variable {d N : ℕ}

private local instance : NormedAddCommGroup (H d) := inferInstance
private local instance : NormedSpace ℝ (H d) := inferInstance
private local instance : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

def negativeWeight (A : Fin N → H d) (x h : Coordinates N) (X Y P Q : H d) : ℝ :=
  ∑ i, kappa (x i)*(h i)^2*(inner ℝ (A i) Y*inner ℝ (A i) P + inner ℝ (A i) X*inner ℝ (A i) Q)

def mixedTerm (c : ℝ) (A : Fin N → H d) (x h : Coordinates N) (P Q U V : H d) : ℝ :=
  ∑ i, 2*c*psi₁ (x i)*h i*(inner ℝ (A i) P*inner ℝ (A i) V + inner ℝ (A i) Q*inner ℝ (A i) U)

lemma mixedTerm_bound {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (A : Fin N → H d) (x h : Coordinates N) (hx : ∀ i, |x i| < 1)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1)
    (X Y P Q U V : H d) (hX : X ∈ pd d) (hY : Y ∈ pd d)
    (hPpos : P ∈ psdCone d) (hQpos : Q ∈ psdCone d)
    (hP : sandwich (invH X) P = eta c A x Q + ε • (Hermitian.one : H d))
    (hQ : sandwich (invH Y) Q = eta c A x P + ε • (Hermitian.one : H d)) :
    mixedTerm c A x h P Q U V ≤ energy X Y P Q U V + (c/2)*negativeWeight A x h X Y P Q := by
  have hi (i : Fin N) := mixed_young_bound hc
    (inner_nonneg_of_psd (A i) P (hA i) hPpos)
    (inner_nonneg_of_psd (A i) Q (hA i) hQpos)
    (inner_nonneg_of_psd (A i) X (hA i) hX.posSemidef)
    (inner_nonneg_of_psd (A i) Y (hA i) hY.posSemidef)
    (derivative_square_le (hx i))
    (trace_inverse_young (A i) X U (hA i) hX (psi_pos (hx i)) (psi₁ (x i)*h i))
    (trace_inverse_young (A i) Y V (hA i) hY (psi_pos (hx i)) (psi₁ (x i)*h i))
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => hi i)
  have he := energy_stationary_bound c ε hε A x hA hrank X Y P Q U V hX hY hP hQ
  change mixedTerm c A x h P Q U V ≤ _ at hh
  rw [Finset.sum_add_distrib] at hh
  have hf : (∑ i, (c/2)*kappa (x i)*(h i)^2*
      (inner ℝ (A i) Y*inner ℝ (A i) P + inner ℝ (A i) X*inner ℝ (A i) Q)) =
      (c/2)*negativeWeight A x h X Y P Q := by
    rw [negativeWeight,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hf] at hh
  exact hh.trans (add_le_add he (le_refl _))

lemma secondExpansion_bound {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (A : Fin N → H d) (x h : Coordinates N) (hx : ∀ i, |x i| < 1)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1)
    (X Y P Q U V : H d) (hX : X ∈ pd d) (hY : Y ∈ pd d)
    (hPpos : P ∈ psdCone d) (hQpos : Q ∈ psdCone d)
    (hP : sandwich (invH X) P = eta c A x Q + ε • (Hermitian.one : H d))
    (hQ : sandwich (invH Y) Q = eta c A x P + ε • (Hermitian.one : H d)) :
    2*energy X Y P Q U V + mixedTerm c A x h P Q U V - c*negativeWeight A x h X Y P Q ≤
      3*energy X Y P Q U V - (c/2)*negativeWeight A x h X Y P Q := by
  have hh := mixedTerm_bound hc hε A x h hx hA hrank X Y P Q U V hX hY hPpos hQpos hP hQ
  linarith

local instance negativeWeightNormedAddCommGroup : NormedAddCommGroup (H d →L[ℝ] H d) :=
  inferInstance
local instance negativeWeightNormedSpace : NormedSpace ℝ (H d →L[ℝ] H d) := inferInstance
private local instance : TopologicalSpace (H d →L[ℝ] H d) :=
  (inferInstance : NormedAddCommGroup (H d →L[ℝ] H d)).toUniformSpace.toTopologicalSpace

lemma hasDerivAt_S_line (A : Fin N → H d) (x h : Coordinates N) (a : ℝ) :
    HasDerivAt (fun s => S A (line x h s)) (S A h) a := by
  exact HasDerivAt.fun_sum fun i _ => (hasDerivAt_line_coord x h a i).smul_const (A i)

def eta₁ (c : ℝ) (A : Fin N → H d) (x h : Coordinates N) : H d →L[ℝ] H d :=
  ∑ i, (c*psi₁ (x i)*h i) • sandwichCLM (A i)

def eta₂ (c : ℝ) (A : Fin N → H d) (x h : Coordinates N) : H d →L[ℝ] H d :=
  ∑ i, (-c*kappa (x i)*(h i)^2) • sandwichCLM (A i)

lemma eta₁_apply (c : ℝ) (A : Fin N → H d) (x h : Coordinates N) (Y : H d) :
    eta₁ c A x h Y = ∑ i, (c*psi₁ (x i)*h i) • sandwich (A i) Y := by
  simp only [eta₁,_root_.sum_apply,_root_.smul_apply,sandwichCLM_apply]

lemma eta₂_apply (c : ℝ) (A : Fin N → H d) (x h : Coordinates N) (Y : H d) :
    eta₂ c A x h Y = ∑ i, (-c*kappa (x i)*(h i)^2) • sandwich (A i) Y := by
  simp only [eta₂,_root_.sum_apply,_root_.smul_apply,sandwichCLM_apply]

lemma hasDerivAt_eta_line (c : ℝ) (A : Fin N → H d) (x h : Coordinates N) (a : ℝ)
    (hx : ∀ i, |line x h a i| < 1) :
    HasDerivAt (fun s => eta c A (line x h s)) (eta₁ c A (line x h a) h) a := by
  unfold eta eta₁
  apply HasDerivAt.fun_sum
  intro i _
  convert ((((hasDerivAt_psi (hx i)).comp a (hasDerivAt_line_coord x h a i)).const_mul c).smul_const
    (sandwichCLM (A i))) using 1
  congr 1
  ring_nf

lemma hasDerivAt_eta₁_line (c : ℝ) (A : Fin N → H d) (x h : Coordinates N) (a : ℝ)
    (hx : ∀ i, |line x h a i| < 1) :
    HasDerivAt (fun s => eta₁ c A (line x h s) h) (eta₂ c A (line x h a) h) a := by
  unfold eta₁ eta₂
  apply HasDerivAt.fun_sum
  intro i _
  convert (((((hasDerivAt_psi₁ (hx i)).comp a (hasDerivAt_line_coord x h a i)).const_mul c).mul_const (h i)).smul_const
    (sandwichCLM (A i))) using 1
  congr 1
  ring_nf

lemma hasDerivAt_deriv_eta_line (c : ℝ) (A : Fin N → H d) (x h : Coordinates N) (a : ℝ)
    (hx : ∀ i, |line x h a i| < 1) :
    HasDerivAt (deriv (fun s => eta c A (line x h s))) (eta₂ c A (line x h a) h) a := by
  apply (hasDerivAt_eta₁_line c A x h a hx).congr_of_eventuallyEq
  filter_upwards [eventually_line_interior x h hx] with s hs
  exact (hasDerivAt_eta_line c A x h s hs).deriv

end CurrentKS.State

end

end OAI
