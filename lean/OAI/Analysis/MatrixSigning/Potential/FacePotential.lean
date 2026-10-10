import Mathlib
import OAI.Analysis.MatrixSigning.Potential.Line
import OAI.Analysis.MatrixSigning.Potential.CoarseBudget
import OAI.Analysis.MatrixSigning.Calculus.Translate

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State
open CurrentKS.Scalar CurrentKS.Calculus
open scoped BigOperators ContDiff

variable {d N : ℕ}

lemma norm_coordinate_projection_le_one (i : Fin N) :
    ‖(ContinuousLinearMap.proj i : Coordinates N →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro y
  simp only [one_mul]
  exact norm_le_pi_norm y i

lemma contDiffAt_penalty_coordinate {x : Coordinates N} {σ : ℝ}
    (hσ : 0 < σ) (hx : ∀ i,|x i| ≤ 1-σ/2) (i : Fin N) :
    ContDiffAt ℝ 3 (fun y : Coordinates N => psi (y i)) x := by
  exact ContDiffAt.comp (f := fun y : Coordinates N => y i) (g := psi) x
    (contDiffAt_psi (strip_interior hσ (hx i))) (contDiffAt_apply ℝ ℝ i x)

lemma penalty_coordinate_jet {x : Coordinates N} {σ : ℝ}
    (hσ : 0 < σ) (hx : ∀ i,|x i| ≤ 1-σ/2) (i : Fin N) :
    JetBound (fun y : Coordinates N => psi (y i)) x (1+800/σ^3) := by
  exact JetBound.comp_linear (E:=Coordinates N) (F:=ℝ) (G:=ℝ) (f:=psi) (x:=x)
    (ContinuousLinearMap.proj i) (contDiffAt_psi (strip_interior hσ (hx i)))
    (jetBound_psi hσ (hx i)) (norm_coordinate_projection_le_one i)

lemma penalty_strip_jet {x : Coordinates N} {σ : ℝ}
    (hσ : 0 < σ) (hx : ∀ i,|x i| ≤ 1-σ/2) :
    JetBound penalty x ((N:ℝ)*(1+800/σ^3)) := by
  have hh := JetBound.sum (E:=Coordinates N) (F:=ℝ) Finset.univ
    (fun i _ => contDiffAt_penalty_coordinate hσ hx i)
    (fun i _ => penalty_coordinate_jet hσ hx i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  exact hh

lemma penalty_strip_deriv {x h : Coordinates N} {σ : ℝ}
    (hσ : 0 < σ) (hx : ∀ i,|x i| ≤ 1-σ/2) (hh : ‖h‖ ≤ 1)
    {n : ℕ} (hn : n ≤ 3) :
    |iteratedDeriv n (fun t : ℝ => penalty (x+t • h)) 0| ≤ (N:ℝ)*(1+800/σ^3) := by
  have hj := JetBound.line (E:=Coordinates N) (F:=ℝ)
    (contDiffAt_penalty (fun i => strip_interior hσ (hx i))) (penalty_strip_jet hσ hx) hh n hn
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,Real.norm_eq_abs] using hj

open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Calculus Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff


def facePotential (ε lam : ℝ) (S₀ : H d) (A : Fin N → H d) (x : Coordinates N) : ℝ :=
  value ε (S₀+S A x) (eta 384 A x)+lam*penalty x

def valueCurve2Bound (d N : ℕ) (ε σ : ℝ) : ℝ :=
  let B := coarseBudget d N ε σ
  let Jb := 10^18*((d:ℝ)+1)*(1+ε⁻¹)^4
  let D := 300*B^5
  (1+|ε| *(2*((d:ℝ)+1)))*(Jb*D*(1+Jb*D)^2)

def valueCurve3Bound (d N : ℕ) (ε σ : ℝ) : ℝ :=
  let B := coarseBudget d N ε σ
  let Jb := 10^18*((d:ℝ)+1)*(1+ε⁻¹)^4
  let D := 300*B^5
  (1+|ε| *(2*((d:ℝ)+1)))*
    (Jb*D*((1+Jb*D)^3+3*(1+Jb*D)*(Jb*D*(1+Jb*D)^2)))

def potentialCurveBound (d N : ℕ) (ε σ lam : ℝ) : ℝ :=
  1+valueCurve2Bound d N ε σ+valueCurve3Bound d N ε σ+|lam| *(N:ℝ)*(1+800/σ^3)

lemma valueCurve_bounds_nonneg {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) :
    0 ≤ valueCurve2Bound d N ε σ ∧ 0 ≤ valueCurve3Bound d N ε σ := by
  have hB := (coarseBudget_bounds (d:=d) (N:=N) hε hσ).1
  dsimp [valueCurve2Bound,valueCurve3Bound]
  constructor <;> positivity

lemma scalar_hundred_bounds {S : H d} (hlo : -(Hermitian.one : H d) ≤ S)
    (hhi : S ≤ (Hermitian.one : H d)) :
    -(100:ℝ) • (Hermitian.one : H d) ≤ S ∧ S ≤ (100:ℝ) • (Hermitian.one : H d) := by
  constructor
  · apply le_trans _ hlo
    have hc := scalar_mono_psd (d:=d) one_mem_psdCone (by norm_num : (-100:ℝ) ≤ -1)
    rw [neg_smul (1:ℝ) (Hermitian.one : H d),one_smul] at hc
    exact hc
  · apply hhi.trans
    simpa only [one_smul] using
      scalar_mono_psd (d:=d) one_mem_psdCone (by norm_num : (1:ℝ) ≤ 100)

theorem contDiffAt_facePotential [NeZero d] (A : Fin N → H d)
    (S₀ : H d) (x : Coordinates N) {ε lam : ℝ} (hε : 0 < ε) (hεd : ε*d ≤ 1)
    (hx : ∀ i,|x i| < 1)
    (hlo : -(Hermitian.one : H d) ≤ S₀+S A x)
    (hhi : S₀+S A x ≤ (Hermitian.one : H d))
    (hηI : eta 384 A x (Hermitian.one : H d) ≤ (384:ℝ) • (Hermitian.one : H d)) :
    ContDiffAt ℝ ∞ (facePotential ε lam S₀ A) x := by
  have hpos := eta_positive (by norm_num : (0:ℝ)≤384) A (fun i => (hx i).le)
  obtain ⟨z,hz,_,hmin⟩ := normalized_minimizer (S₀+S A x) (eta 384 A x)
    hpos hε hεd hlo hhi hηI
  have hS100 := scalar_hundred_bounds hlo hhi
  have hv := contDiffAt_value ε hε (fun y => S₀+S A y) (eta 384 A) x
    (contDiffAt_const.add (contDiff_S A).contDiffAt) (contDiffAt_eta 384 A hx)
    hpos (Filter.Eventually.of_forall (fun y => eta_symmetric 384 A y))
    hS100.1 hS100.2 z hz hmin
  exact hv.add (contDiffAt_const.mul (contDiffAt_penalty hx))

lemma line_potential_derivative_bound {f g : ℝ → ℝ} {n : ℕ} {lam B C : ℝ}
    (hf : ContDiffAt ℝ n f 0) (hg : ContDiffAt ℝ n g 0)
    (hB : |iteratedDeriv n f 0| ≤ B) (hC : |iteratedDeriv n g 0| ≤ C) :
    |iteratedDeriv n (fun t => f t+lam*g t) 0| ≤ B+|lam| *C := by
  rw [iteratedDeriv_fun_add hf (contDiffAt_const.mul hg),iteratedDeriv_const_mul_field]
  exact (abs_add_le _ _).trans (add_le_add hB (by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hC (abs_nonneg lam)))

theorem facePotential_strip_derivatives [NeZero d] (A : Fin N → H d)
    (hA : ∀ i,A i ∈ psdCone d) (hAn : ∀ i,‖A i‖ ≤ 1)
    (S₀ : H d) (hS₀ : ‖S₀‖ ≤ (d:ℝ)+1) (x h : Coordinates N)
    {ε σ lam : ℝ} (hε : 0 < ε) (hεd : ε*d ≤ 1)
    (hσ : 0 < σ) (hx : ∀ i,|x i| ≤ 1-σ/2) (hh : ‖h‖ ≤ 1)
    (hlo : -(Hermitian.one : H d) ≤ S₀+S A x)
    (hhi : S₀+S A x ≤ (Hermitian.one : H d))
    (hηI : eta 384 A x (Hermitian.one : H d) ≤ (384:ℝ) • (Hermitian.one : H d)) :
    |iteratedDeriv 2 (fun t : ℝ => facePotential ε lam S₀ A (x+t • h)) 0| ≤
      potentialCurveBound d N ε σ lam ∧
    |iteratedDeriv 3 (fun t : ℝ => facePotential ε lam S₀ A (x+t • h)) 0| ≤
      potentialCurveBound d N ε σ lam := by
  have hxi (i : Fin N) := strip_interior hσ (hx i)
  have hpos := eta_positive (by norm_num : (0:ℝ)≤384) A (fun i => (hxi i).le)
  obtain ⟨z,hz,hz100,hmin⟩ := normalized_minimizer (S₀+S A x) (eta 384 A x)
    hpos hε hεd hlo hhi hηI
  have hS100 := scalar_hundred_bounds hlo hhi
  have hb := value_strip_derivatives A hA hAn S₀ hS₀ x h hε hσ hx hh
    hS100.1 hS100.2 z hz hz100 hmin
  change _ ≤ valueCurve2Bound d N ε σ ∧ _ ≤ valueCurve3Bound d N ε σ at hb
  have hline : ContDiff ℝ ∞ (fun t : ℝ => x+t • h) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hv := contDiffAt_value ε hε (fun y => S₀+S A y) (eta 384 A) x
    (contDiffAt_const.add (contDiff_S A).contDiffAt) (contDiffAt_eta 384 A hxi)
    hpos (Filter.Eventually.of_forall (fun y => eta_symmetric 384 A y))
    hS100.1 hS100.2 z hz hmin
  have hv0 : ContDiffAt ℝ ∞ (fun t : ℝ => value ε (S₀+S A (x+t • h)) (eta 384 A (x+t • h))) 0 := by
    have hv' : ContDiffAt ℝ ∞ (fun y => value ε (S₀+S A y) (eta 384 A y)) (x+(0:ℝ) • h) := by simpa using hv
    exact ContDiffAt.comp (f:=fun t : ℝ => x+t • h) (g:=fun y => value ε (S₀+S A y) (eta 384 A y)) 0 hv' hline.contDiffAt
  have hp0 : ContDiffAt ℝ ∞ (fun t : ℝ => penalty (x+t • h)) 0 := by
    have hp : ContDiffAt ℝ ∞ penalty (x+(0:ℝ) • h) := by simpa using contDiffAt_penalty hxi
    exact ContDiffAt.comp (f:=fun t : ℝ => x+t • h) (g:=penalty) 0 hp hline.contDiffAt
  have hp (n : ℕ) (hn : n ≤ 3) := penalty_strip_deriv hσ hx hh hn
  have hnon := valueCurve_bounds_nonneg (d:=d) (N:=N) hε hσ
  constructor
  · have ht := line_potential_derivative_bound (lam:=lam)
      (hv0.of_le (WithTop.coe_le_coe.mpr (show (2:ℕ∞) ≤ ⊤ from le_top)))
      (hp0.of_le (WithTop.coe_le_coe.mpr (show (2:ℕ∞) ≤ ⊤ from le_top))) hb.1 (hp 2 (by norm_num))
    change _ ≤ potentialCurveBound d N ε σ lam
    apply ht.trans
    dsimp [potentialCurveBound]
    nlinarith [hnon.2]
  · have ht := line_potential_derivative_bound (lam:=lam)
      (hv0.of_le (WithTop.coe_le_coe.mpr (show (3:ℕ∞) ≤ ⊤ from le_top)))
      (hp0.of_le (WithTop.coe_le_coe.mpr (show (3:ℕ∞) ≤ ⊤ from le_top))) hb.2 (hp 3 (by norm_num))
    apply ht.trans
    dsimp [potentialCurveBound]
    nlinarith [hnon.1]
end CurrentKS.State

end

end OAI
