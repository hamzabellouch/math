import Mathlib
import OAI.Analysis.MatrixSigning.Potential.Potential
import OAI.Analysis.MatrixSigning.Matrices.OperatorNorm

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Variational
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma shift_feasible_of_map_le (S T : H d) (η θ : H d →L[ℝ] H d)
    {r : ℝ} (hplus : T-S ≤ r • (Hermitian.one : H d))
    (hminus : S-T ≤ r • (Hermitian.one : H d))
    (hle : ∀ X ∈ psdCone d, θ X ≤ η X) (z : Point d) (hz : z ∈ feasible S η) :
    (z.1+r,z.2) ∈ feasible T θ := by
  rw [feasible_iff] at hz ⊢
  refine ⟨hz.1,hz.2.1,?_,?_⟩
  · have h := add_le_add hz.2.2.1 hplus
    have he : invH z.2.1+T+θ z.2.2 ≤ invH z.2.1+S+η z.2.2+(T-S) := by
      have hh := add_le_add_left (hle z.2.2 (show z.2.2 ∈ psdCone d from hz.2.1.posSemidef)) (invH z.2.1+T)
      convert hh using 1 <;> first | rfl | abel
    convert he.trans h using 1
    first | rfl | module
  · have h := add_le_add hz.2.2.2 hminus
    have he : invH z.2.2-T+θ z.2.1 ≤ invH z.2.2-S+η z.2.1+(S-T) := by
      have hh := add_le_add_left (hle z.2.1 (show z.2.1 ∈ psdCone d from hz.1.posSemidef)) (invH z.2.2-T)
      convert hh using 1 <;> first | rfl | abel
    convert he.trans h using 1
    first | rfl | module

end CurrentKS.Variational

namespace CurrentKS.State
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma endpoint_eta_le {c : ℝ} (hc : 0 ≤ c) (A : Fin N → H d) (x : Coordinates N)
    (hx : Cube x) (i : Fin N) {t : ℝ} (ht : |t|=1) :
    ∀ X ∈ psdCone d,eta c A (Function.update x i t) X ≤ eta c A x X := by
  intro X hX
  rw [eta_update,psi_endpoint ht]
  have hs : (c*(0-psi (x i))) • sandwich (A i) X ≤ 0 := by
    simpa only [zero_smul] using scalar_mono_psd (sandwich_psd (A i) X hX)
      (show c*(0-psi (x i)) ≤ 0 by nlinarith [(psi_bounds (hx i)).1])
  simpa only [zero_add,add_comm] using add_le_add_left hs (eta c A x X)

lemma negative_le_operatorNorm (A : H d) : -A ≤ operatorNorm A • (Hermitian.one : H d) := by
  have h := le_operatorNorm_smul_one (-A)
  have he : operatorNorm (-A) = operatorNorm A := by
    rw [← neg_one_smul ℝ A,operatorNorm_smul]
    norm_num
  rwa [he] at h

lemma endpoint_value_shift [NeZero d] {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (A : Fin N → H d) (x : Coordinates N) (hx : Cube x) (i : Fin N) {t : ℝ}
    (ht : |t|=1) (z : Point d) (hz : z ∈ feasible (S A x) (eta c A x))
    (hmin : ∀ w ∈ feasible (S A x) (eta c A x),objective ε z ≤ objective ε w) :
    value ε (S A (Function.update x i t)) (eta c A (Function.update x i t)) ≤
      value ε (S A x) (eta c A x)+|t-x i| *operatorNorm (A i) := by
  let D := (t-x i) • A i
  have hd : S A (Function.update x i t)-S A x = D := by rw [S_update]; abel
  have hm : S A x-S A (Function.update x i t) = -D := by rw [S_update]; abel
  have hp : S A (Function.update x i t)-S A x ≤ operatorNorm D • (Hermitian.one : H d) := by
    rw [hd]; exact le_operatorNorm_smul_one D
  have hn : S A x-S A (Function.update x i t) ≤ operatorNorm D • (Hermitian.one : H d) := by
    rw [hm]; exact negative_le_operatorNorm D
  have hf := shift_feasible_of_map_le _ _ _ _ hp hn (endpoint_eta_le hc A x hx i ht) z hz
  have hv := value_le_feasible ε hε _ _ (eta_positive hc A (Cube_update hx i ht.le)) _ hf
  rw [value_eq_of_min ε _ _ z hz hmin]
  calc
    _ ≤ objective ε (z.1+operatorNorm D,z.2) := hv
    _ = objective ε z+|t-x i| *operatorNorm (A i) := by
      dsimp [objective,D]
      rw [operatorNorm_smul]
      ring

lemma endpoint_shift_potential [NeZero d] {c ε lam : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (A : Fin N → H d) (x : Coordinates N) (hx : Cube x) (i : Fin N) {t : ℝ}
    (ht : |t|=1) (z : Point d) (hz : z ∈ feasible (S A x) (eta c A x))
    (hmin : ∀ w ∈ feasible (S A x) (eta c A x),objective ε z ≤ objective ε w) :
    potential c ε lam A (Function.update x i t) ≤
      potential c ε lam A x+|t-x i| *operatorNorm (A i)-lam*psi (x i) := by
  have hv := endpoint_value_shift hc hε A x hx i ht z hz hmin
  rw [potential,potential,sum_update_composite (fun (_ : Fin N) (r : ℝ) => psi r) x i t,
    psi_endpoint ht,add_zero]
  nlinarith

lemma psi_sq_ge_distance {x : ℝ} (hx : |x| ≤ 1) : 1-|x| ≤ psi x^2 := by
  rcases lt_or_eq_of_le hx with hi|he
  · have hp := psi_pos hi
    have hc := psi_cube hi
    have h1 := psi_le_one hi
    have ha := abs_nonneg x
    have hr := sq_abs x
    have hprod := mul_nonneg (sq_nonneg (psi x)) (sub_nonneg.mpr h1)
    have hdist := mul_nonneg ha (sub_nonneg.mpr hx)
    nlinarith
  · rw [psi_endpoint he,he]; norm_num

lemma freeze_scalar {x lam ν : ℝ} (hx : |x| ≤ 1) (hlam : 0 ≤ lam) (hν : 0 < ν)
    (hclose : 1-|x| ≤ lam^2/ν) :
    (1-|x|)*Real.sqrt ν ≤ lam*psi x := by
  have hz : 0 ≤ 1-|x| := sub_nonneg.mpr hx
  have hv := Real.sq_sqrt hν.le
  have hr := Real.sq_sqrt hz
  have hab := (le_div_iff₀ hν).mp hclose
  have hp := (psi_bounds hx).1
  have hsp : Real.sqrt (1-|x|) ≤ psi x := by
    nlinarith [psi_sq_ge_distance hx,Real.sqrt_nonneg (1-|x|)]
  have hroot : Real.sqrt (1-|x|)*Real.sqrt ν ≤ lam := by
    have hs : (Real.sqrt (1-|x|)*Real.sqrt ν)^2 ≤ lam^2 := by
      rw [mul_pow,hr,hv];exact hab
    nlinarith [Real.sqrt_nonneg ν,Real.sqrt_nonneg (1-|x|)]
  have hh := mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg (1-|x|))
  have hh' : (1-|x|)*Real.sqrt ν ≤ lam*Real.sqrt (1-|x|) := by
    calc
      (1-|x|)*Real.sqrt ν = Real.sqrt (1-|x|)*(Real.sqrt (1-|x|)*Real.sqrt ν) := by rw [← mul_assoc,← sq,hr]
      _ ≤ Real.sqrt (1-|x|)*lam := hh
      _ = lam*Real.sqrt (1-|x|) := mul_comm _ _
  exact hh'.trans (mul_le_mul_of_nonneg_left hsp hlam)

theorem freeze_potential [NeZero d] {c ε lam ν : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (hlam : 0 ≤ lam) (hν : 0 < ν) (A : Fin N → H d) (x : Coordinates N)
    (hx : Cube x) (i : Fin N) {t : ℝ} (ht : |t|=1) (hne : |t-x i|=1-|x i|)
    (hAn : operatorNorm (A i) ≤ Real.sqrt ν) (hclose : 1-|x i| ≤ lam^2/ν)
    (z : Point d) (hz : z ∈ feasible (S A x) (eta c A x))
    (hmin : ∀ w ∈ feasible (S A x) (eta c A x),objective ε z ≤ objective ε w) :
    potential c ε lam A (Function.update x i t) ≤ potential c ε lam A x := by
  have he := endpoint_shift_potential hc hε A x hx i ht z hz hmin (lam:=lam)
  rw [hne] at he
  have hh := mul_le_mul_of_nonneg_left hAn (sub_nonneg.mpr (hx i))
  have hs := freeze_scalar (hx i) hlam hν hclose
  linarith

end CurrentKS.State

end

end OAI
