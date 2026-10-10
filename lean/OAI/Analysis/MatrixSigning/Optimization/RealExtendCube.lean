import Mathlib
import OAI.Analysis.MatrixSigning.Potential.FacePotential
import OAI.Analysis.MatrixSigning.Optimization.FixedPart

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.State CurrentKS.Variational
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius ContDiff

variable {d N n : ℕ}

lemma real_extend_cube (e : Fin n → Fin N) (base : Coordinates N) (y : Coordinates n)
    (hb : Cube base) (hy : Cube y) : Cube (extend e base y) := by
  intro i
  unfold extend
  cases lookup e i with
  | none => exact hb i
  | some j => exact hy j

lemma norm_psd_le_trace_h (A : H d) (hA : A∈psdCone d) : ‖A‖≤Hermitian.realTrace A := by
  have ht := trace_bound_above hA
  have hh := inner_nonneg_of_psd A (Hermitian.realTrace A • Hermitian.one-A) hA
    ((mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr ht))
  rw [inner_sub_right,real_inner_smul_right A (Hermitian.one : H d) (Hermitian.realTrace A),inner_one',real_inner_self_eq_norm_sq] at hh
  nlinarith [norm_nonneg A,realTrace_nonneg hA]

lemma norm_atoms_le_one (A : Fin N → H d) (hA : ∀ i,A i∈psdCone d)
    (htr : ∑ i,Hermitian.realTrace (A i)=1) (i : Fin N) : ‖A i‖≤1 := by
  apply (norm_psd_le_trace_h (A i) (hA i)).trans
  rw [←htr]
  exact Finset.single_le_sum (fun j _ => realTrace_nonneg (hA j)) (Finset.mem_univ i)

lemma fixedPart_norm_le_one (e : Fin n → Fin N) (base : Coordinates N)
    (A : Fin N → H d) (hA : ∀ i,A i∈psdCone d)
    (htr : ∑ i,Hermitian.realTrace (A i)=1) (hb : Cube base) : ‖fixedPart e base A‖≤1 := by
  unfold fixedPart
  apply norm_sum_le _ _ |>.trans
  rw [←htr]
  apply Finset.sum_le_sum
  intro i _
  cases hi : lookup e i with
  | none =>
    simp only [Option.elim_none,norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (hb i) (norm_nonneg _)).trans
      (by simpa only [one_mul] using norm_psd_le_trace_h (A i) (hA i))
  | some j => simpa only [Option.elim_some,norm_zero] using realTrace_nonneg (hA i)

lemma face_order_bounds (e : Fin n → Fin N) (he : Function.Injective e)
    (base : Coordinates N) (A : Fin N → H d)
    (hA : ∀ i,A i∈psdCone d) (htr : ∑ i,Hermitian.realTrace (A i)=1)
    (hb : Cube base) (y : Coordinates n) (hy : Cube y) :
    -(Hermitian.one : H d)≤fixedPart e base A+S (fun j => A (e j)) y ∧
    fixedPart e base A+S (fun j => A (e j)) y≤(Hermitian.one : H d) := by
  rw [←S_extend e he]
  exact S_bounds A hA htr (real_extend_cube e base y hb hy)

lemma face_eta_one_bound (e : Fin n → Fin N) (he : Function.Injective e)
    (base : Coordinates N) (A : Fin N → H d)
    (hvar : (∑ i,sandwich (A i) (Hermitian.one : H d))≤(Hermitian.one : H d))
    (hb : Cube base) (hfixed : ∀ i,lookup e i=none → |base i|=1)
    (y : Coordinates n) (hy : Cube y) :
    eta 384 (fun j => A (e j)) y (Hermitian.one : H d)≤(384:ℝ) • (Hermitian.one : H d) := by
  rw [←eta_extend e he base A hfixed y]
  have hv : (∑ i,sandwich (A i) (Hermitian.one : H d))≤(1:ℝ) • (Hermitian.one : H d) := by simpa using hvar
  simpa only [mul_one] using eta_one_bound (by norm_num : (0:ℝ)≤384) A hv
    (real_extend_cube e base y hb hy)

lemma strip_nearby (x y : Coordinates n) {σ r : ℝ} (hr : 0≤r)
    (hx : ∀ i,|x i|≤1-σ) (hy : ‖y-x‖≤r) (hrσ : r≤σ/2) :
    ∀ i,|y i|≤1-σ/2 := by
  intro i
  have hnorm := (pi_norm_le_iff_of_nonneg hr).mp hy i
  change ‖y i-x i‖≤r at hnorm
  rw [Real.norm_eq_abs] at hnorm
  have hab := (abs_sub_le (y i) (x i) 0)
  simp only [sub_zero] at hab
  linarith [hx i]

theorem face_smooth_and_derivatives [NeZero d]
    (e : Fin n → Fin N) (he : Function.Injective e)
    (base : Coordinates N) (A : Fin N → H d)
    (hA : ∀ i,A i∈psdCone d) (htr : ∑ i,Hermitian.realTrace (A i)=1)
    (hvar : (∑ i,sandwich (A i) (Hermitian.one : H d))≤(Hermitian.one : H d))
    (hb : Cube base) (hfixed : ∀ i,lookup e i=none → |base i|=1)
    {ε σ lam : ℝ} (hε : 0<ε) (hεd : ε*d≤1) (hσ : 0<σ)
    (y : Coordinates n) (hy : ∀ j,|y j|≤1-σ/2) :
    ContDiffAt ℝ ∞ (facePotential ε lam (fixedPart e base A) (fun j => A (e j))) y ∧
    ∀ u,‖u‖≤1 →
      |iteratedDeriv 2 (fun t : ℝ => facePotential ε lam (fixedPart e base A)
        (fun j => A (e j)) (y+t • u)) 0|≤potentialCurveBound d n ε σ lam ∧
      |iteratedDeriv 3 (fun t : ℝ => facePotential ε lam (fixedPart e base A)
        (fun j => A (e j)) (y+t • u)) 0|≤potentialCurveBound d n ε σ lam := by
  have hyi : ∀ j,|y j|<1 := fun j => strip_interior hσ (hy j)
  have hyc : Cube y := fun j => (hyi j).le
  have hord := face_order_bounds e he base A hA htr hb y hyc
  have hη := face_eta_one_bound e he base A hvar hb hfixed y hyc
  have hAn : ∀ j,‖A (e j)‖≤1 := fun j => norm_atoms_le_one A hA htr (e j)
  have hS₀ : ‖fixedPart e base A‖≤(d:ℝ)+1 := by
    have hh := fixedPart_norm_le_one e base A hA htr hb
    linarith [Nat.cast_nonneg (α:=ℝ) d]
  exact ⟨contDiffAt_facePotential _ _ y hε hεd hyi hord.1 hord.2 hη,
    fun u hu => facePotential_strip_derivatives _ (fun j => hA (e j)) hAn _ hS₀
      y u hε hεd hσ hy hu hord.1 hord.2 hη⟩

end
end CurrentKS.RationalFace

end OAI
