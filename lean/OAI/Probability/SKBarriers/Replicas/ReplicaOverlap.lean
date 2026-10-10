import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianSpinTrace

namespace OAI

section

section
namespace SK.Analytic
open Matrix
section ReplicaOverlap
variable {S I : Type} [Fintype S] [Fintype I]

def finiteReplicaMoment (p : S → ℝ) (g : S → S → ℝ) : ℝ := ∑ s, ∑ t, p s*p t*g s t

theorem finiteReplicaMoment_dot (p : S → ℝ) (v : S → I → ℝ) :
    finiteReplicaMoment p (fun s t => v s ⬝ᵥ v t) = finiteMean p v ⬝ᵥ finiteMean p v := by
  simp only [finiteMean,finiteReplicaMoment,sum_dotProduct,dotProduct_sum,
    smul_dotProduct,dotProduct_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [dotProduct_comm (v t) (v s)]
  ring

theorem finiteReplicaMoment_square (p : S → ℝ) (v : S → I → ℝ) :
    finiteReplicaMoment p (fun s t => (v s ⬝ᵥ v t)^2) =
      ∑ i, ∑ j, (finiteCovariance p v i j+finiteMean p v i*finiteMean p v j)^2 := by
  simp only [finiteCovariance_apply,sub_add_cancel]
  have h (s t : S) : (v s ⬝ᵥ v t)^2 = ∑ i, ∑ j, (v s i*v t i)*(v s j*v t j) := by
    unfold dotProduct
    rw [pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  simp only [finiteReplicaMoment,h,Finset.mul_sum,pow_two]
  calc
    _ = ∑ s, ∑ i, ∑ j, ∑ t, p s*p t*(v s i*v t i*(v s j*v t j)) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, ∑ s, ∑ t, p s*p t*(v s i*v t i*(v s j*v t j)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      ring

theorem finiteReplica_variance_identity (p : S → ℝ) (v : S → I → ℝ)
    (hp : ∑ s, p s = 1) :
    finiteReplicaMoment p (fun s t => (v s ⬝ᵥ v t-finiteMean p v ⬝ᵥ finiteMean p v)^2) =
      ((finiteCovariance p v)*(finiteCovariance p v)).trace+
        2*(finiteMean p v ⬝ᵥ (finiteCovariance p v)*ᵥ finiteMean p v) := by
  let C := finiteCovariance p v
  let m := finiteMean p v
  have hsymm (i j : I) : C i j = C j i := by
    simp only [C,finiteCovariance_apply]
    congr 1
    · apply Finset.sum_congr rfl; intro s _; ring
    · ring
  have hsquare : finiteReplicaMoment p (fun s t => (v s ⬝ᵥ v t-m ⬝ᵥ m)^2) =
      finiteReplicaMoment p (fun s t => (v s ⬝ᵥ v t)^2)-(m ⬝ᵥ m)^2 := by
    have he (s t : S) : p s*p t*(v s ⬝ᵥ v t-m ⬝ᵥ m)^2 =
        p s*p t*(v s ⬝ᵥ v t)^2-2*(p s*p t*(v s ⬝ᵥ v t))*(m ⬝ᵥ m)+
          p s*p t*(m ⬝ᵥ m)^2 := by ring
    unfold finiteReplicaMoment
    simp_rw [he]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_mul,← Finset.mul_sum,hp,mul_one,one_mul]
    change finiteReplicaMoment p (fun s t => (v s ⬝ᵥ v t)^2)-
      2*finiteReplicaMoment p (fun s t => v s ⬝ᵥ v t)*(m ⬝ᵥ m)+(m ⬝ᵥ m)^2 = _
    rw [finiteReplicaMoment_dot]
    dsimp only [m,finiteReplicaMoment]
    ring
  rw [hsquare,finiteReplicaMoment_square]
  change (∑ i, ∑ j, (C i j+m i*m j)^2)-(m ⬝ᵥ m)^2 = _
  have he (i j : I) : (C i j+m i*m j)^2 = C i j*C j i+2*(m i*C i j*m j)+(m i*m j)^2 := by rw [hsymm j i]; ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  have hmm : (∑ i, ∑ j, (m i*m j)^2) = (m ⬝ᵥ m)^2 := by
    simp only [dotProduct,pow_two,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [hmm]
  have hquad : (∑ i, ∑ j, m i*C i j*m j) = m ⬝ᵥ C*ᵥ m := by
    simp only [dotProduct,mulVec,Finset.mul_sum,mul_assoc]
  rw [hquad]
  change ((C*C).trace+2*(m ⬝ᵥ C*ᵥ m)+(m ⬝ᵥ m)^2)-(m ⬝ᵥ m)^2 = _
  ring

omit [Fintype I] in
theorem finiteMean_abs_le_one (p : S → ℝ) (v : S → I → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hs : ∑ s, p s = 1) (hv : ∀ s i, |v s i| ≤ 1) (i : I) :
    |finiteMean p v i| ≤ 1 := by
  rw [finiteMean_apply]
  calc
    _ ≤ ∑ s, |p s*v s i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s, p s*|v s i| := by simp only [abs_mul,abs_of_nonneg (hp _)]
    _ ≤ ∑ s, p s*1 := Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hv s i) (hp s))
    _ = 1 := by simp only [mul_one,hs]

theorem quadratic_le_sqrt_trace (C : Matrix I I ℝ) (hC : C.IsHermitian) (u : I → ℝ) :
    u ⬝ᵥ C*ᵥ u ≤ Real.sqrt ((C*C).trace)*(u ⬝ᵥ u) := by
  have hs (i j : I) : C j i = C i j := by simpa only [star_trivial] using hC.apply i j
  have ht : (C*C).trace = ∑ z : I×I, (C z.1 z.2)^2 := by
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Fintype.sum_prod_type,hs,pow_two]
  have hq : u ⬝ᵥ C*ᵥ u = ∑ z : I×I, C z.1 z.2*(u z.1*u z.2) := by
    simp only [dotProduct,mulVec,Finset.mul_sum,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  have huu : (∑ z : I×I, (u z.1*u z.2)^2) = (u ⬝ᵥ u)^2 := by
    simp only [Fintype.sum_prod_type,dotProduct,pow_two,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun z : I×I => C z.1 z.2) (fun z => u z.1*u z.2)
  rw [huu,← ht,← hq] at hc
  have ht₀ : 0 ≤ (C*C).trace := by rw [ht]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hu₀ : 0 ≤ u ⬝ᵥ u := by unfold dotProduct; exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have H := Real.le_sqrt_of_sq_le hc
  rwa [Real.sqrt_mul ht₀,Real.sqrt_sq_eq_abs,abs_of_nonneg hu₀] at H

theorem finiteReplica_variance_le (p : S → ℝ) (v : S → I → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hs : ∑ s, p s = 1) (hv : ∀ s i, |v s i| ≤ 1) :
    finiteReplicaMoment p (fun s t => (v s ⬝ᵥ v t-finiteMean p v ⬝ᵥ finiteMean p v)^2) ≤
      ((finiteCovariance p v)*(finiteCovariance p v)).trace+
        2*(Fintype.card I : ℝ)*Real.sqrt (((finiteCovariance p v)*(finiteCovariance p v)).trace) := by
  rw [finiteReplica_variance_identity p v hs]
  have hq := quadratic_le_sqrt_trace (finiteCovariance p v) (finiteCovariance_posSemidef p v hp hs).isHermitian (finiteMean p v)
  have hm : finiteMean p v ⬝ᵥ finiteMean p v ≤ (Fintype.card I : ℝ) := by
    unfold dotProduct
    calc
      _ ≤ ∑ _ : I, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [pow_two] using (sq_le_one_iff_abs_le_one _).mpr (finiteMean_abs_le_one p v hp hs hv i)
      _ = _ := by simp
  have H := mul_le_mul_of_nonneg_left hm (Real.sqrt_nonneg (((finiteCovariance p v)*(finiteCovariance p v)).trace))
  nlinarith
end ReplicaOverlap
end SK.Analytic

end

end

end OAI
