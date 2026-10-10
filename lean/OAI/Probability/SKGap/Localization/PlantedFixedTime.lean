import Mathlib
import OAI.Probability.SKGap.Stability.PositiveRootStability
import OAI.Probability.SKGap.Stability.SmallRootStability

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators ENNReal

lemma badFieldSet_mono_margin {n : ℕ} (j A ε : ℝ) {c c' : ℝ} (h : c ≤ c') :
    badFieldSet n j A ε c ⊆ badFieldSet n j A ε c' := by
  rintro p ⟨a,ha,hd,x,hx,hq⟩
  exact ⟨a,ha,hd,x,hx,hq.trans h⟩

def plantedRootBad (n : ℕ) (j A K ε c ρ t : ℝ) :
    Set ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) :=
  {p | (∀ z : Field n,vectorNorm (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1)*ᵥz) ≤ K*vectorNorm z) ∧
    ∃ y : Field n,vectorNorm (tapField j (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1))
      (fun i=>t+p.2 i) y) ≤ ρ*sqrt (n:ℝ) ∧
      (goeMatrix (j/(n:ℝ)) p.1,y)∈badFieldSet n j A ε c}

lemma plantedRootBad_mono {n : ℕ} (j A K ε t : ℝ) {c c' ρ ρ' : ℝ}
    (hc : c ≤ c') (hρ : ρ ≤ ρ') :
    plantedRootBad n j A K ε c ρ t ⊆ plantedRootBad n j A K ε c' ρ' t := by
  rintro p ⟨hJ,y,hres,hy⟩
  exact ⟨hJ,y,hres.trans (mul_le_mul_of_nonneg_right hρ (sqrt_nonneg _)),
    badFieldSet_mono_margin j A ε hc hy⟩

lemma two_exponential_tails {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ r : ℝ,0 < r ∧ ∃ N : ℕ, ∀ n : ℕ,N ≤ n →
      4*exp (-a*(n:ℝ))+exp (-b*(n:ℝ)) ≤ exp (-r*(n:ℝ)) := by
  let r := min a b/2
  have hr : 0 < r := half_pos (lt_min ha hb)
  obtain ⟨N,hN⟩ := absorb_finite_exponential_factor 5 hr
  refine ⟨r,hr,N,fun n hn=>?_⟩
  have he₁ : exp (-a*(n:ℝ)) ≤ exp (-(2*r)*(n:ℝ)) :=
    exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by dsimp [r];linarith [min_le_left a b]) (Nat.cast_nonneg _))
  have he₂ : exp (-b*(n:ℝ)) ≤ exp (-(2*r)*(n:ℝ)) :=
    exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by dsimp [r];linarith [min_le_right a b]) (Nat.cast_nonneg _))
  have hh := hN n hn (-(2*r))
  calc
    _ ≤ 5*exp (-(2*r)*(n:ℝ)) := by linarith only [he₁,he₂]
    _ ≤ exp (-r*(n:ℝ)) := by
      convert hh using 1 <;> congr 1 <;> ring_nf

theorem planted_fixed_time_root_stability {j T : ℝ} (hj : 0 < j) (hj1 : j < 1)
    (hT : 0 < T) :
    ∃ A K ε c ρ a : ℝ,1 < A ∧ 2*sqrt j < K ∧ sqrt j*A < 1 ∧
      0 < ε ∧ 0 < c ∧ 0 < ρ ∧ 0 < a ∧ ∃ N : ℕ,0 < N ∧
    ∀ n : ℕ,N ≤ n → ∀ t ∈ Icc 0 T,
      ((gaussianCoordinates (MatrixCoordinates (Fin n))).prod
        (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal))).real
        (plantedRootBad n j A K ε c ρ t) ≤ exp (-a*(n:ℝ)) := by
  obtain ⟨A,K,q₀,cs,hA,hK,hq₀,hcs,hsub,hKj,hmargin⟩ := high_temperature_small_margin hj hj1
  have hK0 : 0 ≤ K := (mul_nonneg (by norm_num : (0:ℝ)≤2) (sqrt_nonneg _)).trans hK.le
  obtain ⟨ts,ρs,as,hts,hρs,has,Ns,hNs,hs⟩ := small_time_root_stability hj hj1 hA.le hK0 hKj hq₀ hmargin
  obtain ⟨ε,cp,ρp,ap,hε,hcp,hρp,hap,Np,hNp,hp⟩ := positive_time_root_stability hj hj1 hA.le hsub hK0
    (lt_min hts hT) (min_le_right ts T)
  have hd : 0 < min 1 (1/(π^2*j)) := lt_min zero_lt_one (by positivity)
  obtain ⟨a,ha,Na,hNa⟩ := two_exponential_tails hd (lt_min has hap)
  refine ⟨A,K,ε,min cs cp,min ρs ρp,a,hA,hK,hsub,hε,lt_min hcs hcp,
    lt_min hρs hρp,ha,max Na (max Ns Np),hNs.trans_le ((le_max_left _ _).trans (le_max_right _ _)),?_⟩
  intro n hn t ht
  have hns : Ns ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnp : Np ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hna : Na ≤ n := (le_max_left _ _).trans hn
  apply le_trans ?_ (hNa n hna)
  by_cases htt : t ≤ ts
  · have hh := hs n hns t ⟨ht.1,htt⟩ ε
    apply (measureReal_mono (plantedRootBad_mono j A K ε t (min_le_left _ _) (min_le_left _ _))
      (measure_ne_top _ _)).trans
    exact hh.trans (add_le_add le_rfl (exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left as ap)) (Nat.cast_nonneg _))))
  · have hh := hp n hnp t ⟨(min_le_left ts T).trans (not_le.mp htt).le,ht.2⟩
    apply (measureReal_mono (plantedRootBad_mono j A K ε t (min_le_right _ _) (min_le_right _ _))
      (measure_ne_top _ _)).trans
    exact hh.trans (add_le_add le_rfl (exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right as ap)) (Nat.cast_nonneg _))))
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators

lemma tapField_add_diagonal {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h y d : Field n) :
    tapField j (J+diagonal d) h y=tapField j J h y-(fun i=>d i*magnetization y i) := by
  ext i
  simp only [tapField,Matrix.add_apply,add_mul,Finset.sum_add_distrib,Pi.sub_apply]
  rw [show (∑ k,diagonal d i k*magnetization y k)=d i*magnetization y i by
    simp [Matrix.diagonal_apply]]
  ring

lemma tapField_diagonal_difference_bound {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (h y d : Field n)
    (hd : ∀ i,|d i| ≤ δ) :
    vectorNorm (tapField j (J+diagonal d) h y-tapField j J h y) ≤ δ*sqrt (n:ℝ) := by
  rw [tapField_add_diagonal,sub_sub_cancel_left]
  change ‖-(WithLp.toLp 2 (fun i=>d i*magnetization y i))‖ ≤ _
  rw [norm_neg]
  exact (vectorNorm_diag_le hδ hd (magnetization y)).trans
    (mul_le_mul_of_nonneg_left (magnetization_norm_bound y) hδ)

lemma hessian_diagonal_difference {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (y a d x : Field n) (ha : ∀ i,0 ≤ a i) :
    quadraticForm (fieldHessian j (J+diagonal d) y a) x-
      quadraticForm (fieldHessian j J y a) x = -(∑ i,a i*d i*x i^2) := by
  let v : Field n := fun i=>sqrt (a i)*x i
  have hq : quadraticForm (J+diagonal d) v-quadraticForm J v=∑ i,d i*v i^2 := by
    simp only [quadraticForm,Matrix.add_apply,mul_add,add_mul,Finset.sum_add_distrib,add_sub_cancel_left]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.diagonal_apply,ite_mul,mul_ite,mul_zero,zero_mul]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    ring
  rw [hessian_quadratic_formula,hessian_quadratic_formula]
  have hv : (∑ i,d i*v i^2)=∑ i,a i*d i*x i^2 := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [v]
    rw [mul_pow,sq_sqrt (ha i)]
    ring
  change _-quadraticForm (J+diagonal d) v-_ - (_-quadraticForm J v-_) = _
  rw [← hv]
  linarith only [hq]

lemma hessian_diagonal_difference_bound {n : ℕ} {A δ : ℝ} (hA : 0 ≤ A) (_hδ : 0 ≤ δ)
    (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (y a d x : Field n)
    (ha0 : ∀ i,0 ≤ a i) (haA : ∀ i,a i ≤ A) (hd : ∀ i,|d i| ≤ δ) :
    |quadraticForm (fieldHessian j (J+diagonal d) y a) x-
      quadraticForm (fieldHessian j J y a) x| ≤ A*δ*vectorSqNorm x := by
  rw [hessian_diagonal_difference j J y a d x ha0,abs_neg]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  unfold vectorSqNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simp only [abs_mul, abs_of_nonneg (ha0 i),abs_of_nonneg (sq_nonneg (x i))]
  exact mul_le_mul_of_nonneg_right (mul_le_mul (haA i) (hd i) (abs_nonneg _) hA) (sq_nonneg _)

lemma mulvec_add_diagonal_bound {n : ℕ} {K δ : ℝ} (hδ : 0 ≤ δ)
    (J : Matrix (Fin n) (Fin n) ℝ) (d : Field n)
    (hJ : ∀ z : Field n,vectorNorm (J*ᵥz) ≤ K*vectorNorm z) (hd : ∀ i,|d i| ≤ δ) :
    ∀ z : Field n,vectorNorm ((J+diagonal d)*ᵥz) ≤ (K+δ)*vectorNorm z := by
  intro z
  have he : diagonal d*ᵥz=(fun i=>d i*z i) := by ext i; exact mulVec_diagonal d z i
  rw [add_mulVec,he]
  calc
    _ ≤ vectorNorm (J*ᵥz)+vectorNorm (fun i=>d i*z i) := vectorNorm_add_le _ _
    _ ≤ K*vectorNorm z+δ*vectorNorm z := add_le_add (hJ z) (vectorNorm_diag_le hδ hd z)
    _ = _ := by ring
end SKGap
end
end

end OAI
