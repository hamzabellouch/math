import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Energy

namespace OAI

noncomputable section
namespace BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal
open BalancedTransport.Geometry

structure SliceH2 (w : Space → Space) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) w
  l2 : ∀ i, MemLp (fun x => w x i) 2 (volume : Measure Space)
  d_l2 : ∀ i j, MemLp (fun x => pd j w x i) 2 (volume : Measure Space)
  dd_l2 : ∀ i j, MemLp (fun x => pd j (pd j w) x i) 2 (volume : Measure Space)

lemma sliceH2_of_CH {u : Velocity} (hu : Smooth u) (hH : CH 2 u) {t : ℝ} (ht : 0 ≤ t) :
    SliceH2 (u t) := by
  have hs := Smooth.slice hu ht
  exact ⟨hs, fun i => membrane_component (CH.memLp hH [] (by simp) ht) hs.continuous i,
    fun i j => membrane_component (CH.memLp hH [j] (by simp) ht) (pd_contDiff j hs).continuous i,
    fun i j => membrane_component (CH.memLp hH [j,j] (by simp) ht)
      (pd_contDiff j (pd_contDiff j hs)).continuous i⟩

lemma SliceH2.sub {u v : Space → Space} (hu : SliceH2 u) (hv : SliceH2 v) :
    SliceH2 (fun x => u x - v x) := by
  have he (j : Fin 3) : pd j (fun x => u x - v x) = fun x => pd j u x - pd j v x := by
    ext x i
    rw [pd_sub _ (hu.smooth.differentiable (by simp) x) (hv.smooth.differentiable (by simp) x)]
  refine ⟨hu.smooth.sub hv.smooth, fun i => (hu.l2 i).sub (hv.l2 i), ?_, ?_⟩
  · intro i j
    rw [he]
    exact (hu.d_l2 i j).sub (hv.d_l2 i j)
  · intro i j
    rw [he]
    have hh : pd j (fun x => pd j u x - pd j v x) =
        fun x => pd j (pd j u) x - pd j (pd j v) x :=
      funext (fun x => pd_sub j ((pd_contDiff j hu.smooth).differentiable (by simp) x)
        ((pd_contDiff j hv.smooth).differentiable (by simp) x))
    rw [hh]
    exact (hu.dd_l2 i j).sub (hv.dd_l2 i j)

lemma SliceH2.scalar_d {w : Space → Space} (hw : SliceH2 w) (i j : Fin 3) :
    MemLp (pd j (fun x => w x i)) 2 (volume : Measure Space) := by
  have he : pd j (fun x => w x i) = fun x => pd j w x i :=
    funext (fun x => pd_apply j i (hw.smooth.differentiable (by simp) x))
  rw [he]
  exact hw.d_l2 i j

lemma SliceH2.scalar_dd {w : Space → Space} (hw : SliceH2 w) (i j : Fin 3) :
    MemLp (pd j (pd j (fun x => w x i))) 2 (volume : Measure Space) := by
  have he : pd j (fun x => w x i) = fun x => pd j w x i :=
    funext (fun x => pd_apply j i (hw.smooth.differentiable (by simp) x))
  have he' : pd j (fun x => pd j w x i) = fun x => pd j (pd j w) x i :=
    funext (fun x => pd_apply j i ((pd_contDiff j hw.smooth).differentiable (by simp) x))
  rw [he, he']
  exact hw.dd_l2 i j

lemma minus_triple_bound {a x y C : ℝ} (ha : |a| ≤ C) (hC : 0 ≤ C) :
    -(a*x*y) ≤ C*(x^2+y^2) := by
  have hxy : |x| * |y| ≤ x^2+y^2 := by
    nlinarith [sq_nonneg (|x|-|y|), sq_abs x, sq_abs y, sq_nonneg x, sq_nonneg y]
  calc
    -(a*x*y) ≤ |a*x*y| := neg_le_abs _
    _ = |a| * (|x| * |y|) := by rw [abs_mul, abs_mul]; ring
    _ ≤ C * (|x| * |y|) := mul_le_mul_of_nonneg_right ha (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ ≤ C*(x^2+y^2) := mul_le_mul_of_nonneg_left hxy hC

lemma stretching_bound {a f g : Space → ℝ} {C : ℝ}
    (ha : Continuous a) (hb : ∀ x, ‖a x‖ ≤ C) (hC : 0 ≤ C)
    (hf : MemLp f 2 (volume : Measure Space)) (hg : MemLp g 2 (volume : Measure Space)) :
    -(∫ x, a x * f x * g x) ≤ C * ((∫ x, (f x)^2) + ∫ x, (g x)^2) := by
  have hff : Integrable (fun x => (f x)^2) (volume : Measure Space) := by
    simpa only [pow_two, Pi.mul_def] using hf.integrable_mul hf
  have hgg : Integrable (fun x => (g x)^2) (volume : Measure Space) := by
    simpa only [pow_two, Pi.mul_def] using hg.integrable_mul hg
  rw [← integral_neg, ← integral_add hff hgg, ← integral_const_mul]
  apply integral_mono (integrable_bounded_mul_l2_mul_l2 ha hb hf hg).neg
    ((hff.add hgg).const_mul C)
  exact fun x => minus_triple_bound (hb x) hC

theorem energy_pairing_bound
    {w a v g : Space → Space} {p : Space → ℝ} {ν C A : ℝ}
    (hw : SliceH2 w) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hp : ContDiff ℝ (⊤ : ℕ∞) p)
    (hν : 0 ≤ ν) (hC : 0 ≤ C)
    (ha_b : ∀ x, ‖a x‖ ≤ A) (ha_d : ∀ x j, ‖pd j a x‖ ≤ A)
    (hv_d : ∀ x j, ‖pd j v x‖ ≤ C)
    (ha_div : ∀ x, ∑ j, pd j a x j = 0)
    (hw_div : ∀ x, ∑ j, pd j w x j = 0)
    (hp₂ : MemLp p 2 (volume : Measure Space))
    (hp_d : ∀ j, MemLp (pd j p) 2 (volume : Measure Space))
    (hPDE : ∀ x i, g x i = ν * (∑ j, pd j (pd j w) x i) -
      (∑ j, a x j * pd j w x i) - (∑ j, w x j * pd j v x i) - pd i p x) :
    (∑ i : Fin 3, ∫ x, w x i * g x i) ≤
      6 * C * (∑ i : Fin 3, ∫ x, (w x i)^2) := by
  let E : Fin 3 → ℝ := fun i => ∫ x, (w x i)^2
  let D : Fin 3 → Fin 3 → ℝ := fun i j => ∫ x, w x i * pd j (pd j w) x i
  let T : Fin 3 → Fin 3 → ℝ := fun i j => ∫ x, a x j * pd j w x i * w x i
  let S : Fin 3 → Fin 3 → ℝ := fun i j => ∫ x, pd j v x i * w x j * w x i
  let P : Fin 3 → ℝ := fun i => ∫ x, w x i * pd i p x
  have hdcomp (i j : Fin 3) : pd j (fun x => w x i) = fun x => pd j w x i :=
    funext (fun x => pd_apply j i (hw.smooth.differentiable (by simp) x))
  have hddcomp (i j : Fin 3) : pd j (fun x => pd j w x i) = fun x => pd j (pd j w) x i :=
    funext (fun x => pd_apply j i ((pd_contDiff j hw.smooth).differentiable (by simp) x))
  have hDe (i j : Fin 3) : D i j = -∫ x, (pd j w x i)^2 := by
    simpa only [D, hdcomp, hddcomp] using
      diffusion_component (contDiff_pi.mp hw.smooth i) j (hw.l2 i)
        (hw.scalar_d i j) (hw.scalar_dd i j)
  have hDn (i j : Fin 3) : D i j ≤ 0 := by
    rw [hDe]
    exact neg_nonpos.mpr (integral_nonneg (fun _ => sq_nonneg _))
  have hTe (i : Fin 3) : ∑ j, T i j = 0 := by
    simpa only [T, pd_apply _ i (hw.smooth.differentiable (by simp) _)] using
      transport_cancellation ha (contDiff_pi.mp hw.smooth i) ha_b ha_d ha_div (hw.l2 i)
        (hw.scalar_d i)
  have hPe : ∑ i, P i = 0 := pressure_cancellation hw.smooth hp hw_div hw.l2
    (fun i => hw.d_l2 i i) hp₂ hp_d
  have hSb (i j : Fin 3) : -(S i j) ≤ C * (E j + E i) :=
    stretching_bound ((continuous_apply i).comp (pd_contDiff j hv).continuous)
      (fun x => (norm_le_pi_norm (pd j v x) i).trans (hv_d x j)) hC (hw.l2 j) (hw.l2 i)
  have hdint (i j : Fin 3) : Integrable (fun x => w x i * pd j (pd j w) x i)
      (volume : Measure Space) := (hw.l2 i).integrable_mul (hw.dd_l2 i j)
  have htint (i j : Fin 3) : Integrable (fun x => a x j * pd j w x i * w x i)
      (volume : Measure Space) :=
    integrable_bounded_mul_l2_mul_l2 ((continuous_apply j).comp ha.continuous)
      (fun x => (norm_le_pi_norm (a x) j).trans (ha_b x)) (hw.d_l2 i j) (hw.l2 i)
  have hsint (i j : Fin 3) : Integrable (fun x => pd j v x i * w x j * w x i)
      (volume : Measure Space) :=
    integrable_bounded_mul_l2_mul_l2 ((continuous_apply i).comp (pd_contDiff j hv).continuous)
      (fun x => (norm_le_pi_norm (pd j v x) i).trans (hv_d x j)) (hw.l2 j) (hw.l2 i)
  have hpint (i : Fin 3) : Integrable (fun x => w x i * pd i p x)
      (volume : Measure Space) := (hw.l2 i).integrable_mul (hp_d i)
  have he (i : Fin 3) : (∫ x, w x i * g x i) =
      ν * (∑ j, D i j) - (∑ j, T i j) - (∑ j, S i j) - P i := by
    have hfun : (fun x => w x i * g x i) = fun x =>
        ν * (∑ j, w x i * pd j (pd j w) x i) -
          (∑ j, a x j * pd j w x i * w x i) -
          (∑ j, pd j v x i * w x j * w x i) - w x i * pd i p x := by
      ext x
      rw [hPDE]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      ring
    have hdI : Integrable (fun x => ν * ∑ j, w x i * pd j (pd j w) x i)
        (volume : Measure Space) :=
      (integrable_finsetSum Finset.univ (fun j _ => hdint i j)).const_mul ν
    have htI : Integrable (fun x => ∑ j, a x j * pd j w x i * w x i)
        (volume : Measure Space) := integrable_finsetSum Finset.univ (fun j _ => htint i j)
    have hsI : Integrable (fun x => ∑ j, pd j v x i * w x j * w x i)
        (volume : Measure Space) := integrable_finsetSum Finset.univ (fun j _ => hsint i j)
    have hdtI : Integrable (fun x => ν * (∑ j, w x i * pd j (pd j w) x i) -
        ∑ j, a x j * pd j w x i * w x i) (volume : Measure Space) := hdI.sub htI
    have hdtsI : Integrable (fun x => ν * (∑ j, w x i * pd j (pd j w) x i) -
        (∑ j, a x j * pd j w x i * w x i) - ∑ j, pd j v x i * w x j * w x i)
        (volume : Measure Space) := hdtI.sub hsI
    rw [hfun, integral_sub hdtsI (hpint i), integral_sub hdtI hsI, integral_sub hdI htI]
    rw [integral_const_mul,
      integral_finsetSum _ (fun j _ => hdint i j),
      integral_finsetSum _ (fun j _ => htint i j),
      integral_finsetSum _ (fun j _ => hsint i j)]

  simp only [he, hTe, sub_zero, Finset.sum_sub_distrib, hPe, sub_zero]
  have hdiff : ∑ i, ν * (∑ j, D i j) ≤ 0 :=
    Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos hν
      (Finset.sum_nonpos (fun j _ => hDn i j)))
  have hstr := Finset.sum_le_sum (fun (i : Fin 3) (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun (j : Fin 3) (_ : j ∈ Finset.univ) => hSb i j))
  have hdouble : (∑ i : Fin 3, ∑ j : Fin 3, C * (E j + E i)) = 6*C*(∑ i, E i) := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hdouble] at hstr
  simp only [Finset.sum_neg_distrib] at hstr
  change _ ≤ 6*C*(∑ i, E i)
  linarith

end BalancedTransport.Analysis
end

end OAI
