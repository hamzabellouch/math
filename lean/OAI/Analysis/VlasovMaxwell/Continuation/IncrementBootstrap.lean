import Mathlib
import OAI.Analysis.VlasovMaxwell.Geometry.ParticleBySpacetime

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma norm_fderiv_q_le (v : Vec) : ‖fderiv ℝ q v‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro h
  rw [fderiv_q_apply,Real.norm_eq_abs,one_mul]
  calc
    _ ≤ ‖velocity v‖ * ‖h‖ := by simpa only [dot_eq_inner] using abs_real_inner_le_norm (velocity v) h
    _ ≤ ‖h‖ := mul_le_of_le_one_left (norm_nonneg h) (norm_velocity_lt_one v).le

lemma q_lipschitz (v w : Vec) : |q w-q v| ≤ ‖w-v‖ := by
  have h := (convex_univ : Convex ℝ (univ : Set Vec)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => contDiff_q.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) x)
    (fun x _ => norm_fderiv_q_le x) (mem_univ v) (mem_univ w)
  simpa only [Real.norm_eq_abs,one_mul] using h

lemma norm_relativistic_projection_le (u h : Vec) (hu : ‖u‖ ≤ 1) :
    ‖h-dot u h • u‖ ≤ ‖h‖ := by
  have hsq : ‖h-dot u h • u‖^2 = ‖h‖^2-2*(dot u h)^2+(dot u h)^2*‖u‖^2 := by
    rw [norm_sub_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,← dot_eq_inner,
      dot_smul_right,dot_comm h u]
    ring
  have hu2 : ‖u‖^2 ≤ 1 := by nlinarith [norm_nonneg u]
  have hh := mul_le_mul_of_nonneg_left hu2 (sq_nonneg (dot u h))
  nlinarith [norm_nonneg (h-dot u h • u),norm_nonneg h,sq_nonneg (dot u h)]

lemma norm_fderiv_velocity_le (v : Vec) : ‖fderiv ℝ velocity v‖ ≤ (q v)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (q_pos v).le)
  intro h
  rw [fderiv_velocity_apply,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (q_pos v))]
  exact mul_le_mul_of_nonneg_left
    (norm_relativistic_projection_le _ _ (norm_velocity_lt_one v).le)
    (inv_nonneg.mpr (q_pos v).le)

lemma velocity_local_lipschitz (v w : Vec) (hvw : ‖w-v‖ ≤ q v/2) :
    ‖velocity w-velocity v‖ ≤ (2/q v)*‖w-v‖ := by
  apply (convex_closedBall v (q v/2)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => contDiff_velocity.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) x)
    (fun x hx => ?_) (mem_closedBall_self (div_nonneg (q_pos v).le (by norm_num)))
    (by simpa only [mem_closedBall,dist_eq_norm] using hvw)
  have hb : q v/2 ≤ q x := by
    have h := q_lipschitz x v
    rw [norm_sub_rev] at h
    have hx' : ‖x-v‖ ≤ q v/2 := hx
    have hh := (le_abs_self (q v-q x)).trans h
    linarith
  calc
    _ ≤ (q x)⁻¹ := norm_fderiv_velocity_le x
    _ ≤ (q v/2)⁻¹ := inv_anti₀ (half_pos (q_pos v)) hb
    _ = 2/q v := by field_simp

lemma continuous_barrier {f : ℝ → ℝ} {a b R C : ℝ} (_hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (ha : f a < R) (hCR : C < R)
    (hstop : ∀ t ∈ Icc a b, (∀ u ∈ Icc a t, f u ≤ R) → f t ≤ C) :
    ∀ t ∈ Icc a b, f t ≤ C := by
  have hlt : ∀ t ∈ Icc a b, f t < R := by
    intro t ht
    by_contra ht'
    have hRt : R ≤ f t := le_of_not_gt ht'
    obtain ⟨x,hx,hfx⟩ := intermediate_value_Icc ht.1 (hf.mono (Icc_subset_Icc_right ht.2)) ⟨ha.le,hRt⟩
    let S : Set ℝ := Icc a b ∩ f ⁻¹' {R}
    have hS : IsCompact S := isCompact_Icc.of_isClosed_subset
      (hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
    obtain ⟨m,hm,hmin⟩ := hS.exists_isMinOn ⟨x,⟨⟨hx.1,hx.2.trans ht.2⟩,hfx⟩⟩ continuousOn_id
    have hall : ∀ u ∈ Icc a m, f u ≤ R := by
      intro u hu
      by_contra hu'
      have hRu : R < f u := lt_of_not_ge hu'
      obtain ⟨y,hy,hey⟩ := intermediate_value_Icc hu.1
        (hf.mono (Icc_subset_Icc_right (hu.2.trans hm.1.2))) ⟨ha.le,hRu.le⟩
      have hyS : y ∈ S := ⟨⟨hy.1,hy.2.trans (hu.2.trans hm.1.2)⟩,hey⟩
      have hmu : m ≤ u := (hmin hyS).trans hy.2
      have he : u=m := le_antisymm hu.2 hmu
      have hfm : f m=R := hm.2
      rw [he,hfm] at hRu
      exact (lt_irrefl _ hRu)
    have hb := hstop m hm.1 hall
    have hfm : f m=R := hm.2
    rw [hfm] at hb
    exact (not_le_of_gt hCR) hb
  intro t ht
  exact hstop t ht (fun u hu => (hlt u ⟨hu.1,hu.2.trans ht.2⟩).le)

lemma momentum_stopping {V : ℝ → Vec} {a b ε : ℝ} (hab : a ≤ b)
    (hV : ContinuousOn V (Icc a b)) (hε : ε < q (V a)/2)
    (hb : ∀ t ∈ Icc a b, (∀ u ∈ Icc a t,
      q (V a)/2 ≤ q (V u) ∧ q (V u) ≤ 2*q (V a)) → ‖V t-V a‖ ≤ ε) :
    ∀ t ∈ Icc a b, ‖V t-V a‖ ≤ ε ∧
      q (V a)/2 ≤ q (V t) ∧ q (V t) ≤ 2*q (V a) := by
  have hband (u : ℝ) (hu : ‖V u-V a‖ ≤ q (V a)/2) :
      q (V a)/2 ≤ q (V u) ∧ q (V u) ≤ 2*q (V a) := by
    have h := (q_lipschitz (V a) (V u)).trans hu
    rw [abs_le] at h
    constructor <;> linarith [q_pos (V a)]
  have hbound := continuous_barrier hab ((hV.sub continuousOn_const).norm)
    (by simpa only [Pi.sub_apply,sub_self,norm_zero] using (half_pos (q_pos (V a)))) hε
    (fun t ht hu => hb t ht (fun u hu' => hband u (hu u hu')))
  intro t ht
  exact ⟨hbound t ht,hband t ((hbound t ht).trans hε.le)⟩

lemma one_le_q (v : Vec) : 1 ≤ q v := by
  have := q_sq v
  have := q_pos v
  nlinarith [sq_nonneg ‖v‖]

def IncrementBootstrap (V : ℝ → Vec) (T M A P L : ℝ) : Prop :=
  ∀ (n : ℕ) (a b : ℝ), 0 ≤ a → a ≤ b → b ≤ T →
    (∀ t ∈ Icc a b, (2 : ℝ)^n/8 ≤ q (V t) ∧ q (V t) ≤ 8*(2 : ℝ)^n) →
    ‖V b-V a‖ ≤ M*P*Real.sqrt (b-a)+A*(b-a)*(P^2*L/(2 : ℝ)^n)

lemma IncrementBootstrap.stopped_forward {V : ℝ → Vec} {T M A P L a b ε : ℝ}
    (H : IncrementBootstrap V T M A P L) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hV : ContinuousOn V (Icc a b)) (hM : 0 ≤ M) (hA : 0 ≤ A) (hP : 0 ≤ P)
    (hL : 0 ≤ L) (hε : ε < q (V a)/2)
    (hstep : M*P*Real.sqrt (b-a)+2*A*(b-a)*P^2*L/q (V a) ≤ ε) :
    ∀ t ∈ Icc a b, ‖V t-V a‖ ≤ ε ∧
      q (V a)/2 ≤ q (V t) ∧ q (V t) ≤ 2*q (V a) := by
  obtain ⟨n,hnlo,hnhi⟩ := exists_nat_pow_near (one_le_q (V a)) (by norm_num : (1 : ℝ)<2)
  have hn : 0 < (2 : ℝ)^n := by positivity
  have hq : q (V a) ≤ 2*(2 : ℝ)^n := by
    rw [pow_succ] at hnhi
    nlinarith
  apply momentum_stopping hab hV hε
  intro t ht htband
  have hta := ht.1
  have htb := ht.2
  have hqa := q_pos (V a)
  have hband : ∀ u ∈ Icc a t, (2 : ℝ)^n/8 ≤ q (V u) ∧ q (V u) ≤ 8*(2 : ℝ)^n := by
    intro u hu
    have hu' := htband u hu
    constructor <;> nlinarith
  have Ht := H n a t ha ht.1 (ht.2.trans hb) hband
  have hrat : 1/(2 : ℝ)^n ≤ 2/q (V a) := by
    apply (div_le_div_iff₀ hn (q_pos (V a))).mpr
    nlinarith
  have hfirst : M*P*Real.sqrt (t-a) ≤ M*P*Real.sqrt (b-a) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (mul_nonneg hM hP)
  have hsecond : A*(t-a)*(P^2*L/(2 : ℝ)^n) ≤ 2*A*(b-a)*P^2*L/q (V a) := by
    calc
      _ = (A*(t-a)*P^2*L)*(1/(2 : ℝ)^n) := by ring
      _ ≤ (A*(t-a)*P^2*L)*(2/q (V a)) :=
        mul_le_mul_of_nonneg_left hrat (by positivity)
      _ ≤ (A*(b-a)*P^2*L)*(2/q (V a)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hA) (sq_nonneg P)) hL
      _ = _ := by ring
  exact (Ht.trans (add_le_add hfirst hsecond)).trans hstep

lemma IncrementBootstrap.velocity_stopped_forward {V : ℝ → Vec} {T M A P L a b ε : ℝ}
    (H : IncrementBootstrap V T M A P L) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hV : ContinuousOn V (Icc a b)) (hM : 0 ≤ M) (hA : 0 ≤ A) (hP : 0 ≤ P)
    (hL : 0 ≤ L) (hε : ε < q (V a)/2)
    (hstep : M*P*Real.sqrt (b-a)+2*A*(b-a)*P^2*L/q (V a) ≤ ε) :
    ∀ t ∈ Icc a b, ‖V t-V a‖ ≤ ε ∧
      ‖velocity (V t)-velocity (V a)‖ ≤ 2*ε/q (V a) ∧
      q (V a)/2 ≤ q (V t) ∧ q (V t) ≤ 2*q (V a) := by
  intro t ht
  have hqa := q_pos (V a)
  have hs := H.stopped_forward ha hab hb hV hM hA hP hL hε hstep t ht
  refine ⟨hs.1,?_,hs.2⟩
  calc
    _ ≤ (2/q (V a))*‖V t-V a‖ := velocity_local_lipschitz _ _ (hs.1.trans hε.le)
    _ ≤ (2/q (V a))*ε := mul_le_mul_of_nonneg_left hs.1 (by positivity)
    _ = _ := by ring
end RVM

end

end OAI
