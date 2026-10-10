import OAI.Analysis.IntegralMeans.Eigenmeasure

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun
attribute [local irreducible] rerootClass

def positiveFunctionalCLM.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (Λ : C(X,ℝ) →ₗ[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f) : C(X,ℝ) →L[ℝ] ℝ :=
  Λ.mkContinuous (Λ 1) (positive_functional_bound Λ hp)

def intervalFunctional.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (A : ℝ → C(X,ℝ) →L[ℝ] C(X,ℝ))
    (hc : ∀ f, Continuous (fun t => A t f))
    (hp : ∀ t f, 0 ≤ f → 0 ≤ A t f)
    (Λ : C(X,ℝ) →L[ℝ] ℝ) (hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (a b : ℝ) (hab : a ≤ b) : C(X,ℝ) →L[ℝ] ℝ :=
  positiveFunctionalCLM
    { toFun := fun f => ∫ t in a..b, Λ (A t f)
      map_add' := by
        intro f g
        simp only [map_add]
        exact intervalIntegral.integral_add ((Λ.continuous.comp (hc f)).intervalIntegrable a b)
          ((Λ.continuous.comp (hc g)).intervalIntegrable a b)
      map_smul' := by
        intro c f
        simp only [map_smul,smul_eq_mul]
        exact intervalIntegral.integral_const_mul c _ }
    (by
      intro f hf
      exact intervalIntegral.integral_nonneg hab (fun t _ => hΛ _ (hp t f hf)))

lemma intervalFunctional_apply.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (A : ℝ → C(X,ℝ) →L[ℝ] C(X,ℝ))
    (hc : ∀ f, Continuous (fun t => A t f))
    (hp : ∀ t f, 0 ≤ f → 0 ≤ A t f)
    (Λ : C(X,ℝ) →L[ℝ] ℝ) (hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (a b : ℝ) (hab : a ≤ b) (f : C(X,ℝ)) :
    intervalFunctional A hc hp Λ hΛ a b hab f = ∫ t in a..b, Λ (A t f) := rfl

lemma intervalFunctional_nonneg.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (A : ℝ → C(X,ℝ) →L[ℝ] C(X,ℝ))
    (hc : ∀ f, Continuous (fun t => A t f))
    (hp : ∀ t f, 0 ≤ f → 0 ≤ A t f)
    (Λ : C(X,ℝ) →L[ℝ] ℝ) (hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (a b : ℝ) (hab : a ≤ b) (f : C(X,ℝ)) (hf : 0 ≤ f) :
    0 ≤ intervalFunctional A hc hp Λ hΛ a b hab f :=
  intervalIntegral.integral_nonneg hab (fun t _ => hΛ _ (hp t f hf))

def pointOperator (x y : ℝ) (hy : 0 < y) := affineOperator (halfPoint x y hy)

lemma pointOperator_mul (x y u v : ℝ) (hy : 0 < y) (hv : 0 < v) :
    pointOperator x y hy * pointOperator u v hv = pointOperator (x+y*u) (y*v) (mul_pos hy hv) := by
  simp only [pointOperator,affineOperator_mul,halfPoint_mul]

lemma pointOperator_zero_one : pointOperator 0 1 zero_lt_one = 1 := by
  have h : halfPoint 0 1 zero_lt_one = halfOne := by
    apply Subtype.ext
    simp [halfPoint,halfOne]
  rw [pointOperator,h,affineOperator_one]

lemma pointOperator_horizontal (x : ℝ) : pointOperator x 1 zero_lt_one = affineOperator (horizontal x) := rfl

lemma transfer_endpoint_step (v : ℝ) (hv : 0 < v) :
    transferOperator * (pointOperator (1+v) v hv-pointOperator (-1+v) v hv) =
      (1/2 : ℝ) • (pointOperator (1+v/2) (v/2) (by positivity)-
        pointOperator (-1+v/2) (v/2) (by positivity)) := by
  change ((1/2 : ℝ) • (pointOperator (-1/2) (1/2) (by norm_num)+
    pointOperator (1/2) (1/2) (by norm_num))) * _ = _
  rw [smul_mul_assoc,add_mul,mul_sub,mul_sub]
  simp only [pointOperator_mul]
  have h1 : -1/2+1/2*(1+v) = v/2 := by ring
  have h2 : -1/2+1/2*(-1+v) = -1+v/2 := by ring
  have h3 : 1/2+1/2*(1+v) = 1+v/2 := by ring
  have h4 : 1/2+1/2*(-1+v) = v/2 := by ring
  simp only [h1,h2,h3,h4,show (1/2 : ℝ)*v = v/2 by ring]
  congr 1
  abel

lemma transfer_endpoint (n : ℕ) :
    transferOperator^n * (affineOperator (horizontal 2)-1) =
      ((1/2 : ℝ)^n) • (pointOperator (1+(1/2 : ℝ)^n) ((1/2 : ℝ)^n) (by positivity)-
        pointOperator (-1+(1/2 : ℝ)^n) ((1/2 : ℝ)^n) (by positivity)) := by
  induction n with
  | zero =>
    simp only [pow_zero,one_mul,one_smul]
    norm_num only [show (1+(1 : ℝ)) = 2 by norm_num,show (-1+(1 : ℝ)) = 0 by norm_num]
    rw [pointOperator_zero_one,pointOperator_horizontal]
  | succ n ih =>
    rw [pow_succ',mul_assoc,ih,mul_smul_comm,transfer_endpoint_step,smul_smul]
    simp only [pow_succ,div_eq_mul_inv,one_mul]

lemma endpoint_norm_bound (n : ℕ) :
    ‖pointOperator (1+(1/2 : ℝ)^n) ((1/2 : ℝ)^n) (by positivity)-
      pointOperator (-1+(1/2 : ℝ)^n) ((1/2 : ℝ)^n) (by positivity)‖ ≤
      8192 / ((1/2 : ℝ)^n)^2 := by
  let v := (1/2 : ℝ)^n
  have hv : 0 < v := by positivity
  have hv1 : v ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hb (x : ℝ) (hx : |x| ≤ 2) : ‖pointOperator x v hv‖ ≤ 4096/v^2 := by
    apply affineOperator_norm_le (by positivity)
    intro g
    have hq := classFun_strip_bound_two g (halfPoint x v hv) (by simpa [halfPoint] using hx)
      (by simpa [halfPoint] using hv1)
    simp only [halfPoint,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] at hq
    rw [classWeight]
    have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 64/v)).mpr hq
    simpa only [halfPoint,div_pow,show (64 : ℝ)^2 = 4096 by norm_num] using hh
  have hp := hb (1+v) (by rw [abs_le]; constructor <;> linarith)
  have hm := hb (-1+v) (by rw [abs_le]; constructor <;> linarith)
  calc
    _ ≤ ‖pointOperator (1+v) v hv‖+‖pointOperator (-1+v) v hv‖ := norm_sub_le (pointOperator (1+v) v hv) (pointOperator (-1+v) v hv)
    _ ≤ 4096/v^2+4096/v^2 := add_le_add hp hm
    _ = 8192/v^2 := by ring

lemma eigenfunctional_pow (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ) (ρ : ℝ)
    (hΛ : ∀ f, Λ (transferOperator f) = ρ*Λ f) (n : ℕ) (f : C(DiskClass,ℝ)) :
    Λ ((transferOperator^n) f) = ρ^n*Λ f := by
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ',mul_apply_eq_comp,hΛ,ih]; ring

lemma eigenfunctional_horizontal_period (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ) (ρ : ℝ)
    (hρ : 2 < ρ) (hΛ : ∀ f, Λ (transferOperator f) = ρ*Λ f) (f : C(DiskClass,ℝ)) :
    Λ (affineOperator (horizontal 2) f) = Λ f := by
  have hρ0 : 0 < ρ := by linarith
  have hn (n : ℕ) : ‖Λ (affineOperator (horizontal 2) f)-Λ f‖ ≤
      (8192*‖Λ‖*‖f‖)*(2/ρ)^n := by
    let v := (1/2 : ℝ)^n
    let B := pointOperator (1+v) v (by positivity)-pointOperator (-1+v) v (by positivity)
    have he : ρ^n*(Λ (affineOperator (horizontal 2) f)-Λ f) = v*Λ (B f) := by
      rw [← map_sub,← eigenfunctional_pow Λ ρ hΛ]
      change Λ ((transferOperator^n * (affineOperator (horizontal 2)-1)) f) = _
      rw [transfer_endpoint]
      change Λ (v • B f) = _
      exact map_smul Λ v (B f)
    have hb : ‖B‖ ≤ 8192/v^2 := endpoint_norm_bound n
    have hh : ρ^n*‖Λ (affineOperator (horizontal 2) f)-Λ f‖ ≤
        v*(‖Λ‖*(8192/v^2*‖f‖)) := by
      calc
        _ = ‖v*Λ (B f)‖ := by rw [← he,norm_mul,Real.norm_of_nonneg (pow_nonneg hρ0.le n)]
        _ ≤ v*(‖Λ‖*(‖B‖*‖f‖)) := by
          rw [norm_mul,Real.norm_of_nonneg (by positivity : 0 ≤ v)]
          exact mul_le_mul_of_nonneg_left ((Λ.le_opNorm _).trans
            (mul_le_mul_of_nonneg_left (B.le_opNorm f) (norm_nonneg Λ))) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hb (norm_nonneg f)) (norm_nonneg Λ)) (by positivity)
    calc
      _ ≤ (v*(‖Λ‖*(8192/v^2*‖f‖)))/ρ^n :=
        (le_div_iff₀ (pow_pos hρ0 n)).mpr (by simpa only [mul_comm] using hh)
      _ = _ := by
        dsimp [v]
        simp only [div_pow,one_pow]
        field_simp
  have ht : Tendsto (fun n : ℕ => (8192*‖Λ‖*‖f‖)*(2/ρ)^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ 2/ρ)
      ((div_lt_one hρ0).mpr hρ)).const_mul (8192*‖Λ‖*‖f‖)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (ge_of_tendsto ht (Eventually.of_forall hn)) (norm_nonneg _)))

lemma positive_functional_strict.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [Nonempty X] (Λ : C(X,ℝ) →L[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (h1 : 0 < Λ 1) (f : C(X,ℝ)) (hf : ∀ x, 0 < f x) : 0 < Λ f := by
  obtain ⟨x,_,hx⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty f.continuous.continuousOn
  have hlo : (f x) • (1 : C(X,ℝ)) ≤ f := by intro y; simpa using hx (mem_univ y)
  have hh := hp (f-(f x) • 1) (sub_nonneg.mpr hlo)
  simp only [map_sub,map_smul,smul_eq_mul] at hh
  exact lt_of_lt_of_le (mul_pos (hf x) h1) (sub_nonneg.mp hh)

def probabilityFunctional.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : ProbabilityMeasure X) : C(X,ℝ) →L[ℝ] ℝ :=
  positiveFunctionalCLM
    { toFun := fun f => ∫ x, f x ∂(μ : Measure X)
      map_add' := fun f g => integral_add (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' := fun c f => integral_smul c f }
    (fun _ hf => integral_nonneg hf)

lemma probabilityFunctional_apply.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : ProbabilityMeasure X) (f : C(X,ℝ)) :
    probabilityFunctional μ f = ∫ x, f x ∂(μ : Measure X) := rfl

lemma probabilityFunctional_one.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : ProbabilityMeasure X) :
    probabilityFunctional μ 1 = 1 := by simp [probabilityFunctional_apply]

lemma probabilityFunctional_pos.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : ProbabilityMeasure X) (f : C(X,ℝ)) (hf : 0 ≤ f) :
    0 ≤ probabilityFunctional μ f := integral_nonneg hf

lemma periodic_dyadic_integral (F : ℝ → ℝ) (hc : Continuous F) (hp : Function.Periodic F 2) :
    (∫ x in (0 : ℝ)..2, (F (-1/2+x/2)+F (1/2+x/2))) = 2*∫ x in (0 : ℝ)..2, F x := by
  have hm : (∫ x in (0 : ℝ)..2, F (-1/2+x/2)) = 2*∫ x in (-1/2 : ℝ)..(1/2), F x := by
    have hh := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := 2) F
      (by norm_num : (1/2 : ℝ) ≠ 0) (-1/2)
    convert hh using 1 <;> (try { congr 1; funext x; congr 1; ring }); norm_num
  have hp' : (∫ x in (0 : ℝ)..2, F (1/2+x/2)) = 2*∫ x in (1/2 : ℝ)..(3/2), F x := by
    have hh := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := 2) F
      (by norm_num : (1/2 : ℝ) ≠ 0) (1/2)
    convert hh using 1 <;> (try { congr 1; funext x; congr 1; ring }); norm_num
  have hi : (∫ x in (-1/2 : ℝ)..(3/2), F x) = ∫ x in (0 : ℝ)..2, F x := by
    convert hp.intervalIntegral_add_eq (-1/2) 0 using 1 <;> norm_num
  have hcm : Continuous (fun x : ℝ => F (-1/2+x/2)) := hc.comp (continuous_const.add (continuous_id.div_const 2))
  have hcp : Continuous (fun x : ℝ => F (1/2+x/2)) := hc.comp (continuous_const.add (continuous_id.div_const 2))
  rw [intervalIntegral.integral_add (hcm.intervalIntegrable _ _) (hcp.intervalIntegrable _ _),hm,hp',← mul_add,
    intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),hi]

lemma continuous_pointOperator_x (y : ℝ) (hy : 0 < y) (f : C(DiskClass,ℝ)) :
    Continuous (fun x : ℝ => pointOperator x y hy f) :=
  (continuous_affineOperator_apply f).comp (continuous_halfPoint continuous_id continuous_const (fun _ => hy))

lemma continuous_horizontalOperator (f : C(DiskClass,ℝ)) :
    Continuous (fun x : ℝ => affineOperator (horizontal x) f) := continuous_pointOperator_x 1 zero_lt_one f

def horizontalAverage (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f) :
    C(DiskClass,ℝ) →L[ℝ] ℝ :=
  (1/2 : ℝ) • intervalFunctional (fun x => affineOperator (horizontal x)) continuous_horizontalOperator
    (fun _ => affineOperator_pos _) Λ hp 0 2 (by norm_num)

lemma horizontalAverage_apply (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (f : C(DiskClass,ℝ)) : horizontalAverage Λ hp f = (1/2 : ℝ)*∫ x in (0 : ℝ)..2, Λ (affineOperator (horizontal x) f) := rfl

lemma horizontalAverage_nonneg (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (f : C(DiskClass,ℝ)) (hf : 0 ≤ f) : 0 ≤ horizontalAverage Λ hp f := by
  rw [horizontalAverage_apply]
  apply mul_nonneg (by norm_num)
  exact intervalIntegral.integral_nonneg (by norm_num) (fun x _ => hp _ (affineOperator_pos _ f hf))

lemma horizontalAverage_mass_pos (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (h1 : 0 < Λ 1) : 0 < horizontalAverage Λ hp 1 := by
  rw [horizontalAverage_apply]
  apply mul_pos (by norm_num)
  apply intervalIntegral.integral_pos (by norm_num)
    (Λ.continuous.comp (continuous_horizontalOperator 1)).continuousOn
    (fun x _ => hp _ (affineOperator_pos _ 1 (by intro; simp)))
  refine ⟨0,by norm_num,?_⟩
  change 0 < Λ (pointOperator 0 1 zero_lt_one 1)
  rw [pointOperator_zero_one,one_apply_eq_self]
  exact h1

lemma functional_point_periodic (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ)
    (hper : ∀ f, Λ (affineOperator (horizontal 2) f) = Λ f)
    (y : ℝ) (hy : 0 < y) (f : C(DiskClass,ℝ)) :
    Function.Periodic (fun x : ℝ => Λ (pointOperator x y hy f)) 2 := by
  intro x
  have hh := hper (pointOperator x y hy f)
  rw [← pointOperator_horizontal,← mul_apply_eq_comp,pointOperator_mul] at hh
  simpa only [one_mul,add_comm x 2] using hh

lemma horizontalAverage_point (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (u v : ℝ) (hv : 0 < v) (f : C(DiskClass,ℝ)) :
    horizontalAverage Λ hp (pointOperator u v hv f) =
      (1/2 : ℝ)*∫ x in (0 : ℝ)..2, Λ (pointOperator (x+u) v hv f) := by
  rw [horizontalAverage_apply]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [← pointOperator_horizontal,← mul_apply_eq_comp,pointOperator_mul]
  simp only [one_mul]

lemma horizontalAverage_invariant (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (hper : ∀ f, Λ (affineOperator (horizontal 2) f) = Λ f)
    (t : ℝ) (f : C(DiskClass,ℝ)) :
    horizontalAverage Λ hp (affineOperator (horizontal t) f) = horizontalAverage Λ hp f := by
  rw [← pointOperator_horizontal,horizontalAverage_point]
  rw [intervalIntegral.integral_comp_add_right (fun x => Λ (pointOperator x 1 zero_lt_one f)) t]
  have hh := (functional_point_periodic Λ hper 1 zero_lt_one f).intervalIntegral_add_eq t 0
  rw [zero_add] at hh
  rw [zero_add,add_comm 2 t,hh,horizontalAverage_apply]
  rfl

lemma horizontalAverage_half_scale (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (hper : ∀ f, Λ (affineOperator (horizontal 2) f) = Λ f)
    (ρ : ℝ) (heig : ∀ f, Λ (transferOperator f) = ρ*Λ f) (f : C(DiskClass,ℝ)) :
    horizontalAverage Λ hp (pointOperator 0 (1/2) (by norm_num) f) = ρ*horizontalAverage Λ hp f := by
  have he (x : ℝ) : ρ*Λ (affineOperator (horizontal x) f) =
      (1/2 : ℝ)*(Λ (pointOperator (-1/2+x/2) (1/2) (by norm_num) f)+
        Λ (pointOperator (1/2+x/2) (1/2) (by norm_num) f)) := by
    rw [← heig]
    change Λ (((1/2 : ℝ) • (pointOperator (-1/2) (1/2) (by norm_num)+pointOperator (1/2) (1/2) (by norm_num)))
      (pointOperator x 1 zero_lt_one f)) = _
    rw [← mul_apply_eq_comp,smul_mul_assoc,add_mul]
    simp only [pointOperator_mul,mul_one,smul_apply,map_smul,add_apply,map_add,smul_eq_mul]
    simp only [show (1/2 : ℝ)*x = x/2 by ring]
  have hc : Continuous (fun x : ℝ => Λ (pointOperator x (1/2) (by norm_num) f)) :=
    Λ.continuous.comp (continuous_pointOperator_x _ _ f)
  have hi := periodic_dyadic_integral (fun x => Λ (pointOperator x (1/2) (by norm_num) f)) hc
    (functional_point_periodic Λ hper (1/2) (by norm_num) f)
  rw [horizontalAverage_point,horizontalAverage_apply]
  simp only [add_zero]
  rw [show ρ*((1/2 : ℝ)*∫ x in (0 : ℝ)..2, Λ (affineOperator (horizontal x) f)) =
    (1/2 : ℝ)*(∫ x in (0 : ℝ)..2, ρ*Λ (affineOperator (horizontal x) f)) by
      rw [intervalIntegral.integral_const_mul]; ring]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul,hi]
  ring

lemma period_average_invariant.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (A : ℝ → C(X,ℝ) →L[ℝ] C(X,ℝ))
    (hc : ∀ f, Continuous (fun t => A t f))
    (hp : ∀ t f, 0 ≤ f → 0 ≤ A t f)
    (hm : ∀ t s, A (t+s) = A t*A s)
    (Λ : C(X,ℝ) →L[ℝ] ℝ) (hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (l : ℝ) (hl : 0 ≤ l) (hper : ∀ f, Λ (A l f) = Λ f)
    (s : ℝ) (f : C(X,ℝ)) :
    intervalFunctional A hc hp Λ hΛ 0 l hl (A s f) =
      intervalFunctional A hc hp Λ hΛ 0 l hl f := by
  have hfper : Function.Periodic (fun t : ℝ => Λ (A t f)) l := by
    intro t
    dsimp only
    rw [add_comm t l,hm,mul_apply_eq_comp,hper]
  rw [intervalFunctional_apply,intervalFunctional_apply]
  have he (t : ℝ) : Λ (A t (A s f)) = Λ (A (t+s) f) := by rw [hm,mul_apply_eq_comp]
  simp_rw [he]
  rw [intervalIntegral.integral_comp_add_right (fun t => Λ (A t f)) s]
  simpa only [zero_add,add_comm l s] using hfper.intervalIntegral_add_eq s 0

lemma intervalFunctional_mass_pos.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (A : ℝ → C(X,ℝ) →L[ℝ] C(X,ℝ))
    (hc : ∀ f, Continuous (fun t => A t f))
    (hp : ∀ t f, 0 ≤ f → 0 ≤ A t f)
    (h0 : A 0 = 1)
    (Λ : C(X,ℝ) →L[ℝ] ℝ) (hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (h1 : 0 < Λ 1) (l : ℝ) (hl : 0 < l) :
    0 < intervalFunctional A hc hp Λ hΛ 0 l hl.le 1 := by
  rw [intervalFunctional_apply]
  apply intervalIntegral.integral_pos hl (Λ.continuous.comp (hc 1)).continuousOn
    (fun t _ => hΛ _ (hp _ _ (by intro; simp)))
  refine ⟨0,by simp [hl.le],?_⟩
  change 0 < Λ (A 0 1)
  simpa only [h0,one_apply_eq_self] using h1

def logScaledOperator (β t : ℝ) : C(DiskClass,ℝ) →L[ℝ] C(DiskClass,ℝ) :=
  Real.exp (β*t) • pointOperator 0 (Real.exp t) (Real.exp_pos t)

lemma logScaledOperator_apply (β t : ℝ) (f : C(DiskClass,ℝ)) :
    logScaledOperator β t f = Real.exp (β*t) • pointOperator 0 (Real.exp t) (Real.exp_pos t) f := rfl

lemma continuous_logScaledOperator (β : ℝ) (f : C(DiskClass,ℝ)) :
    Continuous (fun t => logScaledOperator β t f) := by
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
    ((continuous_affineOperator_apply f).comp
      (continuous_halfPoint continuous_const Real.continuous_exp Real.exp_pos))

lemma logScaledOperator_pos (β t : ℝ) (f : C(DiskClass,ℝ)) (hf : 0 ≤ f) :
    0 ≤ logScaledOperator β t f := by
  rw [logScaledOperator_apply]
  exact smul_nonneg (Real.exp_pos _).le (affineOperator_pos _ f hf)

lemma logScaledOperator_zero (β : ℝ) : logScaledOperator β 0 = 1 := by
  simp only [logScaledOperator,mul_zero,Real.exp_zero,one_smul,pointOperator_zero_one]

lemma logScaledOperator_add (β t s : ℝ) :
    logScaledOperator β (t+s) = logScaledOperator β t*logScaledOperator β s := by
  simp only [logScaledOperator,smul_mul_smul_comm,pointOperator_mul,mul_zero,add_zero,Real.exp_add,mul_add]

lemma logScaledOperator_horizontal (β t u : ℝ) :
    logScaledOperator β t*affineOperator (horizontal u) =
      affineOperator (horizontal (Real.exp t*u))*logScaledOperator β t := by
  simp only [logScaledOperator,← pointOperator_horizontal,smul_mul_assoc,mul_smul_comm,pointOperator_mul,
    mul_one,one_mul,mul_zero,zero_add,add_zero]

lemma horizontalAverage_log_period (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ)
    (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (hper : ∀ f, Λ (affineOperator (horizontal 2) f) = Λ f)
    (ρ : ℝ) (hρ : 0 < ρ) (heig : ∀ f, Λ (transferOperator f) = ρ*Λ f)
    (f : C(DiskClass,ℝ)) :
    horizontalAverage Λ hp (logScaledOperator (Real.log ρ/Real.log 2) (Real.log 2) f) =
      horizontalAverage Λ hp f := by
  have he := horizontalAverage_half_scale Λ hp hper ρ heig (pointOperator 0 2 (by norm_num) f)
  rw [← mul_apply_eq_comp,pointOperator_mul] at he
  norm_num only [mul_zero,add_zero,show (1/2 : ℝ)*2 = 1 by norm_num,pointOperator_zero_one,one_apply_eq_self] at he
  rw [logScaledOperator_apply,map_smul,smul_eq_mul]
  rw [div_mul_cancel₀ _ (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))),
    Real.exp_log hρ]
  simp only [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact he.symm

def scaleAverage (β : ℝ) (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ)
    (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f) : C(DiskClass,ℝ) →L[ℝ] ℝ :=
  intervalFunctional (logScaledOperator β) (continuous_logScaledOperator β) (logScaledOperator_pos β)
    Λ hp 0 (Real.log 2) (Real.log_nonneg (by norm_num))

lemma scaleAverage_apply (β : ℝ) (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ)
    (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f) (f : C(DiskClass,ℝ)) :
    scaleAverage β Λ hp f = ∫ t in (0 : ℝ)..Real.log 2, Λ (logScaledOperator β t f) := rfl

lemma scaleAverage_pos (β : ℝ) (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ)
    (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f) (f : C(DiskClass,ℝ)) (hf : 0 ≤ f) :
    0 ≤ scaleAverage β Λ hp f :=
  intervalFunctional_nonneg _ _ _ _ hp _ _ _ f hf

lemma scaleAverage_mass_pos (β : ℝ) (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ)
    (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f) (h1 : 0 < Λ 1) : 0 < scaleAverage β Λ hp 1 :=
  intervalFunctional_mass_pos _ _ _ (logScaledOperator_zero β) Λ hp h1 _ (Real.log_pos (by norm_num))

lemma scaleAverage_covariant (β : ℝ) (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ)
    (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (hper : ∀ f, Λ (logScaledOperator β (Real.log 2) f) = Λ f)
    (y : ℝ) (hy : 0 < y) (f : C(DiskClass,ℝ)) :
    scaleAverage β Λ hp (pointOperator 0 y hy f) = y^(-β)*scaleAverage β Λ hp f := by
  have he := period_average_invariant (logScaledOperator β) (continuous_logScaledOperator β)
    (logScaledOperator_pos β) (logScaledOperator_add β) Λ hp (Real.log 2)
    (Real.log_nonneg (by norm_num)) hper (Real.log y) f
  change scaleAverage β Λ hp (logScaledOperator β (Real.log y) f) = scaleAverage β Λ hp f at he
  simp only [logScaledOperator_apply,map_smul,smul_eq_mul,Real.exp_log hy] at he
  rw [Real.rpow_def_of_pos hy]
  have hinv : Real.exp (Real.log y*(-β))*Real.exp (β*Real.log y) = 1 := by
    rw [← Real.exp_add,show Real.log y*(-β)+β*Real.log y = 0 by ring,Real.exp_zero]
  calc
    _ = (Real.exp (Real.log y*(-β))*Real.exp (β*Real.log y))*scaleAverage β Λ hp (pointOperator 0 y hy f) := by rw [hinv,one_mul]
    _ = _ := by rw [mul_assoc,he]

lemma scaleAverage_horizontal (β : ℝ) (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ)
    (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (hh : ∀ u f, Λ (affineOperator (horizontal u) f) = Λ f)
    (u : ℝ) (f : C(DiskClass,ℝ)) :
    scaleAverage β Λ hp (affineOperator (horizontal u) f) = scaleAverage β Λ hp f := by
  rw [scaleAverage_apply,scaleAverage_apply]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [← mul_apply_eq_comp,logScaledOperator_horizontal,mul_apply_eq_comp,hh]

def transferRho : ℝ := growthRate transferOperator transferOperator_pow_norm_ge_one

def transferBeta : ℝ := Real.log transferRho/Real.log 2

lemma transferBeta_gt_one (hρ : 2 < transferRho) : 1 < transferBeta := by
  apply (lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  rw [one_mul]
  exact Real.log_lt_log (by norm_num) hρ

lemma exists_weighted_continuous_law (hρ : 2 < transferRho) :
    ∃ P : ProbabilityMeasure DiskClass, ∀ z : halfPlane, ∀ f : C(DiskClass,ℝ),
      (∫ g, classWeight g z*f (rerootClass g z) ∂(P : Measure DiskClass)) =
        (z.val.im)^(-transferBeta)*(∫ g, f g ∂(P : Measure DiskClass)) := by
  obtain ⟨μ,hμ⟩ := exists_growth_eigenmeasure transferOperator transferOperator_pos transferOperator_pow_norm_ge_one
  let Λ := probabilityFunctional μ
  have hp : ∀ f, 0 ≤ f → 0 ≤ Λ f := probabilityFunctional_pos μ
  have h1 : Λ 1 = 1 := probabilityFunctional_one μ
  have heig : ∀ f, Λ (transferOperator f) = transferRho*Λ f := hμ
  have hper := eigenfunctional_horizontal_period Λ transferRho hρ heig
  let H := horizontalAverage Λ hp
  have hH : ∀ f, 0 ≤ f → 0 ≤ H f := horizontalAverage_nonneg Λ hp
  have hH1 : 0 < H 1 := horizontalAverage_mass_pos Λ hp (by rw [h1]; norm_num)
  have hHper : ∀ f, H (logScaledOperator transferBeta (Real.log 2) f) = H f :=
    horizontalAverage_log_period Λ hp hper transferRho (by linarith) heig
  have hHh : ∀ u f, H (affineOperator (horizontal u) f) = H f := horizontalAverage_invariant Λ hp hper
  let ν := scaleAverage transferBeta H hH
  have hν : ∀ f, 0 ≤ f → 0 ≤ ν f := scaleAverage_pos transferBeta H hH
  have hν1 : 0 < ν 1 := scaleAverage_mass_pos transferBeta H hH hH1
  have hνh : ∀ u f, ν (affineOperator (horizontal u) f) = ν f := scaleAverage_horizontal transferBeta H hH hHh
  have hνs : ∀ y (hy : 0 < y) f, ν (pointOperator 0 y hy f) = y^(-transferBeta)*ν f :=
    scaleAverage_covariant transferBeta H hH hHper
  let PiF : C(DiskClass,ℝ) →L[ℝ] ℝ := (ν 1)⁻¹ • ν
  have hPiF : ∀ f, 0 ≤ f → 0 ≤ PiF f := fun f hf => mul_nonneg (inv_nonneg.mpr hν1.le) (hν f hf)
  have hPiF1 : PiF 1 = 1 := by change (ν 1)⁻¹*ν 1 = 1; exact inv_mul_cancel₀ (ne_of_gt hν1)
  obtain ⟨P,hP⟩ := probability_of_positive_functional PiF hPiF hPiF1
  refine ⟨P,fun z f => ?_⟩
  have hz : 0 < z.val.im := z.2
  have hez : affineOperator z = affineOperator (horizontal z.val.re)*pointOperator 0 z.val.im hz := by
    rw [← pointOperator_horizontal,pointOperator_mul]
    congr 1
    apply Subtype.ext
    simpa only [halfPoint,mul_zero,add_zero,one_mul] using z.val.re_add_im.symm
  change (∫ g, (affineOperator z f) g ∂(P : Measure DiskClass)) = _
  rw [hP,hP]
  change (ν 1)⁻¹*ν (affineOperator z f) = _
  rw [hez,mul_apply_eq_comp,hνh,hνs]
  change (ν 1)⁻¹*((z.val.im)^(-transferBeta)*ν f) = (z.val.im)^(-transferBeta)*((ν 1)⁻¹*ν f)
  ring

lemma weighted_measure_eq.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [PseudoMetrizableSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (w : C(X,ℝ)) (hw : ∀ x, 0 ≤ w x)
    (T : C(X,X)) (c : ℝ) (hc : 0 ≤ c)
    (he : ∀ f : C(X,ℝ), (∫ x, w x*f (T x) ∂μ) = c*∫ x, f x ∂μ) :
    Measure.map T (μ.withDensity (fun x => ENNReal.ofReal (w x))) = ENNReal.ofReal c • μ := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (w x))
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal
    (w.continuous.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace w)).hasFiniteIntegral
  have : (ENNReal.ofReal c • μ).Regular := Measure.Regular.smul (μ := μ) ENNReal.ofReal_ne_top
  have hwmeas : Measurable (fun x => ENNReal.ofReal (w x)) := w.continuous.measurable.ennreal_ofReal
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  change (∫ x, f.toContinuousMap x ∂Measure.map T (μ.withDensity (fun x => ENNReal.ofReal (w x)))) = ∫ x, f.toContinuousMap x ∂ENNReal.ofReal c • μ
  rw [integral_map T.continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul hwmeas (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hw _),smul_eq_mul]
  rw [he f.toContinuousMap,integral_smul_measure,ENNReal.toReal_ofReal hc,smul_eq_mul]

lemma weighted_lintegral_of_continuous.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [PseudoMetrizableSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (w : C(X,ℝ)) (hw : ∀ x, 0 ≤ w x)
    (T : C(X,X)) (c : ℝ) (hc : 0 ≤ c)
    (he : ∀ f : C(X,ℝ), (∫ x, w x*f (T x) ∂μ) = c*∫ x, f x ∂μ)
    (f : X → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, ENNReal.ofReal (w x)*f (T x) ∂μ) = ENNReal.ofReal c*∫⁻ x, f x ∂μ := by
  have hh := weighted_measure_eq μ w hw T c hc he
  have hi := congrArg (fun ν : Measure X => ∫⁻ x, f x ∂ν) hh
  rw [lintegral_map hf T.continuous.measurable, lintegral_smul_measure] at hi
  change (∫⁻ x, (f ∘ T) x ∂μ.withDensity (fun x => ENNReal.ofReal (w x))) = _ at hi
  rw [lintegral_withDensity_eq_lintegral_mul μ w.continuous.measurable.ennreal_ofReal (hf.comp T.continuous.measurable)] at hi
  simpa only [Pi.mul_apply,smul_eq_mul,Function.comp_def] using hi

end Brennan

end

end OAI
