import Mathlib
import OAI.Analysis.VlasovMaxwell.Flow.FlowDerivative
import OAI.Analysis.VlasovMaxwell.Flow.LorentzPhase

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Filter
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set MeasureTheory

namespace RVM

lemma doubling_log_bound (N n : ℕ) :
    Real.log (2 + 1024 * (2 : ℝ)^(N+n)) ≤
      (Real.log 1026 + N * Real.log 2 + Real.log 2) * (n+1) := by
  have hp : 1 ≤ (2 : ℝ)^(N+n) := one_le_pow₀ (by norm_num)
  have h : 2 + 1024 * (2 : ℝ)^(N+n) ≤ 1026 * (2 : ℝ)^(N+n) := by linarith
  have hlog := Real.log_le_log (by positivity : 0 < 2 + 1024 * (2 : ℝ)^(N+n)) h
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hlog
  push_cast at hlog
  have h1026 : 0 ≤ Real.log 1026 := Real.log_nonneg (by norm_num)
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) h1026,
    mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      (mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) h2)]

lemma doubling_interval_lower_bound {M A C Δ : ℝ} {n : ℕ}
    (hM : 0 < M) (hA : 0 < A) (hC : 0 < C) (hΔ : 0 ≤ Δ)
    (h : (1 : ℝ)/2 ≤ 1024*M*Real.sqrt Δ + 1024^2*A*Δ*(C*(n+1))) :
    min ((4*1024*M)^2)⁻¹ (4*1024^2*A*C)⁻¹ / (n+1) ≤ Δ := by
  have hn : (1 : ℝ) ≤ n+1 := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  have hn0 : (0 : ℝ) < n+1 := by positivity
  have hs : 0 ≤ Real.sqrt Δ := Real.sqrt_nonneg _
  have hs2 := Real.sq_sqrt hΔ
  have hM' : 0 < 4*1024*M := by positivity
  have hA' : 0 < 4*1024^2*A*C := by positivity
  rcases le_total ((1 : ℝ)/4) (1024*M*Real.sqrt Δ) with hbig | hsmall
  · have hsq : 1 ≤ (4*1024*M)^2 * Δ := by
      have hh : 1 ≤ 4*1024*M*Real.sqrt Δ := by linarith
      have hhh : 1 ≤ (4*1024*M*Real.sqrt Δ)^2 := by nlinarith
      nlinarith
    have hlow : ((4*1024*M)^2)⁻¹ ≤ Δ := by
      rw [inv_eq_one_div,div_le_iff₀ (sq_pos_of_pos hM')]
      nlinarith [hsq]
    exact (div_le_self (by positivity : 0 ≤ min ((4*1024*M)^2)⁻¹
      (4*1024^2*A*C)⁻¹) hn).trans ((min_le_left _ _).trans hlow)
  · have hprod : 1 ≤ (4*1024^2*A*C)*(Δ*(n+1)) := by nlinarith
    have hlow : (4*1024^2*A*C)⁻¹ ≤ Δ*(n+1) := by
      rw [inv_eq_one_div,div_le_iff₀ hA']
      nlinarith [hprod]
    exact (div_le_div_of_nonneg_right (min_le_right _ _) hn0.le).trans
      ((div_le_iff₀ hn0).mpr hlow)

lemma no_bounded_harmonic_gaps {t : ℕ → ℝ} {c T : ℝ}
    (hc : 0 < c) (ht : ∀ n, t n ≤ T)
    (hg : ∀ n, c/(n+1) ≤ t (n+1)-t n) : False := by
  have hsum : Summable (fun n : ℕ => c/((n : ℝ)+1)) := by
    apply summable_of_sum_range_le (fun n => by positivity) (c := T-t 0)
    intro n
    calc
      ∑ i ∈ Finset.range n, c/((i : ℝ)+1) ≤
          ∑ i ∈ Finset.range n, (t (i+1)-t i) := Finset.sum_le_sum (fun i _ => hg i)
      _ = t n-t 0 := by
        rw [Finset.sum_sub_distrib]
        have hh := Finset.sum_range_sub' t n
        rw [Finset.sum_sub_distrib] at hh
        linarith
      _ ≤ T-t 0 := by linarith [ht n]
  have hh : Summable (fun n : ℕ => 1/((n : ℝ)+1)) := by
    apply (hsum.mul_left c⁻¹).congr
    intro n
    simp [div_eq_mul_inv,hc.ne']
  apply Real.not_summable_one_div_natCast
  exact (summable_nat_add_iff 1).mp (by simpa only [Nat.cast_add,Nat.cast_one] using hh)

lemma no_bounded_doubling_times {t Δ : ℕ → ℝ} {M A T : ℝ} (N : ℕ)
    (hM : 0 < M) (hA : 0 < A) (ht : ∀ n, t n ≤ T)
    (hΔ : ∀ n, 0 ≤ Δ n) (hgap : ∀ n, Δ n ≤ t (n+1)-t n)
    (hinc : ∀ n, (1 : ℝ)/2 ≤ 1024*M*Real.sqrt (Δ n) +
      1024^2*A*Δ n*Real.log (2+1024*(2 : ℝ)^(N+n))) : False := by
  let C := Real.log 1026 + N * Real.log 2 + Real.log 2
  have hC : 0 < C := by
    dsimp [C]
    have h1 : 0 < Real.log 1026 := Real.log_pos (by norm_num)
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  let c := min ((4*1024*M)^2)⁻¹ (4*1024^2*A*C)⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  apply no_bounded_harmonic_gaps hc ht
  intro n
  apply (doubling_interval_lower_bound hM hA hC (hΔ n) ?_).trans (hgap n)
  apply (hinc n).trans
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left (doubling_log_bound N n)
    (mul_nonneg (mul_nonneg (by positivity) hA.le) (hΔ n))

end RVM

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace RVM
section TimeFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma det_time_triangular (L : (ℝ × E) →ₗ[ℝ] (ℝ × E))
    (hL : (LinearMap.fst ℝ ℝ E).comp L = LinearMap.fst ℝ ℝ E) :
    L.det = ((LinearMap.snd ℝ ℝ E).comp (L.comp (LinearMap.inr ℝ ℝ E))).det := by
  classical
  let b := Module.Basis.singleton Unit ℝ
  let c := Module.finBasis ℝ E
  let C := (LinearMap.snd ℝ ℝ E).comp (L.comp (LinearMap.inl ℝ ℝ E))
  let D := (LinearMap.snd ℝ ℝ E).comp (L.comp (LinearMap.inr ℝ ℝ E))
  have hf (z : ℝ × E) : (L z).1 = z.1 := LinearMap.congr_fun hL z
  have hm : LinearMap.toMatrix (b.prod c) (b.prod c) L =
      Matrix.fromBlocks 1 0 (LinearMap.toMatrix b c C) (LinearMap.toMatrix c c D) := by
    ext (i | i) (j | j)
    · simp [LinearMap.toMatrix, b, hf]
    · simp [LinearMap.toMatrix, b, hf]
    · simp [LinearMap.toMatrix, C]
    · simp [LinearMap.toMatrix, D]
  rw [← LinearMap.det_toMatrix (b.prod c), hm, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_one, one_mul, LinearMap.det_toMatrix]

def extendedField (f : ℝ × E → E) (z : ℝ × E) : ℝ × E := (1, f z)

lemma trace_extendedField {f : ℝ × E → E} (hf : Differentiable ℝ f)
    (hz : ∀ z : ℝ × E, LinearMap.trace ℝ E
      (fderiv ℝ (fun x => f (z.1,x)) z.2).toLinearMap = 0) (z : ℝ × E) :
    LinearMap.trace ℝ (ℝ × E) (fderiv ℝ (extendedField f) z).toLinearMap = 0 := by
  have hd := (hasFDerivAt_const (1 : ℝ) z).prodMk (hf z).hasFDerivAt
  have hd' : fderiv ℝ (extendedField f) z =
      (0 : (ℝ × E) →L[ℝ] ℝ).prod (fderiv ℝ f z) := hd.fderiv
  rw [hd',trace_prod_diagonal]
  have hleft : (LinearMap.fst ℝ ℝ E).comp
      (((0 : (ℝ × E) →L[ℝ] ℝ).prod (fderiv ℝ f z)).toLinearMap.comp
        (LinearMap.inl ℝ ℝ E)) = 0 := by ext; simp
  rw [hleft,map_zero,zero_add]
  have hx := (hf z).hasFDerivAt.comp (f := fun x : E => (z.1,x)) z.2
    ((hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2))
  have heq : (LinearMap.snd ℝ ℝ E).comp
      (((0 : (ℝ × E) →L[ℝ] ℝ).prod (fderiv ℝ f z)).toLinearMap.comp
        (LinearMap.inr ℝ ℝ E)) =
      (fderiv ℝ (fun x => f (z.1,x)) z.2).toLinearMap := by
    have hx' : fderiv ℝ (fun x => f (z.1,x)) z.2 =
      (fderiv ℝ f z).comp ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) := hx.fderiv
    rw [hx']
    rfl
  rw [heq]
  exact hz z

omit [FiniteDimensional ℝ E] in

lemma extended_time_component {f : ℝ × E → E} {α : ℝ → ℝ × E} {T : ℝ}
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt α (extendedField f (α t)) t) :
    ∀ t ∈ Icc 0 T, (α t).1 = (α 0).1 + t := by
  apply eq_of_has_deriv_right_eq (f' := fun _ => (1 : ℝ))
  · intro t ht
    simpa [extendedField] using
      (hd t ⟨ht.1,ht.2.le⟩).hasFDerivAt.fst.hasDerivAt.hasDerivWithinAt (s := Ici t)
  · intro t _
    simpa using ((hasDerivAt_id t).const_add (α 0).1).hasDerivWithinAt
  · exact (HasDerivAt.continuousOn hd).fst
  · fun_prop
  · simp

lemma exists_local_time_volume_flow {f : ℝ × E → E} (hf : ContDiff ℝ 2 f)
    (hdiv : ∀ z : ℝ × E, LinearMap.trace ℝ E
      (fderiv ℝ (fun x => f (z.1,x)) z.2).toLinearMap = 0) (t₀ : ℝ) (x₀ : E) :
    ∃ η > (0 : ℝ), ∃ α : E → ℝ → E, ∃ A : E → ℝ → (E →L[ℝ] E),
      (∀ x ∈ Metric.ball x₀ (1/2 : ℝ), α x 0 = x ∧
        (∀ t ∈ Icc 0 η, HasDerivAt (α x) (f (t₀+t,α x t)) t) ∧
        (∀ t ∈ Icc 0 η, HasFDerivAt (fun y => α y t) (A x t) x) ∧
        ∀ t ∈ Icc 0 η, (A x t).det = 1) ∧
      ∀ t ∈ Icc 0 η, Set.InjOn (fun x => α x t) (Metric.ball x₀ (1/2 : ℝ)) := by
  have hF : ContDiff ℝ 2 (extendedField f) := contDiff_const.prodMk hf
  obtain ⟨η,hη,β,D,hβ,hinj⟩ := exists_local_volume_flow hF
    (trace_extendedField (hf.differentiable (by norm_num)) hdiv) (t₀,x₀)
  have hmem {x : E} (hx : x ∈ Metric.ball x₀ (1/2 : ℝ)) :
      (t₀,x) ∈ Metric.ball (t₀,x₀) (1/2 : ℝ) := by
    simpa only [Metric.mem_ball,Prod.dist_eq,dist_self,max_eq_right (dist_nonneg : 0 ≤ dist x x₀)] using hx
  have htime {z : ℝ × E} (hz : z ∈ Metric.ball (t₀,x₀) (1/2 : ℝ))
      {t : ℝ} (ht : t ∈ Icc 0 η) : (β z t).1 = z.1+t := by
    simpa [(hβ z hz).1] using extended_time_component (hβ z hz).2.1 t ht
  have hfst {z : ℝ × E} (hz : z ∈ Metric.ball (t₀,x₀) (1/2 : ℝ))
      {t : ℝ} (ht : t ∈ Icc 0 η) :
      (LinearMap.fst ℝ ℝ E).comp (D z t).toLinearMap = LinearMap.fst ℝ ℝ E := by
    have hd := ((hβ z hz).2.2.1 t ht).fst
    have he : (fun y => (β y t).1) =ᶠ[𝓝 z] (fun y : ℝ × E => y.1+t) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
      exact htime hy ht
    have hd' : HasFDerivAt (fun y : ℝ × E => y.1+t) (ContinuousLinearMap.fst ℝ ℝ E) z :=
      hasFDerivAt_fst.add_const t
    exact congrArg ContinuousLinearMap.toLinearMap ((hd.congr_of_eventuallyEq he.symm).unique hd')
  let α : E → ℝ → E := fun x t => (β (t₀,x) t).2
  let A : E → ℝ → (E →L[ℝ] E) := fun x t => (ContinuousLinearMap.snd ℝ ℝ E).comp
    ((D (t₀,x) t).comp (ContinuousLinearMap.inr ℝ ℝ E))
  refine ⟨η,hη,α,A,?_,?_⟩
  · intro x hx
    have hh := hβ _ (hmem hx)
    refine ⟨congrArg Prod.snd hh.1,?_,?_,?_⟩
    · intro t ht
      have hd := (hh.2.1 t ht).hasFDerivAt.snd.hasDerivAt
      have hd' : HasDerivAt (α x) (f (β (t₀,x) t)) t := by
        simpa [extendedField,α] using hd
      have heq : β (t₀,x) t = (t₀+t,α x t) := Prod.ext (htime (hmem hx) ht) rfl
      rwa [heq] at hd'
    · intro t ht
      have hd := ((hh.2.2.1 t ht).snd).comp (f := fun y : E => (t₀,y)) x
        ((hasFDerivAt_const t₀ x).prodMk (hasFDerivAt_id x))
      exact hd
    · intro t ht
      have heq := det_time_triangular (D (t₀,x) t).toLinearMap (hfst (hmem hx) ht)
      exact heq.symm.trans (hh.2.2.2 t ht)
  · intro t ht x hx y hy heq
    have hxy : β (t₀,x) t = β (t₀,y) t := by
      apply Prod.ext
      · rw [htime (hmem hx) ht,htime (hmem hy) ht]
      · exact heq
    exact congrArg Prod.snd (hinj t ht (hmem hx) (hmem hy) hxy)

end TimeFlow

def lorentzField (E B : Field) (z : ℝ × Phase) : Phase :=
  lorentzPhase (fun x => E (z.1,x)) (fun x => B (z.1,x)) z.2

lemma contDiff_lorentzField {E B : Field} {k : ℕ∞ω}
    (hE : ContDiff ℝ k E) (hB : ContDiff ℝ k B) : ContDiff ℝ k (lorentzField E B) := by
  have hx : ContDiff ℝ k (fun z : ℝ × Phase => (z.1,z.2.1)) :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hu : ContDiff ℝ k (fun z : ℝ × Phase => velocity z.2.2) :=
    contDiff_velocity.comp (contDiff_snd.comp contDiff_snd)
  exact hu.prodMk ((hE.comp hx).add (contDiff_cross.comp (hu.prodMk (hB.comp hx))))

lemma trace_lorentzField {E B : Field} (hE : Differentiable ℝ E)
    (hB : Differentiable ℝ B) (z : ℝ × Phase) :
    LinearMap.trace ℝ Phase (fderiv ℝ (fun y => lorentzField E B (z.1,y)) z.2).toLinearMap = 0 := by
  exact trace_lorentzPhase (hE.comp ((differentiable_const z.1).prodMk differentiable_id))
    (hB.comp ((differentiable_const z.1).prodMk differentiable_id)) z.2

lemma exists_local_lorentz_volume_flow {E B : Field}
    (hE : ContDiff ℝ 2 E) (hB : ContDiff ℝ 2 B) (t₀ : ℝ) (z₀ : Phase) :
    ∃ η > (0 : ℝ), ∃ α : Phase → ℝ → Phase, ∃ A : Phase → ℝ → (Phase →L[ℝ] Phase),
      (∀ z ∈ Metric.ball z₀ (1/2 : ℝ), α z 0 = z ∧
        (∀ t ∈ Icc 0 η, HasDerivAt (α z) (lorentzField E B (t₀+t,α z t)) t) ∧
        (∀ t ∈ Icc 0 η, HasFDerivAt (fun y => α y t) (A z t) z) ∧
        ∀ t ∈ Icc 0 η, (A z t).det = 1) ∧
      ∀ t ∈ Icc 0 η, Set.InjOn (fun z => α z t) (Metric.ball z₀ (1/2 : ℝ)) := by
  exact exists_local_time_volume_flow (contDiff_lorentzField hE hB)
    (trace_lorentzField (hE.differentiable (by norm_num)) (hB.differentiable (by norm_num))) t₀ z₀

end RVM

end

end OAI
