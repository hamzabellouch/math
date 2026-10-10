import Mathlib
import OAI.Geometry.NearbyLagrangian.CompleteFlow
import OAI.Geometry.NearbyLagrangian.ImplicitRoots
import OAI.Geometry.NearbyLagrangian.Superposition

namespace OAI

/-! Smooth Picard paths and global smoothness of complete flows. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.SmoothFlow
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma exists_bounded_time_cutoff {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ (∀ t, ‖ρ t‖ ≤ δ) ∧
      ∀ t, ‖t‖ ≤ δ/2 → ρ t = t := by
  let χ : ContDiffBump (0:ℝ) := ⟨δ/2,δ,half_pos hδ,half_lt_self hδ⟩
  refine ⟨fun t => χ t*t,χ.contDiff.mul contDiff_id,?_,?_⟩
  · intro t
    dsimp only
    by_cases h : ‖t‖ ≤ δ
    · rw [norm_mul,Real.norm_of_nonneg χ.nonneg]
      exact (mul_le_mul_of_nonneg_right χ.le_one (norm_nonneg t)).trans (by simpa using h)
    · have hz : χ t = 0 := χ.zero_of_le_dist (by simpa only [dist_zero_right] using (lt_of_not_ge h).le)
      rw [hz,zero_mul,norm_zero]
      exact hδ.le
  · intro t ht
    dsimp only
    rw [χ.one_of_mem_closedBall (by simpa using ht),one_mul]

omit [CompleteSpace E] in
lemma pointwiseLinear_bound {A : C(UnitTime,E →L[ℝ] E)} {L : ℝ} (hL : 0 ≤ L)
    (hA : ∀ s, ‖A s‖ ≤ L) : ‖pointwiseLinear A‖ ≤ L := by
  apply ContinuousLinearMap.opNorm_le_bound _ hL
  intro v
  apply (ContinuousMap.norm_le _ (mul_nonneg hL (norm_nonneg v))).mpr
  intro s
  exact ((A s).le_opNorm (v s)).trans (mul_le_mul (hA s)
    (ContinuousMap.norm_coe_le_norm v s) (norm_nonneg _) hL)

lemma fderiv_path_equation {X : E → E} (hX : ContDiff ℝ ∞ X)
    (a : ℝ) (u : C(UnitTime,E)) :
    fderiv ℝ (fun v : C(UnitTime,E) =>
      v-a • volterra ((⟨X,hX.continuous⟩ : C(E,E)).comp v)) u =
      ContinuousLinearMap.id ℝ C(UnitTime,E)-a • volterra.comp
        (pointwiseLinear ((⟨fderiv ℝ X,hX.continuous_fderiv (by simp)⟩ : C(E,E →L[ℝ] E)).comp u)) := by
  have hd := hasFDerivAt_superposition (K:=UnitTime)
    (hX.differentiable (by simp)) (hX.continuous_fderiv (by simp)) u
  have h := (hasFDerivAt_id u).sub
    (((volterra : C(UnitTime,E) →L[ℝ] C(UnitTime,E)).hasFDerivAt.comp u hd).const_smul a)
  simpa only [Function.comp_def,Pi.sub_def,Pi.smul_def,id_eq] using h.fderiv

lemma volterra_pointwise_bound {A : C(UnitTime,E →L[ℝ] E)} {L : ℝ}
    (hL : 0 ≤ L) (hA : ∀ s, ‖A s‖ ≤ L) :
    ‖(volterra : C(UnitTime,E) →L[ℝ] C(UnitTime,E)).comp (pointwiseLinear A)‖ ≤ L := by
  exact ((volterra : C(UnitTime,E) →L[ℝ] C(UnitTime,E)).opNorm_comp_le (pointwiseLinear A)).trans
    ((mul_le_mul norm_volterra_le (pointwiseLinear_bound hL hA)
      ((pointwiseLinear A).opNorm_nonneg) zero_le_one).trans_eq (one_mul L))

lemma path_equation_derivative_bound {X : E → E} (hX : ContDiff ℝ ∞ X)
    {L : ℝ} (hL : 0 ≤ L) (hdf : ∀ x, ‖fderiv ℝ X x‖ ≤ L)
    (a : ℝ) (u : C(UnitTime,E)) :
    ‖fderiv ℝ (fun v : C(UnitTime,E) =>
        v-a • volterra ((⟨X,hX.continuous⟩ : C(E,E)).comp v)) u-
      ContinuousLinearMap.id ℝ C(UnitTime,E)‖ ≤ ‖a‖*L := by
  let A : C(UnitTime,E →L[ℝ] E) :=
    (⟨fderiv ℝ X,hX.continuous_fderiv (by simp)⟩ : C(E,E →L[ℝ] E)).comp u
  let D : C(UnitTime,E) →L[ℝ] C(UnitTime,E) := volterra.comp (pointwiseLinear A)
  have he : fderiv ℝ (fun v : C(UnitTime,E) =>
      v-a • volterra ((⟨X,hX.continuous⟩ : C(E,E)).comp v)) u =
      ContinuousLinearMap.id ℝ C(UnitTime,E)-a • D := fderiv_path_equation hX a u
  have hb : ‖D‖ ≤ L := volterra_pointwise_bound hL (fun s => hdf (u s))
  rw [he,sub_sub_cancel_left]
  calc
    ‖-(a • D)‖ = ‖a • D‖ := ContinuousLinearMap.opNorm_neg _
    _ ≤ ‖a‖*‖D‖ := ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ ‖a‖*L := mul_le_mul_of_nonneg_left hb (norm_nonneg _)

theorem smooth_picard_path {X : E → E} (hX : ContDiff ℝ ∞ X)
    {L δ : ℝ} (hL : 0 ≤ L) (_hδ : 0 < δ) (hsmall : δ*L ≤ (1/2:ℝ))
    (hdf : ∀ x, ‖fderiv ℝ X x‖ ≤ L)
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρb : ∀ t, ‖ρ t‖ ≤ δ) :
    ∃ p : E × ℝ → C(UnitTime,E), ContDiff ℝ ∞ p ∧
      (∀ z, p z-ρ z.2 • volterra ((⟨X,hX.continuous⟩ : C(E,E)).comp (p z)) =
        ContinuousMap.const UnitTime z.1) ∧
      ∀ z v, v-ρ z.2 • volterra ((⟨X,hX.continuous⟩ : C(E,E)).comp v) =
        ContinuousMap.const UnitTime z.1 → v = p z := by
  let F : ℝ × C(UnitTime,E) → C(UnitTime,E) := fun z =>
    z.2 - ρ z.1 • volterra ((⟨X,hX.continuous⟩ : C(E,E)).comp z.2)
  have hF : ContDiff ℝ ∞ F :=
    contDiff_snd.sub ((hρ.comp contDiff_fst).smul
      (volterra.contDiff.comp ((contDiff_superposition hX).comp contDiff_snd)))
  let c : ℝ≥0 := ⟨1/2,by norm_num⟩
  have hc : c < 1 := by
    change (⟨1/2,by norm_num⟩ : ℝ≥0) < 1
    exact_mod_cast (by norm_num : (1/2:ℝ) < 1)
  have hb : ∀ t u, ‖fderiv ℝ (fun v => F (t,v)) u-
      ContinuousLinearMap.id ℝ C(UnitTime,E)‖ ≤ c := by
    intro t u
    exact (path_equation_derivative_bound hX hL hdf (ρ t) u).trans
      ((mul_le_mul_of_nonneg_right (hρb t) hL).trans hsmall)
  obtain ⟨G,hG,hGinv,hGu⟩ := Transport.exists_contDiff_nearIdentity_inverse hF c hc hb
  let p : E × ℝ → C(UnitTime,E) := fun z => G (z.2,ContinuousMap.const UnitTime z.1)
  refine ⟨p,?_,?_,?_⟩
  · have hconst : ContDiff ℝ ∞ (fun x:E => ContinuousMap.const UnitTime x) :=
      (ContinuousLinearMap.const ℝ UnitTime : E →L[ℝ] C(UnitTime,E)).contDiff
    exact hG.comp (contDiff_snd.prodMk (hconst.comp contDiff_fst))
  · intro z
    exact hGinv z.2 (ContinuousMap.const UnitTime z.1)
  · intro z v hv
    exact hGu z.2 (ContinuousMap.const UnitTime z.1) v hv

end NearbyLagrangian.SmoothFlow

namespace NearbyLagrangian.SmoothFlow
open Set Filter ContinuousLinearMap MeasureTheory
open scoped ContDiff Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma completeFlow_path_equation {X : E → E} (φ : ODE.CompleteFlow X)
    (hX : Continuous X) (x : E) (a : ℝ) :
    let u : C(UnitTime,E) := ⟨fun s => φ.toFun (x,a*(s:ℝ)),
      φ.continuous_toFun.comp (continuous_const.prodMk
        (continuous_const.mul continuous_subtype_val))⟩
    u-a • volterra ((⟨X,hX⟩ : C(E,E)).comp u) = ContinuousMap.const UnitTime x := by
  dsimp only
  let u : C(UnitTime,E) := ⟨fun s => φ.toFun (x,a*(s:ℝ)),
      φ.continuous_toFun.comp (continuous_const.prodMk
        (continuous_const.mul continuous_subtype_val))⟩
  ext s
  change φ.toFun (x,a*(s:ℝ))-a • (∫ t in (0:ℝ)..(s:ℝ),
    pathExtend ((⟨X,hX⟩ : C(E,E)).comp u) t) = x
  have hi : (∫ t in (0:ℝ)..(s:ℝ), pathExtend ((⟨X,hX⟩ : C(E,E)).comp u) t) =
      ∫ t in (0:ℝ)..(s:ℝ), X (φ.toFun (x,a*t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le s.property.1] at ht
    have hm : t ∈ Icc (0:ℝ) 1 := ⟨ht.1,ht.2.trans s.property.2⟩
    dsimp only [pathExtend]
    rw [IccExtend_of_mem _ _ hm]
    rfl
  have hd : ∀ t, HasDerivAt (fun t => φ.toFun (x,a*t))
      (a • X (φ.toFun (x,a*t))) t := by
    intro t
    simpa only [Function.comp_def,mul_one] using
      (φ.derivative x (a*t)).scomp t ((hasDerivAt_id t).const_mul a)
  have hc : Continuous (fun t => a • X (φ.toFun (x,a*t))) :=
    continuous_const.smul (hX.comp (φ.continuous_toFun.comp
      (continuous_const.prodMk (continuous_const.mul continuous_id))))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a:=(0:ℝ)) (b:=(s:ℝ)) (fun t _ => hd t) (hc.intervalIntegrable _ _)
  rw [intervalIntegral.integral_smul,mul_zero,φ.initial] at he
  rw [hi,he]
  abel

theorem contDiff_capped_flow {X : E → E} (φ : ODE.CompleteFlow X)
    (hX : ContDiff ℝ ∞ X) {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (hsmall : δ*L ≤ (1/2:ℝ)) (hdf : ∀ x, ‖fderiv ℝ X x‖ ≤ L)
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρb : ∀ t, ‖ρ t‖ ≤ δ) :
    ContDiff ℝ ∞ (fun z : E × ℝ => φ.toFun (z.1,ρ z.2)) := by
  obtain ⟨p,hp,_,hu⟩ := smooth_picard_path hX hL hδ hsmall hdf hρ hρb
  let one : UnitTime := ⟨1,by constructor <;> norm_num⟩
  have he : ∀ z, p z one = φ.toFun (z.1,ρ z.2) := by
    intro z
    have h := hu z _ (completeFlow_path_equation φ hX.continuous z.1 (ρ z.2))
    have hv := congrArg (fun v : C(UnitTime,E) => v one) h
    change φ.toFun (z.1,ρ z.2*1) = p z one at hv
    simpa only [mul_one] using hv.symm
  have hc : ContDiff ℝ ∞ (fun z => p z one) :=
    ((ContinuousMap.evalCLM ℝ one : C(UnitTime,E) →L[ℝ] E).contDiff.comp hp)
  simpa only [he] using hc

theorem completeFlow_smooth_small_time {X : E → E} (φ : ODE.CompleteFlow X)
    (hX : ContDiff ℝ ∞ X) {L : ℝ} (hL : 0 ≤ L)
    (hdf : ∀ x, ‖fderiv ℝ X x‖ ≤ L) :
    ∃ r : ℝ, 0 < r ∧ ∀ x t, ‖t‖ < r → ContDiffAt ℝ ∞ φ.toFun (x,t) := by
  let δ : ℝ := 1/(2*(L+1))
  have hδ : 0 < δ := div_pos zero_lt_one (by positivity)
  have hsmall : δ*L ≤ (1/2:ℝ) := by
    dsimp [δ]
    apply (mul_le_mul_of_nonneg_left (show L ≤ L+1 by linarith)
      (div_nonneg zero_le_one (by positivity))).trans
    have he : (1/(2*(L+1)))*(L+1) = (1/2:ℝ) := by field_simp
    exact he.le
  obtain ⟨ρ,hρ,hρb,hρid⟩ := exists_bounded_time_cutoff hδ
  have hs := contDiff_capped_flow φ hX hL hδ hsmall hdf hρ hρb
  refine ⟨δ/2,half_pos hδ,fun x t ht => ?_⟩
  apply hs.contDiffAt.congr_of_eventuallyEq
  filter_upwards [(continuous_snd.norm.continuousAt (x:=(x,t))).eventually_lt
    continuousAt_const ht] with z hz
  rw [hρid z.2 hz.le]

theorem contDiff_completeFlow {X : E → E} (φ : ODE.CompleteFlow X)
    (hX : ContDiff ℝ ∞ X) {K : ℝ≥0} (hK : LipschitzWith K X) :
    ContDiff ℝ ∞ φ.toFun := by
  have hdf : ∀ x, ‖fderiv ℝ X x‖ ≤ (K:ℝ) := fun _ => norm_fderiv_le_of_lipschitz ℝ hK
  obtain ⟨r,hr,hsmall⟩ := completeFlow_smooth_small_time φ hX K.2 hdf
  have htime : ∀ t, ContDiff ℝ ∞ (fun x => φ.toFun (x,t)) := by
    intro t
    obtain ⟨n,hn⟩ := exists_nat_gt (‖t‖/r)
    have hnpos : (0:ℝ) < n := (div_nonneg (norm_nonneg t) hr.le).trans_lt hn
    let a : ℝ := t/n
    have ha : ‖a‖ < r := by
      dsimp only [a]
      rw [norm_div,Real.norm_of_nonneg hnpos.le,div_lt_iff₀ hnpos]
      exact (div_lt_iff₀ hr).mp hn |> fun h => by simpa only [mul_comm] using h
    have hs : ContDiff ℝ ∞ (fun x => φ.toFun (x,a)) := by
      apply contDiff_iff_contDiffAt.mpr
      intro x
      exact (hsmall x a ha).comp x (contDiff_id.prodMk contDiff_const).contDiffAt
    have hi : ∀ m : ℕ, ContDiff ℝ ∞ (fun x => φ.toFun (x,(m:ℝ)*a)) := by
      intro m
      induction m with
      | zero =>
        convert (contDiff_id : ContDiff ℝ ∞ (id : E → E)) using 1
        funext x
        simp only [Nat.cast_zero,zero_mul,φ.initial,id_eq]
      | succ m ih =>
        have h := hs.comp ih
        convert h using 1
        funext x
        dsimp only [Function.comp_def]
        rw [φ.add hK]
        congr 1
        push_cast
        ring_nf
    have he : (n:ℝ)*a = t := by dsimp [a]; field_simp
    simpa only [he] using hi n
  apply contDiff_iff_contDiffAt.mpr
  rintro ⟨x,t⟩
  have hpair : ContDiffAt ℝ ∞ (fun z:E × ℝ => (φ.toFun (z.1,t),z.2-t)) (x,t) :=
    (((htime t).comp contDiff_fst).prodMk (contDiff_snd.sub contDiff_const)).contDiffAt
  have h0 : ContDiffAt ℝ ∞ φ.toFun (φ.toFun (x,t),t-t) := by
    simpa only [sub_self] using hsmall (φ.toFun (x,t)) 0 (by simpa using hr)
  have hlocal := h0.comp (x,t) hpair
  convert hlocal using 1
  funext z
  dsimp only [Function.comp_def]
  rw [φ.add hK]
  simp only [add_sub_cancel]

end NearbyLagrangian.SmoothFlow

end

end OAI
