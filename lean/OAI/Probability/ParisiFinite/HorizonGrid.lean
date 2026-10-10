import Mathlib
import OAI.Probability.ParisiFinite.Law
import OAI.Probability.ParisiFinite.Time

namespace OAI

/-! Horizon Grid. -/

noncomputable section

open MeasureTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiPath
open ProbabilityTheory

 
def horizonGrid (T : ℝ≥0) (n k : ℕ) : ℝ≥0 :=
  T * ⟨grid n k, mul_nonneg (Nat.cast_nonneg _) (mesh_pos n).le⟩

lemma horizonGrid_coe (T : ℝ≥0) (n k : ℕ) :
    (horizonGrid T n k : ℝ) = (T:ℝ)*grid n k := rfl

lemma horizonGrid_mono (T : ℝ≥0) (n : ℕ) : Monotone (horizonGrid T n) := by
  intro j k h
  exact NNReal.coe_le_coe.mp (mul_le_mul_of_nonneg_left (grid_mono n h) T.coe_nonneg)

lemma horizonGrid_nndist (T : ℝ≥0) (n k : ℕ) :
    nndist (horizonGrid T n (k+1) : ℝ) (horizonGrid T n k : ℝ) =
      T * NNReal.mk (mesh n) (mesh_pos n).le := by
  apply NNReal.coe_injective
  rw [coe_nndist,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr
    (show (horizonGrid T n k:ℝ) ≤ horizonGrid T n (k+1) from
      NNReal.coe_le_coe.mpr (horizonGrid_mono T n (Nat.le_succ k))))]
  change (T:ℝ)*grid n (k+1)-(T:ℝ)*grid n k = (T:ℝ)*mesh n
  rw [grid_succ]
  ring

 

def standardStep {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n k : ℕ) (ω : Ω) : ℝ :=
  (W (horizonGrid T n (k+1)) ω-W (horizonGrid T n k) ω) /
    Real.sqrt ((T:ℝ)*mesh n)

section Brownian
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

lemma standardStep_hasLaw (hW : IsBrownianReal W P) {T : ℝ≥0} (hT : 0<T) (n k : ℕ) :
    HasLaw (standardStep W T n k) (gaussianReal 0 1) P := by
  have hΔ : 0 < (T:ℝ)*mesh n := mul_pos (by exact_mod_cast hT) (mesh_pos n)
  have hl : HasLaw (W (horizonGrid T n (k+1))-W (horizonGrid T n k))
      (gaussianReal 0 (T*NNReal.mk (mesh n) (mesh_pos n).le)) P := by
    convert hW.hasLaw_sub (horizonGrid T n (k+1)) (horizonGrid T n k) using 1
    congr 1
    exact (horizonGrid_nndist T n k).symm
  have hh := gaussianReal_div_const hl (Real.sqrt ((T:ℝ)*mesh n))
  rw [zero_div] at hh
  have he : NNReal.mk ((Real.sqrt ((T:ℝ)*mesh n))^2) (sq_nonneg _) =
      T*NNReal.mk (mesh n) (mesh_pos n).le := by
    apply NNReal.coe_injective
    exact Real.sq_sqrt hΔ.le
  have hNN : 0 < T* NNReal.mk (mesh n) (mesh_pos n).le :=
    mul_pos hT (by exact_mod_cast mesh_pos n)
  rw [he,div_self hNN.ne'] at hh
  exact hh

lemma standardStep_independent (hW : IsBrownianReal W P) (T : ℝ≥0) (n : ℕ) :
    iIndepFun (standardStep W T n) P := by
  have h := hW.hasIndepIncrements.nat (horizonGrid_mono T n)
  exact h.comp (fun _ x => x/Real.sqrt ((T:ℝ)*mesh n)) (fun _ => by fun_prop)

lemma standardStep_jointLaw (hW : IsBrownianReal W P) {T : ℝ≥0} (hT : 0<T) (n r : ℕ) :
    HasLaw (fun ω (i : Fin r) => standardStep W T n i ω)
      (Measure.pi (fun _ : Fin r => gaussianReal 0 1)) P := by
  exact ((standardStep_independent hW T n).precomp Fin.val_injective).hasLaw_pi
    (fun i => standardStep_hasLaw hW hT n i)

end Brownian
end ParisiPath

namespace ParisiPath
variable {K M : ℝ≥0}

def translatePath (W : Path) (a : ℝ) : Path := W + ContinuousMap.const Time a

@[simp] lemma extend_translatePath (W : Path) (a t : ℝ) :
    extend (translatePath W a) t = extend W t + a := rfl

lemma euler_translate_step (b : Drift K M) (W : Path) (a : ℝ) (n k : ℕ) :
    ‖euler b (translatePath W a) n (k+1)-euler b W n (k+1)‖ ≤
      (1+(K:ℝ)*mesh n)*‖euler b (translatePath W a) n k-euler b W n k‖ := by
  have he : euler b (translatePath W a) n (k+1)-euler b W n (k+1) =
      (euler b (translatePath W a) n k-euler b W n k)+mesh n*
        (b.val (grid n k) (euler b (translatePath W a) n k)-
          b.val (grid n k) (euler b W n k)) := by
    simp only [euler,extend_translatePath]
    ring
  rw [he]
  calc
    _ ≤ ‖euler b (translatePath W a) n k-euler b W n k‖+
        ‖mesh n*(b.val (grid n k) (euler b (translatePath W a) n k)-
          b.val (grid n k) (euler b W n k))‖ := norm_add_le _ _
    _ ≤ ‖euler b (translatePath W a) n k-euler b W n k‖+
        mesh n*((K:ℝ)*‖euler b (translatePath W a) n k-euler b W n k‖) := by
      rw [norm_mul,Real.norm_of_nonneg (mesh_pos n).le]
      exact add_le_add_right (mul_le_mul_of_nonneg_left
        (by simpa only [dist_eq_norm] using ((b.lipschitz (grid n k)).dist_le_mul
          (euler b (translatePath W a) n k) (euler b W n k))) (mesh_pos n).le) _
    _ = _ := by ring

 
lemma euler_translate_bound (b : Drift K M) (W : Path) (a : ℝ) (n k : ℕ) (hk : k≤n+1) :
    ‖euler b (translatePath W a) n k-euler b W n k‖ ≤ |a| *Real.exp (K:ℝ) := by
  have h := finite_discrete_gronwall (N := n+1)
    (u := fun k => ‖euler b (translatePath W a) n k-euler b W n k‖)
    (r := fun _ => 0) (c := (K:ℝ)*mesh n) (fun _ => norm_nonneg _)
    (fun _ => le_rfl) (mul_nonneg K.coe_nonneg (mesh_pos n).le)
    (fun j _ => by simpa using euler_translate_step b W a n j) hk
  simp only [euler,extend_translatePath,add_sub_cancel_left,Real.norm_eq_abs,
    Finset.sum_const_zero,add_zero] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply Real.exp_le_exp.mpr
  have ht := (grid_mem n k hk).2
  dsimp only [grid] at ht
  nlinarith [mul_le_mul_of_nonneg_left ht K.coe_nonneg]

lemma scaled_translatePath (T : ℝ≥0) (W : Path) (a : ℝ) :
    scaledPath T (translatePath W a) = translatePath (scaledPath T W) a := by
  ext t
  rfl

lemma horizonEuler_translate_bound (b : Drift K M) (W : Path) (a : ℝ)
    (T : ℝ≥0) (n k : ℕ) (hk : k≤n+1) :
    ‖horizonEuler b (translatePath W a) T n k-horizonEuler b W T n k‖ ≤
      |a| *Real.exp (T*K:ℝ≥0) := by
  simpa only [horizonEuler,scaled_translatePath] using
    euler_translate_bound (scaledDrift b T) (scaledPath T W) a n k hk

 

def sourceIndex (n : ℕ) (k : Fin (n+2)) : ℕ := if k.val=0 then n+1 else k.val-1

lemma sourceIndex_injective (n : ℕ) : Function.Injective (sourceIndex n) := by
  intro i j h
  apply Fin.ext
  dsimp only [sourceIndex] at h
  split_ifs at h <;> omega

open ProbabilityTheory
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

def sourceNoise (W : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (k : Fin (n+2)) (ω : Ω) : ℝ :=
  standardStep W T n (sourceIndex n k) ω

lemma sourceNoise_jointLaw (hW : IsBrownianReal W P) {T : ℝ≥0} (hT : 0<T) (n : ℕ) :
    HasLaw (fun ω k => sourceNoise W T n k ω)
      (Measure.pi (fun _ : Fin (n+2) => gaussianReal 0 1)) P :=
  ((standardStep_independent hW T n).precomp (sourceIndex_injective n)).hasLaw_pi
    (fun k => standardStep_hasLaw hW hT n (sourceIndex n k))

 
def initialSeed (W : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  Real.sqrt ((T:ℝ)*mesh n)*standardStep W T n (n+1) ω

lemma initialSeed_aemeasurable (hW : IsBrownianReal W P) {T : ℝ≥0} (hT : 0<T) (n : ℕ) :
    AEMeasurable (initialSeed W T n) P :=
  (standardStep_hasLaw hW hT n (n+1)).aemeasurable.const_mul _

lemma initialSeed_integrable_sq (hW : IsBrownianReal W P) {T : ℝ≥0} (hT : 0<T) (n : ℕ) :
    Integrable (fun ω => (initialSeed W T n ω)^2) P := by
  have h := (standardStep_hasLaw hW hT n (n+1)).hasGaussianLaw.memLp (p := 2) (by norm_num)
  have hi := (h.const_mul (Real.sqrt ((T:ℝ)*mesh n))).integrable_sq
  exact hi

lemma initialSeed_integral_sq (hW : IsBrownianReal W P) {T : ℝ≥0} (hT : 0<T) (n : ℕ) :
    (∫ ω,(initialSeed W T n ω)^2 ∂P) = (T:ℝ)*mesh n := by
  have hi : (∫ z:ℝ,z^2 ∂gaussianReal 0 1) = 1 := by
    have h := variance_fun_id_gaussianReal (μ:=0) (v:=1)
    rw [variance_eq_integral (X:= fun x:ℝ => x) (show AEMeasurable (fun x:ℝ => x) (gaussianReal 0 1) from measurable_id.aemeasurable)] at h
    simpa [integral_id_gaussianReal] using h
  have hn := (standardStep_hasLaw hW hT n (n+1)).integral_comp
    (f := fun z:ℝ => z^2) (by fun_prop)
  simp only [Function.comp_def] at hn
  simp only [initialSeed,mul_pow,integral_const_mul,hn,hi,mul_one]
  exact Real.sq_sqrt (mul_nonneg T.coe_nonneg (mesh_pos n).le)

end ParisiPath

namespace ParisiPath
open ProbabilityTheory

 

variable {K M : ℝ≥0}

def innovationEuler (b : Drift K M) (T : ℝ≥0) (n : ℕ) : ℕ → (ℕ → ℝ) → ℝ
  | 0,_ => 0
  | k+1,z => innovationEuler b T n k z +
      ((T:ℝ)*mesh n)*b.val ((T:ℝ)*grid n k) (innovationEuler b T n k z) +
      Real.sqrt ((T:ℝ)*mesh n)*z k

lemma innovationEuler_measurable (b : Drift K M) (T : ℝ≥0) (n k : ℕ) :
    Measurable (innovationEuler b T n k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    exact (ih.add (((b.measurable.comp (measurable_const.prodMk measurable_id)).comp ih).const_mul _)).add
      ((measurable_pi_apply k).const_mul _)

lemma innovationEuler_congr (b : Drift K M) (T : ℝ≥0) (n k : ℕ)
    {z w : ℕ → ℝ} (hzw : ∀ j<k,z j=w j) :
    innovationEuler b T n k z=innovationEuler b T n k w := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [innovationEuler,ih (fun j hj => hzw j (by omega)),hzw k (by omega)]

def pastExtension (k : ℕ) (z : (↑(Finset.range k)) → ℝ) (j : ℕ) : ℝ :=
  if h : j<k then z ⟨j,Finset.mem_range.mpr h⟩ else 0

lemma pastExtension_measurable (k : ℕ) : Measurable (pastExtension k) := by
  apply Measurable.of_eval
  intro j
  by_cases hj : j<k
  · simpa only [pastExtension,dite_eq_left hj] using
      (measurable_pi_apply (⟨j,Finset.mem_range.mpr hj⟩ : ↑(Finset.range k)))
  · simpa only [pastExtension,dite_eq_right hj] using
      (measurable_const : Measurable (fun _ : ((↑(Finset.range k)) → ℝ) => (0:ℝ)))

lemma innovationEuler_past (b : Drift K M) (T : ℝ≥0) (n k : ℕ) (z : ℕ → ℝ) :
    innovationEuler b T n k (pastExtension k (fun j => z j))=innovationEuler b T n k z := by
  apply innovationEuler_congr
  intro j hj
  simp only [pastExtension,dite_eq_left hj]

lemma innovationEuler_independent {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : ℕ → Ω → ℝ} (hZ : iIndepFun Z P) (hm : ∀ k,AEMeasurable (Z k) P)
    (b : Drift K M) (T : ℝ≥0) (n k : ℕ) :
    IndepFun (fun ω => innovationEuler b T n k (fun j => Z j ω)) (Z k) P := by
  have hd : Disjoint (Finset.range k) {k} := by simp
  have h := hZ.indepFun_finset₀ (Finset.range k) {k} hd hm
  have hh : IndepFun
      (fun ω => innovationEuler b T n k (pastExtension k (fun j => Z j ω)))
      (Z k) P := h.comp (φ := (innovationEuler b T n k) ∘ pastExtension k)
        (ψ := fun z : (↑({k} : Finset ℕ)) → ℝ => z ⟨k,by simp⟩)
        ((innovationEuler_measurable b T n k).comp (pastExtension_measurable k))
        (measurable_pi_apply _)
  have he : (fun ω => innovationEuler b T n k (pastExtension k (fun j => Z j ω)))=
      (fun ω => innovationEuler b T n k (fun j => Z j ω)) := by
    funext ω
    exact innovationEuler_past b T n k (fun j => Z j ω)
  rwa [he] at hh

lemma innovationEuler_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : ℕ → Ω → ℝ} (hm : ∀ k,AEMeasurable (Z k) P)
    (b : Drift K M) (T : ℝ≥0) (n k : ℕ) :
    AEMeasurable (fun ω => innovationEuler b T n k (fun j => Z j ω)) P :=
  (innovationEuler_measurable b T n k).comp_aemeasurable (AEMeasurable.of_eval hm)

lemma gaussian_standard_integral : (∫ z:ℝ,z ∂gaussianReal 0 1)=0 := by
  simp [integral_id_gaussianReal]

lemma gaussian_standard_integral_sq : (∫ z:ℝ,z^2 ∂gaussianReal 0 1)=1 := by
  have h := variance_fun_id_gaussianReal (μ:=0) (v:=1)
  rw [variance_eq_integral (X:= fun x:ℝ => x)
    (show AEMeasurable (fun x:ℝ => x) (gaussianReal 0 1) from measurable_id.aemeasurable)] at h
  simpa [integral_id_gaussianReal] using h

 
lemma innovationEuler_noise_mean {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : ℕ → Ω → ℝ} (hZ : iIndepFun Z P)
    (hl : ∀ k,HasLaw (Z k) (gaussianReal 0 1) P)
    (b : Drift K M) (T : ℝ≥0) (n k : ℕ) {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ ω,f (innovationEuler b T n k (fun j => Z j ω))*Z k ω ∂P)=0 := by
  have h := (innovationEuler_independent hZ (fun k => (hl k).aemeasurable) b T n k).comp
    (φ := f) (ψ := id) hf measurable_id
  simp only [Function.comp_def,id_eq] at h
  rw [h.integral_fun_mul_eq_mul_integral
    (hf.comp_aemeasurable (innovationEuler_aemeasurable (fun k => (hl k).aemeasurable) b T n k)).aestronglyMeasurable
    (hl k).aemeasurable.aestronglyMeasurable]
  have hz : (∫ ω,Z k ω ∂P)=0 := by
    simpa only [Function.comp_def,gaussian_standard_integral] using
      (hl k).integral_comp (f := fun z:ℝ => z) (by fun_prop)
  rw [hz,mul_zero]

lemma innovationEuler_noise_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : ℕ → Ω → ℝ} (hZ : iIndepFun Z P)
    (hl : ∀ k,HasLaw (Z k) (gaussianReal 0 1) P)
    (b : Drift K M) (T : ℝ≥0) (n k : ℕ) {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ ω,f (innovationEuler b T n k (fun j => Z j ω))*(Z k ω)^2 ∂P)=
      ∫ ω,f (innovationEuler b T n k (fun j => Z j ω)) ∂P := by
  have h := (innovationEuler_independent hZ (fun k => (hl k).aemeasurable) b T n k).comp
    (φ := f) (ψ := fun z : ℝ => z^2) hf (by fun_prop)
  simp only [Function.comp_def] at h
  rw [h.integral_fun_mul_eq_mul_integral
    (hf.comp_aemeasurable (innovationEuler_aemeasurable (fun k => (hl k).aemeasurable) b T n k)).aestronglyMeasurable
    ((hl k).aemeasurable.pow_const 2).aestronglyMeasurable]
  have hz : (∫ ω,(Z k ω)^2 ∂P)=1 := by
    exact ((hl k).integral_comp (f := fun z:ℝ => z^2) (by fun_prop)).trans
      gaussian_standard_integral_sq
  rw [hz,mul_one]

end ParisiPath

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace ParisiPath

lemma cubic_taylor_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) {L : ℝ}
    (hL : ∀ x,‖iteratedDeriv 3 f x‖ ≤ L) (x h : ℝ) :
    ‖f (x+h)-f x-h*deriv f x-(h^2/2)*iteratedDeriv 2 f x‖ ≤ L*|h|^3/6 := by
  by_cases hh : h=0
  · simp [hh]
  have hne : x≠x+h := by intro he; apply hh; linarith
  obtain ⟨y,_,hy⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hne hf.contDiffOn
  have h₁ : iteratedDerivWithin 1 f (uIcc x (x+h)) x=deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
      (hf.of_le (by norm_num)).contDiffAt (left_mem_uIcc),iteratedDeriv_one]
  have h₂ : iteratedDerivWithin 2 f (uIcc x (x+h)) x=iteratedDeriv 2 f x :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
      (hf.of_le (by norm_num)).contDiffAt (left_mem_uIcc)
  have ht : taylorWithinEval f 2 (uIcc x (x+h)) x (x+h)=
      f x+h*deriv f x+(h^2/2)*iteratedDeriv 2 f x := by
    simp only [taylorWithinEval_succ,taylor_within_zero_eval,h₁,h₂,smul_eq_mul]
    norm_num only [Nat.factorial, Nat.cast_one, Nat.cast_ofNat, mul_one, one_mul, inv_one, pow_one, add_sub_cancel_left]
    ring
  rw [ht] at hy
  have he : f (x+h)-f x-h*deriv f x-(h^2/2)*iteratedDeriv 2 f x=
      iteratedDeriv 3 f y*h^3/6 := by
    norm_num at hy
    nlinarith [hy]
  rw [he,norm_div,norm_mul,Real.norm_eq_abs,norm_pow,Real.norm_eq_abs]
  norm_num
  gcongr
  exact hL y

 

structure CubicTest where
  val : ℝ → ℝ
  smooth : ContDiff ℝ 3 val
  c1 : ℝ≥0
  c2 : ℝ≥0
  c3 : ℝ≥0
  bound1 : ∀ x,‖deriv val x‖≤c1
  bound2 : ∀ x,‖iteratedDeriv 2 val x‖≤c2
  bound3 : ∀ x,‖iteratedDeriv 3 val x‖≤c3

namespace CubicTest
lemma continuous (f : CubicTest) : Continuous f.val := f.smooth.continuous
lemma continuous_d1 (f : CubicTest) : Continuous (deriv f.val) :=
  f.smooth.continuous_deriv (by norm_num)
lemma continuous_d2 (f : CubicTest) : Continuous (iteratedDeriv 2 f.val) :=
  f.smooth.continuous_iteratedDeriv 2 (by norm_num)
lemma lipschitz (f : CubicTest) : LipschitzWith f.c1 f.val := by
  apply lipschitzWith_of_nnnorm_deriv_le (f.smooth.differentiable (by norm_num))
  intro x
  exact_mod_cast f.bound1 x
end CubicTest

end ParisiPath

namespace ParisiPath

 
def thirdMomentBound (M : ℝ≥0) : ℝ := ∫ z:ℝ,((M:ℝ)+‖z‖)^3 ∂gaussianReal 0 1

lemma shiftedNorm_integrable_cube {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P) (M : ℝ≥0) :
    Integrable (fun ω => ((M:ℝ)+‖Z ω‖)^3) P := by
  let : IsProbabilityMeasure P := hZ.isProbabilityMeasure
  have h := ((memLp_const (M:ℝ) : MemLp (fun _ : Ω => (M:ℝ)) (3:ℝ≥0∞) P).add
    (hZ.hasGaussianLaw.memLp (p := 3) (by norm_num)).norm).integrable_norm_pow (by decide : (3:ℕ)≠0)
  simpa only [Pi.add_apply,Real.norm_of_nonneg (add_nonneg M.coe_nonneg (norm_nonneg _))] using h

lemma shiftedNorm_integral_cube {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P) (M : ℝ≥0) :
    (∫ ω,((M:ℝ)+‖Z ω‖)^3 ∂P)=thirdMomentBound M :=
  by simpa only [Function.comp_def,thirdMomentBound] using
    hZ.integral_comp (f := fun z : ℝ => ((M:ℝ)+‖z‖)^3) (by fun_prop)

lemma thirdMomentBound_nonneg (M : ℝ≥0) : 0≤thirdMomentBound M :=
  integral_nonneg fun _ => pow_nonneg (add_nonneg M.coe_nonneg (norm_nonneg _)) _

lemma scalar_euler_increment_bound (M : ℝ≥0) {δ : ℝ} (hδ0 : 0≤δ) (hδ1 : δ≤1)
    {u : ℝ} (hu : ‖u‖≤M) (z : ℝ) :
    ‖δ*u+Real.sqrt δ*z‖≤Real.sqrt δ*((M:ℝ)+‖z‖) := by
  have hδs : δ≤Real.sqrt δ := by
    apply (Real.le_sqrt hδ0 hδ0).mpr
    nlinarith
  calc
    _ ≤ ‖δ*u‖+‖Real.sqrt δ*z‖ := norm_add_le _ _
    _ = δ*‖u‖+Real.sqrt δ*‖z‖ := by
      rw [norm_mul,norm_mul,Real.norm_of_nonneg hδ0,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ Real.sqrt δ*(M:ℝ)+Real.sqrt δ*‖z‖ :=
      add_le_add_left (mul_le_mul hδs hu (norm_nonneg _) (Real.sqrt_nonneg _)) _
    _ = _ := by ring

lemma scalar_euler_increment_cube (M : ℝ≥0) {δ : ℝ} (hδ0 : 0≤δ) (hδ1 : δ≤1)
    {u : ℝ} (hu : ‖u‖≤M) (z : ℝ) :
    ‖δ*u+Real.sqrt δ*z‖^3≤(δ*Real.sqrt δ)*((M:ℝ)+‖z‖)^3 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (scalar_euler_increment_bound M hδ0 hδ1 hu z) 3
  have he : (Real.sqrt δ)^3=δ*Real.sqrt δ := by
    calc
      _ = (Real.sqrt δ)^2*Real.sqrt δ := by ring
      _ = _ := by rw [Real.sq_sqrt hδ0]
  simpa only [mul_pow,he] using h

lemma scalar_euler_increment_thirdMoment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P) (M : ℝ≥0)
    {δ : ℝ} (hδ0 : 0≤δ) (hδ1 : δ≤1) {u : Ω → ℝ} (hu : ∀ ω,‖u ω‖≤M) :
    (∫ ω,‖δ*u ω+Real.sqrt δ*Z ω‖^3 ∂P)≤(δ*Real.sqrt δ)*thirdMomentBound M := by
  have h := integral_mono_of_nonneg (ae_of_all _ fun _ => pow_nonneg (norm_nonneg _) _)
    ((shiftedNorm_integrable_cube hZ M).const_mul (δ*Real.sqrt δ))
    (ae_of_all _ fun ω => scalar_euler_increment_cube M hδ0 hδ1 (hu ω) (Z ω))
  rw [integral_const_mul,shiftedNorm_integral_cube hZ M] at h
  exact h

lemma scalar_euler_increment_memLp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P) (M : ℝ≥0)
    (δ : ℝ) {u : Ω → ℝ} (hum : AEMeasurable u P) (hu : ∀ ω,‖u ω‖≤M)
    {p : ℝ≥0∞} (hp : p≠∞) : MemLp (fun ω => δ*u ω+Real.sqrt δ*Z ω) p P := by
  let : IsProbabilityMeasure P := hZ.isProbabilityMeasure
  exact ((MemLp.of_bound hum.aestronglyMeasurable (M:ℝ) (ae_of_all _ hu)).const_mul δ).add
    ((hZ.hasGaussianLaw.memLp hp).const_mul (Real.sqrt δ))

end ParisiPath

namespace ParisiPath
section IndependentStep
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X Z : Ω → ℝ} (hX : AEMeasurable X P) (hZ : HasLaw Z (gaussianReal 0 1) P)
  (hXZ : IndepFun X Z P)

include hX hZ hXZ in
lemma independent_gaussian_first {g : ℝ → ℝ} (hg : Measurable g) :
    (∫ ω,g (X ω)*Z ω ∂P)=0 := by
  have hi : IndepFun (fun ω => g (X ω)) Z P := hXZ.comp hg measurable_id
  rw [hi.integral_fun_mul_eq_mul_integral (hg.comp_aemeasurable hX).aestronglyMeasurable
    hZ.aemeasurable.aestronglyMeasurable]
  have hz : (∫ ω,Z ω ∂P)=0 := by
    simpa only [Function.comp_def,integral_id_gaussianReal] using
      hZ.integral_comp (f := fun z:ℝ => z) (by fun_prop)
  rw [hz,mul_zero]

include hX hZ hXZ in
lemma independent_gaussian_second {g : ℝ → ℝ} (hg : Measurable g) :
    (∫ ω,g (X ω)*(Z ω)^2 ∂P)=∫ ω,g (X ω) ∂P := by
  have hi : IndepFun (fun ω => g (X ω)) (fun ω => (Z ω)^2) P := hXZ.comp (φ := g) (ψ := fun z:ℝ => z^2) hg (by fun_prop)
  rw [hi.integral_fun_mul_eq_mul_integral (hg.comp_aemeasurable hX).aestronglyMeasurable
    (hZ.aemeasurable.pow_const 2).aestronglyMeasurable]
  have hz : (∫ ω,(Z ω)^2 ∂P)=1 := by
    have hg := variance_fun_id_gaussianReal (μ:=0) (v:=1)
    rw [variance_eq_integral (X:= fun x:ℝ => x)
      (show AEMeasurable (fun x:ℝ => x) (gaussianReal 0 1) from measurable_id.aemeasurable)] at hg
    have hh := hZ.integral_comp (f := fun z:ℝ => z^2) (by fun_prop)
    have hg' : (∫ z:ℝ,z^2 ∂gaussianReal 0 1)=1 := by
      simpa [integral_id_gaussianReal] using hg
    exact hh.trans hg'
  rw [hz,mul_one]

include hX hZ in
lemma integrable_bounded_comp {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : ∀ x,‖g x‖≤C) : Integrable (fun ω => g (X ω)) P := by
  let : IsProbabilityMeasure P := hZ.isProbabilityMeasure
  exact (integrable_const C).mono' (hg.comp_aemeasurable hX).aestronglyMeasurable
    (ae_of_all _ fun _ => hC _)

include hX hZ hXZ in
 

lemma weak_step_polynomial (f : CubicTest) {g : ℝ → ℝ} (hg : Measurable g)
    (M : ℝ≥0) (hM : ∀ x,‖g x‖≤M) {δ : ℝ} (hδ : 0≤δ) :
    (∫ ω,deriv f.val (X ω)*(δ*g (X ω)+Real.sqrt δ*Z ω)+
      (1/2:ℝ)*iteratedDeriv 2 f.val (X ω)*(δ*g (X ω)+Real.sqrt δ*Z ω)^2 ∂P)=
      δ*(∫ ω,deriv f.val (X ω)*g (X ω)+(1/2:ℝ)*iteratedDeriv 2 f.val (X ω) ∂P)+
      (δ^2/2)*(∫ ω,iteratedDeriv 2 f.val (X ω)*(g (X ω))^2 ∂P) := by
  let : IsProbabilityMeasure P := hZ.isProbabilityMeasure
  have hm1 := f.continuous_d1.measurable
  have hm2 := f.continuous_d2.measurable
  have ig1 := integrable_bounded_comp hX hZ (hm1.mul hg) (fun x => by
    simp only [Pi.mul_apply,norm_mul]; exact mul_le_mul (f.bound1 x) (hM x) (norm_nonneg _) f.c1.coe_nonneg)
  have i1Z := (hZ.hasGaussianLaw.memLp (p:=1) (by norm_num) |>.integrable le_rfl).bdd_mul
    (hm1.comp_aemeasurable hX).aestronglyMeasurable (ae_of_all _ fun _ => f.bound1 _)
  have ig2 := integrable_bounded_comp hX hZ (hm2.mul (hg.pow_const 2)) (fun x => by
    simp only [Pi.mul_apply,norm_mul,norm_pow]
    exact mul_le_mul (f.bound2 x) (pow_le_pow_left₀ (norm_nonneg _) (hM x) 2)
      (pow_nonneg (norm_nonneg _) _) f.c2.coe_nonneg)
  have i2gZ := (hZ.hasGaussianLaw.memLp (p:=1) (by norm_num) |>.integrable le_rfl).bdd_mul
    ((hm2.mul hg).comp_aemeasurable hX).aestronglyMeasurable
    (ae_of_all _ fun ω => by
      change ‖iteratedDeriv 2 f.val (X ω)*g (X ω)‖≤(f.c2:ℝ)*(M:ℝ)
      rw [norm_mul]
      exact mul_le_mul (f.bound2 _) (hM _) (norm_nonneg _) f.c2.coe_nonneg)
  have i2Z := (hZ.hasGaussianLaw.memLp (p:=2) (by norm_num) |>.integrable_sq).bdd_mul
    (hm2.comp_aemeasurable hX).aestronglyMeasurable (ae_of_all _ fun _ => f.bound2 _)
  have i2 := integrable_bounded_comp hX hZ hm2 f.bound2
  simp only [Function.comp_def,Pi.mul_apply] at ig1 i1Z ig2 i2gZ i2Z
  have he : (fun ω => deriv f.val (X ω)*(δ*g (X ω)+Real.sqrt δ*Z ω)+
      (1/2:ℝ)*iteratedDeriv 2 f.val (X ω)*(δ*g (X ω)+Real.sqrt δ*Z ω)^2)=
      (fun ω => δ*(deriv f.val (X ω)*g (X ω))+Real.sqrt δ*(deriv f.val (X ω)*Z ω)+
        (δ^2/2)*(iteratedDeriv 2 f.val (X ω)*(g (X ω))^2)+
        (δ*Real.sqrt δ)*(iteratedDeriv 2 f.val (X ω)*g (X ω)*Z ω)+
        (δ/2)*(iteratedDeriv 2 f.val (X ω)*(Z ω)^2)) := by
    funext ω
    simp only [add_sq,mul_pow,Real.sq_sqrt hδ]
    ring
  rw [he]
  rw [integral_add]
  · rw [integral_add]
    · rw [integral_add]
      · rw [integral_add (ig1.const_mul δ) (i1Z.const_mul (Real.sqrt δ))]
        simp only [integral_const_mul]
        have hz2 := independent_gaussian_first hX hZ hXZ (hm2.mul hg)
        simp only [Pi.mul_apply] at hz2
        rw [independent_gaussian_first hX hZ hXZ hm1,hz2,
          independent_gaussian_second hX hZ hXZ hm2,
          integral_add ig1 (i2.const_mul (1/2)),integral_const_mul]
        ring
      · exact (ig1.const_mul δ).add (i1Z.const_mul (Real.sqrt δ))
      · exact ig2.const_mul (δ^2/2)
    · exact ((ig1.const_mul δ).add (i1Z.const_mul (Real.sqrt δ))).add (ig2.const_mul (δ^2/2))
    · exact i2gZ.const_mul (δ*Real.sqrt δ)
  · exact (((ig1.const_mul δ).add (i1Z.const_mul (Real.sqrt δ))).add
      (ig2.const_mul (δ^2/2))).add (i2gZ.const_mul (δ*Real.sqrt δ))
  · exact i2Z.const_mul (δ/2)

include hX hZ in
lemma weak_step_integrable (f : CubicTest) {g : ℝ → ℝ} (hg : Measurable g)
    (M : ℝ≥0) (hM : ∀ x,‖g x‖≤M) (δ : ℝ) :
    Integrable (fun ω => f.val (X ω+(δ*g (X ω)+Real.sqrt δ*Z ω))-f.val (X ω)) P := by
  let : IsProbabilityMeasure P := hZ.isProbabilityMeasure
  have hD := scalar_euler_increment_memLp hZ M δ (hg.comp_aemeasurable hX)
    (fun ω => hM (X ω)) (p := 1) (by norm_num)
  apply ((hD.integrable le_rfl).norm.const_mul (f.c1:ℝ)).mono'
    ((f.continuous.measurable.comp_aemeasurable (hX.add hD.aemeasurable)).sub
      (f.continuous.measurable.comp_aemeasurable hX)).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    simpa only [add_sub_cancel_left,Function.comp_def,Pi.add_apply,Pi.sub_apply] using f.lipschitz.norm_sub_le
      (X ω+(δ*g (X ω)+Real.sqrt δ*Z ω)) (X ω)

include hX hZ in
lemma weak_step_integrable_polynomial (f : CubicTest) {g : ℝ → ℝ} (hg : Measurable g)
    (M : ℝ≥0) (hM : ∀ x,‖g x‖≤M) (δ : ℝ) :
    Integrable (fun ω => deriv f.val (X ω)*(δ*g (X ω)+Real.sqrt δ*Z ω)+
      (1/2:ℝ)*iteratedDeriv 2 f.val (X ω)*(δ*g (X ω)+Real.sqrt δ*Z ω)^2) P := by
  let : IsProbabilityMeasure P := hZ.isProbabilityMeasure
  have hD1 := scalar_euler_increment_memLp hZ M δ (hg.comp_aemeasurable hX)
    (fun ω => hM (X ω)) (p := 1) (by norm_num)
  have hD2 := scalar_euler_increment_memLp hZ M δ (hg.comp_aemeasurable hX)
    (fun ω => hM (X ω)) (p := 2) (by norm_num)
  have h1 := (hD1.integrable le_rfl).bdd_mul
    (f.continuous_d1.measurable.comp_aemeasurable hX).aestronglyMeasurable
    (ae_of_all _ fun ω => f.bound1 (X ω))
  have h2 := hD2.integrable_sq.bdd_mul
    (f.continuous_d2.measurable.comp_aemeasurable hX).aestronglyMeasurable
    (ae_of_all _ fun ω => f.bound2 (X ω))
  convert! h1.add (h2.const_mul (1/2:ℝ)) using 1
  first | rfl | (funext ω; simp only [Function.comp_def,Pi.add_apply]; ring)

include hX hZ in
lemma weak_step_taylor_error (f : CubicTest) {g : ℝ → ℝ} (hg : Measurable g)
    (M : ℝ≥0) (hM : ∀ x,‖g x‖≤M) {δ : ℝ} (hδ0 : 0≤δ) (hδ1 : δ≤1) :
    ‖(∫ ω,f.val (X ω+(δ*g (X ω)+Real.sqrt δ*Z ω))-f.val (X ω) ∂P)-
      (∫ ω,deriv f.val (X ω)*(δ*g (X ω)+Real.sqrt δ*Z ω)+
        (1/2:ℝ)*iteratedDeriv 2 f.val (X ω)*(δ*g (X ω)+Real.sqrt δ*Z ω)^2 ∂P)‖≤
      ((f.c3:ℝ)/6)*(δ*Real.sqrt δ)*thirdMomentBound M := by
  have hD3 := scalar_euler_increment_memLp hZ M δ (hg.comp_aemeasurable hX)
    (fun ω => hM (X ω)) (p := 3) (by norm_num)
  rw [←integral_sub (weak_step_integrable hX hZ f hg M hM δ)
    (weak_step_integrable_polynomial hX hZ f hg M hM δ)]
  calc
    _ ≤ ∫ ω,((f.c3:ℝ)/6)*‖δ*g (X ω)+Real.sqrt δ*Z ω‖^3 ∂P := by
      apply norm_integral_le_of_norm_le
        ((hD3.integrable_norm_pow (by decide : (3:ℕ)≠0)).const_mul ((f.c3:ℝ)/6))
      exact ae_of_all _ fun ω => by
        have hh := cubic_taylor_bound f.smooth f.bound3 (X ω) (δ*g (X ω)+Real.sqrt δ*Z ω)
        convert hh using 1
        · congr 1; ring
        · simp only [Real.norm_eq_abs,Function.comp_def]
          ring
    _ = ((f.c3:ℝ)/6)*(∫ ω,‖δ*g (X ω)+Real.sqrt δ*Z ω‖^3 ∂P) := integral_const_mul _ _
    _ ≤ ((f.c3:ℝ)/6)*((δ*Real.sqrt δ)*thirdMomentBound M) :=
      mul_le_mul_of_nonneg_left
        (scalar_euler_increment_thirdMoment hZ M hδ0 hδ1 (fun ω => hM (X ω))) (by positivity)
    _ = _ := by ring

include hX hZ hXZ in
 

lemma weak_step_error (f : CubicTest) {g : ℝ → ℝ} (hg : Measurable g)
    (M : ℝ≥0) (hM : ∀ x,‖g x‖≤M) {δ : ℝ} (hδ0 : 0≤δ) (hδ1 : δ≤1) :
    ‖(∫ ω,f.val (X ω+(δ*g (X ω)+Real.sqrt δ*Z ω))-f.val (X ω) ∂P)-
      δ*(∫ ω,deriv f.val (X ω)*g (X ω)+(1/2:ℝ)*iteratedDeriv 2 f.val (X ω) ∂P)‖≤
      (δ*Real.sqrt δ)*((f.c3:ℝ)/6*thirdMomentBound M+(f.c2:ℝ)*(M:ℝ)^2/2) := by
  let : IsProbabilityMeasure P := hZ.isProbabilityMeasure
  have he := weak_step_taylor_error hX hZ f hg M hM hδ0 hδ1
  rw [weak_step_polynomial hX hZ hXZ f hg M hM hδ0] at he
  have hi : ‖∫ ω,iteratedDeriv 2 f.val (X ω)*(g (X ω))^2 ∂P‖≤(f.c2:ℝ)*(M:ℝ)^2 := by
    simpa using norm_integral_le_of_norm_le_const (μ:=P) (f:=fun ω =>
      iteratedDeriv 2 f.val (X ω)*(g (X ω))^2) (C:=(f.c2:ℝ)*(M:ℝ)^2)
      (ae_of_all _ fun ω => by
        rw [norm_mul,norm_pow]
        exact mul_le_mul (f.bound2 _) (pow_le_pow_left₀ (norm_nonneg _) (hM _) 2)
          (pow_nonneg (norm_nonneg _) _) f.c2.coe_nonneg)
  have hterm : ‖δ^2/2*(∫ ω,iteratedDeriv 2 f.val (X ω)*(g (X ω))^2 ∂P)‖≤
      δ^2/2*((f.c2:ℝ)*(M:ℝ)^2) := by
    rw [norm_mul,Real.norm_of_nonneg (by positivity : 0≤δ^2/2)]
    exact mul_le_mul_of_nonneg_left hi (by positivity)
  have htriangle := norm_le_norm_add_norm_sub'
    ((∫ ω,f.val (X ω+(δ*g (X ω)+Real.sqrt δ*Z ω))-f.val (X ω) ∂P)-
      δ*(∫ ω,deriv f.val (X ω)*g (X ω)+(1/2:ℝ)*iteratedDeriv 2 f.val (X ω) ∂P))
    (δ^2/2*(∫ ω,iteratedDeriv 2 f.val (X ω)*(g (X ω))^2 ∂P))
  have hδs : δ≤Real.sqrt δ := (Real.le_sqrt hδ0 hδ0).mpr (by nlinarith)
  have herr := mul_le_mul_of_nonneg_left hδs hδ0
  have hprod := mul_le_mul_of_nonneg_right herr (show 0≤(f.c2:ℝ)*(M:ℝ)^2/2 by positivity)
  rw [sub_add_eq_sub_sub] at he
  nlinarith [he,hterm]

end IndependentStep
end ParisiPath

end

end OAI
