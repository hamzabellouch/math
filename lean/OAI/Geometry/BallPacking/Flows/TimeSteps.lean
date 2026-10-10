import Mathlib
import OAI.Geometry.BallPacking.Moser.RelativeForms

namespace OAI

noncomputable section
open scoped ContDiff Topology NNReal
open scoped ContDiff Topology
open Set Metric
open scoped ContDiff Topology
open Set Metric
namespace PackingSufficiencySupport.Hamiltonian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
def stepHomeomorph {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    [FiniteDimensional ℝ E] (hXs : ContDiff ℝ ∞ X) {h : ℝ} (hh : ‖h‖ * L < 1) : E ≃ₜ E where
  toFun := stepEndpoint X hX h
  invFun := stepEndpoint X hX (-h)
  left_inv := stepEndpoint_neg_leftInverse X hX hh
  right_inv := by
    have hh' : ‖-h‖ * L < 1 := by simpa using hh
    intro x
    simpa using stepEndpoint_neg_leftInverse X hX hh' x
  continuous_toFun := (stepEndpoint_smooth X hX hXs hh).continuous
  continuous_invFun := (stepEndpoint_smooth X hX hXs (h := -h) (by simpa using hh)).continuous


theorem fixedStep_of_zero {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    {h : ℝ} (hh : ‖h‖ * L < 1) {x : E} (hx : X x = 0) :
    fixedStep X hX h x = constantPath x := by
  apply (picard_contracts X hX (p := (x,h)) hh).fixedPoint_unique'
    (localPath_fixed X hX (p := (x,h)) hh)
  change constantPath x + h • pathIntegral (X.comp (constantPath x)) = constantPath x
  have hz : X.comp (constantPath x) = 0 := by ext t; exact hx
  rw [hz, map_zero, smul_zero, add_zero]

theorem stepEndpoint_of_zero {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    {h : ℝ} (hh : ‖h‖ * L < 1) {x : E} (hx : X x = 0) :
    stepEndpoint X hX h x = x := by
  simp only [stepEndpoint, fixedStep_of_zero X hX hh hx, constantPath_apply]

theorem stepEndpoint_hasCompactSupport {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    (hXc : HasCompactSupport X) {h : ℝ} (hh : ‖h‖ * L < 1) :
    HasCompactSupport (fun x => stepEndpoint X hX h x - x) := by
  apply hXc.mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  exact sub_eq_zero.mpr (stepEndpoint_of_zero X hX hh hx)


def clockField (X : C(ℝ × E,E)) : C(ℝ × E,ℝ × E) :=
  ⟨fun p => (1,X p), continuous_const.prodMk X.continuous⟩

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[simp] theorem clockField_apply (X : C(ℝ × E,E)) (p : ℝ × E) :
    clockField X p = (1,X p) := rfl

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem clockField_lipschitz {L : ℝ≥0} (X : C(ℝ × E,E)) (hX : LipschitzWith L X) :
    LipschitzWith L (clockField X) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simpa only [clockField_apply, Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using hX.dist_le_mul p q

omit [CompleteSpace E] in
theorem clockField_smooth (X : C(ℝ × E,E)) (hX : ContDiff ℝ ∞ X) :
    ContDiff ℝ ∞ (clockField X) := contDiff_const.prodMk hX

theorem fixedStep_clock {L : ℝ≥0} (X : C(ℝ × E,E)) (hX : LipschitzWith L X)
    {h : ℝ} (hh : ‖h‖ * L < 1) (p : ℝ × E) (s : Time) :
    (fixedStep (clockField X) (clockField_lipschitz X hX) h p s).1 = p.1 + h * (s : ℝ) := by
  let u := fixedStep (clockField X) (clockField_lipschitz X hX) h p
  have he := congrArg (fun v : C(Time,ℝ × E) => (v s).1)
    (fixedStep_equation (clockField X) (clockField_lipschitz X hX) hh p)
  have hi := (ContinuousLinearMap.fst ℝ ℝ E).intervalIntegral_comp_comm (μ := MeasureTheory.volume)
    ((extendPath ((clockField X).comp u)).continuous.intervalIntegrable 0 (s:ℝ))
  have hc : (fun t : ℝ => (extendPath ((clockField X).comp u) t).1) = fun _ => (1:ℝ) := by
    funext t
    rfl
  change (∫ t in 0..(s:ℝ), (extendPath ((clockField X).comp u) t).1) =
    (∫ t in 0..(s:ℝ), extendPath ((clockField X).comp u) t).1 at hi
  rw [hc] at hi
  change (u s).1 = p.1 + h * (∫ t in 0..(s:ℝ), extendPath ((clockField X).comp u) t).1 at he
  rw [← hi] at he
  simpa using he

@[simp] theorem stepEndpoint_clock {L : ℝ≥0} (X : C(ℝ × E,E)) (hX : LipschitzWith L X)
    {h : ℝ} (hh : ‖h‖ * L < 1) (p : ℝ × E) :
    (stepEndpoint (clockField X) (clockField_lipschitz X hX) h p).1 = p.1 + h := by
  simpa only [stepEndpoint,mul_one] using fixedStep_clock X hX hh p ⟨1,by simp⟩

def timeStep {L : ℝ≥0} (X : C(ℝ × E,E)) (hX : LipschitzWith L X) (h t : ℝ) (x : E) : E :=
  (stepEndpoint (clockField X) (clockField_lipschitz X hX) h (t,x)).2

theorem timeStep_smooth [FiniteDimensional ℝ E] {L : ℝ≥0}
    (X : C(ℝ × E,E)) (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) : ContDiff ℝ ∞ (timeStep X hX h t) :=
  ((stepEndpoint_smooth (clockField X) (clockField_lipschitz X hX)
    (clockField_smooth X hXs) hh).comp (contDiff_const.prodMk contDiff_id)).snd

theorem timeStep_inverse {L : ℝ≥0} (X : C(ℝ × E,E)) (hX : LipschitzWith L X)
    {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) :
    Function.LeftInverse (timeStep X hX (-h) (t+h)) (timeStep X hX h t) := by
  intro x
  have he := congrArg Prod.snd (stepEndpoint_neg_leftInverse (clockField X)
    (clockField_lipschitz X hX) hh (t,x))
  have hp : stepEndpoint (clockField X) (clockField_lipschitz X hX) h (t,x) =
      (t+h,timeStep X hX h t x) := by
    apply Prod.ext
    · exact stepEndpoint_clock X hX hh (t,x)
    · rfl
  rw [hp] at he
  exact he

def timeStepHomeomorph [FiniteDimensional ℝ E] {L : ℝ≥0}
    (X : C(ℝ × E,E)) (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) : E ≃ₜ E where
  toFun := timeStep X hX h t
  invFun := timeStep X hX (-h) (t+h)
  left_inv := timeStep_inverse X hX hh t
  right_inv := by
    intro x
    simpa only [neg_neg, add_neg_cancel_right] using
      timeStep_inverse X hX (h := -h) (by simpa using hh) (t+h) x
  continuous_toFun := (timeStep_smooth X hX hXs hh t).continuous
  continuous_invFun := (timeStep_smooth X hX hXs (h := -h) (by simpa using hh) (t+h)).continuous

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

theorem fixedStep_variation_clock {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X) {h : ℝ} (hh : ‖h‖ * L < 1)
    (p : ℝ × E) (v : E) (s : Time) :
    ((fderiv ℝ (fixedStep (clockField X) (clockField_lipschitz X hX) h) p (0,v)) s).1 = 0 := by
  let u := fixedStep (clockField X) (clockField_lipschitz X hX) h
  have hu := ((fixedStep_smooth (clockField X) (clockField_lipschitz X hX)
    (clockField_smooth X hXs) hh).differentiable (by simp) p).hasFDerivAt
  have hd := (ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt.comp p
    ((ContinuousMap.evalCLM (M := ℝ × E) ℝ s).hasFDerivAt.comp p hu)
  have he : (fun q => (u q s).1) = fun q : ℝ × E => q.1 + h * (s:ℝ) := by
    funext q
    exact fixedStep_clock X hX hh q s
  change HasFDerivAt (fun q => (u q s).1) _ p at hd
  rw [he] at hd
  have hd' := (ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt.add_const (h * (s:ℝ)) (x := p)
  have huniq := congrArg (fun A : (ℝ × E) →L[ℝ] ℝ => A (0,v)) (hd.unique hd')
  exact huniq

theorem timeStep_fderiv {L : ℝ≥0} (X : C(ℝ × E,E)) (hX : LipschitzWith L X)
    (hXs : ContDiff ℝ ∞ X) {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) (x v : E) :
    fderiv ℝ (timeStep X hX h t) x v =
      (fderiv ℝ (stepEndpoint (clockField X) (clockField_lipschitz X hX) h) (t,x) (0,v)).2 := by
  have hs := ((stepEndpoint_smooth (clockField X) (clockField_lipschitz X hX)
    (clockField_smooth X hXs) hh).differentiable (by simp) (t,x)).hasFDerivAt
  have hp : HasFDerivAt (fun x : E => (t,x)) (ContinuousLinearMap.inr ℝ ℝ E) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have hd := (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt.comp x (hs.comp x hp)
  exact congrArg (fun A : E →L[ℝ] E => A v) hd.fderiv


omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem clockField_fderiv {X : C(ℝ × E,E)} (hXs : ContDiff ℝ ∞ X) (p v : ℝ × E) :
    fderiv ℝ (clockField X) p v = (0, fderiv ℝ X p v) := by
  have hd := (hasFDerivAt_const (1:ℝ) p).prodMk
    ((hXs.differentiable (by simp) p).hasFDerivAt)
  exact congrArg (fun A : (ℝ × E) →L[ℝ] (ℝ × E) => A v) hd.fderiv

theorem timeStep_preserves_density {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    (ρ : ℝ × E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hPDE : ∀ p v w, fderiv ℝ ρ p (1,X p) * B v w +
      ρ p * (B (fderiv ℝ X p (0,v)) w + B v (fderiv ℝ X p (0,w))) = 0)
    {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) (x v w : E) :
    ρ (t+h,timeStep X hX h t x) *
      B (fderiv ℝ (timeStep X hX h t) x v) (fderiv ℝ (timeStep X hX h t) x w) =
      ρ (t,x) * B v w := by
  let Y := clockField X
  let hY := clockField_lipschitz X hX
  let u := fixedStep Y hY h (t,x)
  let A := fderiv ℝ (fixedStep Y hY h) (t,x)
  let D : C(Time,(ℝ × E) →L[ℝ] (ℝ × E)) :=
    ⟨fun s => fderiv ℝ Y (u s),
      ((clockField_smooth X hXs).continuous_fderiv (by simp)).comp u.continuous⟩
  have hA (z : ℝ × E) : A z = constantPath z + h • pathIntegral (pathLinear D (A z)) :=
    congrArg (fun T : (ℝ × E) →L[ℝ] C(Time,ℝ × E) => T z)
      (fixedStep_variation Y hY (clockField_smooth X hXs) hh (t,x))
  have hA0 (z : ℝ × E) : extendPath (A z) 0 = z := by
    have he := congrArg (fun V : C(Time,ℝ × E) => V ⟨0,by simp⟩) (hA z)
    exact (extendPath_coe (A z) ⟨0,by simp⟩).trans (by simpa using he)
  let V : E → ℝ → E := fun z s => (extendPath (A (0,z)) s).2
  have hhor (z : E) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      extendPath (A (0,z)) s = (0,V z s) := by
    apply Prod.ext
    · rw [show extendPath (A (0,z)) s = A (0,z) ⟨s,hs⟩ from extendPath_coe _ ⟨s,hs⟩]
      exact fixedStep_variation_clock X hX hXs hh (t,x) z ⟨s,hs⟩
    · rfl
  have hVd (z : E) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivWithinAt (V z) (h • fderiv ℝ X (extendPath u s) (0,V z s)) (Icc (0:ℝ) 1) s := by
    have hd := (path_equation_derivative _ _ (0,z) h (hA (0,z)) hs).snd
    change HasDerivWithinAt (V z)
      (h • (fderiv ℝ Y (extendPath u s) (extendPath (A (0,z)) s)).2) _ s at hd
    rw [hhor z s hs,clockField_fderiv hXs] at hd
    exact hd
  let F : ℝ → ℝ := fun s => ρ (extendPath u s) * B (V v s) (V w s)
  have hFc : Continuous F := (hρ.continuous.comp (extendPath u).continuous).mul
    ((B.continuous.comp (extendPath (A (0,v))).continuous.snd).clm_apply
      (extendPath (A (0,w))).continuous.snd)
  have hFd (s : ℝ) (hs : s ∈ Ioo (0:ℝ) 1) : HasDerivAt F 0 s := by
    have hs' : s ∈ Icc (0:ℝ) 1 := ⟨hs.1.le,hs.2.le⟩
    have hUd := fixedStep_derivative Y hY hh (t,x) hs'
    have hρd := ((hρ.differentiable (by simp) (extendPath u s)).hasFDerivAt).comp_hasDerivWithinAt s hUd
    have hBd := ContinuousLinearMap.hasDerivWithinAt_of_bilinear (B := B)
      (hVd v s hs') (hVd w s hs')
    have hd := hρd.mul hBd
    have hz : fderiv ℝ ρ (extendPath u s) (h • Y (extendPath u s)) *
          B (V v s) (V w s) + ρ (extendPath u s) *
          (B (V v s) (h • fderiv ℝ X (extendPath u s) (0,V w s)) +
            B (h • fderiv ℝ X (extendPath u s) (0,V v s)) (V w s)) = 0 := by
      simp only [map_smul,smul_apply, smul_eq_mul]
      have he := hPDE (extendPath u s) (V v s) (V w s)
      change fderiv ℝ ρ (extendPath u s) (Y (extendPath u s)) * B (V v s) (V w s) +
        ρ (extendPath u s) * _ = 0 at he
      linear_combination h * he
    have hd0 : HasDerivWithinAt F 0 (Icc (0:ℝ) 1) s := hd.congr_deriv hz
    exact hd0.hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ) ≤ 1)
    hFc.continuousOn hFd (intervalIntegrable_const (c := (0:ℝ)))
  have hend : F 1 = F 0 := sub_eq_zero.mp (by simpa using hi.symm)
  have hzero : F 0 = ρ (t,x) * B v w := by
    change ρ (extendPath u 0) * B (extendPath (A (0,v)) 0).2 (extendPath (A (0,w)) 0).2 = _
    rw [hA0,hA0,show extendPath u 0 = (t,x) from
      (extendPath_coe u ⟨0,by simp⟩).trans (fixedStep_initial Y hY hh (t,x))]
  have hfinal : extendPath u 1 = (t+h,timeStep X hX h t x) := by
    rw [show extendPath u 1 = u ⟨1,by simp⟩ from extendPath_coe u ⟨1,by simp⟩]
    exact Prod.ext (stepEndpoint_clock X hX hh (t,x)) rfl
  have hfinalV (z : E) : V z 1 = fderiv ℝ (timeStep X hX h t) x z := by
    rw [timeStep_fderiv X hX hXs hh, stepEndpoint_fderiv Y hY (clockField_smooth X hXs) hh]
    exact congrArg Prod.snd (extendPath_coe (A (0,z)) ⟨1,by simp⟩)
  have hone : F 1 = ρ (t+h,timeStep X hX h t x) *
      B (fderiv ℝ (timeStep X hX h t) x v) (fderiv ℝ (timeStep X hX h t) x w) := by
    change ρ (extendPath u 1) * B (V v 1) (V w 1) = _
    rw [hfinal,hfinalV,hfinalV]
  exact hone.symm.trans (hend.trans hzero)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem timeStep_of_stationary {L : ℝ≥0} (X : C(ℝ × E,E)) (hX : LipschitzWith L X)
    {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) {x : E} (hx : ∀ s, X (s,x) = 0) :
    timeStep X hX h t x = x := by
  let q : C(Time,ℝ × E) := constantPath (t,x) + h • pathIntegral (constantPath (1,0))
  have hq (s : Time) : q s = (t+h*(s:ℝ),x) := by
    change (t,x) + h • (∫ a in (0:ℝ)..(s:ℝ), extendPath (constantPath (1,0)) a) = _
    have he : (fun a : ℝ => extendPath (constantPath ((1:ℝ),(0:E))) a) = fun _ => ((1:ℝ),(0:E)) := rfl
    rw [he,intervalIntegral.integral_const]
    simp
  have hy : (clockField X).comp q = constantPath (1,0) := by
    apply ContinuousMap.ext
    intro s
    change clockField X (q s) = (1,0)
    rw [hq,clockField_apply,hx]
  have hu : fixedStep (clockField X) (clockField_lipschitz X hX) h (t,x) = q := by
    apply (picard_contracts (clockField X) (clockField_lipschitz X hX) (p := ((t,x),h)) hh).fixedPoint_unique'
      (localPath_fixed (clockField X) (clockField_lipschitz X hX) (p := ((t,x),h)) hh)
    change constantPath (t,x) + h • pathIntegral ((clockField X).comp q) = q
    rw [hy]
  change (fixedStep (clockField X) (clockField_lipschitz X hX) h (t,x) ⟨1,by simp⟩).2 = x
  rw [hu,hq]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

def timeSteps {L : ℝ≥0} (X : C(ℝ × E,E)) (hX : LipschitzWith L X)
    (hXs : ContDiff ℝ ∞ X) {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) : ℕ → E ≃ₜ E
  | 0 => Homeomorph.refl E
  | N+1 => (timeSteps X hX hXs hh t N).trans (timeStepHomeomorph X hX hXs hh (t+N*h))

theorem timeSteps_smooth {L : ℝ≥0} (X : C(ℝ × E,E)) (hX : LipschitzWith L X)
    (hXs : ContDiff ℝ ∞ X) {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) (N : ℕ) :
    ContDiff ℝ ∞ (timeSteps X hX hXs hh t N) ∧
      ContDiff ℝ ∞ (timeSteps X hX hXs hh t N).symm := by
  induction N with
  | zero => exact ⟨contDiff_id,contDiff_id⟩
  | succ N ih =>
    constructor
    · exact (timeStep_smooth X hX hXs hh (t+N*h)).comp ih.1
    · exact ih.2.comp (timeStep_smooth X hX hXs (h := -h) (by simpa using hh) ((t+N*h)+h))

theorem timeSteps_of_stationary {L : ℝ≥0} (X : C(ℝ × E,E)) (hX : LipschitzWith L X)
    (hXs : ContDiff ℝ ∞ X) {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) (N : ℕ)
    {x : E} (hx : ∀ s, X (s,x) = 0) : timeSteps X hX hXs hh t N x = x := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change timeStep X hX h (t+N*h) (timeSteps X hX hXs hh t N x) = x
    rw [ih,timeStep_of_stationary X hX hh _ hx]

theorem timeSteps_preserves_density {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    (ρ : ℝ × E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hPDE : ∀ p v w, fderiv ℝ ρ p (1,X p) * B v w +
      ρ p * (B (fderiv ℝ X p (0,v)) w + B v (fderiv ℝ X p (0,w))) = 0)
    {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) (N : ℕ) (x v w : E) :
    ρ (t+N*h,timeSteps X hX hXs hh t N x) *
      B (fderiv ℝ (timeSteps X hX hXs hh t N) x v)
        (fderiv ℝ (timeSteps X hX hXs hh t N) x w) = ρ (t,x) * B v w := by
  induction N with
  | zero => simp [timeSteps]
  | succ N ih =>
    let F := timeSteps X hX hXs hh t N
    let G := timeStep X hX h (t+N*h)
    have hF : Differentiable ℝ F := (timeSteps_smooth X hX hXs hh t N).1.differentiable (by simp)
    have hG : Differentiable ℝ G := (timeStep_smooth X hX hXs hh (t+N*h)).differentiable (by simp)
    change ρ (t+(N+1:ℕ)*h,G (F x)) *
      B (fderiv ℝ (G ∘ F) x v) (fderiv ℝ (G ∘ F) x w) = _
    rw [fderiv_comp x (hG (F x)) (hF x)]
    have ht : t + (N+1:ℕ)*h = (t+N*h)+h := by push_cast; ring
    rw [ht]
    exact (timeStep_preserves_density X hX hXs ρ hρ B hPDE hh (t+N*h) (F x)
      (fderiv ℝ F x v) (fderiv ℝ F x w)).trans ih

theorem exists_density_transport {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    (ρ : ℝ × E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hPDE : ∀ p v w, fderiv ℝ ρ p (1,X p) * B v w +
      ρ p * (B (fderiv ℝ X p (0,v)) w + B v (fderiv ℝ X p (0,w))) = 0)
    (K : Set E) (hK : IsCompact K) (hXspt : ∀ s x, x ∉ K → X (s,x) = 0)
    (t T : ℝ) : ∃ Φ : E ≃ₜ E, ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Φ.symm ∧
      (∀ x, x ∉ K → Φ x = x) ∧ HasCompactSupport (fun x => Φ x - x) ∧
      (∀ x v w, ρ (t+T,Φ x) * B (fderiv ℝ Φ x v) (fderiv ℝ Φ x w) = ρ (t,x) * B v w) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (‖T‖ * L)
  have hN0 : (0:ℝ) < N := (mul_nonneg (norm_nonneg _) L.coe_nonneg).trans_lt hN
  let h := T / N
  have hh : ‖h‖ * L < 1 := by
    change ‖T / (N:ℝ)‖ * L < 1
    rw [norm_div,Real.norm_of_nonneg hN0.le, div_mul_eq_mul_div]
    exact (div_lt_one hN0).mpr hN
  have he : (N:ℝ) * h = T := by dsimp [h]; field_simp
  let Φ := timeSteps X hX hXs hh t N
  have hfix (x : E) (hx : x ∉ K) : Φ x = x :=
    timeSteps_of_stationary X hX hXs hh t N (fun s => hXspt s x hx)
  refine ⟨Φ,(timeSteps_smooth X hX hXs hh t N).1,
    (timeSteps_smooth X hX hXs hh t N).2,hfix,?_,?_⟩
  · exact HasCompactSupport.intro hK (fun x hx => sub_eq_zero.mpr (hfix x hx))
  · intro x v w
    simpa only [he] using timeSteps_preserves_density X hX hXs ρ hρ B hPDE hh t N x v w

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian

def segmentLinear : (ℝ × ℝ) →L[ℝ] C(Time,ℝ × ℝ) :=
  LinearMap.mkContinuous {
    toFun := fun p => ⟨fun s => ((s : ℝ) * p.1,p.2),
      (continuous_subtype_val.mul continuous_const).prodMk continuous_const⟩
    map_add' := by intros; ext s <;> simp [mul_add]
    map_smul' := by intros; ext s <;> simp [mul_left_comm] }
    1 (by
      intro p
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg p)).mpr
      intro s
      change ‖((s:ℝ)*p.1,p.2)‖ ≤ ‖p‖
      simp only [Prod.norm_def, norm_mul, Real.norm_eq_abs, abs_of_nonneg s.property.1]
      apply max_le
      · exact (mul_le_of_le_one_left (abs_nonneg p.1)
          (by simpa only [abs_of_nonneg s.property.1] using s.property.2)).trans (le_max_left _ _)
      · exact le_max_right _ _)

def segmentPath (a : ℝ) (p : ℝ × ℝ) : C(Time,ℝ × ℝ) :=
  constantPath (a,0) + segmentLinear (p - (a,0))

@[simp] theorem segmentPath_apply (a : ℝ) (p : ℝ × ℝ) (s : Time) :
    segmentPath a p s = (a + (s : ℝ) * (p.1-a),p.2) := by
  change (a + (s:ℝ)*(p.1-a),0+(p.2-0)) = _
  simp

theorem segmentPath_smooth (a : ℝ) : ContDiff ℝ ∞ (segmentPath a) :=
  contDiff_const.add (segmentLinear.contDiff.comp (contDiff_id.sub contDiff_const))

def pathAverage : C(Time,ℝ) →L[ℝ] ℝ :=
  (ContinuousMap.evalCLM ℝ (⟨1,by simp⟩ : Time)).comp pathIntegral

theorem segment_integral_eq (f : ℝ × ℝ → ℝ) (hf : Continuous f) (a : ℝ) (p : ℝ × ℝ) :
    (∫ x in a..p.1, f (x,p.2)) =
      (p.1-a) * pathAverage ((⟨f,hf⟩ : C(ℝ × ℝ,ℝ)).comp (segmentPath a p)) := by
  let u := (⟨f,hf⟩ : C(ℝ × ℝ,ℝ)).comp (segmentPath a p)
  have he : (∫ s in (0:ℝ)..1, extendPath u s) = ∫ s in (0:ℝ)..1, f (a+s*(p.1-a),p.2) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
    change extendPath u s = f (a+s*(p.1-a),p.2)
    rw [show extendPath u s = u ⟨s,hs⟩ from extendPath_coe u ⟨s,hs⟩]
    change f (segmentPath a p ⟨s,hs⟩) = _
    rw [segmentPath_apply]
  change _ = (p.1-a) * (∫ s in (0:ℝ)..1, extendPath u s)
  rw [he]
  have hi := intervalIntegral.smul_integral_comp_add_mul (fun x => f (x,p.2))
    (a := (0:ℝ)) (b := 1) (p.1-a) a
  simpa only [smul_eq_mul, mul_zero, mul_one, add_zero, add_sub_cancel, mul_comm] using hi.symm

theorem contDiff_segment_integral {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (a : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => ∫ x in a..p.1, f (x,p.2)) := by
  have he : (fun p : ℝ × ℝ => ∫ x in a..p.1, f (x,p.2)) =
      fun p => (p.1-a) * pathAverage ((⟨f,hf.continuous⟩ : C(ℝ × ℝ,ℝ)).comp (segmentPath a p)) := by
    funext p
    exact segment_integral_eq f hf.continuous a p
  rw [he]
  exact (contDiff_fst.sub contDiff_const).mul
    (pathAverage.contDiff.comp ((postcomp_contDiff hf).comp (segmentPath_smooth a)))

def planarMarginal (A : ℝ) (f : ℝ × ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in -A..A, f (x,t)

def planarPrimitiveX (A : ℝ) (f : ℝ × ℝ → ℝ) (ρ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  -ρ p.1 * ∫ t in -A..p.2, planarMarginal A f t

def planarPrimitiveY (A : ℝ) (f : ℝ × ℝ → ℝ) (ρ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ x in -A..p.1, f (x,p.2) - ρ x * planarMarginal A f p.2

theorem planarMarginal_smooth {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (A : ℝ) :
    ContDiff ℝ ∞ (planarMarginal A f) :=
  (contDiff_segment_integral hf (-A)).comp (contDiff_const.prodMk contDiff_id)

theorem planarPrimitive_smooth {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (A : ℝ) :
    ContDiff ℝ ∞ (planarPrimitiveX A f ρ) ∧ ContDiff ℝ ∞ (planarPrimitiveY A f ρ) := by
  have hg := planarMarginal_smooth hf A
  have hG : ContDiff ℝ ∞ (fun p : ℝ × ℝ => ∫ t in -A..p.2, planarMarginal A f t) := by
    exact (contDiff_segment_integral (hg.comp contDiff_fst) (-A)).comp
      (contDiff_snd.prodMk contDiff_fst)
  exact ⟨(hρ.comp contDiff_fst).neg.mul hG,
    contDiff_segment_integral (hf.sub ((hρ.comp contDiff_fst).mul (hg.comp contDiff_snd))) (-A)⟩

theorem planarPrimitive_curl {A : ℝ} {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hg : Continuous (planarMarginal A f)) (p : ℝ × ℝ) :
    deriv (fun x => planarPrimitiveY A f ρ (x,p.2)) p.1 -
      deriv (fun t => planarPrimitiveX A f ρ (p.1,t)) p.2 = f p := by
  have hc : Continuous (fun x => f (x,p.2) - ρ x * planarMarginal A f p.2) :=
    (hf.comp (continuous_id.prodMk continuous_const)).sub (hρ.mul continuous_const)
  have hY := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable (-A) p.1)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hG := intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable (-A) p.2)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  have hX := hG.const_mul (-ρ p.1)
  change deriv (fun x => ∫ v in -A..x, f (v,p.2) - ρ v * planarMarginal A f p.2) p.1 -
    deriv (fun t => -ρ p.1 * ∫ v in -A..t, planarMarginal A f v) p.2 = _
  rw [hY.deriv, hX.deriv]
  ring

theorem interval_primitive_zero_outside {A : ℝ} (hA : 0 ≤ A) {g : ℝ → ℝ}
    (hg : Continuous g) (hgs : ∀ x, A ≤ |x| → g x = 0)
    (hg0 : (∫ x in -A..A, g x) = 0) {t : ℝ} (ht : A ≤ |t|) :
    (∫ x in -A..t, g x) = 0 := by
  rcases le_abs.mp ht with ht | ht
  · have hi := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hg.intervalIntegrable (-A) A) (hg.intervalIntegrable A t)
    have hz : (∫ x in A..t, g x) = 0 := by
      have he : (∫ x in A..t, g x) = ∫ x in A..t, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le ht] at hx
        exact hgs x (hx.1.trans (le_abs_self x))
      simpa using he
    rw [hg0,hz,zero_add] at hi
    exact hi.symm
  · have hta : t ≤ -A := by linarith
    have hz : (∫ x in -A..t, g x) = ∫ x in -A..t, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_ge hta] at hx
      apply hgs x
      rw [abs_of_nonpos (hx.2.trans (neg_nonpos.mpr hA))]
      linarith [hx.2]
    simpa using hz

theorem planarPrimitive_support {A : ℝ} (hA : 0 ≤ A) {f : ℝ × ℝ → ℝ}
    (hf : Continuous f) {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    (hfs : ∀ x t, A ≤ |x| ∨ A ≤ |t| → f (x,t) = 0)
    (hρs : ∀ x, A ≤ |x| → ρ x = 0)
    (hρ1 : (∫ x in -A..A, ρ x) = 1)
    (hg : Continuous (planarMarginal A f))
    (hf0 : (∫ t in -A..A, planarMarginal A f t) = 0) :
    HasCompactSupport (planarPrimitiveX A f ρ) ∧
      HasCompactSupport (planarPrimitiveY A f ρ) := by
  have hgt (t : ℝ) (ht : A ≤ |t|) : planarMarginal A f t = 0 := by
    unfold planarMarginal
    have he : (fun x => f (x,t)) = fun _ => (0:ℝ) := by
      funext x
      exact hfs x t (Or.inr ht)
    rw [he,intervalIntegral.integral_zero]
  have hF (t : ℝ) : (∫ x in -A..A, f (x,t) - ρ x * planarMarginal A f t) = 0 := by
    have hc : Continuous (fun x => f (x,t)) := hf.comp (continuous_id.prodMk continuous_const)
    have hd : Continuous (fun x => ρ x * planarMarginal A f t) := hρ.mul continuous_const
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable (-A) A)
      (hd.intervalIntegrable (-A) A)]
    rw [intervalIntegral.integral_mul_const, hρ1, one_mul]
    exact sub_self _
  have hzero (p : ℝ × ℝ) (hp : A ≤ |p.1| ∨ A ≤ |p.2|) :
      planarPrimitiveX A f ρ p = 0 ∧ planarPrimitiveY A f ρ p = 0 := by
    rcases hp with hp | hp
    · constructor
      · simp [planarPrimitiveX, hρs _ hp]
      · apply interval_primitive_zero_outside hA
          ((hf.comp (continuous_id.prodMk continuous_const)).sub (hρ.mul continuous_const))
          (fun x hx => by
            change f (x,p.2) - ρ x * planarMarginal A f p.2 = 0
            rw [hfs x p.2 (Or.inl hx),hρs x hx]; ring) (hF p.2) hp
    · constructor
      · unfold planarPrimitiveX
        rw [interval_primitive_zero_outside hA hg hgt hf0 hp, mul_zero]
      · unfold planarPrimitiveY
        have he : (fun x => f (x,p.2) - ρ x * planarMarginal A f p.2) = fun _ => (0:ℝ) := by
          funext x
          rw [hfs x p.2 (Or.inr hp), hgt p.2 hp]
          ring
        rw [he,intervalIntegral.integral_zero]
  have hK : IsCompact (Icc (-A,-A) (A,A) : Set (ℝ × ℝ)) := isCompact_Icc
  have hout (p : ℝ × ℝ) (hp : p ∉ Icc (-A,-A) (A,A)) : A ≤ |p.1| ∨ A ≤ |p.2| := by
    by_contra! ht
    apply hp
    have hx := abs_lt.mp ht.1
    have hy := abs_lt.mp ht.2
    exact ⟨⟨hx.1.le,hy.1.le⟩,⟨hx.2.le,hy.2.le⟩⟩
  exact ⟨HasCompactSupport.intro hK (fun p hp => (hzero p (hout p hp)).1),
    HasCompactSupport.intro hK (fun p hp => (hzero p (hout p hp)).2)⟩

open MeasureTheory Function

theorem integral_eq_full_of_box_support {A : ℝ} {g : ℝ → ℝ}
    (hgs : ∀ x, A ≤ |x| → g x = 0) : (∫ x in -A..A, g x) = ∫ x, g x := by
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro x hx
  have hx' : |x| < A := by
    by_contra! ha
    exact hx (hgs x ha)
  exact ⟨(abs_lt.mp hx').1,(abs_lt.mp hx').2.le⟩

end PackingSufficiencySupport.Hamiltonian
end

end OAI
