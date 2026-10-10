import Mathlib
import OAI.Geometry.NearbyLagrangian.PicardPaths

namespace OAI

/-! Smooth nonautonomous evolution, uniqueness and compact support. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.SmoothFlow
open Set Filter ContinuousLinearMap
open scoped ContDiff Topology NNReal Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def flowDiffeomorph {X : E → E} (φ : ODE.CompleteFlow X)
    (hX : ContDiff ℝ ∞ X) {K : ℝ≥0} (hK : LipschitzWith K X) (t : ℝ) :
    Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) E E ∞ where
  toEquiv := (φ.homeomorph hK t).toEquiv
  contMDiff_toFun := ((contDiff_completeFlow φ hX hK).comp
    (contDiff_id.prodMk contDiff_const)).contMDiff
  contMDiff_invFun := ((contDiff_completeFlow φ hX hK).comp
    (contDiff_id.prodMk contDiff_const)).contMDiff

theorem exists_smooth_completeFlow_compact {X : E → E}
    (hX : ContDiff ℝ ∞ X) (hs : HasCompactSupport X) :
    ∃ φ : ODE.CompleteFlow X, ContDiff ℝ ∞ φ.toFun ∧
      ∀ t, Function.support (fun x => φ.toFun (x,t)-x) ⊆ Function.support X := by
  obtain ⟨L,K,hL,hK⟩ := ODE.compact_field_bounds hs (hX.of_le (by simp))
  obtain ⟨φ⟩ := ODE.exists_completeFlow X hL hK
  exact ⟨φ,contDiff_completeFlow φ hX hK,φ.displacement_support_subset hK⟩

def timeLift (X : ℝ × E → E) : ℝ × E → ℝ × E := fun z => (1,X z)

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma timeLift_lipschitz {X : ℝ × E → E} {K : ℝ≥0} (hK : LipschitzWith K X) :
    LipschitzWith K (timeLift X) := by
  change LipschitzWith K (fun z => ((1:ℝ),X z))
  simpa only [max_eq_right (show (0:ℝ≥0) ≤ K from bot_le)] using
    (LipschitzWith.const (1:ℝ)).prodMk hK

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma timeLift_bound {X : ℝ × E → E} {L : ℝ≥0} (hL : ∀ z, ‖X z‖ ≤ L) :
    ∀ z, ‖timeLift X z‖ ≤ (max 1 L : ℝ≥0) := by
  intro z
  simp only [timeLift,Prod.norm_def,norm_one,NNReal.coe_max,NNReal.coe_one]
  exact max_le_max le_rfl (hL z)

omit [CompleteSpace E] in
lemma lifted_time {X : ℝ × E → E} (φ : ODE.CompleteFlow (timeLift X))
    (z : ℝ × E) (u : ℝ) : (φ.toFun (z,u)).1 = z.1+u := by
  have hd (v:ℝ) : HasDerivAt (fun w => (φ.toFun (z,w)).1-w) 0 v := by
    have h := ((fst ℝ ℝ E).hasFDerivAt.comp_hasDerivAt v (φ.derivative z v)).sub
      (hasDerivAt_id v)
    simpa only [timeLift,coe_fst',sub_self,Function.comp_def,Pi.sub_def,id_eq] using h
  have he := is_const_of_deriv_eq_zero (fun v => (hd v).differentiableAt)
    (fun v => (hd v).deriv) u 0
  rw [φ.initial,sub_zero] at he
  exact sub_eq_iff_eq_add.mp he

def evolution {X : ℝ × E → E} (φ : ODE.CompleteFlow (timeLift X))
    (z : (ℝ × E) × ℝ) : E := (φ.toFun (z.1,z.2-z.1.1)).2

omit [CompleteSpace E] in
lemma evolution_initial {X : ℝ × E → E} (φ : ODE.CompleteFlow (timeLift X))
    (s : ℝ) (x : E) : evolution φ ((s,x),s) = x := by
  simp only [evolution,sub_self,φ.initial]

omit [CompleteSpace E] in
lemma evolution_derivative {X : ℝ × E → E} (φ : ODE.CompleteFlow (timeLift X))
    (s : ℝ) (x : E) (t : ℝ) :
    HasDerivAt (fun t => evolution φ ((s,x),t)) (X (t,evolution φ ((s,x),t))) t := by
  have h := ((snd ℝ ℝ E).hasFDerivAt.comp_hasDerivAt (t-s)
    (φ.derivative (s,x) (t-s))).scomp t ((hasDerivAt_id t).sub_const s)
  have ht := lifted_time φ (s,x) (t-s)
  have he : φ.toFun ((s,x),t-s) = (t,evolution φ ((s,x),t)) := by
    apply Prod.ext
    · change (φ.toFun ((s,x),t-s)).1 = t
      simpa only [add_sub_cancel] using ht
    · rfl
  have hd : HasDerivAt (fun t => evolution φ ((s,x),t)) (X (φ.toFun ((s,x),t-s))) t := by
    simpa only [Function.comp_def,timeLift,coe_snd',one_smul,evolution,id_eq] using h
  rw [he] at hd
  exact hd

omit [CompleteSpace E] in
lemma evolution_cocycle {X : ℝ × E → E} (φ : ODE.CompleteFlow (timeLift X))
    {K : ℝ≥0} (hK : LipschitzWith K X) (s r t : ℝ) (x : E) :
    evolution φ ((r,evolution φ ((s,x),r)),t) = evolution φ ((s,x),t) := by
  have he : (r,evolution φ ((s,x),r)) = φ.toFun ((s,x),r-s) := by
    apply Prod.ext
    · simpa only [add_sub_cancel] using (lifted_time φ (s,x) (r-s)).symm
    · rfl
  dsimp only [evolution]
  rw [← he]
  change (φ.toFun ((r,evolution φ ((s,x),r)),t-r)).2 = _
  rw [he,φ.add (timeLift_lipschitz hK)]
  congr 2
  ring_nf

lemma contDiff_evolution {X : ℝ × E → E} (φ : ODE.CompleteFlow (timeLift X))
    (hX : ContDiff ℝ ∞ X) {K : ℝ≥0} (hK : LipschitzWith K X) :
    ContDiff ℝ ∞ (evolution φ) := by
  have h := contDiff_completeFlow φ (contDiff_const.prodMk hX) (timeLift_lipschitz hK)
  exact (h.comp (contDiff_fst.prodMk (contDiff_snd.sub contDiff_fst.fst))).snd

def evolutionDiffeomorph {X : ℝ × E → E} (φ : ODE.CompleteFlow (timeLift X))
    (hX : ContDiff ℝ ∞ X) {K : ℝ≥0} (hK : LipschitzWith K X) (s t : ℝ) :
    Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) E E ∞ where
  toFun x := evolution φ ((s,x),t)
  invFun x := evolution φ ((t,x),s)
  left_inv x := by
    change evolution φ ((t,evolution φ ((s,x),t)),s) = x
    rw [evolution_cocycle φ hK,evolution_initial]
  right_inv x := by
    change evolution φ ((s,evolution φ ((t,x),s)),t) = x
    rw [evolution_cocycle φ hK,evolution_initial]
  contMDiff_toFun := ((contDiff_evolution φ hX hK).comp
    ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const)).contMDiff
  contMDiff_invFun := ((contDiff_evolution φ hX hK).comp
    ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const)).contMDiff

theorem exists_smooth_evolution {X : ℝ × E → E} (hX : ContDiff ℝ ∞ X)
    {L K : ℝ≥0} (hL : ∀ z, ‖X z‖ ≤ L) (hK : LipschitzWith K X) :
    ∃ φ : ODE.CompleteFlow (timeLift X), ContDiff ℝ ∞ (evolution φ) := by
  obtain ⟨φ⟩ := ODE.exists_completeFlow (timeLift X) (timeLift_bound hL) (timeLift_lipschitz hK)
  exact ⟨φ,contDiff_evolution φ hX hK⟩

end NearbyLagrangian.SmoothFlow

namespace NearbyLagrangian.SmoothFlow
open Set Filter
open scoped ContDiff Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
lemma field_lipschitz_spatial {X : ℝ × E → E} {K : ℝ≥0}
    (hK : LipschitzWith K X) (t : ℝ) : LipschitzWith K (fun x => X (t,x)) := by
  simpa [Function.comp_def] using hK.comp ((LipschitzWith.const t).prodMk LipschitzWith.id)

lemma evolution_unique {X : ℝ × E → E} (φ : ODE.CompleteFlow (timeLift X))
    {K : ℝ≥0} (hK : LipschitzWith K X) {y : ℝ → E} {s : ℝ} {x : E}
    (hy : ∀ t, HasDerivAt y (X (t,y t)) t) (hys : y s = x) :
    ∀ t, evolution φ ((s,x),t) = y t := by
  have heq := ODE_solution_unique_univ (v := fun t x => X (t,x)) (s := fun _ => univ)
    (fun t => (field_lipschitz_spatial hK t).lipschitzOnWith)
    (fun t => ⟨evolution_derivative φ s x t,mem_univ _⟩)
    (fun t => ⟨hy t,mem_univ _⟩)
    ((evolution_initial φ s x).trans hys.symm)
  exact fun t => congr_fun heq t

lemma evolution_fixed {X : ℝ × E → E} (φ : ODE.CompleteFlow (timeLift X))
    {K : ℝ≥0} (hK : LipschitzWith K X) {x : E} (hx : ∀ t, X (t,x) = 0)
    (s t : ℝ) : evolution φ ((s,x),t) = x := by
  apply evolution_unique φ hK (y := fun _ => x) (s := s) ?_ rfl t
  intro t
  rw [hx t]
  exact hasDerivAt_const t x

lemma evolution_support {X : ℝ × E → E} (φ : ODE.CompleteFlow (timeLift X))
    {K : ℝ≥0} (hK : LipschitzWith K X) {S : Set E}
    (hs : ∀ t, Function.support (fun x => X (t,x)) ⊆ S) (s t : ℝ) :
    Function.support (fun x => evolution φ ((s,x),t)-x) ⊆ S := by
  intro x hx
  by_contra hn
  have hz : ∀ t, X (t,x) = 0 := by
    intro t
    by_contra h
    exact hn (hs t h)
  exact hx (by
    change evolution φ ((s,x),t)-x = 0
    rw [evolution_fixed φ hK hz,sub_self])

end NearbyLagrangian.SmoothFlow

end

end OAI
