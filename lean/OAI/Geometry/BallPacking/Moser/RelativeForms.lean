import Mathlib
import OAI.Geometry.BallPacking.Holder.BanachSpace

namespace OAI

noncomputable section
open scoped ContDiff Topology NNReal

namespace PackingSufficiencySupport.Hamiltonian

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem smooth_fixedPoint {K : ℝ≥0} {φ : E → F → F}
    (hφ : ContDiff ℝ ∞ (Function.uncurry φ)) (hc : ∀ x, ContractingWith K (φ x)) :
    ContDiff ℝ ∞ (fun x => (hc x).fixedPoint (φ x)) := by
  let z : E → F := fun x => (hc x).fixedPoint (φ x)
  let G : E × F → F := fun p => p.2 - φ p.1 p.2
  have hG : ContDiff ℝ ∞ G := contDiff_snd.sub hφ
  have hfix (x : E) : φ x (z x) = z x := (hc x).fixedPoint_isFixedPt
  have hzero (x : E) : G (x,z x) = 0 := sub_eq_zero.mpr (hfix x).symm
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hinr : fderiv ℝ G (x,z x) ∘L ContinuousLinearMap.inr ℝ E F =
      1 - fderiv ℝ (φ x) (z x) := by
    have hpx : HasFDerivAt (fun y : F => (x,y)) (ContinuousLinearMap.inr ℝ E F) (z x) :=
      (hasFDerivAt_const x (z x)).prodMk (hasFDerivAt_id (z x))
    have hcomp := (hG.differentiable (by simp) (x,z x)).hasFDerivAt.comp (z x) hpx
    have hφx : ContDiff ℝ ∞ (φ x) := hφ.comp (contDiff_const.prodMk contDiff_id)
    have hsub := (hasFDerivAt_id (z x)).sub ((hφx.differentiable (by simp) (z x)).hasFDerivAt)
    exact hcomp.unique hsub
  have hnorm : ‖fderiv ℝ (φ x) (z x)‖ < 1 :=
    (norm_fderiv_le_of_lipschitz ℝ (hc x).2).trans_lt
      (show (K : ℝ) < 1 from (hc x).1)
  have hunit := isUnit_one_sub_of_norm_lt_one hnorm
  obtain ⟨u, hu⟩ := hunit
  have hinv : (fderiv ℝ G (x,z x) ∘L ContinuousLinearMap.inr ℝ E F).IsInvertible := by
    rw [hinr]
    exact ⟨ContinuousLinearEquiv.ofUnit u, hu⟩
  have hloc := hG.contDiffAt.contDiffAt_implicitFunction (by simp) hinv
  apply hloc.congr_of_eventuallyEq
  filter_upwards [hG.contDiffAt.eventually_apply_implicitFunction (by simp) hinv] with y hy
  change z y = _
  apply (hc y).fixedPoint_unique' (hfix y)
  change φ y _ = _
  rw [hzero x] at hy
  exact (sub_eq_zero.mp hy).symm

theorem smoothOn_contraction_solution {φ : E → F → F} {z : E → F}
    {U : Set E} (hU : IsOpen U)
    (hφ : ContDiff ℝ ∞ (Function.uncurry φ))
    (hc : ∀ x ∈ U, ∃ K : ℝ≥0, ContractingWith K (φ x))
    (hz : ∀ x ∈ U, φ x (z x) = z x) : ContDiffOn ℝ ∞ z U := by
  let G : E × F → F := fun p => p.2 - φ p.1 p.2
  have hG : ContDiff ℝ ∞ G := contDiff_snd.sub hφ
  intro x hx
  obtain ⟨K,hK⟩ := hc x hx
  have hinr : fderiv ℝ G (x,z x) ∘L ContinuousLinearMap.inr ℝ E F =
      1 - fderiv ℝ (φ x) (z x) := by
    have hpx : HasFDerivAt (fun y : F => (x,y)) (ContinuousLinearMap.inr ℝ E F) (z x) :=
      (hasFDerivAt_const x (z x)).prodMk (hasFDerivAt_id (z x))
    have hcomp := (hG.differentiable (by simp) (x,z x)).hasFDerivAt.comp (z x) hpx
    have hφx : ContDiff ℝ ∞ (φ x) := hφ.comp (contDiff_const.prodMk contDiff_id)
    have hsub := (hasFDerivAt_id (z x)).sub ((hφx.differentiable (by simp) (z x)).hasFDerivAt)
    exact hcomp.unique hsub
  have hnorm : ‖fderiv ℝ (φ x) (z x)‖ < 1 :=
    (norm_fderiv_le_of_lipschitz ℝ hK.2).trans_lt (show (K : ℝ) < 1 from hK.1)
  obtain ⟨u,hu⟩ := isUnit_one_sub_of_norm_lt_one hnorm
  have hinv : (fderiv ℝ G (x,z x) ∘L ContinuousLinearMap.inr ℝ E F).IsInvertible := by
    rw [hinr]
    exact ⟨ContinuousLinearEquiv.ofUnit u,hu⟩
  have hloc := hG.contDiffAt.contDiffAt_implicitFunction (by simp) hinv
  have hzero : G (x,z x) = 0 := sub_eq_zero.mpr (hz x hx).symm
  apply ContDiffAt.contDiffWithinAt
  apply hloc.congr_of_eventuallyEq
  filter_upwards [hG.contDiffAt.eventually_apply_implicitFunction (by simp) hinv,
    hU.mem_nhds hx] with y hy hyU
  obtain ⟨L,hL⟩ := hc y hyU
  apply hL.fixedPoint_unique' (hz y hyU)
  change φ y _ = _
  rw [hzero] at hy
  exact (sub_eq_zero.mp hy).symm

end PackingSufficiencySupport.Hamiltonian

open scoped ContDiff Topology
open Set Metric

namespace PackingSufficiencySupport.Hamiltonian

universe u v
variable {K : Type v} {E F : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def pathLinear (A : C(K, E →L[ℝ] F)) : C(K,E) →L[ℝ] C(K,F) :=
  LinearMap.mkContinuous {
    toFun := fun u => ⟨fun t => A t (u t), A.continuous.clm_apply u.continuous⟩
    map_add' := by intros; ext t; simp
    map_smul' := by intros; ext t; simp }
    ‖A‖ (by
      intro u
      apply (ContinuousMap.norm_le _ (by positivity)).mpr
      intro t
      exact ((A t).le_opNorm _).trans (mul_le_mul (A.norm_coe_le_norm t)
        (u.norm_coe_le_norm t) (by positivity) (by positivity)))

@[simp] theorem pathLinear_apply (A : C(K, E →L[ℝ] F)) (u : C(K,E)) (t : K) :
    pathLinear A u t = A t (u t) := rfl

def pathLinearOperator : C(K, E →L[ℝ] F) →L[ℝ] C(K,E) →L[ℝ] C(K,F) :=
  LinearMap.mkContinuous {
    toFun := fun A : C(K, E →L[ℝ] F) => pathLinear A
    map_add' := by intros; ext u t; simp
    map_smul' := by intros; ext u t; simp }
    1 (by
      intro A
      rw [one_mul]
      change ‖pathLinear A‖ ≤ ‖A‖
      refine (pathLinear A).opNorm_le_bound (norm_nonneg A) ?_
      intro u
      apply (ContinuousMap.norm_le _ (by positivity)).mpr
      intro t
      exact ((A t).le_opNorm _).trans (mul_le_mul (A.norm_coe_le_norm t)
        (u.norm_coe_le_norm t) (by positivity) (by positivity)))

@[simp] theorem pathLinearOperator_apply (A : C(K, E →L[ℝ] F)) :
    pathLinearOperator A = pathLinear A := rfl

theorem uniform_taylor [FiniteDimensional ℝ E] {f : E → F}
    (hf : ContDiff ℝ 1 f) (S : Set E) (hS : IsCompact S) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ S, ∀ v : E, ‖v‖ < δ →
      ‖f (x+v) - f x - fderiv ℝ f x v‖ ≤ ε * ‖v‖ := by
  have huc : UniformContinuousOn (fderiv ℝ f) (cthickening 1 S) :=
    hS.cthickening.uniformContinuousOn_of_continuous
      (hf.continuous_fderiv (by simp)).continuousOn
  obtain ⟨δ,hδ,hδf⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  let r := min 1 (δ/2)
  have hr : 0 < r := lt_min one_pos (half_pos hδ)
  refine ⟨r,hr,fun x hx v hv => ?_⟩
  have hbound : ∀ y ∈ Metric.closedBall x r,
      ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ ε := by
    intro y hy
    have hy' : dist y x ≤ r := hy
    have hyr : y ∈ cthickening 1 S :=
      mem_cthickening_of_dist_le _ x _ _ hx (hy'.trans (min_le_left _ _))
    have hxr : x ∈ cthickening 1 S := self_subset_cthickening _ hx
    have hyd : dist y x < δ := hy'.trans_lt
      ((min_le_right _ _).trans_lt (half_lt_self hδ))
    simpa only [dist_eq_norm] using (hδf y hyr x hxr hyd).le
  have he := (convex_closedBall x r).norm_image_sub_le_of_norm_fderiv_le'
    (fun y _ => hf.differentiable_one y) hbound (mem_closedBall_self hr.le)
    (show x+v ∈ Metric.closedBall x r by simpa [mem_closedBall, dist_eq_norm] using hv.le)
  simpa only [add_sub_cancel_left] using he

theorem postcomp_hasFDerivAt [FiniteDimensional ℝ E] {f : E → F}
    (hf : ContDiff ℝ 1 f) (u : C(K,E)) :
    HasFDerivAt (ContinuousMap.comp (⟨f,hf.continuous⟩ : C(E,F)))
      (pathLinear ⟨fun t => fderiv ℝ f (u t),
        (hf.continuous_fderiv (by simp)).comp u.continuous⟩) u := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ,hδ,hrem⟩ := uniform_taylor hf (range u)
    (isCompact_range u.continuous) hε
  filter_upwards [Metric.ball_mem_nhds (0 : C(K,E)) hδ] with v hv
  have hv' : ‖v‖ < δ := by simpa only [mem_ball, dist_zero_right] using hv
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  have hvt : ‖v t‖ < δ := (v.norm_coe_le_norm t).trans_lt hv'
  exact (hrem (u t) ⟨t,rfl⟩ (v t) hvt).trans
    (mul_le_mul_of_nonneg_left (v.norm_coe_le_norm t) hε.le)

theorem postcomp_contDiff_nat [FiniteDimensional ℝ E] (q : ℕ) {f : E → F}
    (hf : ContDiff ℝ q f) :
    ContDiff ℝ q (ContinuousMap.comp (⟨f,hf.continuous⟩ : C(E,F)) : C(K,E) → C(K,F)) := by
  induction q generalizing F with
  | zero => exact contDiff_zero.mpr (ContinuousMap.continuous_postcomp _)
  | succ q ih =>
    have hdf : ContDiff ℝ q (fderiv ℝ f) := hf.fderiv_right (by simp)
    have hf1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast Nat.succ_pos q)
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun u => pathLinear ((⟨fderiv ℝ f,hdf.continuous⟩ : C(E,E →L[ℝ] F)).comp u), ?_, ?_⟩
    · exact (pathLinearOperator (K := K) (E := E) (F := F)).contDiff.comp (ih hdf)
    · intro u
      exact postcomp_hasFDerivAt hf1 u

theorem postcomp_contDiff [FiniteDimensional ℝ E] {f : E → F}
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (ContinuousMap.comp (⟨f,hf.continuous⟩ : C(E,F)) : C(K,E) → C(K,F)) := by
  apply contDiff_infty.mpr
  intro q
  exact postcomp_contDiff_nat q ((contDiff_infty.mp hf) q)

end PackingSufficiencySupport.Hamiltonian

open scoped ContDiff Topology
open Set Metric

namespace PackingSufficiencySupport.Hamiltonian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

abbrev Time := Set.Icc (0 : ℝ) 1

def extendPath (u : C(Time,E)) : C(ℝ,E) :=
  u.comp ⟨Set.projIcc 0 1 (by norm_num), continuous_projIcc⟩

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[simp] theorem extendPath_coe (u : C(Time,E)) (t : Time) :
    extendPath u t = u t := by
  simp [extendPath]

def pathIntegral : C(Time,E) →L[ℝ] C(Time,E) :=
  LinearMap.mkContinuous {
    toFun := fun u => ⟨fun t => ∫ s in 0..(t : ℝ), extendPath u s,
      (intervalIntegral.differentiable_integral_of_continuous
        (extendPath u).continuous).continuous.comp continuous_subtype_val⟩
    map_add' := by
      intro u v
      ext t
      exact intervalIntegral.integral_add
        ((extendPath u).continuous.intervalIntegrable _ _)
        ((extendPath v).continuous.intervalIntegrable _ _)
    map_smul' := by
      intro c u
      ext t
      exact intervalIntegral.integral_smul c _ }
    1 (by
      intro u
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
      intro t
      exact (intervalIntegral.norm_integral_le_of_norm_le_const
        (fun s _ => u.norm_coe_le_norm _)).trans (by
          simp only [sub_zero, abs_of_nonneg t.property.1]
          exact mul_le_of_le_one_right (norm_nonneg u) t.property.2))

@[simp] theorem pathIntegral_apply (u : C(Time,E)) (t : Time) :
    pathIntegral u t = ∫ s in 0..(t : ℝ), extendPath u s := rfl

@[simp] theorem pathIntegral_zero (u : C(Time,E)) :
    pathIntegral u ⟨0,by simp⟩ = 0 := by simp

theorem norm_pathIntegral_le (u : C(Time,E)) : ‖pathIntegral u‖ ≤ ‖u‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
  intro t
  exact (intervalIntegral.norm_integral_le_of_norm_le_const
    (fun s _ => u.norm_coe_le_norm _)).trans (by
      simp only [sub_zero, abs_of_nonneg t.property.1]
      exact mul_le_of_le_one_right (norm_nonneg u) t.property.2)


open scoped NNReal

def constantPath : E →L[ℝ] C(Time,E) :=
  LinearMap.mkContinuous {
    toFun := ContinuousMap.const Time
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
    1 (by
      intro x
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg x)).mpr
      intro t
      exact le_rfl)

omit [CompleteSpace E] in
@[simp] theorem constantPath_apply (x : E) (t : Time) : constantPath x t = x := rfl

def picard (X : C(E,E)) (p : E × ℝ) (u : C(Time,E)) : C(Time,E) :=
  constantPath p.1 + p.2 • pathIntegral (X.comp u)

@[simp] theorem picard_apply (X : C(E,E)) (p : E × ℝ) (u : C(Time,E)) (s : Time) :
    picard X p u s = p.1 + p.2 • ∫ t in 0..(s : ℝ), extendPath (X.comp u) t := rfl

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem postcomp_lipschitz {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X) :
    LipschitzWith L (X.comp : C(Time,E) → C(Time,E)) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  apply (ContinuousMap.dist_le (mul_nonneg L.coe_nonneg dist_nonneg)).mpr
  intro t
  exact (hX.dist_le_mul _ _).trans
    (mul_le_mul_of_nonneg_left (ContinuousMap.dist_apply_le_dist t) L.coe_nonneg)

theorem picard_lipschitz {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X) (p : E × ℝ) :
    LipschitzWith (‖p.2‖₊ * L) (picard X p) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simp only [picard, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub,
    norm_smul, ← map_sub, NNReal.coe_mul, coe_nnnorm]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    ((norm_pathIntegral_le (X.comp u - X.comp v)).trans
      ((postcomp_lipschitz X hX).norm_sub_le u v))
    (norm_nonneg p.2)

theorem picard_contDiff [FiniteDimensional ℝ E] (X : C(E,E)) (hX : ContDiff ℝ ∞ X) :
    ContDiff ℝ ∞ (Function.uncurry (picard X)) := by
  exact ((constantPath (E := E)).contDiff.comp (contDiff_fst.comp contDiff_fst)).add
    ((contDiff_snd.comp contDiff_fst).smul
      ((pathIntegral (E := E)).contDiff.comp
        ((postcomp_contDiff hX).comp contDiff_snd)))

def picardDomain (L : ℝ≥0) : Set (E × ℝ) := {p | ‖p.2‖ * L < 1}

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem picardDomain_open (L : ℝ≥0) : IsOpen (picardDomain (E := E) L) :=
  isOpen_lt (continuous_snd.norm.mul continuous_const) continuous_const

theorem picard_contracts {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    {p : E × ℝ} (hp : p ∈ picardDomain L) :
    ContractingWith (‖p.2‖₊ * L) (picard X p) :=
  ⟨by exact_mod_cast hp,picard_lipschitz X hX p⟩

def localPath {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X) (p : E × ℝ) : C(Time,E) := by
  classical
  exact if hp : p ∈ picardDomain L then (picard_contracts X hX hp).fixedPoint (picard X p)
  else constantPath p.1

theorem localPath_fixed {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    {p : E × ℝ} (hp : p ∈ picardDomain L) :
    picard X p (localPath X hX p) = localPath X hX p := by
  simp only [localPath, dite_eq_left hp]
  exact (picard_contracts X hX hp).fixedPoint_isFixedPt

theorem localPath_smooth [FiniteDimensional ℝ E] {L : ℝ≥0}
    (X : C(E,E)) (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X) :
    ContDiffOn ℝ ∞ (localPath X hX) (picardDomain L) := by
  apply smoothOn_contraction_solution (picardDomain_open L) (picard_contDiff X hXs)
  · intro p hp
    exact ⟨_,picard_contracts X hX hp⟩
  · exact fun _ hp => localPath_fixed X hX hp

def fixedStep {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X) (h : ℝ) : E → C(Time,E) :=
  fun x => localPath X hX (x,h)

theorem fixedStep_smooth [FiniteDimensional ℝ E] {L : ℝ≥0}
    (X : C(E,E)) (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    {h : ℝ} (hh : ‖h‖ * L < 1) : ContDiff ℝ ∞ (fixedStep X hX h) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact ((localPath_smooth X hX hXs).contDiffAt
    ((picardDomain_open L).mem_nhds hh)).comp x
      (contDiff_id.prodMk contDiff_const).contDiffAt

theorem fixedStep_equation {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    {h : ℝ} (hh : ‖h‖ * L < 1) (x : E) :
    fixedStep X hX h x = constantPath x + h • pathIntegral (X.comp (fixedStep X hX h x)) :=
  (localPath_fixed X hX (p := (x,h)) hh).symm

@[simp] theorem fixedStep_initial {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    {h : ℝ} (hh : ‖h‖ * L < 1) (x : E) :
    fixedStep X hX h x ⟨0,by simp⟩ = x := by
  have he := congrArg (fun u : C(Time,E) => u ⟨0,by simp⟩) (fixedStep_equation X hX hh x)
  simpa using he

theorem fixedStep_variation [FiniteDimensional ℝ E] {L : ℝ≥0}
    (X : C(E,E)) (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    {h : ℝ} (hh : ‖h‖ * L < 1) (x : E) :
    fderiv ℝ (fixedStep X hX h) x = constantPath +
      h • pathIntegral ∘L pathLinear
        ⟨fun t => fderiv ℝ X (fixedStep X hX h x t),
          (hXs.continuous_fderiv (by simp)).comp (fixedStep X hX h x).continuous⟩ ∘L
        fderiv ℝ (fixedStep X hX h) x := by
  let u := fixedStep X hX h
  have hu : HasFDerivAt u (fderiv ℝ u x) x :=
    ((fixedStep_smooth X hX hXs hh).differentiable (by simp) x).hasFDerivAt
  have hN := (postcomp_hasFDerivAt (hXs.of_le (by simp)) (u x)).comp x hu
  have hI := (pathIntegral (E := E)).hasFDerivAt.comp x hN
  have hR := (constantPath (E := E)).hasFDerivAt.add (hI.const_smul h)
  have heq : (fun y => constantPath y + h • pathIntegral (X.comp (u y))) = u := by
    funext y
    exact (fixedStep_equation X hX hh y).symm
  change HasFDerivAt (fun y => constantPath y + h • pathIntegral (X.comp (u y))) _ x at hR
  rw [heq] at hR
  exact hu.unique hR

theorem path_equation_derivative (u v : C(Time,E)) (a : E) (h : ℝ)
    (hu : u = constantPath a + h • pathIntegral v)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (extendPath u) (h • extendPath v s) (Icc (0 : ℝ) 1) s := by
  have hi := intervalIntegral.integral_hasDerivAt_right
    ((extendPath v).continuous.intervalIntegrable 0 s)
    (extendPath v).continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    (extendPath v).continuous.continuousAt
  have hd := (hasDerivAt_const s a).add (HasDerivAt.const_smul h hi)
  simp only [zero_add] at hd
  apply hd.hasDerivWithinAt.congr_of_mem _ hs
  intro t ht
  have he := congrArg (fun w : C(Time,E) => w ⟨t,ht⟩) hu
  rw [show extendPath u t = u ⟨t,ht⟩ from extendPath_coe u ⟨t,ht⟩]
  exact he

theorem fixedStep_derivative {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    {h : ℝ} (hh : ‖h‖ * L < 1) (x : E) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (extendPath (fixedStep X hX h x))
      (h • X (extendPath (fixedStep X hX h x) s)) (Icc (0 : ℝ) 1) s :=
  path_equation_derivative _ _ x h (fixedStep_equation X hX hh x) hs

def stepEndpoint {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X) (h : ℝ) (x : E) : E :=
  fixedStep X hX h x ⟨1,by simp⟩

theorem stepEndpoint_smooth [FiniteDimensional ℝ E] {L : ℝ≥0}
    (X : C(E,E)) (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    {h : ℝ} (hh : ‖h‖ * L < 1) : ContDiff ℝ ∞ (stepEndpoint X hX h) :=
  (ContinuousMap.evalCLM (M := E) ℝ (⟨1,by simp⟩ : Time)).contDiff.comp
    (fixedStep_smooth X hX hXs hh)

theorem stepEndpoint_injective {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    {h : ℝ} (hh : ‖h‖ * L < 1) : Function.Injective (stepEndpoint X hX h) := by
  intro x y he
  have hLip : LipschitzWith (‖h‖₊ * L) (fun z : E => h • X z) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simp only [dist_eq_norm, ← smul_sub, norm_smul, NNReal.coe_mul, coe_nnnorm]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (hX.norm_sub_le z w) (norm_nonneg h)
  have hder (z : E) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      HasDerivWithinAt (extendPath (fixedStep X hX h z))
        (h • X (extendPath (fixedStep X hX h z) t)) (Iic t) t := by
    apply (fixedStep_derivative X hX hh z ⟨ht.1.le,ht.2⟩).mono_of_mem_nhdsWithin
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ht.1),
      (self_mem_nhdsWithin : Iic t ∈ 𝓝[Iic t] t)] with s hs hst
    exact ⟨hs.le,hst.trans ht.2⟩
  have heq : Set.EqOn (extendPath (fixedStep X hX h x))
      (extendPath (fixedStep X hX h y)) (Icc (0 : ℝ) 1) :=
    ODE_solution_unique_of_mem_Icc_left (v := fun _ z => h • X z)
      (s := fun _ => Set.univ) (fun _ _ => hLip.lipschitzOnWith)
      (extendPath (fixedStep X hX h x)).continuous.continuousOn (hder x) (by simp)
      (extendPath (fixedStep X hX h y)).continuous.continuousOn (hder y) (by simp)
      (by simpa only [stepEndpoint, ← extendPath_coe] using he)
  have hzero := heq (x := 0) (by simp)
  have hx0 := (extendPath_coe (fixedStep X hX h x) ⟨0,by simp⟩).trans
    (fixedStep_initial X hX hh x)
  have hy0 := (extendPath_coe (fixedStep X hX h y) ⟨0,by simp⟩).trans
    (fixedStep_initial X hX hh y)
  exact hx0.symm.trans (hzero.trans hy0)

theorem stepEndpoint_fderiv [FiniteDimensional ℝ E] {L : ℝ≥0}
    (X : C(E,E)) (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    {h : ℝ} (hh : ‖h‖ * L < 1) (x : E) :
    fderiv ℝ (stepEndpoint X hX h) x =
      (ContinuousMap.evalCLM (M := E) ℝ (⟨1,by simp⟩ : Time)).comp
        (fderiv ℝ (fixedStep X hX h) x) := by
  exact ((ContinuousMap.evalCLM (M := E) ℝ (⟨1,by simp⟩ : Time)).hasFDerivAt.comp x
    (((fixedStep_smooth X hX hXs hh).differentiable (by simp) x).hasFDerivAt)).fderiv

theorem stepEndpoint_preserves_bilinear [FiniteDimensional ℝ E] {L : ℝ≥0}
    (X : C(E,E)) (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ x u v, B (fderiv ℝ X x u) v + B u (fderiv ℝ X x v) = 0)
    {h : ℝ} (hh : ‖h‖ * L < 1) (x v w : E) :
    B (fderiv ℝ (stepEndpoint X hX h) x v)
      (fderiv ℝ (stepEndpoint X hX h) x w) = B v w := by
  let u := fixedStep X hX h x
  let A := fderiv ℝ (fixedStep X hX h) x
  let D : C(Time,E →L[ℝ] E) := ⟨fun t => fderiv ℝ X (u t),
    (hXs.continuous_fderiv (by simp)).comp u.continuous⟩
  have hA (z : E) : A z = constantPath z + h • pathIntegral (pathLinear D (A z)) := by
    exact congrArg (fun T : E →L[ℝ] C(Time,E) => T z) (fixedStep_variation X hX hXs hh x)
  have hA0 (z : E) : extendPath (A z) 0 = z := by
    have he := congrArg (fun V : C(Time,E) => V ⟨0,by simp⟩) (hA z)
    have he' : A z ⟨0,by simp⟩ = z := by simpa using he
    exact (extendPath_coe (A z) ⟨0,by simp⟩).trans he'
  have hAd (z : E) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (extendPath (A z))
        (h • fderiv ℝ X (extendPath u s) (extendPath (A z) s)) (Icc (0 : ℝ) 1) s :=
    path_equation_derivative _ _ z h (hA z) hs
  let f : ℝ → ℝ := fun s => B (extendPath (A v) s) (extendPath (A w) s)
  have hfc : Continuous f :=
    (B.continuous.comp (extendPath (A v)).continuous).clm_apply (extendPath (A w)).continuous
  have hfd (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : HasDerivAt f 0 s := by
    have hd := ContinuousLinearMap.hasDerivWithinAt_of_bilinear (B := B)
      (hAd v s ⟨hs.1.le,hs.2.le⟩) (hAd w s ⟨hs.1.le,hs.2.le⟩)
    have hz : B (extendPath (A v) s)
          (h • fderiv ℝ X (extendPath u s) (extendPath (A w) s)) +
        B (h • fderiv ℝ X (extendPath u s) (extendPath (A v) s))
          (extendPath (A w) s) = 0 := by
      simp only [map_smul, smul_apply, smul_eq_mul]
      rw [← mul_add, add_comm, hB, mul_zero]
    rw [hz] at hd
    exact hd.hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ) ≤ 1)
    hfc.continuousOn hfd (intervalIntegrable_const (c := (0 : ℝ)))
  have hend : f 1 = f 0 := by
    apply sub_eq_zero.mp
    simpa only [intervalIntegral.integral_zero] using hi.symm
  have hf0 : f 0 = B v w := by change B _ _ = _; rw [hA0, hA0]
  rw [stepEndpoint_fderiv X hX hXs hh]
  change B (A v ⟨1,by simp⟩) (A w ⟨1,by simp⟩) = B v w
  have hf1 : f 1 = B (A v ⟨1,by simp⟩) (A w ⟨1,by simp⟩) := by
    change B _ _ = _
    rw [extendPath_coe (A v) ⟨1,by simp⟩, extendPath_coe (A w) ⟨1,by simp⟩]
  exact hf1.symm.trans (hend.trans hf0)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def reverseTime (s : Time) : Time :=
  ⟨1 - (s : ℝ), sub_nonneg.mpr s.property.2, sub_le_self 1 s.property.1⟩

def reversePath (u : C(Time,E)) : C(Time,E) :=
  u.comp ⟨reverseTime, (continuous_const.sub continuous_subtype_val).subtype_mk _⟩

omit [CompleteSpace E] in
theorem reversePath_integral (X : C(E,E)) (u : C(Time,E)) (s : Time) :
    (∫ t in 0..(s : ℝ), extendPath (X.comp (reversePath u)) t) =
      ∫ t in 1 - (s : ℝ)..1, extendPath (X.comp u) t := by
  have he : (∫ t in 0..(s : ℝ), extendPath (X.comp (reversePath u)) t) =
      ∫ t in 0..(s : ℝ), extendPath (X.comp u) (1 - t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le s.property.1] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans s.property.2⟩
    have ht'' : 1 - t ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht'.1,ht'.2]
    change extendPath (X.comp (reversePath u)) t = extendPath (X.comp u) (1-t)
    rw [show extendPath (X.comp (reversePath u)) t = (X.comp (reversePath u)) ⟨t,ht'⟩
      from extendPath_coe _ ⟨t,ht'⟩,
      show extendPath (X.comp u) (1-t) = (X.comp u) ⟨1-t,ht''⟩
      from extendPath_coe _ ⟨1-t,ht''⟩]
    rfl
  rw [he, intervalIntegral.integral_comp_sub_left]
  simp

theorem fixedStep_reverse {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    {h : ℝ} (hh : ‖h‖ * L < 1) (x : E) :
    fixedStep X hX (-h) (stepEndpoint X hX h x) = reversePath (fixedStep X hX h x) := by
  let u := fixedStep X hX h x
  have hh' : ‖-h‖ * L < 1 := by simpa using hh
  apply (picard_contracts X hX (p := (stepEndpoint X hX h x,-h)) hh').fixedPoint_unique'
    (localPath_fixed X hX (p := (stepEndpoint X hX h x,-h)) hh')
  ext s
  change stepEndpoint X hX h x + (-h) •
    (∫ t in 0..(s : ℝ), extendPath (X.comp (reversePath u)) t) = reversePath u s
  rw [reversePath_integral]
  have hs : 1 - (s : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [s.property.1,s.property.2]
  have h1 := congrArg (fun v : C(Time,E) => v ⟨1,by simp⟩) (fixedStep_equation X hX hh x)
  have h2 := congrArg (fun v : C(Time,E) => v ⟨1-(s:ℝ),hs⟩) (fixedStep_equation X hX hh x)
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    ((extendPath (X.comp u)).continuous.intervalIntegrable 0 (1-(s:ℝ)))
    ((extendPath (X.comp u)).continuous.intervalIntegrable (1-(s:ℝ)) 1)
  change u ⟨1,by simp⟩ = x + h • (∫ t in 0..1, extendPath (X.comp u) t) at h1
  change u ⟨1-(s:ℝ),hs⟩ = x + h • (∫ t in 0..1-(s:ℝ), extendPath (X.comp u) t) at h2
  change u ⟨1,by simp⟩ + _ = u ⟨1-(s:ℝ),hs⟩
  rw [h1,h2,← hi, smul_add,neg_smul]
  abel

theorem stepEndpoint_neg_leftInverse {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    {h : ℝ} (hh : ‖h‖ * L < 1) :
    Function.LeftInverse (stepEndpoint X hX (-h)) (stepEndpoint X hX h) := by
  intro x
  change fixedStep X hX (-h) (stepEndpoint X hX h x) ⟨1,by simp⟩ = x
  rw [fixedStep_reverse X hX hh]
  change fixedStep X hX h x ⟨1-1,by norm_num⟩ = x
  convert fixedStep_initial X hX hh x using 1; norm_num

end PackingSufficiencySupport.Hamiltonian
end

end OAI
