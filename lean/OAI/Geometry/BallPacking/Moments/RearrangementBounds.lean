import Mathlib
import OAI.Geometry.BallPacking.Rigidity.CompatibleStructures
import OAI.Geometry.BallPacking.Layers.PlanarRotation
import OAI.Geometry.BallPacking.Moments.PolytopeSlices

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.MomentPolytope
open scoped ContDiff ENNReal Pointwise Classical
open Comparison MeasureTheory
section
variable {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)
variable [∀ j, Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i)
theorem successive_bound (js : List (Fin m))
    (F : ConvexMaps (region b c) (convex_region b c)) (a : ℝ) (hF : ∀ p, F.val p ≤ a) :
    ∀ p, (successive b c hb js F).val p ≤ a := by
  induction js generalizing F with
  | nil => exact hF
  | cons j js ih => exact ih _ (coordRearrange_bound b c j hb F.val a hF)

theorem successive_increasing (js : List (Fin m)) (i : Fin m)
    (F : ConvexMaps (region b c) (convex_region b c))
    (hi : i ∈ js ∨ IncreasingIn b c i F.val) :
    IncreasingIn b c i (successive b c hb js F).val := by
  induction js generalizing F with
  | nil => exact hi.resolve_left List.not_mem_nil
  | cons j js ih =>
    apply ih
    by_cases hij : i = j
    · subst i
      exact Or.inr (coordRearrange_increasing b c j hb F)
    · rcases hi with hmem | hinc
      · exact Or.inl ((List.mem_cons.mp hmem).resolve_left hij)
      · exact Or.inr (coordRearrange_preserves_increasing b c j hb i hij F.val hinc)

def fullRearrangement (F : ConvexMaps (region b c) (convex_region b c)) :=
  successive b c hb (List.finRange m) F

theorem fullRearrangement_increasing (F : ConvexMaps (region b c) (convex_region b c))
    (i : Fin m) : IncreasingIn b c i (fullRearrangement b c hb F).val :=
  successive_increasing b c hb _ i F (Or.inl (List.mem_finRange i))

end

variable {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)

theorem increasing_min_at_zero (hb : ∀ ν i, 0 ≤ b ν i) (hc : ∀ ν, 0 ≤ c ν)
    (F : C(region b c, ℝ)) (hF : ∀ i, IncreasingIn b c i F) (q : region b c) :
    F ⟨0, zero_mem b c hc⟩ ≤ F q := by
  let p (s : Finset (Fin m)) : region b c :=
    ⟨fun i => if i ∈ s then q.val i else 0,
      lower_closed b c hb q.property
        (fun i => by split_ifs <;> [exact q.property.1 i; exact le_rfl])
        (fun i => by split_ifs <;> [exact le_rfl; exact q.property.1 i])⟩
  have h (s : Finset (Fin m)) : F (p ∅) ≤ F (p s) := by
    induction s using Finset.induction_on with
    | empty => exact le_rfl
    | @insert i s hi ih =>
      apply ih.trans
      apply hF i
      · change (if i ∈ s then q.val i else 0) ≤
          if i ∈ insert i s then q.val i else 0
        simpa [hi] using q.property.1 i
      · intro l hli
        change (if l ∈ s then q.val l else 0) =
          if l ∈ insert i s then q.val l else 0
        simp [hli]
  have h0 : p ∅ = ⟨0, zero_mem b c hc⟩ := by ext i; simp [p]
  have h1 : p Finset.univ = q := by ext i; simp [p]
  simpa only [h0,h1] using h Finset.univ

theorem volume_region_pos (hc : ∀ ν, 0 < c ν) : 0 < volume (region b c) := by
  let U : Set (Moments m) := {p | ∀ ν, ∑ i, b ν i * p i < c ν}
  have hU : IsOpen U := by
    simpa only [U, Set.ofPred_forall] using
      isOpen_iInter_of_finite (fun ν => isOpen_lt
        (show Continuous (fun p : Moments m => ∑ i, b ν i * p i) by fun_prop)
        (continuous_const (y := c ν)))
  have hU0 : (0 : Moments m) ∈ U := by
    intro ν
    simpa using hc ν
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU 0 hU0
  let p : Moments m := fun _ => δ/2
  have hpU : p ∈ U := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ δ/2)).mpr
      (fun i => by simp [p, Real.norm_eq_abs, abs_of_pos hδ]) |>.trans_lt (by linarith)
  let W : Set (Moments m) := {q | (∀ i, 0 < q i) ∧ q ∈ U}
  have hW : IsOpen W := by
    apply IsOpen.inter _ hU
    change IsOpen {q : Moments m | ∀ i, 0 < q i}
    simpa only [Set.ofPred_forall] using
      isOpen_iInter_of_finite (fun i : Fin m => isOpen_lt
        (continuous_const (y := (0 : ℝ))) (continuous_apply i))
  have hpW : p ∈ W := ⟨fun _ => half_pos hδ, hpU⟩
  have hsub : W ⊆ region b c := by
    intro q hq
    exact ⟨fun i => (hq.1 i).le, fun ν => (hq.2 ν).le⟩
  exact (hW.measure_pos volume ⟨p,hpW⟩).trans_le (measure_mono hsub)

theorem volume_region_toReal_pos (hc : ∀ ν, 0 < c ν) (hcomp : IsCompact (region b c)) :
    0 < (volume (region b c)).toReal :=
  ENNReal.toReal_pos (ne_of_gt (volume_region_pos b c hc)) hcomp.measure_ne_top

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.Comparison
open scoped ContDiff ENNReal Pointwise Classical
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E]
variable [MeasureSpace E] [BorelSpace E]
variable [IsFiniteMeasureOnCompacts (volume : Measure E)]

def averageMap (S : Set E) (hS : IsCompact S) : C(S, ℝ) →ₗ[ℝ] ℝ :=
  (volume S).toReal⁻¹ • integralMap volume S hS

theorem averageMap_mono (S : Set E) (hS : IsCompact S) (F G : C(S, ℝ)) (hFG : F ≤ G) :
    averageMap S hS F ≤ averageMap S hS G := by
  exact mul_le_mul_of_nonneg_left (integralMap_mono volume S hS F G hFG) (by positivity)

theorem averageMap_const (S : Set E) (hS : IsCompact S) (hvol : 0 < (volume S).toReal) (a : ℝ) :
    averageMap S hS (ContinuousMap.const _ a) = a := by
  change (volume S).toReal⁻¹ * integralMap volume S hS (ContinuousMap.const _ a) = a
  rw [integralMap_const, ← mul_assoc, inv_mul_cancel₀ hvol.ne', one_mul]

theorem averageMap_lower (S : Set E) (hS : IsCompact S) (hvol : 0 < (volume S).toReal)
    (F : C(S, ℝ)) (a : ℝ) (hF : ∀ p, a ≤ F p) : a ≤ averageMap S hS F := by
  rw [← averageMap_const S hS hvol a]
  exact averageMap_mono S hS _ _ hF

end PackingSufficiencySupport.Comparison

namespace PackingSufficiencySupport.MomentPolytope
open scoped ContDiff ENNReal Pointwise Classical
open Comparison MeasureTheory

variable {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)

theorem analytic_gap (hb : ∀ ν i, 0 ≤ b ν i) (hc : ∀ ν, 0 < c ν)
    (hcomp : IsCompact (region b c))
    (Q : ConvexMaps (region b c) (convex_region b c))
    {τ a : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) (ha : 0 < a)
    (hmean : averageMap (region b c) hcomp Q.val < 0)
    (houter : ∀ p : region b c, p.val ∉ τ • region b c → Q.val p ≤ -a) :
    letI : ∀ j, Nonempty (Active b j) := fun j => active_nonempty b c hb hc hcomp j
    ∃ (K : ConvexMaps (region b c) (convex_region b c)) (d : ℝ), 0 < d ∧
      ∀ p, (fullRearrangement b c hb (affineStep 1 (by norm_num) Q K)).val p ≤ K.val p - d := by
  let : CompactSpace (region b c) := isCompact_iff_compactSpace.mp hcomp
  let : ∀ j, Nonempty (Active b j) := fun j => active_nonempty b c hb hc hcomp j
  apply exists_rearranged_gap (zero_mem b c (fun ν => (hc ν).le)) Q
    (fullRearrangement b c hb) (averageMap (region b c) hcomp)
    (successive_nonexpansive b c hb (List.finRange m))
    (averageMap_lower _ _ (volume_region_toReal_pos b c hc hcomp))
  · intro F
    change (volume (region b c)).toReal⁻¹ * integralMap volume (region b c) hcomp
      (successive b c hb (List.finRange m) F).val =
        (volume (region b c)).toReal⁻¹ * integralMap volume (region b c) hcomp F.val
    rw [successive_integral]
  · intro F p
    exact increasing_min_at_zero b c hb (fun ν => (hc ν).le) _
      (fullRearrangement_increasing b c hb F) p
  · intro F G hFG
    exact successive_mono b c hb (List.finRange m) F G hFG
  · exact successive_translate b c hb (List.finRange m)
  · exact successive_bound b c hb (List.finRange m)
  · exact hτ
  · exact hτ1
  · exact neg_pos.mpr hmean
  · exact ha
  · exact (neg_neg _).symm
  · exact houter

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.Comparison
open scoped ContDiff ENNReal Pointwise Classical
open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem smooth_approximation (S : Set E) (hS : IsCompact S) (F : C(S, ℝ))
    {ε : ℝ} (hε : 0 < ε) : ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧
      ∀ p : S, dist (f p.val) (F p) < ε := by
  obtain ⟨f,hf⟩ := ContinuousMap.exists_extension hS.isClosed.isClosedEmbedding_subtypeVal F
  have huc : UniformContinuousOn f (cthickening 1 S) :=
    hS.cthickening.uniformContinuousOn_of_continuous f.continuous.continuousOn
  obtain ⟨δ,hδ,hfδ⟩ := Metric.uniformContinuousOn_iff.mp huc (ε/2) (half_pos hε)
  obtain ⟨g,hg,hgf⟩ := f.continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le
    (lt_min one_pos hδ)
  refine ⟨g,hg,fun p => ?_⟩
  have hdist : dist (g p.val) (f p.val) ≤ ε/2 := by
    apply hgf
    intro y hy
    rw [mem_ball, lt_min_iff] at hy
    exact (hfδ y (mem_cthickening_of_dist_le _ p.val _ _ p.property hy.1.le)
      p.val (self_subset_cthickening _ p.property) hy.2).le
  have heq : f p.val = F p := congrArg (fun H : C(S, ℝ) => H p) hf
  rw [heq] at hdist
  exact hdist.trans_lt (half_lt_self hε)

end PackingSufficiencySupport.Comparison

namespace HigherDimensionalBallPacking
open scoped ContDiff ENNReal Pointwise Classical

theorem hasPacking_iff_support {n k : ℕ} {R : ℝ} {r : Fin k → ℝ} :
    HasPacking n k R r ↔ PackingSufficiencySupport.HasPacking n k R r := by
  constructor
  · rintro ⟨U,f,h,hdis⟩
    refine ⟨f,?_,?_,hdis⟩
    · intro i
      exact ⟨U i,(h i).2.1.1,(h i).1,(h i).2.1.2⟩
    · intro i
      exact Set.image_subset_iff.mpr (h i).2.2
  · rintro ⟨f,hf,ht,hdis⟩
    choose U hUopen hUsub hUs hUemb hUsymp using hf
    refine ⟨U,f,?_,hdis⟩
    intro i
    exact ⟨hUsub i,⟨hUopen i,hUs i,hUemb i,hUsymp i⟩,Set.image_subset_iff.mp (ht i)⟩

theorem HasPacking.volume_lt {n k : ℕ} {R : ℝ} {r : Fin k → ℝ}
    (hn : 0 < n) (hR : 0 < R) (hr : ∀ i, 0 < r i)
    (hp : HasPacking n k R r) : (∑ i, r i ^ n) < R ^ n :=
  (hasPacking_iff_support.mp hp).volume_lt hn hR hr

end HigherDimensionalBallPacking

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology BigOperators
open Set Function
section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def outerMoments (j : ι) (z : PlanePhase ι) : ι → ℝ :=
  fun i => if i=j then 0 else radialArea (z i)

omit [Fintype ι] in
@[simp] theorem outerMoments_self (j : ι) (z : PlanePhase ι) : outerMoments j z j = 0 := by
  simp [outerMoments]

omit [Fintype ι] in
@[simp] theorem outerMoments_other (j : ι) (z : PlanePhase ι) {i : ι} (hi : i ≠ j) :
    outerMoments j z i = radialArea (z i) := by simp [outerMoments,hi]

@[fun_prop] theorem outerMoments_smooth (j : ι) : ContDiff ℝ ∞ (outerMoments j) := by
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i=j
  · simp only [outerMoments,hi,ite_true]
    exact contDiff_const
  · simp only [outerMoments,hi,ite_false]
    exact radialArea_smooth.comp (contDiff_apply ℝ Plane i)

def outerDifferential (j : ι) (z : PlanePhase ι) : PlanePhase ι →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun i => if i=j then 0 else
    (fderiv ℝ radialArea (z i)).comp (ContinuousLinearMap.proj i))

theorem outerMoments_hasFDerivAt (j : ι) (z : PlanePhase ι) :
    HasFDerivAt (outerMoments j) (outerDifferential j z) z := by
  apply hasFDerivAt_pi.mpr
  intro i
  by_cases hi : i=j
  · simpa only [outerMoments,hi,ite_true] using hasFDerivAt_const (c := (0:ℝ)) z
  · have hd := (radialArea_smooth.differentiable (by simp) (z i)).hasFDerivAt.comp z
      (ContinuousLinearMap.proj i : PlanePhase ι →L[ℝ] Plane).hasFDerivAt
    simpa only [outerMoments,hi,ite_false,Function.comp_def,ContinuousLinearMap.proj_apply] using hd

@[simp] theorem outerMoments_fderiv_apply (j : ι) (z v : PlanePhase ι) (i : ι) :
    fderiv ℝ (outerMoments j) z v i =
      if i=j then 0 else 2*Real.pi*((z i).1*(v i).1+(z i).2*(v i).2) := by
  rw [(outerMoments_hasFDerivAt j z).fderiv]
  dsimp [outerDifferential]
  split_ifs <;> simp

theorem outerMoments_fderiv_single (j i : ι) (z : PlanePhase ι) (w : Plane) :
    fderiv ℝ (outerMoments j) z (Pi.single i w) =
      if i=j then 0 else (2*Real.pi*((z i).1*w.1+(z i).2*w.2)) • Pi.single i (1:ℝ) := by
  funext k
  by_cases hi : i=j
  · subst i
    by_cases hk : k=j <;> simp [outerMoments_fderiv_apply,hk]
  · by_cases hk : k=i
    · subst k
      simp [outerMoments_fderiv_apply,hi]
    · by_cases hkj : k=j <;> simp [outerMoments_fderiv_apply,hi,hk,hkj]

end

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

namespace HamiltonianDiskIsotopyFamily

def refl (R : ℝ) : HamiltonianDiskIsotopyFamily P R where
  isotopy := SupportedSmoothIsotopyFamily.refl _
  symplectic := by
    intro y t x v w
    change planarArea (fderiv ℝ id x v) (fderiv ℝ id x w) = planarArea v w
    simp
  hamiltonian := fun _ => 0
  smooth := contDiff_const
  compact := HasCompactSupport.zero
  support := by simp
  flow := by
    intro y t x
    change HasDerivAt (fun _ : ℝ => x) (planarHamiltonianField (fderiv ℝ (fun _ : Plane => (0:ℝ)) x)) t
    have hz : fderiv ℝ (fun _ : Plane => (0:ℝ)) x = 0 :=
      (hasFDerivAt_const (c := (0:ℝ)) x).fderiv
    rw [hz]
    have he : planarHamiltonianField (0 : Plane →L[ℝ] ℝ) = 0 := by ext <;> simp [planarHamiltonianField]
    rw [he]
    exact hasDerivAt_const t x

theorem mapsTo_closed {R : ℝ} (Ψ : HamiltonianDiskIsotopyFamily P R) (y : P) (t : ℝ) :
    MapsTo (Ψ.isotopy.map y t) (closedRoundDisk R) (closedRoundDisk R) := by
  intro x hx
  by_cases hi : x ∈ roundDisk R
  · have hm := (Ψ.isotopy.eval y).mapsTo t hi
    change radiusSq (Ψ.isotopy.map y t x) < R^2 at hm
    exact hm.le
  · rw [Ψ.isotopy.fixed y t x (fun hs => hi (Ψ.isotopy.support_subset hs))]
    exact hx

end HamiltonianDiskIsotopyFamily

theorem radialArea_nonneg (x : Plane) : 0 ≤ radialArea x :=
  mul_nonneg Real.pi_pos.le (by dsimp [radiusSq]; positivity)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.MomentPolytope
open scoped ContDiff Topology BigOperators
open Set Function
open Hamiltonian

variable {m N : ℕ}

def baseProjection (j : Fin m) (y : Moments m) : Base j := fun i => y i

def baseProjectionL (j : Fin m) : Moments m →ₗ[ℝ] Base j where
  toFun := baseProjection j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[fun_prop] theorem baseProjection_smooth (j : Fin m) : ContDiff ℝ ∞ (baseProjection j) :=
  (baseProjectionL j).toContinuousLinearMap.contDiff

@[fun_prop] theorem assemble_zero_smooth (j : Fin m) :
    ContDiff ℝ ∞ (fun y : Base j => assemble j y 0) := by
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i=j
  · simp only [assemble,hi,dite_eq_left]; exact contDiff_const
  · simp only [assemble,dite_eq_right hi]
    exact contDiff_apply ℝ ℝ (⟨i,hi⟩ : {i : Fin m // i ≠ j})

@[simp] theorem baseProjection_assemble (j : Fin m) (y : Base j) (h : ℝ) :
    baseProjection j (assemble j y h) = y := by funext i; simp [baseProjection]

def fullBase (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m) : Set (Moments m) :=
  {y | y j=0 ∧ baseProjection j y ∈ baseRegion b c j}

theorem fullBase_eq_image (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m) :
    fullBase b c j = (fun y : Base j => assemble j y 0) '' baseRegion b c j := by
  ext y
  constructor
  · intro hy
    refine ⟨baseProjection j y,hy.2,?_⟩
    funext i
    by_cases hi : i=j
    · subst i; simpa using hy.1.symm
    · simp [assemble,hi,baseProjection]
  · rintro ⟨y,hy,rfl⟩
    exact ⟨by simp,by simpa using hy⟩

theorem fullBase_compact (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m)
    (hb : ∀ ν i, 0 ≤ b ν i) (hK : IsCompact (region b c)) : IsCompact (fullBase b c j) := by
  rw [fullBase_eq_image]
  exact (isCompact_baseRegion b c hb hK j).image (assemble_zero_smooth j).continuous

theorem fullBase_convex (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m) :
    Convex ℝ (fullBase b c j) := by
  intro y hy z hz a d ha hd had
  refine ⟨by change a*y j+d*z j=0; simp [hy.1,hz.1],?_⟩
  exact (convex_baseRegion b c j) hy.2 hz.2 ha hd had

variable (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m) [Nonempty (Active b j)]

def fullLength (y : Moments m) : ℝ := length b c j (baseProjection j y)

@[fun_prop] theorem continuous_fullLength : Continuous (fullLength b c j) :=
  (continuous_length b c j).comp (baseProjection_smooth j).continuous

theorem concave_fullLength : ConcaveOn ℝ (fullBase b c j) (fullLength b c j) := by
  refine ⟨fullBase_convex b c j,?_⟩
  intro y hy z hz a d ha hd had
  exact (concave_length b c j).2 hy.2 hz.2 ha hd had

def activeParameters (η : ℝ) : Set (Moments m) :=
  {y ∈ fullBase b c j | η ≤ fullLength b c j y}

theorem activeParameters_compact (hb : ∀ ν i, 0 ≤ b ν i) (hK : IsCompact (region b c)) (η : ℝ) :
    IsCompact (activeParameters b c j η) :=
  (fullBase_compact b c j hb hK).inter_right (isClosed_le continuous_const (continuous_fullLength b c j))

theorem activeParameters_convex (η : ℝ) : Convex ℝ (activeParameters b c j η) :=
  (concave_fullLength b c j).convex_ge η

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology BigOperators
open Set Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def planeMoments (z : PlanePhase ι) : ι → ℝ := fun i => radialArea (z i)

omit [DecidableEq ι] in
@[fun_prop] theorem planeMoments_smooth : ContDiff ℝ ∞ (planeMoments (ι := ι)) := by
  apply contDiff_pi.mpr
  intro i
  exact radialArea_smooth.comp (contDiff_apply ℝ Plane i)

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem planeMoments_nonneg (z : PlanePhase ι) (i : ι) : 0 ≤ planeMoments z i :=
  radialArea_nonneg (z i)

def momentDifferential (z : PlanePhase ι) : PlanePhase ι →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun i => (fderiv ℝ radialArea (z i)).comp (ContinuousLinearMap.proj i))

omit [DecidableEq ι] in
theorem planeMoments_hasFDerivAt (z : PlanePhase ι) :
    HasFDerivAt planeMoments (momentDifferential z) z := by
  apply hasFDerivAt_pi.mpr
  intro i
  exact (radialArea_smooth.differentiable (by simp) (z i)).hasFDerivAt.comp z
    (ContinuousLinearMap.proj i : PlanePhase ι →L[ℝ] Plane).hasFDerivAt

omit [DecidableEq ι] in
@[simp] theorem planeMoments_fderiv_apply (z v : PlanePhase ι) (i : ι) :
    fderiv ℝ planeMoments z v i = 2*Real.pi*((z i).1*(v i).1+(z i).2*(v i).2) := by
  rw [(planeMoments_hasFDerivAt z).fderiv]
  simp [momentDifferential]

theorem planeMoments_fderiv_single (i : ι) (z : PlanePhase ι) (w : Plane) :
    fderiv ℝ planeMoments z (Pi.single i w) =
      (2*Real.pi*((z i).1*w.1+(z i).2*w.2)) • Pi.single i (1:ℝ) := by
  funext j
  by_cases hji : j=i
  · subst j; simp
  · simp [hji]

def toricHamiltonian (F : (ι → ℝ) → ℝ) (p : ℝ × PlanePhase ι) : ℝ := F (planeMoments p.2)

omit [DecidableEq ι] in
@[fun_prop] theorem toricHamiltonian_smooth {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (toricHamiltonian F) := hF.comp (planeMoments_smooth.comp contDiff_snd)

def toricAngularSpeed (F : (ι → ℝ) → ℝ) (z : PlanePhase ι) (i : ι) : ℝ :=
  2*Real.pi*fderiv ℝ F (planeMoments z) (Pi.single i 1)

@[fun_prop] theorem toricAngularSpeed_smooth {F : (ι → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (i : ι) : ContDiff ℝ ∞ (fun z => toricAngularSpeed F z i) :=
  contDiff_const.mul (((hF.fderiv_right (by simp)).comp planeMoments_smooth).clm_apply contDiff_const)

theorem toricHamiltonian_fderiv_single {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (p : ℝ × PlanePhase ι) (i : ι) (w : Plane) :
    fderiv ℝ (toricHamiltonian F) p (0,Pi.single i w) =
      toricAngularSpeed F p.2 i*((p.2 i).1*w.1+(p.2 i).2*w.2) := by
  have hd := (hF.differentiable (by simp) (planeMoments p.2)).hasFDerivAt.comp p
    ((planeMoments_hasFDerivAt p.2).comp p (hasFDerivAt_snd (𝕜 := ℝ) (p := p)))
  change HasFDerivAt (toricHamiltonian F) _ p at hd
  rw [hd.fderiv]
  change fderiv ℝ F (planeMoments p.2) (momentDifferential p.2 (Pi.single i w)) = _
  rw [←(planeMoments_hasFDerivAt p.2).fderiv,planeMoments_fderiv_single,map_smul]
  dsimp [toricAngularSpeed]
  ring

theorem toricHamiltonian_field {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (p : ℝ × PlanePhase ι) (i : ι) :
    hamiltonianField phaseArea (toricHamiltonian F) p i =
      toricAngularSpeed F p.2 i • (-(p.2 i).2,(p.2 i).1) := by
  have h₁ := hamiltonianField_contraction phaseArea_isInvertible (toricHamiltonian F) p
    (Pi.single i (0,1))
  have h₂ := hamiltonianField_contraction phaseArea_isInvertible (toricHamiltonian F) p
    (Pi.single i (1,0))
  rw [phaseArea_single_right,toricHamiltonian_fderiv_single hF] at h₁ h₂
  simp only [planarArea_apply,mul_one,mul_zero,sub_zero,zero_sub,zero_add,add_zero] at h₁ h₂
  apply Prod.ext
  · change _ = toricAngularSpeed F p.2 i * -(p.2 i).2
    linarith
  · change _ = toricAngularSpeed F p.2 i * (p.2 i).1
    linarith

theorem toricHamiltonian_preserves_moments {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (p : ℝ × PlanePhase ι) :
    fderiv ℝ planeMoments p.2 (hamiltonianField phaseArea (toricHamiltonian F) p) = 0 := by
  funext i
  rw [planeMoments_fderiv_apply,toricHamiltonian_field hF]
  simp only [Pi.zero_apply,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

end PackingSufficiencySupport.Hamiltonian
end

end OAI
