import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.SparseClusters
import OAI.Probability.LatticeSurface.Dynamics.ClusterShift
import OAI.Probability.LatticeSurface.Dynamics.JacobianIdentity
import OAI.Probability.LatticeSurface.Dynamics.LogDet
import OAI.Probability.LatticeSurface.Dynamics.MatrixJacobi
import OAI.Probability.LatticeSurface.Dynamics.ShiftAnalysis
import OAI.Probability.LatticeSurface.Dynamics.ShiftAsymptotics
import OAI.Probability.LatticeSurface.Dynamics.ShiftData

namespace OAI

universe u v

open Set MeasureTheory

namespace FeasibleShift.ShiftData

open SparseClusters

variable {V : Type u} [Fintype V] [DecidableEq V]

variable {W : Type v} [Fintype W] [DecidableEq W]

variable {n D Db B : ℕ} {ρ : ENNReal} {sstar L M N : ℝ}

variable (S : ShiftData (V := V) W n D Db B ρ sstar L M N)

noncomputable def active := shiftGraph S.graph S.ground

noncomputable def H (s : ℝ) (x : V) (h : FreeSites S.pins → ℝ) : ℕ :=
  (FeasibleShift.component (contactGraph S.active (extendHeight S.pins S.boundary h) s) x).card

noncomputable def good (s R : ℝ) : Set (FreeSites S.pins → ℝ) := {h | ∀ x, (S.H s x h : ℝ) ≤ R}

instance law_isProbabilityMeasure : IsProbabilityMeasure S.law :=
  ProbabilityTheory.cond_isProbabilityMeasure_of_finite S.polytope_positive S.polytope_finite

lemma active_le : S.active ≤ S.graph := fun _ _ h => h.1

lemma active_degree (x : V) : (neighbors S.active x).card ≤ D := by
  apply (Finset.card_le_card ?_).trans (S.degree x)
  intro y hy
  exact (mem_neighbors _ _ _).mpr (S.active_le ((mem_neighbors _ _ _).mp hy))

lemma H_pos (s : ℝ) (x : V) (h : FreeSites S.pins → ℝ) : 0 < S.H s x h :=
  Finset.card_pos.mpr ⟨x, self_mem_component _ x⟩

lemma H_le_card (s : ℝ) (x : V) (h : FreeSites S.pins → ℝ) : S.H s x h ≤ Fintype.card V :=
  Finset.card_le_univ _

lemma H_measurable (s : ℝ) (x : V) : Measurable (S.H s x) := by
  apply measurable_graph_statistic (fun h => contactGraph S.active (extendHeight S.pins S.boundary h) s) ?_
    (fun G => (FeasibleShift.component G x).card)
  intro y z
  by_cases hG : S.active.Adj y z
  · have hm : Measurable (fun h : FreeSites S.pins → ℝ =>
        1 - |extendHeight S.pins S.boundary h y - extendHeight S.pins S.boundary h z|) :=
      (measurable_const.sub (((continuous_apply y).comp (extendHeight_lipschitz S.pins S.boundary).continuous).measurable.sub
        (((continuous_apply z).comp (extendHeight_lipschitz S.pins S.boundary).continuous).measurable)).abs)
    simpa only [contactGraph, hG, true_and] using measurableSet_le hm measurable_const
  · simp only [contactGraph, hG, false_and, Set.ofPred_false, MeasurableSet.empty]

lemma good_measurable (s R : ℝ) : MeasurableSet (S.good s R) := by
  unfold good
  simp_rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro x
  exact measurableSet_le ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp (S.H_measurable s x)) measurable_const

lemma H_tail (s : ℝ) (hs : s ≤ sstar) (hρ : ρ ≤ 1)
    (hsparse : (Db : ENNReal)^2 * ρ ≤ 1/2) (x : V) (m : ℕ) (hm : 1 ≤ m) :
    S.law {h | B*m+1 ≤ S.H s x h} ≤ (1/2 : ENNReal)^m := by
  classical
  have hh := sparse_cover_component_tail S.law S.boxGraph Db B S.box_degree S.boxMap S.box_fiber
    (fun h => contactGraph S.active (extendHeight S.pins S.boundary h) s) S.badBoxes
    (fun h x y hadj => S.box_adjacent x y hadj.1.1)
    (fun h x y hadj => S.contact_bad h x y ⟨hadj.1, hadj.2.trans hs⟩)
    ρ hρ S.sparse x m hm
  exact hh.trans (pow_le_pow_left' hsparse m)

lemma H_integrable (s : ℝ) (x : V) (k : ℕ) :
    Integrable (fun h => (S.H s x h : ℝ)^k) S.law :=
  nat_pow_integrable_of_bound S.law (S.H s x) (S.H_measurable s x)
    (Fintype.card V) (S.H_le_card s x) k

lemma H_moment (s : ℝ) (hs : s ≤ sstar) (hB : 0 < B) (hρ : ρ ≤ 1)
    (hsparse : (Db : ENNReal)^2 * ρ ≤ 1/2) (x : V) (k : ℕ) :
    (∫ h, (S.H s x h : ℝ)^k ∂S.law) ≤ boxMoment B k :=
  nat_real_moment_of_geometric_tail S.law (S.H s x) (S.H_measurable s x) (S.H_pos s x)
    B hB (S.H_tail s hs hρ hsparse x) k

lemma mem_local_of_not_ground {x : V} (hx : x ∉ S.ground) : x ∈ localSites S.graph S.ground := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, Or.inl hx⟩

lemma H_outside_local (s : ℝ) (x : V) (hx : x ∉ localSites S.graph S.ground)
    (h : FreeSites S.pins → ℝ) : S.H s x h = 1 := by
  classical
  have hxg : x ∈ S.ground := by
    by_contra hh
    exact hx (S.mem_local_of_not_ground hh)
  have hno (y : V) : ¬ (contactGraph S.active (extendHeight S.pins S.boundary h) s).Adj x y := by
    intro hh
    have hy : y ∉ S.ground := fun hyy => hh.1.2 ⟨hxg, hyy⟩
    exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, Or.inr ⟨y, hy, hh.1.1⟩⟩)
  have he : FeasibleShift.component (contactGraph S.active (extendHeight S.pins S.boundary h) s) x = {x} := by
    ext y
    rw [mem_component, Finset.mem_singleton]
    constructor
    · rintro ⟨w⟩
      cases w with
      | nil => rfl
      | cons hadj w => exact (hno _ hadj).elim
    · rintro rfl
      exact SimpleGraph.Reachable.refl _
  change (FeasibleShift.component _ x).card = 1
  rw [he, Finset.card_singleton]

lemma bad_good_bound (s R : ℝ) (hs : s ≤ sstar) (hB : 0 < B) (hρ : ρ ≤ 1)
    (hsparse : (Db : ENNReal)^2 * ρ ≤ 1/2) (hR : 1 ≤ R) (k : ℕ) (hk : 0 < k) :
    S.law.real (S.good s R)ᶜ ≤ ((localSites S.graph S.ground).card : ℝ) * boxMoment B k / R^k := by
  classical
  let U := {x // x ∈ localSites S.graph S.ground}
  have he : (S.good s R)ᶜ = {h | ∃ x : U, R < (S.H s x h : ℝ)} := by
    ext h
    simp only [good, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le]
    constructor
    · rintro ⟨x, hx⟩
      have hxl : x ∈ localSites S.graph S.ground := by
        by_contra hh
        rw [S.H_outside_local s x hh, Nat.cast_one] at hx
        exact (not_lt_of_ge hR) hx
      exact ⟨⟨x, hxl⟩, hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, hx⟩
  rw [he]
  have hh := maximum_nat_moment_bound S.law (fun x : U => S.H s x)
    (fun x => S.H_measurable s x) (Fintype.card V) (fun x => S.H_le_card s x)
    k hk _ R (by linarith) (fun x => S.H_moment s hs hB hρ hsparse x k)
  simpa only [U, Fintype.card_coe] using hh

lemma active_or_ground {x y : V} (hxy : S.graph.Adj x y) :
    S.active.Adj x y ∨ (x ∈ S.ground ∧ y ∈ S.ground) := by
  by_cases hh : x ∈ S.ground ∧ y ∈ S.ground
  · exact Or.inr hh
  · exact Or.inl ⟨hxy, hh⟩

lemma shift_lipschitz (s₀ s₁ : ℝ) (hs : s₀ < s₁) (hM : 0 ≤ M) :
    LipschitzWith ⟨(s₁-s₀)⁻¹ * (4*M*Fintype.card (V × V)), by positivity⟩ (S.shift s₀ s₁) :=
  freeShift_lipschitz S.active S.ground S.pins S.boundary S.prescribed s₀ s₁ M hs hM S.prescribed_bound

lemma extend_map (s₀ s₁ : ℝ) (h : FreeSites S.pins → ℝ) :
    extendHeight S.pins S.boundary (S.map s₀ s₁ h) =
      extendHeight S.pins S.boundary h +
        averagedShift S.active S.ground S.prescribed (extendHeight S.pins S.boundary h) s₀ s₁ := by
  simpa only [one_smul, map, shift, active] using extendHeight_shift S.active S.ground S.pins S.pins_ground
    S.boundary S.prescribed s₀ s₁ 1 h

lemma map_feasible (s₀ s₁ s₂ R : ℝ) (hs : s₀ < s₁) (hss : s₁ ≤ s₂) (hL : 0 ≤ L)
    (hsmall : L / n * (2*R+1) ≤ s₀) (h : FreeSites S.pins → ℝ)
    (hP : h ∈ S.polytope) (hg : h ∈ S.good s₂ R) : S.map s₀ s₁ h ∈ S.polytope := by
  change (∀ x y, S.graph.Adj x y → |extendHeight S.pins S.boundary (S.map s₀ s₁ h) x -
    extendHeight S.pins S.boundary (S.map s₀ s₁ h) y| ≤ 1) ∧ _
  rw [S.extend_map]
  constructor
  · intro x y hxy
    rcases S.active_or_ground hxy with ha | ⟨hx, hy⟩
    · exact averagedShift_feasible S.active S.ground S.prescribed
        (extendHeight S.pins S.boundary h) s₀ s₁ s₂ (L/n) R hs hss (by positivity)
        S.prescribed_ground (fun x y hh => S.prescribed_gradient x y hh.1) hg hsmall
        (fun x y hh => hP.1 x y hh.1) x y ha
    · simpa only [Pi.add_apply, averagedShift_ground S.active S.ground S.prescribed
        (extendHeight S.pins S.boundary h) s₀ s₁ hx,
        averagedShift_ground S.active S.ground S.prescribed
        (extendHeight S.pins S.boundary h) s₀ s₁ hy, add_zero] using hP.1 x y hxy
  · intro x hx
    simpa only [Pi.add_apply, averagedShift_ground S.active S.ground S.prescribed
      (extendHeight S.pins S.boundary h) s₀ s₁ (S.walls_ground hx), add_zero] using hP.2 x hx

lemma map_injective (s₀ s₁ s₂ R : ℝ) (hs : s₀ < s₁) (hss : s₁ ≤ s₂)
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hbuf : s₁ + 4*(L/n)*R ≤ s₂)
    (hsmall : (s₁-s₀)⁻¹ * (4*D*(L/n)) * R^2 < 1) :
    Set.InjOn (S.map s₀ s₁) (S.good s₂ R) := by
  intro h hh k hk hc
  have hh' := averagedShift_injective_good S.active S.ground S.prescribed s₀ s₁ s₂ (L/n) R D
    hs hss (by positivity) hR S.prescribed_ground
    (fun x y hxy => S.prescribed_gradient x y hxy.1) S.active_degree hbuf hsmall hh hk
  have he := congrArg (extendHeight S.pins S.boundary) hc
  rw [S.extend_map, S.extend_map] at he
  have hhk := hh' he
  ext x
  simpa only [extendHeight_free] using congrFun hhk (x : V)

lemma approximation_on_good (s₀ s₁ s₂ R : ℝ) (hs : s₀ < s₁) (hss : s₁ ≤ s₂)
    (hL : 0 ≤ L) (hR : 0 ≤ R) (h : FreeSites S.pins → ℝ) (hg : h ∈ S.good s₂ R) :
    ‖S.map s₀ s₁ h - h - (fun x : FreeSites S.pins => S.prescribed x)‖ ≤ (L/n)*R := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro x
  change |(h x + S.shift s₀ s₁ h x) - h x - S.prescribed x| ≤ _
  rw [add_sub_cancel_left]
  exact (averagedShift_approximation S.active S.ground S.prescribed
    (extendHeight S.pins S.boundary h) s₀ s₁ s₂ (L/n) hs hss (by positivity)
    S.prescribed_ground (fun x y hh => S.prescribed_gradient x y hh.1) x).trans
      (mul_le_mul_of_nonneg_left (hg x) (by positivity))

open TangentialJacobian

lemma derivative_on_good (s₀ s₁ s₂ R : ℝ) (hs : s₀ < s₁) (hss : s₁ < s₂)
    (hL : 0 ≤ L) (hR : 0 ≤ R) (h : FreeSites S.pins → ℝ) (hg : h ∈ S.good s₂ R) :
    ‖fderiv ℝ (S.shift s₀ s₁) h‖ ≤ (s₁-s₀)⁻¹ * (4*D*(L/n)) * R^2 := by
  have hd : 0 < s₁-s₀ := sub_pos.mpr hs
  by_cases hu : DifferentiableAt ℝ (S.shift s₀ s₁) h
  · exact freeShift_derivative_opNorm S.active S.ground S.pins S.boundary S.prescribed h
      s₀ s₁ s₂ (L/n) R D hs hss (by positivity) hR S.prescribed_ground
      (fun x y hh => S.prescribed_gradient x y hh.1) S.active_degree hg _ hu.hasFDerivAt
  · rw [fderiv_zero_of_not_differentiableAt hu, norm_zero]; positivity

lemma derivative_cost_bound (s₀ s₁ s₂ : ℝ) (hs : s₀ < s₁) (hss : s₁ < s₂)
    (hL : 0 ≤ L) (h : FreeSites S.pins → ℝ) :
    jacobianCost (fderiv ℝ (S.shift s₀ s₁) h) ≤
      ((s₁-s₀)⁻¹ * (4*D*(L/n)))^2 * ∑ x ∈ localSites S.graph S.ground, (S.H s₂ x h : ℝ)^3 := by
  classical
  have hd : 0 < s₁-s₀ := sub_pos.mpr hs
  by_cases hu : DifferentiableAt ℝ (S.shift s₀ s₁) h
  · apply (freeShift_derivative_cost S.active S.ground S.pins S.boundary S.prescribed h
      s₀ s₁ s₂ (L/n) D hs hss (by positivity) S.prescribed_ground
      (fun x y hh => S.prescribed_gradient x y hh.1) S.active_degree _ hu.hasFDerivAt).trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    calc
      _ ≤ ∑ x : FreeSites S.pins, if (x:V) ∈ localSites S.graph S.ground then (S.H s₂ x h : ℝ)^3 else 0 := by
        apply Finset.sum_le_sum; intro x _
        by_cases hx : (x:V) ∈ S.ground
        · simp only [ite_eq_left hx]; split_ifs <;> positivity
        · simp only [ite_eq_right hx, ite_eq_left (S.mem_local_of_not_ground hx)]
          exact le_rfl
      _ ≤ ∑ x : V, if x ∈ localSites S.graph S.ground then (S.H s₂ x h : ℝ)^3 else 0 := by
        rw [← Finset.sum_subtype (Finset.univ.filter fun x : V => x ∉ S.pins) (by simp)
          (fun x => if x ∈ localSites S.graph S.ground then (S.H s₂ x h : ℝ)^3 else 0)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; split_ifs <;> positivity)
      _ = ∑ x ∈ localSites S.graph S.ground, (S.H s₂ x h : ℝ)^3 := by
        rw [← Finset.sum_filter]
        congr 1
        ext x; simp

  · rw [fderiv_zero_of_not_differentiableAt hu]
    simp only [jacobianCost, asMatrix_apply, zero_apply,
      Finset.sum_const_zero, norm_zero, mul_zero]
    positivity

lemma derivative_integrable (s₀ s₁ : ℝ) (hs : s₀ < s₁) (hM : 0 ≤ M)
    (F : ((FreeSites S.pins → ℝ) →L[ℝ] (FreeSites S.pins → ℝ)) → ℝ) (hF : Continuous F) :
    Integrable (fun h => F (fderiv ℝ (S.shift s₀ s₁) h)) S.law :=
  continuous_integrable_of_bounded S.law _ (measurable_fderiv ℝ _) _
    (fun _h => norm_fderiv_le_of_lipschitz ℝ (S.shift_lipschitz s₀ s₁ hs hM)) F hF

lemma divergence_square_identity (s₀ s₁ : ℝ) (hs : s₀ < s₁) (hs₀ : 0 < s₀) (hM : 0 ≤ M) :
    (∫ h, (asMatrix (fderiv ℝ (S.shift s₀ s₁) h)).trace^2 ∂S.law) =
      ∫ h, (asMatrix (fderiv ℝ (S.shift s₀ s₁) h * fderiv ℝ (S.shift s₀ s₁) h)).trace ∂S.law := by
  have hid := (freeShift_divergence_identities S.graph S.active S.ground S.pins S.walls
    S.pins_ground S.walls_ground (fun _ _ hh => S.active_or_ground hh)
    S.boundary S.prescribed S.intervals s₀ s₁ M hs hs₀ hM S.prescribed_bound
    S.polytope_measurable S.polytope_finite).2
  change ∫ h, _ ∂((volume S.polytope)⁻¹ • volume.restrict S.polytope) =
    ∫ h, _ ∂((volume S.polytope)⁻¹ • volume.restrict S.polytope)
  rw [MeasureTheory.integral_smul_measure, MeasureTheory.integral_smul_measure]
  exact congrArg (fun r : ℝ => (volume S.polytope)⁻¹.toReal • r) hid

lemma trace_square_le_cost_integral (s₀ s₁ : ℝ) (hs : s₀ < s₁)
    (hs₀ : 0 < s₀) (hM : 0 ≤ M) :
    (∫ h, (asMatrix (fderiv ℝ (S.shift s₀ s₁) h)).trace^2 ∂S.law) ≤
      ∫ h, jacobianCost (fderiv ℝ (S.shift s₀ s₁) h) ∂S.law := by
  rw [S.divergence_square_identity s₀ s₁ hs hs₀ hM]
  apply integral_mono (S.derivative_integrable s₀ s₁ hs hM _
    (continuous_trace.comp (continuous_id.mul continuous_id)))
      (S.derivative_integrable s₀ s₁ hs hM _ continuous_jacobianCost)
  intro h
  let A := fderiv ℝ (S.shift s₀ s₁) h
  have hb := trace_sandwich_bound A 1
  rw [mul_one] at hb
  calc
    _ ≤ |(asMatrix (A*A)).trace| := le_abs_self _
    _ ≤ ‖(1 : (FreeSites S.pins → ℝ) →L[ℝ] (FreeSites S.pins → ℝ))‖ * jacobianCost A := hb
    _ ≤ 1 * jacobianCost A := mul_le_mul_of_nonneg_right ContinuousLinearMap.norm_id_le (jacobianCost_nonneg A)
    _ = _ := one_mul _

lemma cost_integral_bound (s₀ s₁ s₂ : ℝ) (hs : s₀ < s₁) (hss : s₁ < s₂) (hstar : s₂ ≤ sstar)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hB : 0 < B) (hρ : ρ ≤ 1)
    (hsparse : (Db : ENNReal)^2 * ρ ≤ 1/2) :
    (∫ h, jacobianCost (fderiv ℝ (S.shift s₀ s₁) h) ∂S.law) ≤
      ((s₁-s₀)⁻¹ * (4*D*(L/n)))^2 * ((localSites S.graph S.ground).card : ℝ) * boxMoment B 3 := by
  have hi : Integrable (fun h => ∑ x ∈ localSites S.graph S.ground, (S.H s₂ x h : ℝ)^3) S.law :=
    integrable_finsetSum _ (fun x _ => S.H_integrable s₂ x 3)
  calc
    _ ≤ ∫ h, ((s₁-s₀)⁻¹ * (4*D*(L/n)))^2 * ∑ x ∈ localSites S.graph S.ground, (S.H s₂ x h : ℝ)^3 ∂S.law := by
      exact integral_mono (S.derivative_integrable s₀ s₁ hs hM _ continuous_jacobianCost)
        (hi.const_mul _) (S.derivative_cost_bound s₀ s₁ s₂ hs hss hL)
    _ = ((s₁-s₀)⁻¹ * (4*D*(L/n)))^2 * ∑ x ∈ localSites S.graph S.ground, ∫ h, (S.H s₂ x h : ℝ)^3 ∂S.law := by
      rw [MeasureTheory.integral_const_mul, integral_finsetSum _ (fun x _ => S.H_integrable s₂ x 3)]
    _ ≤ ((s₁-s₀)⁻¹ * (4*D*(L/n)))^2 * ∑ x ∈ localSites S.graph S.ground, boxMoment B 3 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact Finset.sum_le_sum (fun x _ => S.H_moment s₂ hstar hB hρ hsparse x 3)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

lemma uniform_moment_bound (s₀ s₁ s₂ : ℝ) (hs₀ : 0 < s₀) (hs : s₀ < s₁)
    (hss : s₁ < s₂) (hstar : s₂ ≤ sstar) (hn : 0 < n)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hB : 0 < B) (hρ : ρ ≤ 1)
    (hsparse : (Db : ENNReal)^2 * ρ ≤ 1/2) :
    (∫ h, (asMatrix (fderiv ℝ (S.shift s₀ s₁) h)).trace^2 +
      jacobianCost (fderiv ℝ (S.shift s₀ s₁) h) ∂S.law) ≤
      2 * ((s₁-s₀)⁻¹ * (4*D*L))^2 * N * boxMoment B 3 := by
  rw [integral_add (S.derivative_integrable s₀ s₁ hs hM (fun A => (asMatrix A).trace^2) (continuous_trace.pow 2))
    (S.derivative_integrable s₀ s₁ hs hM _ continuous_jacobianCost)]
  have hc := S.cost_integral_bound s₀ s₁ s₂ hs hss hstar hL hM hB hρ hsparse
  have ht := S.trace_square_le_cost_integral s₀ s₁ hs hs₀ hM
  have hb : 0 ≤ boxMoment B 3 := boxMoment_nonneg B 3
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    _ ≤ 2 * (((s₁-s₀)⁻¹ * (4*D*(L/n)))^2 * ((localSites S.graph S.ground).card : ℝ) * boxMoment B 3) := by linarith
    _ ≤ 2 * (((s₁-s₀)⁻¹ * (4*D*(L/n)))^2 * (N*(n:ℝ)^2) * boxMoment B 3) := by
      gcongr
      exact S.vertex_count
    _ = _ := by field_simp

end FeasibleShift.ShiftData

open Filter

namespace FeasibleShift

open Filter

theorem feasible_shifts (D Db B : ℕ) (ρ : ENNReal) (s₀ s₁ s₂ sstar L M N p : ℝ)
    (hB : 0 < B) (hρ : ρ ≤ 1) (hsparse : (Db : ENNReal)^2 * ρ ≤ 1/2)
    (hs₀ : 0 < s₀) (hs : s₀ < s₁) (hss : s₁ < s₂) (hstar : s₂ < sstar)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hN : 0 ≤ N) (hp : 0 < p) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      Tendsto (fun n : ℕ => (L / n) * (n : ℝ)^(1/8 : ℝ)) atTop (nhds 0) ∧
      ∀ (n : ℕ), n₀ ≤ n → ∀ (V : Type u) [Fintype V] [DecidableEq V]
        (W : Type v) [Fintype W] [DecidableEq W]
        (S : ShiftData (V := V) W n D Db B ρ sstar L M N)
        (E : Set (FreeSites S.pins → ℝ)), MeasurableSet E → p ≤ S.law.real E →
        ∃ E' : Set (FreeSites S.pins → ℝ), MeasurableSet E' ∧ E' ⊆ E ∧
          p/2 ≤ S.law.real E' ∧ Set.InjOn (S.map s₀ s₁) E' ∧
          (S.map s₀ s₁) '' E' ⊆ S.polytope ∧ MeasurableSet ((S.map s₀ s₁) '' E') ∧
          (∀ h ∈ E', ‖S.map s₀ s₁ h - h - (fun x : FreeSites S.pins => S.prescribed x)‖ ≤
            (L / n) * (n : ℝ)^(1/8 : ℝ)) ∧ c ≤ S.law.real ((S.map s₀ s₁) '' E') := by
  classical
  let C : ℝ := 2 * ((s₁-s₀)⁻¹ * (4*D*L))^2 * N * SparseClusters.boxMoment B 3
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hN)
      (SparseClusters.boxMoment_nonneg B 3)
  let K : ℝ := 1+4*C/p
  have hK : 1 ≤ K := by
    have hh : 0 ≤ 4*C/p := by positivity
    dsimp [K]; linarith
  have hKpos : 0 < K := by linarith
  have hCK : C/K ≤ p/4 := by
    apply (div_le_iff₀ hKpos).mpr
    have he : p/4*(4*C/p) = C := by field_simp
    have hm := mul_le_mul_of_nonneg_left (show 4*C/p ≤ K by dsimp [K]; linarith)
      (show 0 ≤ p/4 by positivity)
    linarith
  obtain ⟨n₀, hn₀⟩ := (small_parameter_eventually D s₀ s₁ s₂ L
    (N*SparseClusters.boxMoment B 32) p hs₀ hs hss hp).exists_forall_of_atTop
  refine ⟨Real.exp (-2*K)*p/2, by positivity, n₀,
    scaled_radius_tendsto L (1/8) (by norm_num), ?_⟩
  intro n hn V iV dV W iW dW S E hE hEp
  obtain ⟨hnpos, hfeas, hbuf, hnorm, htail⟩ := hn₀ n hn
  let R : ℝ := (n:ℝ)^(1/8:ℝ)
  have hR : 1 ≤ R := Real.one_le_rpow (by exact_mod_cast hnpos) (by norm_num)
  have hRpos : 0 < R := by linarith
  have hj := S.map_injective s₀ s₁ s₂ R hs hss.le hL (by linarith) hbuf
    (hnorm.trans_lt (by norm_num))
  have hm := S.uniform_moment_bound s₀ s₁ s₂ hs₀ hs hss hstar.le hnpos hL hM hB hρ hsparse
  have hb : S.law.real (S.good s₂ R)ᶜ ≤ p/4 := by
    calc
      _ ≤ ((localSites S.graph S.ground).card : ℝ) * SparseClusters.boxMoment B 32 / R^32 :=
        S.bad_good_bound s₂ R hstar.le hB hρ hsparse hR 32 (by norm_num)
      _ ≤ (N*(n:ℝ)^2)*SparseClusters.boxMoment B 32 / R^32 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right S.vertex_count (SparseClusters.boxMoment_nonneg B 32)
      _ = (N*SparseClusters.boxMoment B 32)*(n:ℝ)^2 / R^32 := by ring
      _ ≤ p/4 := htail
  obtain ⟨E', hEm, hsub, hmass, hinj, himage, himagem, himagep⟩ :=
    TangentialJacobian.event_volume_of_moments S.polytope (S.good s₂ R)
      S.polytope_measurable (S.good_measurable s₂ R) S.polytope_positive S.polytope_finite
      (S.shift s₀ s₁) _ (S.shift_lipschitz s₀ s₁ hs hM) hj
      (fun h hh => S.map_feasible s₀ s₁ s₂ R hs hss.le hL hfeas h hh.1 hh.2)
      (fun h hh => (S.derivative_on_good s₀ s₁ s₂ R hs hss hL hRpos.le h hh).trans hnorm)
      C p K hp hK hm hCK hb E hE hEp
  refine ⟨E', hEm, fun h hh => (hsub hh).1.1, hmass, hinj, himage, himagem, ?_, himagep⟩
  intro h hh
  exact S.approximation_on_good s₀ s₁ s₂ R hs hss.le hL hRpos.le h (hsub hh).2

end FeasibleShift

end OAI
