import Mathlib
import OAI.Analysis.Conductivity.Variational.CompactBridge

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped NNReal

lemma lipschitz_weakDirection {C : ℝ≥0} {f : R3 → ℝ}
    (hf : LipschitzWith C f) (v : R3) :
    WeakL2Direction f (fun x => lineDeriv ℝ f x v) v := by
  intro ψ hψ hc
  obtain ⟨D,hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hψ (by simp)
  have he := hf.integral_lineDeriv_mul_eq (μ := volume) hD hc v
  have hd (x : R3) : lineDeriv ℝ ψ x (-v)= -(fderiv ℝ ψ x v) := by
    rw [(hψ.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv,map_neg]
  simp_rw [hd,neg_mul,integral_neg,mul_comm (fderiv ℝ ψ _ v)] at he
  linarith

lemma WeakL2Direction.congr {f g f' g' : R3 → ℝ} {v : R3}
    (hw : WeakL2Direction f g v) (hf : f'=ᵐ[volume] f) (hg : g'=ᵐ[volume] g) :
    WeakL2Direction f' g' v := by
  intro ψ hψ hc
  calc
    _ = ∫ x, f x*fderiv ℝ ψ x v := integral_congr_ae (by
      filter_upwards [hf] with x hx; rw [hx])
    _ = -(∫ x, g x*ψ x) := hw ψ hψ hc
    _ = _ := congrArg Neg.neg (integral_congr_ae (by
      filter_upwards [hg] with x hx; rw [hx]))

lemma lineDeriv_zero_outside {f : R3 → ℝ} {R : ℝ}
    (hs : ∀ x, R<‖x‖ → f x=0) {x : R3} (hx : R<‖x‖) (v : R3) :
    lineDeriv ℝ f x v=0 := by
  have he : f=ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [isOpen_lt continuous_const continuous_norm |>.mem_nhds hx] with y hy
    exact hs y hy
  rw [he.lineDeriv_eq]
  rw [(differentiableAt_const (0:ℝ)).lineDeriv_eq_fderiv]
  simp

lemma bounded_support_compact {f : R3 → ℝ} {R : ℝ}
    (hs : ∀ x, R<‖x‖ → f x=0) : HasCompactSupport f := by
  apply (isCompact_closedBall (0:R3) R).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  simp only [Metric.mem_closedBall,dist_zero_right]
  exact le_of_not_gt (fun hn => hx (hs x hn))

lemma lipschitz_lineDeriv_memLp {C : ℝ≥0} {f : R3 → ℝ}
    (hf : LipschitzWith C f) {R : ℝ} (hs : ∀ x, R<‖x‖ → f x=0) (v : R3) :
    MemLp (fun x => lineDeriv ℝ f x v) 2 volume := by
  apply (hf.memLp_lineDeriv v).mono_exponent_of_measure_support_ne_top
    (s := Metric.closedBall 0 R) _ (measure_closedBall_lt_top.ne) le_top
  intro x hx
  apply lineDeriv_zero_outside hs _ v
  simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hx

theorem compact_lipschitz_H1 {C : ℝ≥0} {f : R3 → ℝ}
    (hf : LipschitzWith C f) {R : ℝ} (hR : R<3)
    (hs : ∀ x, R<‖x‖ → f x=0) :
    ∃ u : H1, u∈H10 ∧ (∀ᵐ x ∂ballMeasure,
      weakValue u x=f x ∧ ∀ i : Fin 3,
        weakGradient u x i=lineDeriv ℝ f x (EuclideanSpace.single i 1)) := by
  have hm : MemLp f 2 volume := hf.continuous.memLp_of_hasCompactSupport (bounded_support_compact hs)
  have hd (i : Fin 3) := lipschitz_lineDeriv_memLp hf hs (EuclideanSpace.single i 1)
  let F : Fin 4 → WholeL2 := Fin.cases (hm.toLp f)
    (fun i => (hd i).toLp (fun x => lineDeriv ℝ f x (EuclideanSpace.single i 1)))
  have hv : (F 0 : R3 → ℝ)=ᵐ[volume] f := hm.coeFn_toLp
  have hg (i : Fin 3) : (F i.succ : R3 → ℝ)=ᵐ[volume]
      (fun x => lineDeriv ℝ f x (EuclideanSpace.single i 1)) := (hd i).coeFn_toLp
  have hw (i : Fin 3) : WeakL2Direction (F 0) (F i.succ) (EuclideanSpace.single i 1) :=
    (lipschitz_weakDirection hf _).congr hv (hg i)
  obtain ⟨u,hu,he⟩ := compact_weak_H1 F hw hR (by
    filter_upwards [hv] with x hx
    intro hn
    exact hx.trans (hs x hn))
  refine ⟨u,hu,?_⟩
  have hv' := hv.filter_mono (ae_mono (Measure.restrict_le_self (s := ball)))
  have hg' := (ae_all_iff.mpr hg).filter_mono (ae_mono (Measure.restrict_le_self (s := ball)))
  filter_upwards [he,hv',hg'] with x hx hy hz
  exact ⟨hx.1.trans hy,fun i => (hx.2 i).trans (hz i)⟩

lemma segment_meets_frontier {s : Set R3} {x y : R3} (hx : x∈s) (hy : y∉s) :
    ∃ z∈segment ℝ x y,z∈frontier s := by
  have hc : segment ℝ x y⊆closure s∪closure sᶜ := by
    intro z _
    by_cases hz : z∈s
    · exact Or.inl (subset_closure hz)
    · exact Or.inr (subset_closure hz)
  obtain ⟨z,hz,hb⟩ := isPreconnected_closed_iff.mp (convex_segment x y).isPreconnected
    (closure s) (closure sᶜ) isClosed_closure isClosed_closure hc
    ⟨x,left_mem_segment ℝ x y,subset_closure hx⟩
    ⟨y,right_mem_segment ℝ x y,subset_closure hy⟩
  exact ⟨z,hz,by rwa [frontier_eq_closure_inter_closure]⟩

lemma lipschitz_piecewise_frontier (s : Set R3) [DecidablePred (·∈s)]
    {f g : R3 → ℝ} {K L : ℝ≥0}
    (hf : LipschitzOnWith K f (closure s))
    (hg : LipschitzOnWith L g (closure sᶜ))
    (he : EqOn f g (frontier s)) :
    LipschitzWith (max K L) (s.piecewise f g) := by
  have hcross {x y : R3} (hx : x∈s) (hy : y∉s) :
      dist (f x) (g y) ≤ (max K L:ℝ≥0)*dist x y := by
    obtain ⟨z,hz,hb⟩ := segment_meets_frontier hx hy
    have hb' := frontier_eq_closure_inter_closure (s := s) ▸ hb
    calc
      dist (f x) (g y) ≤ dist (f x) (f z)+dist (f z) (g y) := dist_triangle _ _ _
      _ = dist (f x) (f z)+dist (g z) (g y) := by rw [he hb]
      _ ≤ K*dist x z+L*dist z y := add_le_add
        (hf.dist_le_mul x (subset_closure hx) z hb'.1)
        (hg.dist_le_mul z hb'.2 y (subset_closure hy))
      _ ≤ (max K L:ℝ≥0)*dist x z+(max K L:ℝ≥0)*dist z y := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left K L) dist_nonneg
        · exact mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right K L) dist_nonneg
      _ = (max K L:ℝ≥0)*dist x y := by rw [←mul_add,dist_add_dist_of_mem_segment hz]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hx : x∈s <;> by_cases hy : y∈s
  · simp only [piecewise_eq_of_mem s f g hx,piecewise_eq_of_mem s f g hy]
    exact (hf.dist_le_mul x (subset_closure hx) y (subset_closure hy)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left K L) dist_nonneg)
  · simpa only [piecewise_eq_of_mem s f g hx,piecewise_eq_of_notMem s f g hy] using hcross hx hy
  · rw [dist_comm,dist_comm x y]
    simpa only [piecewise_eq_of_mem s f g hy,piecewise_eq_of_notMem s f g hx] using hcross hy hx
  · simp only [piecewise_eq_of_notMem s f g hx,piecewise_eq_of_notMem s f g hy]
    exact (hg.dist_le_mul x (subset_closure hx) y (subset_closure hy)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right K L) dist_nonneg)

lemma piecewise_lineDeriv_off_frontier (s : Set R3) [DecidablePred (·∈s)]
    (f g : R3 → ℝ) {x : R3} (hx : x∉frontier s) (v : R3) :
    lineDeriv ℝ (s.piecewise f g) x v=
      s.piecewise (fun x => lineDeriv ℝ f x v) (fun x => lineDeriv ℝ g x v) x := by
  by_cases hs : x∈s
  · have hi : x∈interior s := by
      by_contra hn
      exact hx ⟨subset_closure hs,hn⟩
    have he : s.piecewise f g=ᶠ[𝓝 x] f := by
      filter_upwards [mem_interior_iff_mem_nhds.mp hi] with y hy
      exact piecewise_eq_of_mem s f g hy
    rw [he.lineDeriv_eq,piecewise_eq_of_mem s _ _ hs]
  · have hi : x∈interior sᶜ := by
      by_contra hn
      have hb : x∈frontier sᶜ := ⟨subset_closure hs,hn⟩
      rw [frontier_compl] at hb
      exact hx hb
    have he : s.piecewise f g=ᶠ[𝓝 x] g := by
      filter_upwards [mem_interior_iff_mem_nhds.mp hi] with y hy
      exact piecewise_eq_of_notMem s f g hy
    rw [he.lineDeriv_eq,piecewise_eq_of_notMem s _ _ hs]

theorem compact_lipschitz_seam_H1 (s : Set R3) [DecidablePred (·∈s)]
    {f g : R3 → ℝ} {K L : ℝ≥0}
    (hf : LipschitzOnWith K f (closure s))
    (hg : LipschitzOnWith L g (closure sᶜ))
    (he : EqOn f g (frontier s)) (hn : volume (frontier s)=0)
    {R : ℝ} (hR : R<3) (hs : ∀ x,R<‖x‖ → s.piecewise f g x=0) :
    ∃ u : H1,u∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue u x=s.piecewise f g x ∧ ∀ i : Fin 3,
        weakGradient u x i=s.piecewise
          (fun x => lineDeriv ℝ f x (EuclideanSpace.single i 1))
          (fun x => lineDeriv ℝ g x (EuclideanSpace.single i 1)) x) := by
  obtain ⟨u,hu,hj⟩ := compact_lipschitz_H1 (lipschitz_piecewise_frontier s hf hg he) hR hs
  refine ⟨u,hu,?_⟩
  have hb : ∀ᵐ x∂volume,x∉frontier s := by
    rw [ae_iff]
    simpa using hn
  have hb' := hb.filter_mono (ae_mono (Measure.restrict_le_self (s := ball)))
  filter_upwards [hj,hb'] with x hx hxb
  exact ⟨hx.1,fun i => (hx.2 i).trans (piecewise_lineDeriv_off_frontier s f g hxb _)⟩

end ScalarConductivity

end

end OAI
