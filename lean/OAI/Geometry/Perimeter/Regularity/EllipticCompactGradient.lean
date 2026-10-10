import OAI.Geometry.Perimeter.Regularity.ContinuousWithinAtSurfaceGradientOfLocalLevel

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace BoundedContinuousFunction
namespace RPISingularHarnack
variable {n : ℕ}

 theorem geometric_equicontinuous {X V : Type*} [PseudoMetricSpace X] [PseudoMetricSpace V]
    {G : ℕ → X → V} {θ R C : ℝ} (hθ : 0<θ) (hR : 0<R)
    (hmod : ∀ i j x y, dist x y≤θ^j*R → dist (G i x) (G i y)≤C*(1/2)^j) :
    Equicontinuous G := by
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  have ht : Tendsto (fun j : ℕ ↦ C*(1/2:ℝ)^j) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)).const_mul C
  obtain ⟨j,hj⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨θ^j*R,by positivity,fun y hy i ↦ ?_⟩
  exact (hmod i j x y (by simpa only [dist_comm] using hy.le)).trans_lt hj

 theorem compact_field_subsequence {V : Type*} [NormedAddCommGroup V] [ProperSpace V]
    {K : Set (Euc n)} (hK : IsCompact K) {G : ℕ → Euc n → V}
    (hG : ∀ i, ContinuousOn (G i) K) {θ R C B : ℝ} (hθ : 0<θ) (hR : 0<R)
    (hb : ∀ i x, x∈K → ‖G i x‖≤B)
    (hmod : ∀ i j x, x∈K → ∀ y, y∈K → dist x y≤θ^j*R → ‖G i x-G i y‖≤C*(1/2)^j) :
    ∃ W : Euc n → V, ContinuousOn W K ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      TendstoUniformlyOn (fun i ↦ G (σ i)) W atTop K := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : ℕ → K →ᵇ V := fun i ↦ BoundedContinuousFunction.mkOfCompact
    ⟨fun x ↦ G i x,continuousOn_iff_continuous_domRestrict.mp (hG i)⟩
  have hFeq (i : ℕ) (x : K) : F i x=G i x := rfl
  have heq : Equicontinuous (fun i (x : K) ↦ F i x) := by
    apply geometric_equicontinuous (C := C) hθ hR
    intro i j x y hxy
    simpa only [hFeq,dist_eq_norm] using hmod i j x x.property y y.property hxy
  have hc : IsCompact (closure (range F)) := by
    apply BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0:V) B) (isCompact_closedBall _ _)
    · rintro g x ⟨i,rfl⟩
      exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right,hFeq] using hb i x x.property)
    · intro x
      rw [Metric.equicontinuousAt_iff]
      intro ε hε
      obtain ⟨δ,hδ,hh⟩ := Metric.equicontinuousAt_iff.mp (heq x) ε hε
      refine ⟨δ,hδ,fun y hy g ↦ ?_⟩
      obtain ⟨i,hi⟩ := g.property
      simpa only [←hi] using hh y hy i
  obtain ⟨W,hW,σ,hσ,hlim⟩ := hc.tendsto_subseq (fun i ↦ subset_closure (mem_range_self i))
  let W' : Euc n → V := fun x ↦ if hx : x∈K then W ⟨x,hx⟩ else 0
  have hW'eq (x : K) : W' x=W x := by simp [W',x.property]
  have hW' : ContinuousOn W' K := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact W.continuous.congr (fun x ↦ (hW'eq x).symm)
  refine ⟨W',hW',σ,hσ,?_⟩
  have hu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformly_iff.mp hu) ε hε] with i hi x hx
  have hh : dist (W ⟨x,hx⟩) (G (σ i) x)<ε := hi ⟨x,hx⟩
  simpa only [←hW'eq ⟨x,hx⟩] using hh

end RPISingularHarnack

end

end OAI
