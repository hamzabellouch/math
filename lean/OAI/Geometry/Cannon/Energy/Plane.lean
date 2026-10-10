import Mathlib

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval
open Set Metric Topology

namespace CannonCharts

abbrev Plane := ℝ × ℝ

abbrev SphereTwo := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

def box (r : ℝ) : Set Plane := closedBall 0 r

def openBox (r : ℝ) : Set Plane := ball 0 r

lemma box_coords (r : ℝ) (z : Plane) :
    z ∈ box r ↔ |z.1| ≤ r ∧ |z.2| ≤ r := by
  simp [box, mem_closedBall, Prod.norm_def, Real.norm_eq_abs]

lemma openBox_coords (r : ℝ) (z : Plane) :
    z ∈ openBox r ↔ |z.1| < r ∧ |z.2| < r := by
  simp [openBox, mem_ball, Prod.norm_def, Real.norm_eq_abs]

theorem sphere_planar_chart (p : SphereTwo) :
    ∃ e : Plane → SphereTwo, IsOpenEmbedding e ∧ p ∈ range e := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2+1) := ⟨by simp⟩
  let s := stereographic' 2 (-p)
  let h : Plane ≃ₜ EuclideanSpace ℝ (Fin 2) :=
    Homeomorph.finTwoArrow.symm.trans (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.symm
  let e : Plane → SphereTwo := s.symm ∘ h
  have hs : IsOpenEmbedding (s.symm : EuclideanSpace ℝ (Fin 2) → SphereTwo) :=
    s.symm.isOpenEmbedding (by simp [s])
  refine ⟨e,hs.comp h.isOpenEmbedding,?_⟩
  have hp : p ∈ s.source := by
    simp only [s, stereographic'_source, mem_compl_iff, mem_singleton_iff]
    exact ne_neg_of_mem_unit_sphere ℝ p
  refine ⟨h.symm (s p),?_⟩
  dsimp [e]
  rw [h.apply_symm_apply]
  exact s.left_inv hp

theorem planar_chart {X : Type*} [TopologicalSpace X] (φ : X ≃ₜ SphereTwo) (p : X) :
    ∃ e : Plane → X, IsOpenEmbedding e ∧ p ∈ range e := by
  obtain ⟨e,he,z,hz⟩ := sphere_planar_chart (φ p)
  refine ⟨φ.symm ∘ e,φ.symm.isOpenEmbedding.comp he,z,?_⟩
  simp only [Function.comp_apply,hz,φ.symm_apply_apply]

theorem small_planar_chart {X : Type*} [MetricSpace X] (φ : X ≃ₜ SphereTwo)
    (p : X) (d : ℝ) (hd : 0 < d) :
    ∃ e : Plane → X, IsOpenEmbedding e ∧ e 0 = p ∧
      e '' box 8 ⊆ ball p (d/3) ∧ diam (e '' box 8) < d := by
  obtain ⟨e,he,c,hc⟩ := planar_chart φ p
  obtain ⟨δ,hδ,hcont⟩ := Metric.continuousAt_iff.mp he.continuous.continuousAt
    (d/3) (by positivity)
  let r : ℝ := δ/16
  have hr : 0 < r := by dsimp [r]; positivity
  let h : Plane ≃ₜ Plane :=
    (Homeomorph.smul (α := Plane) (Units.mk0 r hr.ne')).trans (Homeomorph.addLeft c)
  have hh (z : Plane) : h z = c+r • z := rfl
  let f : Plane → X := e ∘ h
  have hf (z : Plane) (hz : z ∈ box 8) : f z ∈ ball p (d/3) := by
    have hz' : ‖z‖ ≤ 8 := by simpa [box] using hz
    have hdist : dist (h z) c < δ := by
      rw [hh, dist_self_add_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      calc
        r*‖z‖ ≤ r*8 := mul_le_mul_of_nonneg_left hz' hr.le
        _ < δ := by dsimp [r]; linarith
    simpa [f,hc] using hcont hdist
  refine ⟨f,he.comp h.isOpenEmbedding,?_,by rintro _ ⟨z,hz,rfl⟩; exact hf z hz,?_⟩
  · simp [f,hh,hc]
  · have hsub : f '' box 8 ⊆ closedBall p (d/3) := by
      rintro _ ⟨z,hz,rfl⟩
      exact ball_subset_closedBall (hf z hz)
    calc
      diam (f '' box 8) ≤ diam (closedBall p (d/3)) := diam_mono hsub isBounded_closedBall
      _ ≤ 2*(d/3) := diam_closedBall (by positivity)
      _ < d := by linarith

theorem finite_small_charts {X : Type*} [MetricSpace X] [CompactSpace X]
    (φ : X ≃ₜ SphereTwo) (d : ℝ) (hd : 0 < d) :
    ∃ (J : Finset X) (e : J → Plane → X),
      (∀ j, IsOpenEmbedding (e j)) ∧
      (∀ j, diam (e j '' box 8) < d) ∧
      ∀ x : X, ∃ j, x ∈ e j '' openBox 1 := by
  classical
  choose e he hp hball hdiam using fun p : X => small_planar_chart φ p d hd
  have hopen (p : X) : IsOpen (e p '' openBox 1) := (he p).isOpenMap _ isOpen_ball
  have hcover : (univ : Set X) ⊆ ⋃ p : X, e p '' openBox 1 := by
    intro x _
    exact mem_iUnion.mpr ⟨x,0,by simp [openBox],hp x⟩
  obtain ⟨T,hT⟩ := isCompact_univ.elim_finite_subcover _ hopen hcover
  refine ⟨T,fun j => e j.val,fun j => he j.val,fun j => hdiam j.val,?_⟩
  intro x
  obtain ⟨p,hp,hx⟩ := mem_iUnion₂.mp (hT (mem_univ x))
  exact ⟨⟨p,hp⟩,hx⟩

end CannonCharts

open Set Topology unitInterval

namespace CannonCharts

theorem first_exit {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsClosed K) (p : I → X) (hp : Continuous p)
    (hzero : p 0 ∈ interior K) (hone : p 1 ∉ K) :
    ∃ b : I, 0 < b ∧ p b ∈ frontier K ∧ ∀ t ≤ b, p t ∈ K := by
  let S : Set I := {t | p t ∉ interior K}
  have hS : IsCompact S := (isOpen_interior.preimage hp).isClosed_compl.isCompact
  have hSn : S.Nonempty := ⟨1,fun h => hone (interior_subset h)⟩
  obtain ⟨b,hb,hmin⟩ := hS.exists_isMinOn hSn continuous_id.continuousOn
  have hbpos : 0 < b := lt_of_le_of_ne zero_le (by
    intro heq
    exact hb (heq ▸ hzero))
  have hlt (t : I) (ht : t < b) : p t ∈ K := by
    have ht' : p t ∈ interior K := by
      by_contra hn
      exact (not_lt_of_ge (hmin hn)) ht
    exact interior_subset ht'
  have hpreclosed : IsClosed (p ⁻¹' K) := hK.preimage hp
  have hsub : Iic b ⊆ p ⁻¹' K := by
    rw [← closure_Iio' (show (Iio b).Nonempty from ⟨0,hbpos⟩)]
    exact hpreclosed.closure_subset_iff.mpr hlt
  refine ⟨b,hbpos,?_,fun t ht => hsub ht⟩
  rw [frontier, hK.closure_eq]
  exact ⟨hsub (mem_Iic.mpr le_rfl),hb⟩

theorem continuous_lift {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {e : X → Y} (he : IsEmbedding e) (p : I → Y) (hp : Continuous p)
    (hmem : ∀ t, p t ∈ range e) :
    ∃ q : I → X, Continuous q ∧ ∀ t, e (q t) = p t := by
  choose q hq using hmem
  refine ⟨q,?_,hq⟩
  apply he.isInducing.continuous_iff.mpr
  convert hp using 1
  exact funext hq

end CannonCharts

end
end
end
end
end
end
end
end
end

end OAI
