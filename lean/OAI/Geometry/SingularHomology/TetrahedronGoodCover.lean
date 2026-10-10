import OAI.Geometry.SingularHomology.SimplexCoordinates
import OAI.Geometry.SingularHomology.TetrahedronSingular
import Mathlib.Analysis.Convex.Contractible

namespace OAI

noncomputable section

namespace Problem340.SimplicialSphere

def vertexStar (i : Fin 4) : Set TopologicalBoundary :=
  {p | 0 < p.val i}

def starIntersection (s : Finset (Fin 4)) : Set TopologicalBoundary :=
  {p | ∀ i ∈ s, p ∈ vertexStar i}

lemma isOpen_vertexStar (i : Fin 4) : IsOpen (vertexStar i) := by
  apply isOpen_lt continuous_const
  exact (Convexity.StdSimplex.continuous_weights_apply ℝ i).comp continuous_subtype_val

lemma vertexStar_cover : (⋃ i : Fin 4, vertexStar i) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  have hs := p.val.total_of_fintype
  have hp : ∃ i : Fin 4, 0 < p.val i := by
    by_contra hn
    push Not at hn
    have hz : ∀ i, p.val i = 0 := fun i => le_antisymm (hn i) (p.val.weights_nonneg i)
    simp only [hz, Finset.sum_const_zero] at hs
    norm_num at hs
  simpa only [Set.mem_iUnion, vertexStar, Set.mem_ofPred_eq] using hp

lemma starIntersection_univ : starIntersection Finset.univ = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨j, hj⟩ := p.property
  have h := hp j (Finset.mem_univ j)
  change 0 < p.val j at h
  exact (ne_of_gt h) hj

def starAmbient (s : Finset (Fin 4)) : Set (Fin 4 → ℝ) :=
  {p | p ∈ RealSimplex.coordinateSet (Fin 4) ∧ (∃ j, p j = 0) ∧ ∀ i ∈ s, 0 < p i}

def faceCenter (s : Finset (Fin 4)) : Fin 4 → ℝ :=
  fun i => if i ∈ s then (s.card : ℝ)⁻¹ else 0

lemma faceCenter_mem_simplex (s : Finset (Fin 4)) (hs : s.Nonempty) :
    faceCenter s ∈ RealSimplex.coordinateSet (Fin 4) := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_ne_zero.mpr hs)
  constructor
  · intro i
    simp only [faceCenter]
    split_ifs <;> positivity
  · simp [faceCenter, Finset.sum_ite_mem, hc]

lemma faceCenter_pos (s : Finset (Fin 4)) (hs : s.Nonempty) (i : Fin 4) (hi : i ∈ s) :
    0 < faceCenter s i := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast (Finset.card_pos.mpr hs)
  simpa [faceCenter, hi] using inv_pos.mpr hc

lemma faceCenter_mem_starAmbient (s : Finset (Fin 4)) (hs : s.Nonempty)
    (hproper : s ≠ Finset.univ) : faceCenter s ∈ starAmbient s := by
  refine ⟨faceCenter_mem_simplex s hs, ?_, faceCenter_pos s hs⟩
  have hj : ∃ j : Fin 4, j ∉ s := by
    by_contra h
    push Not at h
    exact hproper (Finset.eq_univ_iff_forall.mpr h)
  obtain ⟨j, hj⟩ := hj
  exact ⟨j, by simp [faceCenter, hj]⟩

lemma starAmbient_starConvex (s : Finset (Fin 4)) (hs : s.Nonempty) : StarConvex ℝ (faceCenter s) (starAmbient s) := by
  rintro p ⟨hp, ⟨j, hj⟩, hpos⟩ a b ha hb hab
  refine ⟨RealSimplex.convex_coordinateSet (faceCenter_mem_simplex s hs) hp ha hb hab,
    ?_, ?_⟩
  · have hjs : j ∉ s := by
      intro hjs
      have h := hpos j hjs
      rw [hj] at h
      exact (lt_irrefl 0) h
    refine ⟨j, ?_⟩
    simp [faceCenter, hjs, hj]
  · intro i hi
    change 0 < a * faceCenter s i + b * p i
    have hc := faceCenter_pos s hs i hi
    have hp' := hpos i hi
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb' : b = 1 := by linarith
      simpa [hb'] using hp'
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hc) (mul_nonneg hb hp'.le)

def starIntersectionHomeomorph (s : Finset (Fin 4)) :
    starIntersection s ≃ₜ starAmbient s where
  toFun p := ⟨RealSimplex.coordinates p.val.val, RealSimplex.mem_coordinateSet _,
    p.val.property, p.property⟩
  invFun p := ⟨⟨RealSimplex.coordinateHomeomorph.symm ⟨p.val, p.property.1⟩,
    by simpa only [RealSimplex.coordinateHomeomorph_symm_apply_at] using p.property.2.1⟩,
    by simpa only [starIntersection, vertexStar, Set.mem_ofPred_eq,
      RealSimplex.coordinateHomeomorph_symm_apply_at] using p.property.2.2⟩
  left_inv point := by
    apply Subtype.ext
    apply Subtype.ext
    apply RealSimplex.coordinates_injective
    exact RealSimplex.coordinateHomeomorph_symm_apply _
  right_inv point := Subtype.ext (RealSimplex.coordinateHomeomorph_symm_apply _)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (RealSimplex.coordinateHomeomorph.continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact RealSimplex.coordinateHomeomorph.symm.continuous.comp
      (continuous_subtype_val.subtype_mk _)

theorem contractible_starIntersection (s : Finset (Fin 4)) (hs : s.Nonempty)
    (hproper : s ≠ Finset.univ) : ContractibleSpace (starIntersection s) := by
  let : ContractibleSpace (starAmbient s) :=
    (starAmbient_starConvex s hs).contractibleSpace
      ⟨faceCenter s, faceCenter_mem_starAmbient s hs hproper⟩
  exact (starIntersectionHomeomorph s).contractibleSpace

lemma starIntersection_eq_biInter (s : Finset (Fin 4)) :
    starIntersection s = ⋂ i ∈ s, vertexStar i := by
  ext p
  simp [starIntersection]

lemma isOpen_starIntersection (s : Finset (Fin 4)) : IsOpen (starIntersection s) := by
  rw [starIntersection_eq_biInter]
  exact isOpen_biInter_finset (fun i _ => isOpen_vertexStar i)

lemma starIntersection_nonempty (s : Finset (Fin 4)) (hs : s.Nonempty)
    (hproper : s ≠ Finset.univ) : (starIntersection s).Nonempty := by
  exact ⟨((starIntersectionHomeomorph s).symm
    ⟨faceCenter s, faceCenter_mem_starAmbient s hs hproper⟩).val,
    ((starIntersectionHomeomorph s).symm
    ⟨faceCenter s, faceCenter_mem_starAmbient s hs hproper⟩).property⟩

theorem starIntersection_nonempty_iff (s : Finset (Fin 4)) :
    (starIntersection s).Nonempty ↔ s ≠ Finset.univ := by
  constructor
  · intro h heq
    rw [heq, starIntersection_univ] at h
    exact Set.not_nonempty_empty h
  · intro hs
    by_cases hne : s.Nonempty
    · exact starIntersection_nonempty s hne hs
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      obtain ⟨p, _⟩ := starIntersection_nonempty {0} (by simp) (by decide)
      exact ⟨p, by simp [he, starIntersection]⟩

lemma vertexStar_list_nonempty_iff {ι : Type*} [Fintype ι] (v : ι → Fin 4) :
    (⋂ i, vertexStar (v i)).Nonempty ↔ ¬ Function.Surjective v := by
  classical
  have heq : (⋂ i, vertexStar (v i)) =
      starIntersection (Finset.univ.image v) := by
    ext p
    simp [starIntersection]
  rw [heq, starIntersection_nonempty_iff]
  constructor
  · intro h hv
    apply h
    apply Finset.eq_univ_iff_forall.mpr
    intro j
    obtain ⟨i, rfl⟩ := hv j
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  · intro h he
    apply h
    intro j
    have hj : j ∈ Finset.univ.image v := by rw [he]; exact Finset.mem_univ j
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hj
    exact ⟨i, hi⟩

theorem contractible_starPreimage {X : Type*} [TopologicalSpace X]
    (e : X ≃ₜ TopologicalBoundary) (s : Finset (Fin 4)) (hs : s.Nonempty)
    (hproper : s ≠ Finset.univ) : ContractibleSpace (e ⁻¹' starIntersection s) := by
  let := contractible_starIntersection s hs hproper
  exact (e.sets rfl).contractibleSpace

lemma exists_coordinate_ge_quarter (p : TopologicalBoundary) :
    ∃ i : Fin 4, (1 / 4 : ℝ) ≤ p.val i := by
  by_contra h
  push Not at h
  have hs := p.val.total_of_fintype
  rw [Fin.sum_univ_four] at hs
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  linarith

theorem exists_ball_subset_vertexStar (p : TopologicalBoundary) :
    ∃ i : Fin 4, Metric.ball p (1 / 4 : ℝ) ⊆ vertexStar i := by
  obtain ⟨i, hi⟩ := exists_coordinate_ge_quarter p
  refine ⟨i, ?_⟩
  intro q hq
  have hdist : dist (p.val i) (q.val i) < (1 / 4 : ℝ) := by
    apply lt_of_le_of_lt (dist_le_pi_dist (RealSimplex.coordinates p.val)
      (RealSimplex.coordinates q.val) i)
    change dist p q < 1 / 4
    simpa only [Metric.mem_ball, dist_comm] using hq
  rw [Real.dist_eq] at hdist
  have hsub := (abs_lt.mp hdist).2
  change 0 < q.val i
  linarith

theorem subset_vertexStar_of_pairwise_dist_lt (A : Set TopologicalBoundary)
    (hA : A.Nonempty) (hsmall : ∀ p ∈ A, ∀ q ∈ A, dist p q < (1 / 4 : ℝ)) :
    ∃ i : Fin 4, A ⊆ vertexStar i := by
  obtain ⟨p, hp⟩ := hA
  obtain ⟨i, hi⟩ := exists_ball_subset_vertexStar p
  refine ⟨i, fun q hq => hi ?_⟩
  exact hsmall q hq p hp

end Problem340.SimplicialSphere

end

end OAI
