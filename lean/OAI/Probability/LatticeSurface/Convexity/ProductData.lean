import Mathlib
import OAI.Probability.LatticeSurface.Convexity.ProductGraph
import OAI.Probability.LatticeSurface.Convexity.ProductVolume
import OAI.Probability.LatticeSurface.Dynamics.ShiftData

namespace OAI

open Set MeasureTheory intervalIntegral

universe u v

namespace FeasibleShift.DisjointUnion

open Set MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {V : ι → Type u} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]

variable {W : ι → Type v} [∀ i, Fintype (W i)] [∀ i, DecidableEq (W i)]

variable {n D Db B : ℕ} {ρ : ENNReal} {sstar L M N : ℝ}

lemma heightEquiv_volume (pins : ∀ i, Finset (V i)) :
    MeasurePreserving (heightEquiv pins) volume volume :=
  (ProductVolume.curry_volume).comp
    (volume_measurePreserving_piCongrLeft (fun _ => ℝ) (freeEquiv pins))

lemma equiv_measure_preimage {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) {μ : Measure X} {ν : Measure Y} (he : MeasurePreserving e μ ν)
    (E : Set Y) : μ (e ⁻¹' E) = ν E := by
  rw [← MeasurableEquiv.map_apply, he.map_eq]

variable (S : ∀ i, ShiftData (V := V i) (W i) n D Db B ρ sstar L M N)

noncomputable def combinedPolytope : Set (FreeSites (sites (fun i => (S i).pins)) → ℝ) :=
  heightPolytope (graph (fun i => (S i).graph)) (sites (fun i => (S i).pins))
    (sites (fun i => (S i).walls)) (fun x => (S x.1).boundary x.2)
    (fun x => (S x.1).intervals x.2)

lemma combinedPolytope_eq : combinedPolytope S = heightEquiv (fun i => (S i).pins) ⁻¹'
    Set.pi Set.univ (fun i => (S i).polytope) :=
  polytope_same (fun i => (S i).graph) (fun i => (S i).pins) (fun i => (S i).walls)
    (fun i => (S i).boundary) (fun i => (S i).intervals)

lemma combinedPolytope_measurable : MeasurableSet (combinedPolytope S) := by
  rw [combinedPolytope_eq]
  exact (MeasurableSet.univ_pi (fun i => (S i).polytope_measurable)).preimage
    (heightEquiv _).measurable

lemma combinedPolytope_volume : volume (combinedPolytope S) = ∏ i, volume (S i).polytope := by
  rw [combinedPolytope_eq, equiv_measure_preimage _ (heightEquiv_volume _), volume_pi_pi]

lemma combinedPolytope_positive : volume (combinedPolytope S) ≠ 0 := by
  rw [combinedPolytope_volume]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => (S i).polytope_positive

lemma combinedPolytope_finite : volume (combinedPolytope S) ≠ ⊤ := by
  rw [combinedPolytope_volume]
  exact ENNReal.prod_ne_top fun i _ => (S i).polytope_finite

lemma combined_law : MeasurePreserving (heightEquiv (fun i => (S i).pins))
    (ProbabilityTheory.cond volume (combinedPolytope S)) (Measure.pi (fun i => (S i).law)) := by
  have h := ProductVolume.preserving_cond (heightEquiv (fun i => (S i).pins))
    (heightEquiv_volume _) (Set.pi Set.univ (fun i => (S i).polytope))
    (MeasurableSet.univ_pi (fun i => (S i).polytope_measurable))
  rw [← combinedPolytope_eq] at h
  convert! h using 1
  all_goals first | rfl | exact (ProductVolume.cond_pi (fun _ => volume) (fun i => (S i).polytope)
    (fun i => (S i).polytope_measurable) (fun i => (S i).polytope_positive)
    (fun i => (S i).polytope_finite)).symm

omit [∀ i, DecidableEq (V i)] [∀ i, Fintype (W i)] in
lemma box_fiber_same (b : ∀ i, V i → W i) (i : ι) (w : W i) :
    (Finset.univ.filter fun x : Sigma V => (⟨x.1,b x.1 x.2⟩ : Sigma W) = ⟨i,w⟩) =
      (Finset.univ.filter fun x => b i x = w).map (Function.Embedding.sigmaMk i) := by
  classical
  ext ⟨j,x⟩
  by_cases h : j = i
  · subst j
    simp
  · have hn : ¬i = j := Ne.symm h
    simp [h, hn]

noncomputable def fiber (A : Finset (Sigma W)) (i : ι) : Finset (W i) :=
  Finset.univ.filter fun w => (⟨i,w⟩ : Sigma W) ∈ A

omit [Fintype ι] in
@[simp] lemma mem_fiber (A : Finset (Sigma W)) (i : ι) (w : W i) :
    w ∈ fiber A i ↔ (⟨i,w⟩ : Sigma W) ∈ A := by simp [fiber]

lemma sites_fiber (A : Finset (Sigma W)) : sites (fiber A) = A := by
  classical
  ext ⟨i,w⟩
  simp

lemma fiber_card (A : Finset (Sigma W)) : ∑ i, (fiber A i).card = A.card := by
  rw [← sites_card, sites_fiber]

noncomputable def combinedBad (h : FreeSites (sites (fun i => (S i).pins)) → ℝ) : Set (Sigma W) :=
  {w | w.2 ∈ (S w.1).badBoxes (heightEquiv (fun i => (S i).pins) h w.1)}

lemma combined_sparse (A : Finset (Sigma W)) :
    (ProbabilityTheory.cond volume (combinedPolytope S))
      {h | ∀ w ∈ A, w ∈ combinedBad S h} ≤ ρ^A.card := by
  let : ∀ i, IsProbabilityMeasure (S i).law := fun i =>
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite (S i).polytope_positive (S i).polytope_finite
  have he : {h | ∀ w ∈ A, w ∈ combinedBad S h} =
      heightEquiv (fun i => (S i).pins) ⁻¹' Set.pi Set.univ
        (fun i => {h | ∀ w ∈ fiber A i, w ∈ (S i).badBoxes h}) := by
    ext h
    simp only [Set.mem_ofPred_eq, combinedBad, Set.mem_preimage, Set.mem_pi,
      Set.mem_univ, forall_const, mem_fiber, Sigma.forall]
  rw [he, equiv_measure_preimage _ (combined_law S), Measure.pi_pi]
  calc
    _ ≤ ∏ i, ρ ^ (fiber A i).card := Finset.prod_le_prod fun i _ => (S i).sparse _
    _ = ρ^A.card := by rw [Finset.prod_pow_eq_pow_sum, fiber_card]

noncomputable def combine : ShiftData (V := Sigma V) (Sigma W) n D Db B ρ sstar L M
    (N * Fintype.card ι) where
  graph := graph (fun i => (S i).graph)
  ground := sites (fun i => (S i).ground)
  pins := sites (fun i => (S i).pins)
  walls := sites (fun i => (S i).walls)
  pins_ground := by rintro ⟨i,x⟩ hx; simpa using (S i).pins_ground (by simpa using hx)
  walls_ground := by rintro ⟨i,x⟩ hx; simpa using (S i).walls_ground (by simpa using hx)
  boundary x := (S x.1).boundary x.2
  intervals x := (S x.1).intervals x.2
  prescribed x := (S x.1).prescribed x.2
  prescribed_ground := by rintro ⟨i,x⟩ hx; exact (S i).prescribed_ground x (by simpa using hx)
  prescribed_bound x := (S x.1).prescribed_bound x.2
  prescribed_gradient := by rintro ⟨i,x⟩ ⟨j,y⟩ ⟨hij,hxy⟩; cases hij; exact (S i).prescribed_gradient x y hxy
  vertex_count := by
    rw [localSites_same, sites_card, Nat.cast_sum]
    calc
      _ ≤ ∑ i : ι, N * (n:ℝ)^2 := Finset.sum_le_sum fun i _ => (S i).vertex_count
      _ = (N * Fintype.card ι) * (n:ℝ)^2 := by simp; ring
  degree := by
    rintro ⟨i,x⟩
    rw [neighbors_same, Finset.card_map]
    exact (S i).degree x
  polytope_measurable := combinedPolytope_measurable S
  polytope_positive := combinedPolytope_positive S
  polytope_finite := combinedPolytope_finite S
  boxGraph := graph (fun i => (S i).boxGraph)
  box_degree := by
    rintro ⟨i,w⟩
    rw [neighbors_same, Finset.card_map]
    exact (S i).box_degree w
  boxMap x := ⟨x.1, (S x.1).boxMap x.2⟩
  box_fiber := by
    rintro ⟨i,w⟩
    rw [box_fiber_same (fun i => (S i).boxMap) i w, Finset.card_map]
    exact (S i).box_fiber w
  box_adjacent := by
    rintro ⟨i,x⟩ ⟨j,y⟩ ⟨hij,hxy⟩
    cases hij
    rcases (S i).box_adjacent x y hxy with he | ha
    · exact Or.inl (congrArg (Sigma.mk i) he)
    · exact Or.inr ⟨rfl,ha⟩
  badBoxes := combinedBad S
  contact_bad := by
    intro h
    rintro ⟨i,x⟩ ⟨j,y⟩ hc
    rw [shiftGraph_same, contactGraph_same] at hc
    obtain ⟨hij,hc⟩ := hc
    cases hij
    have hc' : (contactGraph (shiftGraph (S i).graph (S i).ground)
        (extendHeight (S i).pins (S i).boundary (heightEquiv (fun i => (S i).pins) h i)) sstar).Adj x y := by
      have ehe := funext (fun z => extendHeight_same (fun i => (S i).pins)
        (fun i => (S i).boundary) h i z)
      change (contactGraph (shiftGraph (S i).graph (S i).ground)
        (fun z => extendHeight (sites (fun j => (S j).pins))
          (fun z => (S z.1).boundary z.2) h ⟨i,z⟩) sstar).Adj x y at hc
      rw [ehe] at hc
      exact hc
    exact (S i).contact_bad _ x y hc'
  sparse := combined_sparse S

lemma combine_law : MeasurePreserving (heightEquiv (fun i => (S i).pins))
    (combine S).law (Measure.pi (fun i => (S i).law)) := combined_law S

lemma combine_map (s₀ s₁ : ℝ) (h : FreeSites (sites (fun i => (S i).pins)) → ℝ) :
    heightEquiv (fun i => (S i).pins) ((combine S).map s₀ s₁ h) =
      fun i => (S i).map s₀ s₁ (heightEquiv (fun i => (S i).pins) h i) := by
  ext i x
  have hh := freeShift_same (fun i => (S i).graph) (fun i => (S i).ground)
    (fun i => (S i).pins) (fun i => (S i).boundary) (fun i => (S i).prescribed) s₀ s₁ h i x
  exact congrArg (fun z => heightEquiv (fun i => (S i).pins) h i x + z) hh

end FeasibleShift.DisjointUnion

end OAI
