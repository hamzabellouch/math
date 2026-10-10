import OAI.Geometry.HeilbronnTriangle.IntegralPlaneLattice
import OAI.Geometry.HeilbronnTriangle.PlaneCount
import OAI.Geometry.HeilbronnTriangle.PlaneRadius
import OAI.Geometry.HeilbronnTriangle.LatticeBox
import OAI.Geometry.HeilbronnTriangle.ShortestIntegralVector

namespace OAI


noncomputable section

namespace Problem355.IntegerPlaneEstimates

open Module Matrix IntegralPlaneLattice

abbrev Vec := Fin 3 → ℤ

@[simp] lemma castVec_zero : castVec (0 : Vec) = 0 := by
  ext i
  simp [castVec]

def toLattice (y v : Vec) (hv : y ⬝ᵥ v = 0) : lattice y :=
  kernelMap y ⟨v, hv⟩

@[simp] lemma toLattice_coe (y v : Vec) (hv : y ⬝ᵥ v = 0) :
    ((toLattice y v hv : plane y) : Ambient) = castVec v := rfl

@[simp] lemma norm_toLattice (y v : Vec) (hv : y ⬝ᵥ v = 0) :
    ‖(toLattice y v hv : plane y)‖ = ‖LatticeBox.realVector v‖ := rfl

lemma toLattice_injective (y v w : Vec) (hv : y ⬝ᵥ v = 0) (hw : y ⬝ᵥ w = 0)
    (h : toLattice y v hv = toLattice y w hw) : v = w := by
  exact congrArg Subtype.val (kernelMap_injective y h)

def liftFinset (y : Vec) (S : Finset Vec) (hS : ∀ v ∈ S, y ⬝ᵥ v = 0) :
    Finset (lattice y) :=
  S.attach.map ⟨fun v : {v // v ∈ S} => toLattice y v (hS v v.property), by
    intro v w h
    apply Subtype.ext
    exact toLattice_injective y v w _ _ h⟩

@[simp] lemma card_liftFinset (y : Vec) (S : Finset Vec)
    (hS : ∀ v ∈ S, y ⬝ᵥ v = 0) :
    (liftFinset y S hS).card = S.card := by simp [liftFinset]

lemma norm_liftFinset_le (y : Vec) (S : Finset Vec)
    (hS : ∀ v ∈ S, y ⬝ᵥ v = 0) (R : ℝ)
    (hR : ∀ v ∈ S, ‖LatticeBox.realVector v‖ ≤ R) :
    ∀ a ∈ liftFinset y S hS, ‖(a : plane y)‖ ≤ R := by
  intro a ha
  obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp ha
  exact hR v v.property

lemma one_le_norm_of_int_ne_zero (v : Vec) (hv : v ≠ 0) :
    1 ≤ ‖LatticeBox.realVector v‖ := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have habs : (1 : ℤ) ≤ |v i| := Int.one_le_abs hi
  have hreal : (1 : ℝ) ≤ |(v i : ℝ)| := by exact_mod_cast habs
  exact hreal.trans (LatticeBox.abs_coord_le_norm v i)

lemma one_le_norm_of_lattice_ne_zero (y : Vec) (v : plane y)
    (hv : v ∈ lattice y) (hne : v ≠ 0) : 1 ≤ ‖v‖ := by
  obtain ⟨w, hw⟩ := kernelMap_surjective y ⟨v, hv⟩
  have hcast : castVec (w : Vec) = (v : Ambient) :=
    congrArg (fun a : lattice y => ((a : plane y) : Ambient)) hw
  have hwne : (w : Vec) ≠ 0 := by
    intro hzero
    apply hne
    apply Subtype.ext
    rw [← hcast, hzero]
    ext i
    simp [castVec]
  have hn := one_le_norm_of_int_ne_zero w hwne
  change 1 ≤ ‖(v : Ambient)‖
  rw [← hcast]
  exact hn

def successiveBasis (y z : Vec) (hz : y ⬝ᵥ z = 1) : Basis (Fin 2) ℝ (plane y) := by
  letI := isZLattice y z hz
  exact Classical.choose (PlaneCount.exists_successive_plane_basis (lattice y)
    (plane_finrank y z hz))

lemma successiveBasis_spec (y z : Vec) (hz : y ⬝ᵥ z = 1) :
    (∀ i, successiveBasis y z hz i ∈ lattice y) ∧
    (∀ v ∈ lattice y, v ≠ 0 → ‖successiveBasis y z hz 0‖ ≤ ‖v‖) ∧
    (∀ v ∈ lattice y, v ∉ Submodule.span ℝ {successiveBasis y z hz 0} →
      ‖successiveBasis y z hz 1‖ ≤ ‖v‖) := by
  let := isZLattice y z hz
  exact Classical.choose_spec (PlaneCount.exists_successive_plane_basis (lattice y)
    (plane_finrank y z hz))

def first (y z : Vec) (hz : y ⬝ᵥ z = 1) : ℝ := ‖successiveBasis y z hz 0‖
def second (y z : Vec) (hz : y ⬝ᵥ z = 1) : ℝ := ‖successiveBasis y z hz 1‖

lemma one_le_first (y z : Vec) (hz : y ⬝ᵥ z = 1) : 1 ≤ first y z hz :=
  one_le_norm_of_lattice_ne_zero y _ ((successiveBasis_spec y z hz).1 0)
    (by exact (successiveBasis y z hz).ne_zero 0)

lemma first_le_second (y z : Vec) (hz : y ⬝ᵥ z = 1) :
    first y z hz ≤ second y z hz :=
  (successiveBasis_spec y z hz).2.1 _ ((successiveBasis_spec y z hz).1 1)
    ((successiveBasis y z hz).ne_zero 1)

def fromLattice (y : Vec) (v : lattice y) : Vec :=
  ((kernelEquiv y).symm v : integerPlane y)

lemma fromLattice_dot (y : Vec) (v : lattice y) : y ⬝ᵥ fromLattice y v = 0 :=
  ((kernelEquiv y).symm v).property

lemma cast_fromLattice (y : Vec) (v : lattice y) :
    castVec (fromLattice y v) = ((v : plane y) : Ambient) := by
  exact congrArg (fun a : lattice y => ((a : plane y) : Ambient))
    ((kernelEquiv y).apply_symm_apply v)

lemma toLattice_ne_zero (y v : Vec) (hv : y ⬝ᵥ v = 0) (hne : v ≠ 0) :
    (toLattice y v hv : plane y) ≠ 0 := by
  intro h
  apply hne
  have he : toLattice y v hv = toLattice y 0 (by simp) := by
    apply Subtype.ext
    apply Subtype.ext
    simpa only [toLattice_coe, castVec_zero, Submodule.coe_zero] using congrArg Subtype.val h
  exact toLattice_injective y v 0 hv (by simp) he

lemma first_le_norm (y z : Vec) (hz : y ⬝ᵥ z = 1)
    (v : Vec) (hv : y ⬝ᵥ v = 0) (hne : v ≠ 0) :
    first y z hz ≤ ‖LatticeBox.realVector v‖ := by
  have h := (successiveBasis_spec y z hz).2.1
    (toLattice y v hv : plane y) (toLattice y v hv).property
    (toLattice_ne_zero y v hv hne)
  rw [norm_toLattice] at h
  exact h

theorem exists_shortest_integer (y z : Vec) (hz : y ⬝ᵥ z = 1) :
    ∃ v : Vec, v ≠ 0 ∧ y ⬝ᵥ v = 0 ∧
      ‖LatticeBox.realVector v‖ = first y z hz := by
  let a : lattice y := ⟨successiveBasis y z hz 0, (successiveBasis_spec y z hz).1 0⟩
  refine ⟨fromLattice y a, ?_, fromLattice_dot y a, ?_⟩
  · intro hzero
    have hcast := cast_fromLattice y a
    rw [hzero] at hcast
    have hb : successiveBasis y z hz 0 = 0 := by
      apply Subtype.ext
      simpa only [a, castVec_zero, Submodule.coe_zero] using hcast.symm
    exact (successiveBasis y z hz).ne_zero 0 hb
  · change ‖castVec (fromLattice y a)‖ = ‖successiveBasis y z hz 0‖
    rw [cast_fromLattice]
    rfl

theorem product_bounds (y z : Vec) (hz : y ⬝ᵥ z = 1) :
    ZLattice.covolume (lattice y) ≤ first y z hz * second y z hz ∧
    first y z hz * second y z hz ≤ 2 * ZLattice.covolume (lattice y) := by
  let := isZLattice y z hz
  obtain ⟨hb, hf, hs⟩ := successiveBasis_spec y z hz
  exact (PlaneCount.plane_covolume_bounds (lattice y) (successiveBasis y z hz)
    hb hf hs).imp_right And.left

theorem plane_counts (y z : Vec) (hz : y ⬝ᵥ z = 1)
    (S : Finset Vec) (hS : ∀ v ∈ S, y ⬝ᵥ v = 0)
    (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ v ∈ S, ‖LatticeBox.realVector v‖ ≤ R) :
    (second y z hz ≤ R →
      (S.card : ℝ) ≤ 9 * Real.pi * R ^ 2 / ZLattice.covolume (lattice y)) ∧
    (R < second y z hz → (S.card : ℝ) ≤ 1 + 2 * R / first y z hz) := by
  let := isZLattice y z hz
  obtain ⟨hb, hf, hs⟩ := successiveBasis_spec y z hz
  have h := PlaneCount.plane_lattice_count (lattice y) (successiveBasis y z hz)
    hb hf hs (liftFinset y S hS) R hR (norm_liftFinset_le y S hS R hbound)
  constructor
  · intro hlarge
    simpa only [card_liftFinset] using h.1 hlarge
  · intro hsmall
    simpa only [card_liftFinset, first] using (h.2 hsmall).2

theorem count_of_covolume_radius (y z : Vec) (hz : y ⬝ᵥ z = 1)
    (S : Finset Vec) (hS : ∀ v ∈ S, y ⬝ᵥ v = 0)
    (R : ℝ) (hR : 2 * ZLattice.covolume (lattice y) ≤ R)
    (hbound : ∀ v ∈ S, ‖LatticeBox.realVector v‖ ≤ R) :
    (S.card : ℝ) ≤ 9 * Real.pi * R ^ 2 / ZLattice.covolume (lattice y) := by
  let := isZLattice y z hz
  have h := PlaneRadius.card_le_of_covolume_radius (plane_finrank y z hz)
    (lattice y) (by norm_num : (0 : ℝ) < 1)
    (one_le_norm_of_lattice_ne_zero y) (by simpa using hR)
    (liftFinset y S hS) 0 (by
      intro a ha
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using
        norm_liftFinset_le y S hS R hbound a ha)
  simpa only [card_liftFinset] using h

theorem exists_primitive_shortest_integer (y z : Vec) (hz : y ⬝ᵥ z = 1) :
    ∃ v : Vec, v ≠ 0 ∧ y ⬝ᵥ v = 0 ∧
      ‖LatticeBox.realVector v‖ = first y z hz ∧ ∃ w : Vec, v ⬝ᵥ w = 1 := by
  obtain ⟨v, hv, hyv, hnorm⟩ := exists_shortest_integer y z hz
  have hker : Matrix.mulVec (fun _ : Unit => y) v = 0 := by
    funext i
    exact hyv
  obtain ⟨w, hw⟩ := IntegralMinima.shortest_kernel_has_bezout
    (fun _ : Unit => y) v hv hker (by
      intro u hu hku
      change ‖LatticeBox.realVector v‖ ≤ ‖LatticeBox.realVector u‖
      rw [hnorm]
      exact first_le_norm y z hz u (congrFun hku ()) hu)
  exact ⟨v, hv, hyv, hnorm, w, hw⟩

theorem second_le_of_independent (y z : Vec) (hz : y ⬝ᵥ z = 1)
    (w : Fin 2 → Vec) (hw : ∀ i, y ⬝ᵥ w i = 0)
    (hind : LinearIndependent ℝ (fun i => LatticeBox.realVector (w i)))
    (R : ℝ) (hR : ∀ i, ‖LatticeBox.realVector (w i)‖ ≤ R) :
    second y z hz ≤ R := by
  let f : Fin 2 → plane y := fun i => toLattice y (w i) (hw i)
  have hfind : LinearIndependent ℝ f := by
    apply LinearIndependent.of_comp (plane y).subtype
    exact hind
  have hex : ∃ i, f i ∉ Submodule.span ℝ {successiveBasis y z hz 0} := by
    by_contra! hall
    have hle : Submodule.span ℝ (Set.range f) ≤
        Submodule.span ℝ {successiveBasis y z hz 0} := by
      apply Submodule.span_le.mpr
      rintro u ⟨i, rfl⟩
      exact hall i
    have hd := Submodule.finrank_mono hle
    rw [finrank_span_eq_card hfind,
      finrank_span_singleton ((successiveBasis y z hz).ne_zero 0)] at hd
    norm_num at hd
  obtain ⟨i, hi⟩ := hex
  have hmin := (successiveBasis_spec y z hz).2.2 (f i)
    (toLattice y (w i) (hw i)).property hi
  exact hmin.trans (hR i)

theorem thin_count (y z : Vec) (hz : y ⬝ᵥ z = 1)
    (S : Finset Vec) (hS : ∀ v ∈ S, y ⬝ᵥ v = 0)
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ v ∈ S, ‖LatticeBox.realVector v‖ ≤ R)
    (hsmall : R < second y z hz) (hone : first y z hz ≤ R) :
    (S.card : ℝ) ≤ 3 * R / first y z hz := by
  have h := (plane_counts y z hz S hS R hR hbound).2 hsmall
  have hp : 0 < first y z hz := lt_of_lt_of_le zero_lt_one (one_le_first y z hz)
  have hr : 1 ≤ R / first y z hz := (le_div_iff₀ hp).mpr (by simpa using hone)
  calc
    (S.card : ℝ) ≤ 1 + 2 * R / first y z hz := h
    _ ≤ 3 * R / first y z hz := by
      simp only [mul_div_assoc]
      linarith

end Problem355.IntegerPlaneEstimates

end

end OAI
