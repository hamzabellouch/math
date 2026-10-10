import OAI.Analysis.PlanarEndpoint.Fourier

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Set
open scoped Topology BigOperators
namespace PlanarEndpoint
attribute [local instance] Classical.propDecidable

abbrev GridBox (M : ℕ) := Fin 2 → Set.Icc (-(M : ℤ)) (M : ℤ)

def gridLabel (x₀ : Plane) (r : ℝ) (x : Plane) (i : Fin 2) : ℤ :=
  ⌊(x i-x₀ i)/r⌋

def gridCell (x₀ : Plane) (r : ℝ) (a : Fin 2 → ℤ) : Set Plane :=
  {x | gridLabel x₀ r x = a}

def gridCenter (x₀ : Plane) (r : ℝ) (a : Fin 2 → ℤ) : Plane :=
  WithLp.toLp 2 (fun i => x₀ i+r*((a i:ℝ)+1/2))

lemma measurable_gridLabel (x₀ : Plane) (r : ℝ) : Measurable (gridLabel x₀ r) := by
  apply measurable_pi_iff.mpr
  intro i
  unfold gridLabel
  exact Int.measurable_floor.comp (((EuclideanSpace.proj i).continuous.measurable.sub
    measurable_const).div_const r)

lemma measurableSet_gridCell (x₀ : Plane) (r : ℝ) (a : Fin 2 → ℤ) :
    MeasurableSet (gridCell x₀ r a) :=
  (measurable_gridLabel x₀ r) (measurableSet_singleton a)

lemma gridCell_coord {x₀ : Plane} {r : ℝ} (hr : 0 < r) {a : Fin 2 → ℤ}
    {x : Plane} (hx : x ∈ gridCell x₀ r a) (i : Fin 2) :
    x₀ i+r*(a i:ℝ) ≤ x i ∧ x i < x₀ i+r*((a i:ℝ)+1) := by
  have he : ⌊(x i-x₀ i)/r⌋ = a i := congrFun hx i
  constructor
  · have h := Int.floor_le ((x i-x₀ i)/r)
    rw [he] at h
    have := (le_div_iff₀ hr).mp h
    nlinarith
  · have h := Int.lt_floor_add_one ((x i-x₀ i)/r)
    rw [he] at h
    have := (div_lt_iff₀ hr).mp h
    nlinarith

lemma gridCell_in_ball {x₀ : Plane} {r : ℝ} (hr : 0 < r) (a : Fin 2 → ℤ) :
    gridCell x₀ r a ⊆ Metric.ball (gridCenter x₀ r a) r := by
  intro x hx
  have hc (i : Fin 2) : |(x-gridCenter x₀ r a) i| ≤ r/2 := by
    have hh := gridCell_coord hr hx i
    change |x i-(x₀ i+r*((a i:ℝ)+1/2))| ≤ r/2
    apply abs_le.mpr
    constructor <;> linarith [hh.1,hh.2]
  have hsq (i : Fin 2) : ‖(x-gridCenter x₀ r a) i‖^2 ≤ (r/2)^2 := by
    simpa only [Real.norm_eq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 (hc i)
  rw [Metric.mem_ball, dist_eq_norm]
  have hn := EuclideanSpace.norm_sq_eq (x-gridCenter x₀ r a)
  simp only [Fin.sum_univ_two] at hn
  nlinarith [hsq 0, hsq 1, norm_nonneg (x-gridCenter x₀ r a)]

lemma gridLabel_mem_box {x₀ : Plane} {r : ℝ} (hr : 0 < r) {M : ℕ}
    (hM : 1/r+1 ≤ (M:ℝ)) {x : Plane} (hx : x ∈ Metric.ball x₀ 1) :
    ∀ i, gridLabel x₀ r x i ∈ Set.Icc (-(M:ℤ)) (M:ℤ) := by
  intro i
  have hc : |x i-x₀ i| < 1 := by
    have := PiLp.norm_apply_le (x-x₀) i
    simp only [PiLp.sub_apply, Real.norm_eq_abs] at this
    exact this.trans_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using hx)
  have hq : |(x i-x₀ i)/r| < 1/r := by
    rw [abs_div, abs_of_pos hr]
    exact div_lt_div_of_pos_right hc hr
  simp only [Set.mem_Icc, gridLabel]
  constructor
  · apply Int.le_floor.mpr
    have h := (abs_lt.mp hq).1
    push_cast
    linarith
  · have hlt : ⌊(x i-x₀ i)/r⌋ < (M:ℤ)+1 := by
      apply Int.floor_lt.mpr
      push_cast
      linarith [(abs_lt.mp hq).2]
    omega

lemma gridCell_disjoint {x₀ : Plane} {r : ℝ} {a b : Fin 2 → ℤ} (hab : a ≠ b) :
    Disjoint (gridCell x₀ r a) (gridCell x₀ r b) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hab (hx.symm.trans hy)

lemma gridBox_injective (M : ℕ) :
    Function.Injective (fun a : GridBox M => fun i => (a i : ℤ)) := by
  intro a b hab
  funext i
  exact Subtype.ext (congrFun hab i)

lemma grid_partition {x₀ : Plane} {r : ℝ} (hr : 0 < r) {M : ℕ}
    (hM : 1/r+1 ≤ (M:ℝ)) {E : Set Plane} (hE : E ⊆ Metric.ball x₀ 1) :
    ⋃ a : GridBox M, E ∩ gridCell x₀ r (fun i => (a i:ℤ)) = E := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset (fun a => Set.inter_subset_left)
  · intro x hx
    let a : GridBox M := fun i => ⟨gridLabel x₀ r x i, gridLabel_mem_box hr hM (hE hx) i⟩
    exact Set.mem_iUnion.mpr ⟨a,hx,rfl⟩

lemma grid_restrict_eq_sum {x₀ : Plane} {r : ℝ} (hr : 0 < r) {M : ℕ}
    (hM : 1/r+1 ≤ (M:ℝ)) {E : Set Plane} (hEm : MeasurableSet E)
    (hE : E ⊆ Metric.ball x₀ 1) :
    volume.restrict E = ∑ a : GridBox M,
      volume.restrict (E ∩ gridCell x₀ r (fun i => (a i:ℤ))) := by
  rw [← Measure.sum_fintype, ← Measure.restrict_iUnion]
  · rw [grid_partition hr hM hE]
  · intro a b hab
    exact (gridCell_disjoint (fun h => hab (gridBox_injective M h))).mono
      Set.inter_subset_right Set.inter_subset_right
  · exact fun a => hEm.inter (measurableSet_gridCell _ _ _)

def gridNear {M : ℕ} (K : ℕ) (a b : GridBox M) : Prop :=
  ∀ i, |(a i:ℤ)-(b i:ℤ)| ≤ (K:ℤ)

lemma gridNear_symm {M K : ℕ} : Std.Symm (gridNear (M:=M) K) := by
  constructor
  intro a b hab i
  simpa only [abs_sub_comm] using hab i

lemma gridNear_degree {M : ℕ} (K : ℕ) (a : GridBox M) :
    (Finset.univ.filter (gridNear K a)).card ≤ Fintype.card (GridBox K) := by
  classical
  let f : {b : GridBox M // b ∈ Finset.univ.filter (gridNear K a)} → GridBox K :=
    fun b i => ⟨(a i:ℤ)-(b.1 i:ℤ), abs_le.mp ((Finset.mem_filter.mp b.2).2 i)⟩
  have hf : Function.Injective f := by
    intro b c he
    apply Subtype.ext
    funext i
    apply Subtype.ext
    have h := congrArg (fun x : GridBox K => (x i:ℤ)) he
    change (a i:ℤ)-(b.1 i:ℤ) = (a i:ℤ)-(c.1 i:ℤ) at h
    omega
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

lemma grid_far_distance {x₀ : Plane} {r : ℝ} (hr : 0 < r) {M K : ℕ}
    {a b : GridBox M} (hab : ¬gridNear K a b) {x y : Plane}
    (hx : x ∈ gridCell x₀ r (fun i => (a i:ℤ)))
    (hy : y ∈ gridCell x₀ r (fun i => (b i:ℤ))) :
    (K:ℝ)*r ≤ ‖x-y‖ := by
  classical
  obtain ⟨i,hi⟩ := not_forall.mp hab
  have hc := gridCell_coord hr hx i
  have hd := gridCell_coord hr hy i
  have hnorm : |x i-y i| ≤ ‖x-y‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x-y) i
  apply le_trans _ hnorm
  have hi' : (K:ℤ)+1 ≤ |(a i:ℤ)-(b i:ℤ)| := by omega
  have hiR : (K:ℝ)+1 ≤ |((a i:ℤ):ℝ)-((b i:ℤ):ℝ)| := by exact_mod_cast hi'
  rcases le_total ((a i:ℤ):ℝ) ((b i:ℤ):ℝ) with hle | hle
  · rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hiR
    rw [abs_of_nonpos (by nlinarith : x i-y i ≤ 0)]
    nlinarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hle)] at hiR
    rw [abs_of_nonneg (by nlinarith : 0 ≤ x i-y i)]
    nlinarith

end PlanarEndpoint
end

end OAI
