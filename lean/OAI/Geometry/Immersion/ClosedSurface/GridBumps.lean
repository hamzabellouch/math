import OAI.Geometry.Immersion.ClosedSurface.MeanError
import OAI.Geometry.Immersion.ClosedSurface.PhaseGrid
import OAI.Geometry.Immersion.ClosedSurface.NormalFrame

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGrid
open Set

def gridBump : ContDiffBump (0 : Base) := ⟨1, 2, by norm_num, by norm_num⟩
def center (a : Index) : Base := ((a.1 : ℝ),(a.2 : ℝ))
def cutoff (h : ℝ) (a : Index) (x : Base) : ℝ :=
  gridBump (h⁻¹ • x - center a)

lemma cutoff_smooth (h : ℝ) (a : Index) : ContDiff ℝ ∞ (cutoff h a) := by
  have hs : ContDiff ℝ ∞ (fun x : Base => h⁻¹ • x) := contDiff_const_smul _
  exact gridBump.contDiff.comp (hs.sub contDiff_const)

lemma cutoff_nonneg (h : ℝ) (a : Index) (x : Base) : 0 ≤ cutoff h a x :=
  gridBump.nonneg
lemma cutoff_le_one (h : ℝ) (a : Index) (x : Base) : cutoff h a x ≤ 1 :=
  gridBump.le_one

lemma scaled_coordinate_lt {h R x : ℝ} {a : ℤ} (hh : 0 < h) :
    |h⁻¹ * x - a| < R ↔ |x - h * a| < R * h := by
  have he : h⁻¹ * x - a = (x-h*a)/h := by field_simp
  rw [he, abs_div, abs_of_pos hh, div_lt_iff₀ hh]

lemma cutoff_support {h : ℝ} (hh : 0 < h) (a : Index) :
    Function.support (cutoff h a) = cell h 2 a := by
  ext x
  change gridBump (h⁻¹ • x - center a) ≠ 0 ↔ _
  rw [← Function.mem_support, gridBump.support_eq]
  simp only [Metric.mem_ball, dist_zero_right, gridBump, Prod.norm_def]
  change (max |h⁻¹*x.1-a.1| |h⁻¹*x.2-a.2| < 2) ↔ _
  rw [max_lt_iff]
  exact and_congr (scaled_coordinate_lt hh) (scaled_coordinate_lt hh)

lemma cutoff_one_on_cell {h : ℝ} (hh : 0 < h) (a : Index) {x : Base}
    (hx : x ∈ cell h 1 a) : cutoff h a x = 1 := by
  apply gridBump.one_of_mem_closedBall
  simp only [Metric.mem_closedBall, dist_zero_right, gridBump]
  change ‖h⁻¹ • x - center a‖ ≤ 1
  rw [Prod.norm_def, max_le_iff]
  have hx1 := (scaled_coordinate_lt hh).mpr hx.1
  have hx2 := (scaled_coordinate_lt hh).mpr hx.2
  exact ⟨hx1.le,hx2.le⟩

lemma cutoff_tsupport_subset {h : ℝ} (hh : 0 < h) (a : Index) :
    tsupport (cutoff h a) ⊆ cell h 3 a := by
  have hclosed : IsClosed {x : Base | |x.1-h*a.1| ≤ 2*h ∧ |x.2-h*a.2| ≤ 2*h} :=
    (isClosed_le ((continuous_fst.sub continuous_const).abs) continuous_const).inter
      (isClosed_le ((continuous_snd.sub continuous_const).abs) continuous_const)
  have hs : Function.support (cutoff h a) ⊆
      {x : Base | |x.1-h*a.1| ≤ 2*h ∧ |x.2-h*a.2| ≤ 2*h} := by
    rw [cutoff_support hh]
    exact fun _ hx => ⟨hx.1.le,hx.2.le⟩
  have ht := closure_minimal hs hclosed
  intro x hx
  have hp := ht hx
  exact ⟨lt_of_le_of_lt hp.1 (by linarith),lt_of_le_of_lt hp.2 (by linarith)⟩



theorem cutoff_derivative_bounds : ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
    ∀ (h : ℝ), 0 < h → ∀ (a : Index) (j : ℕ) (x : Base),
      ‖iteratedFDeriv ℝ j (cutoff h a) x‖ ≤ C j / h^j := by
  have hbound (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : Base, ‖iteratedFDeriv ℝ j (gridBump : Base → ℝ) x‖ ≤ C := by
    have hc := (gridBump.contDiff (n := ⊤)).continuous_iteratedFDeriv (m := j) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    obtain ⟨x₀,hx₀⟩ := hc.norm.exists_forall_ge_of_hasCompactSupport
      ((gridBump.hasCompactSupport.iteratedFDeriv j).norm)
    exact ⟨_, norm_nonneg _, hx₀⟩
  choose C hC hbound using hbound
  refine ⟨C,hC,fun h hh a j x => ?_⟩
  let L : Base →L[ℝ] Base := h⁻¹ • ContinuousLinearMap.id ℝ Base
  let f : Base → ℝ := fun x => gridBump (x-center a)
  have hf : ContDiff ℝ ∞ f := gridBump.contDiff.comp (contDiff_id.sub contDiff_const)
  have he : cutoff h a = f ∘ L := rfl
  rw [he,L.iteratedFDeriv_comp_right hf x (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))]
  have hd : ‖iteratedFDeriv ℝ j f (L x)‖ ≤ C j := by
    simpa [f, iteratedFDeriv_comp_sub] using hbound j (L x-center a)
  have hL : ‖L‖ = h⁻¹ := by simp [L, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j f (L x)‖ * ∏ _ : Fin j, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ C j * h⁻¹ ^ j := by simp only [hL, Finset.prod_const, Finset.card_univ, Fintype.card_fin]; gcongr
    _ = C j / h^j := by rw [inv_pow, div_eq_mul_inv]


theorem cutoff_same_color_disjoint {h : ℝ} (hh : 0 < h) {a b : Index} (hne : a ≠ b)
    (he : color 6 a = color 6 b) :
    Disjoint (tsupport (cutoff h a)) (tsupport (cutoff h b)) :=
  (same_color_disjoint (by norm_num : 0 < 6) hh (by norm_num : (2:ℝ)*3 ≤ 6) hne he).mono
    (cutoff_tsupport_subset hh a) (cutoff_tsupport_subset hh b)

end ClosedSurfaceR4.PhaseGrid

end

end OAI
