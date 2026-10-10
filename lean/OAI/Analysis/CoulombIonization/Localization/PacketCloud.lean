import Mathlib
import OAI.Analysis.CoulombIonization.Localization.PacketInsert
import OAI.Analysis.CoulombIonization.Variational.SpatialRotation
import OAI.Analysis.CoulombIonization.Variational.TruncatedCoulomb

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

def packetCloud (p : ℕ → Space) (r : ℝ) (k : ℕ) (x : Space) : ℝ :=
  ∑ i ∈ Finset.range k, packetDensity (p i) r x

lemma packetCloud_nonneg (p : ℕ → Space) (r : ℝ) (k : ℕ) (x : Space) :
    0 ≤ packetCloud p r k x :=
  Finset.sum_nonneg (fun i _ => packetDensity_nonneg (p i) r x)

lemma packetCloud_integrable (p : ℕ → Space) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    Integrable (packetCloud p r k) := by
  exact integrable_finsetSum _ (fun i _ => packetDensity_integrable (p i) hr)

lemma packetCloud_memLp (p : ℕ → Space) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    MemLp (packetCloud p r k) (5/3) := by
  exact memLp_finsetSum _ (fun i _ => packetDensity_memLp (p i) hr)

lemma packetCloud_exists {p : ℕ → Space} {r : ℝ} {k : ℕ} {x : Space}
    (hx : packetCloud p r k x ≠ 0) : ∃ i < k, packetDensity (p i) r x ≠ 0 := by
  by_contra hh
  push Not at hh
  exact hx (Finset.sum_eq_zero (fun i hi => hh i (Finset.mem_range.mp hi)))

lemma packetCloud_bound (p : ℕ → Space) {r : ℝ} (hr : 0 < r) (k : ℕ)
    (hsep : ∀ i j, i < j → j < k → 3*r ≤ ‖p i-p j‖) (x : Space) :
    packetCloud p r k x ≤ packetDensityConstant/r^3 := by
  by_cases hx : packetCloud p r k x = 0
  · rw [hx]; positivity [packetDensityConstant_pos]
  obtain ⟨i,hi,hix⟩ := packetCloud_exists hx
  have unique (j : ℕ) (hj : j ∈ Finset.range k) (hji : j ≠ i) : packetDensity (p j) r x = 0 := by
    by_contra hjx
    have h1 := packetDensity_support (p i) hr hix
    have h2 := packetDensity_support (p j) hr hjx
    have h3 : 3*r ≤ ‖p i-p j‖ := by
      rcases lt_or_gt_of_ne hji with hji | hij
      · rw [norm_sub_rev]; exact hsep j i hji hi
      · exact hsep i j hij (Finset.mem_range.mp hj)
    have ht := norm_sub_le_norm_sub_add_norm_sub (p i) x (p j)
    rw [norm_sub_rev (p i) x] at ht
    linarith
  unfold packetCloud
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr hi) unique]
  exact packetDensity_bound (p i) x hr

lemma packetCloud_support (p : ℕ → Space) {r : ℝ} (hr : 0 < r) (k : ℕ)
    {a : ℝ} (hp : ∀ i < k, ‖p i‖ ≤ a) {x : Space} (hx : packetCloud p r k x ≠ 0) :
    ‖x‖ ≤ a+r := by
  obtain ⟨i,hi,hix⟩ := packetCloud_exists hx
  have h1 := packetDensity_support (p i) hr hix
  have ht := norm_add_le (x-p i) (p i)
  rw [sub_add_cancel] at ht
  have h2 := hp i hi
  linarith

lemma packetCloud_potential_bound (p : ℕ → Space) {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (k : ℕ)
    (hsep : ∀ i j, i < j → j < k → 3*r ≤ ‖p i-p j‖)
    (hp : ∀ i < k, ‖p i‖ ≤ a) (z : Space) (hz : ‖z‖ ≤ a) :
    (∫ x : Space, packetCloud p r k x/‖z-x‖) ≤
      packetDensityConstant/r^3 * (2*a+2*r)^2 * unitCoulombIntegral := by
  have hL : 0 < 2*a+2*r := by linarith
  have hi := CoulombAnalysis.tfPotential_integrable (packetCloud_integrable p hr k)
    (packetCloud_memLp p hr k) z
  have hk : Integrable (fun x : Space => truncatedCoulomb (2*a+2*r) (z-x)) :=
    (integrable_comp_sub_left _ z).mpr (truncatedCoulomb_integrable _)
  calc
    _ ≤ ∫ x : Space, (packetDensityConstant/r^3)*truncatedCoulomb (2*a+2*r) (z-x) := by
      apply integral_mono hi (hk.const_mul _)
      intro x
      change packetCloud p r k x / ‖z-x‖ ≤
        (packetDensityConstant/r^3)*truncatedCoulomb (2*a+2*r) (z-x)
      by_cases hx : packetCloud p r k x = 0
      · rw [hx,zero_div]
        exact mul_nonneg (div_nonneg packetDensityConstant_pos.le (pow_nonneg hr.le _))
          (truncatedCoulomb_nonneg _ _)
      · have hxs := packetCloud_support p hr k hp hx
        have ht := norm_sub_le z x
        have hmem : z-x ∈ ball (0 : Space) (2*a+2*r) := by
          rw [mem_ball_zero_iff]; linarith
        rw [truncatedCoulomb,indicator_of_mem hmem,mul_one_div]
        exact div_le_div_of_nonneg_right (packetCloud_bound p hr k hsep x) (norm_nonneg _)
    _ = _ := by
      rw [integral_const_mul,integral_sub_left_eq_self,truncatedCoulomb_integral hL]
      ring

theorem packetPairEnergy_bound (p : ℕ → Space) {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (k : ℕ)
    (hsep : ∀ i j, i < j → j < k → 3*r ≤ ‖p i-p j‖)
    (hp : ∀ i < k, ‖p i‖ ≤ a) :
    packetPairEnergy p k ≤ (k:ℝ)*(packetDensityConstant/r^3*(2*a+2*r)^2*unitCoulombIntegral) := by
  have hterm (j : ℕ) (hj : j ∈ Finset.range k) :
      (∑ i ∈ Finset.range j, 1/‖p i-p j‖) ≤
      packetDensityConstant/r^3*(2*a+2*r)^2*unitCoulombIntegral := by
    have hjk := Finset.mem_range.mp hj
    have he : (∑ i ∈ Finset.range j, 1/‖p i-p j‖) =
        ∫ x : Space, packetCloud p r j x/‖p j-x‖ := by
      simp only [packetCloud,Finset.sum_div]
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        have his := hsep i j (Finset.mem_range.mp hi) hjk
        rw [packetDensity_potential (p i) hr (by rw [norm_sub_rev]; linarith),norm_sub_rev]
      · intro i _
        exact CoulombAnalysis.tfPotential_integrable (packetDensity_integrable (p i) hr)
          (packetDensity_memLp (p i) hr) (p j)
    rw [he]
    exact packetCloud_potential_bound p hr ha j
      (fun i l hil hl => hsep i l hil (by omega)) (fun i hi => hp i (by omega)) (p j) (hp j hjk)
  calc
    _ ≤ ∑ _j ∈ Finset.range k, packetDensityConstant/r^3*(2*a+2*r)^2*unitCoulombIntegral :=
      Finset.sum_le_sum hterm
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]


open MeasureTheory Filter Set Metric
open scoped Topology BigOperators


def packetGridPoint {n : ℕ} (r : ℝ) (v : Fin 3 → Fin n) : Space :=
  WithLp.toLp 2 (fun t => (3*r)*(v t : ℝ))

lemma packetGridPoint_apply {n : ℕ} (r : ℝ) (v : Fin 3 → Fin n) (t : Fin 3) :
    packetGridPoint r v t = (3*r)*(v t : ℝ) := rfl

lemma packetGridPoint_norm {n : ℕ} {r : ℝ} (hr : 0 < r) (v : Fin 3 → Fin n) :
    ‖packetGridPoint r v‖ ≤ 9*r*n := by
  have hb (t : Fin 3) : |packetGridPoint r v t| ≤ 3*r*n := by
    rw [packetGridPoint_apply,abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (v t).isLt.le) (by positivity)
  have hs := EuclideanSpace.norm_sq_eq (packetGridPoint r v)
  have hsq : ‖packetGridPoint r v‖^2 ≤ 3*(3*r*n)^2 := by
    rw [hs]
    calc
      _ ≤ ∑ _t : Fin 3, (3*r*n)^2 := by
        apply Finset.sum_le_sum
        intro t _
        simpa only [Real.norm_eq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (hb t)
      _ = _ := by simp
  have hp : 0 ≤ 9*r*n := by positivity
  nlinarith [sq_nonneg (3*r*n),norm_nonneg (packetGridPoint r v)]

lemma packetGridPoint_separated {n : ℕ} {r : ℝ} (hr : 0 < r)
    (v w : Fin 3 → Fin n) (hvw : v ≠ w) : 3*r ≤ ‖packetGridPoint r v-packetGridPoint r w‖ := by
  obtain ⟨t,ht⟩ : ∃ t, v t ≠ w t := by
    by_contra hh
    push Not at hh
    exact hvw (funext hh)
  have hcast : 1 ≤ |(v t : ℝ)-(w t : ℝ)| := by
    rcases lt_or_gt_of_ne (show (v t).val ≠ (w t).val from fun hh => ht (Fin.ext hh)) with h | h
    · have hh : (v t : ℝ)+1 ≤ (w t : ℝ) := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith : (v t : ℝ)-(w t : ℝ) ≤ 0)]
      have := hh
      linarith
    · have hh : (w t : ℝ)+1 ≤ (v t : ℝ) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith : 0 ≤ (v t : ℝ)-(w t : ℝ))]
      have := hh
      linarith
  have hb := PiLp.norm_apply_le (packetGridPoint r v-packetGridPoint r w) t
  change |(3*r)*(v t : ℝ)-(3*r)*(w t : ℝ)| ≤ _ at hb
  rw [← mul_sub,abs_mul,abs_of_pos (by positivity : 0 < 3*r)] at hb
  nlinarith

lemma packetGrid_card (n : ℕ) : Fintype.card (Fin 3 → Fin n) = n^3 := by simp

def packetGrid (n : ℕ) (r : ℝ) (i : ℕ) : Space :=
  if h : i < Fintype.card (Fin 3 → Fin n) then
    packetGridPoint r ((Fintype.equivFin (Fin 3 → Fin n)).symm ⟨i,h⟩) else 0

lemma packetGrid_norm (n : ℕ) {r : ℝ} (hr : 0 < r) (i : ℕ) :
    ‖packetGrid n r i‖ ≤ 9*r*n := by
  unfold packetGrid
  split_ifs
  · exact packetGridPoint_norm hr _
  · simp only [norm_zero]; positivity

lemma packetGrid_separated (n : ℕ) {r : ℝ} (hr : 0 < r)
    (i j : ℕ) (hij : i < j) (hj : j < n^3) :
    3*r ≤ ‖packetGrid n r i-packetGrid n r j‖ := by
  have hj' : j < Fintype.card (Fin 3 → Fin n) := by rwa [packetGrid_card]
  have hi' : i < Fintype.card (Fin 3 → Fin n) := lt_trans hij hj'
  simp only [packetGrid,dite_eq_left hi',dite_eq_left hj']
  apply packetGridPoint_separated hr
  intro hh
  have he := (Fintype.equivFin (Fin 3 → Fin n)).symm.injective hh
  have : i = j := congrArg Fin.val he
  omega


open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

end CoulombAtom

end

end OAI
