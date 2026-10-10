import OAI.Geometry.Kahler.BaseTestAveraging

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

def peakPatch (k : ℕ) (R : ℝ) (p : Sphere) : Set Sphere :=
  {ξ | Real.exp (-R/k) < ‖bracket (ξ:Base) (p:Base)‖}

def patchHeight (k : ℕ) (p : Sphere) (z : Base) : ℝ := -(k:ℝ)*Real.log ‖bracket z (p:Base)‖

lemma peakPatch_open (k : ℕ) (R : ℝ) (p : Sphere) : IsOpen (peakPatch k R p) :=
  isOpen_lt continuous_const (((bracket_analytic (p:Base)).continuous.comp continuous_subtype_val).norm)

lemma peakPatch_norm_pos {k : ℕ} {R : ℝ} {p ξ : Sphere} (hξ : ξ ∈ peakPatch k R p) :
    0 < ‖bracket (ξ:Base) (p:Base)‖ := lt_trans (Real.exp_pos _) hξ

lemma patchHeight_nonneg (k : ℕ) (p ξ : Sphere) : 0 ≤ patchHeight k p (ξ:Base) := by
  unfold patchHeight
  exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (Nat.cast_nonneg k)) (Real.log_nonpos (norm_nonneg _) (bracket_norm_le_one ξ p))

lemma peakPatch_iff_height {k : ℕ} (hk : 0 < k) (R : ℝ) (p ξ : Sphere) :
    ξ ∈ peakPatch k R p ↔ 0 < ‖bracket (ξ:Base) (p:Base)‖ ∧ patchHeight k p (ξ:Base) < R := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  constructor
  · intro hξ
    refine ⟨peakPatch_norm_pos hξ,?_⟩
    have hh := Real.log_lt_log (Real.exp_pos (-R/k)) hξ
    rw [Real.log_exp] at hh
    unfold patchHeight
    have hm := (div_lt_iff₀ hk0).mp hh
    nlinarith
  · rintro ⟨hn,hy⟩
    apply (Real.log_lt_log_iff (Real.exp_pos _) hn).mp
    rw [Real.log_exp]
    apply (div_lt_iff₀ hk0).mpr
    unfold patchHeight at hy
    nlinarith

lemma peakPatch_radius {k : ℕ} (hk : 0 < k) {R : ℝ} (hR : 0 < R)
    {p ξ : Sphere} (hξ : ξ ∈ peakPatch k R p) :
    Real.sqrt (k:ℝ)*projectiveDistance ξ p < Real.sqrt (2*R) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hnorm := peakPatch_norm_pos hξ
  have he : Real.exp (-R/k)^2 = Real.exp (-2*R/k) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hsq : Real.exp (-2*R/k) < ‖bracket (ξ:Base) (p:Base)‖^2 := by
    rw [← he]
    have hp : Real.exp (-R/k) < ‖bracket (ξ:Base) (p:Base)‖ := hξ
    exact sq_lt_sq₀ (Real.exp_pos _).le (norm_nonneg _) |>.mpr hp
  have hl := Real.one_sub_le_exp_neg (2*R/k)
  rw [← neg_div] at hl
  have hh2 : -(2*R) / (k:ℝ) = -2*R/k := by ring
  rw [hh2] at hl
  have hd := projectiveDistance_sq ξ p
  have hmul : (k:ℝ)*projectiveDistance ξ p^2 < 2*R := by
    have hh : projectiveDistance ξ p^2 < 2*R/k := by linarith
    simpa only [mul_comm] using (lt_div_iff₀ hk0).mp hh
  have hkn := Real.sq_sqrt hk0.le
  have hrn := Real.sq_sqrt (show 0 ≤ 2*R by positivity)
  have hd0 := projectiveDistance_nonneg ξ p
  have hk1 := Real.sqrt_nonneg (k:ℝ)
  have hr1 := Real.sqrt_nonneg (2*R)
  have heq : (Real.sqrt (k:ℝ)*projectiveDistance ξ p)^2 = (k:ℝ)*projectiveDistance ξ p^2 := by rw [mul_pow,hkn]
  nlinarith

lemma peakPatch_disjoint {k : ℕ} (hk : 0 < k) {R D : ℝ} (hR : 0 < R)
    (hD : 2*Real.sqrt (2*R) < D) {P : Finset Sphere}
    (hP : ProjectivelySeparated (D/Real.sqrt k) P) :
    (P : Set Sphere).PairwiseDisjoint (peakPatch k R) := by
  intro p hp q hq hpq
  apply Set.disjoint_left.mpr
  intro ξ hξp hξq
  have hs : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hk)
  have hp1 := peakPatch_radius hk hR hξp
  have hq1 := peakPatch_radius hk hR hξq
  have hh := hP p hp q hq hpq
  have ht := projectiveDistance_triangle p ξ q
  rw [projectiveDistance_symm p ξ] at ht
  have hm := mul_le_mul_of_nonneg_left ht hs.le
  have hd := (div_le_iff₀ hs).mp hh
  nlinarith

lemma peakPatch_single {k : ℕ} (hk : 1 ≤ k) {R D : ℝ} (hR : 0 < R)
    (hD : 1 ≤ D) (hDR : Real.sqrt (2*R) ≤ D) {P : Finset Sphere}
    (hP : ProjectivelySeparated (D/Real.sqrt k) P) {p ξ : Sphere}
    (hp : p ∈ P) (hξ : ξ ∈ peakPatch k R p) :
    ‖peakPolynomial P k (ξ:Base) - bracket (ξ:Base) (p:Base)^k‖ ≤
      gaussianConstant*Real.exp (-(D-Real.sqrt (2*R))^2/4) := by
  classical
  have hk0 : 0 < k := by omega
  have hs : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hk0)
  have hξp := peakPatch_radius hk0 hR hξ
  have hsub : P.erase p ⊆ P.filter (fun q => D-Real.sqrt (2*R) ≤ Real.sqrt k*projectiveDistance ξ q) := by
    intro q hq
    obtain ⟨hqp,hqP⟩ := Finset.mem_erase.mp hq
    refine Finset.mem_filter.mpr ⟨hqP,?_⟩
    have hh := (div_le_iff₀ hs).mp (hP p hp q hqP hqp.symm)
    have ht := projectiveDistance_triangle p ξ q
    rw [projectiveDistance_symm p ξ] at ht
    have hm := mul_le_mul_of_nonneg_left ht hs.le
    nlinarith
  have he : peakPolynomial P k (ξ:Base) - bracket (ξ:Base) (p:Base)^k =
      ∑ q ∈ P.erase p, bracket (ξ:Base) (q:Base)^k := by
    unfold peakPolynomial
    rw [← Finset.add_sum_erase _ _ hp]
    ring
  rw [he]
  apply (norm_sum_le _ _).trans
  simp only [norm_pow]
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)).trans
    (peak_gaussian hD hk hP ξ (sub_nonneg.mpr hDR))

lemma off_peakPatch_radius {k : ℕ} (hk : 0 < k) {R : ℝ} (hR : 0 < R)
    (hkR : 2*R ≤ k) {p ξ : Sphere} (hξ : ξ ∉ peakPatch k R p) :
    Real.sqrt R ≤ Real.sqrt (k:ℝ)*projectiveDistance ξ p := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hs : 0 ≤ 2*R/k := by positivity
  have hs1 : 2*R/k ≤ 1 := (div_le_one hk0).mpr hkR
  have he0 : 0 < Real.exp (2*R/k) := Real.exp_pos _
  have he1 := Real.add_one_le_exp (2*R/k)
  have hc0 : 0 ≤ ‖bracket (ξ:Base) (p:Base)‖ := norm_nonneg _
  have hcn : ‖bracket (ξ:Base) (p:Base)‖ ≤ Real.exp (-R/k) := le_of_not_gt hξ
  have he : Real.exp (-R/k)^2 = (Real.exp (2*R/k))⁻¹ := by
    rw [← Real.exp_nat_mul,← Real.exp_neg]; congr 1; ring
  have hsq : ‖bracket (ξ:Base) (p:Base)‖^2 ≤ (Real.exp (2*R/k))⁻¹ := by
    rw [← he]
    exact (sq_le_sq₀ hc0 (Real.exp_pos _).le).mpr hcn
  have hm : ‖bracket (ξ:Base) (p:Base)‖^2*Real.exp (2*R/k) ≤ 1 := by
    have ht := mul_le_mul_of_nonneg_right hsq he0.le
    simpa only [inv_mul_cancel₀ he0.ne',one_mul] using ht
  have hm1 : ‖bracket (ξ:Base) (p:Base)‖^2*(1+2*R/k) ≤ 1 := by
    have ht := mul_le_mul_of_nonneg_left he1 (sq_nonneg ‖bracket (ξ:Base) (p:Base)‖)
    nlinarith
  have hd := projectiveDistance_sq ξ p
  have hd0 := projectiveDistance_nonneg ξ p
  have hds : R/k ≤ projectiveDistance ξ p^2 := by
    have hh := mul_le_mul_of_nonneg_left hs1 (sq_nonneg (projectiveDistance ξ p))
    have hs2 : 2*R/(k:ℝ) = 2*(R/k) := by ring
    have hn : ‖bracket (ξ:Base) (p:Base)‖^2 = 1-projectiveDistance ξ p^2 := by linarith
    rw [hn,hs2] at hm1
    rw [hs2] at hh
    nlinarith
  have hh := (div_le_iff₀ hk0).mp hds
  have hkn := Real.sq_sqrt hk0.le
  have hrn := Real.sq_sqrt hR.le
  have heq : (Real.sqrt (k:ℝ)*projectiveDistance ξ p)^2 = (k:ℝ)*projectiveDistance ξ p^2 := by rw [mul_pow,hkn]
  have hprod : 0 ≤ Real.sqrt (k:ℝ)*projectiveDistance ξ p := mul_nonneg (Real.sqrt_nonneg _) hd0
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) hprod).mp (by nlinarith)

lemma peak_off_patch {k : ℕ} (hk : 1 ≤ k) {R D : ℝ} (hR : 0 < R)
    (hkR : 2*R ≤ k) (hD : 1 ≤ D) {P : Finset Sphere}
    (hP : ProjectivelySeparated (D/Real.sqrt k) P) (ξ : Sphere)
    (hξ : ∀ p ∈ P, ξ ∉ peakPatch k R p) :
    ‖peakPolynomial P k (ξ:Base)‖ ≤ gaussianConstant*Real.exp (-R/4) := by
  classical
  have hfilter : P.filter (fun p => Real.sqrt R ≤ Real.sqrt k*projectiveDistance ξ p) = P := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    exact off_peakPatch_radius (by omega) hR hkR (hξ p hp)
  have hh := peak_gaussian hD hk hP ξ (Real.sqrt_nonneg R)
  rw [hfilter,Real.sq_sqrt hR.le] at hh
  exact (norm_sum_le _ _).trans (by simpa only [norm_pow] using hh)

end PinchedHartogs.BaseConstruction

end

end OAI
