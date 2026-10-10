import OAI.Geometry.Kahler.BaseRadii

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma TestSystem.series_mean_bound (S : TestSystem) :
    ∃ T : ℝ, ∀ N : ℕ,
      (∫ ξ : Sphere, (∑' j, logarithmicTest S.a S.ε (S.P (S.Q^(j+1))) (S.Q^(j+1))
        ((testRadius S.Q S.η N:ℂ) • (ξ:Base)))
        ∂densityMeasure (density S.Q S.pr.R S.pr.f S.pr.b S.P N)) ≤ -(S.d)*(N:ℝ)+T := by
  obtain ⟨B,hB,hBb⟩ := logarithmicTest_sphere_bound S.a S.eps_pos.ne' S.D_ge
  let t := Real.exp (-S.η)
  have ht : 0 ≤ t := (Real.exp_pos _).le
  have ht1 : t < 1 := Real.exp_lt_one_iff.mpr (by linarith [S.eta_pos])
  have hsum : Summable (fun m : ℕ => B*t^(m+1)) := by
    simpa only [pow_succ,mul_assoc,mul_left_comm,mul_comm] using
      ((summable_geometric_of_lt_one ht ht1).mul_left B).mul_right t
  refine ⟨∑' m : ℕ, B*t^(m+1),?_⟩
  intro N
  let μ := densityMeasure (density S.Q S.pr.R S.pr.f S.pr.b S.P N)
  let : IsProbabilityMeasure μ := S.probability N
  let r := testRadius S.Q S.η N
  have hr := testRadius_mem S.Q_ge S.eta_pos (by linarith [S.eta_lt] : S.η < 1) N
  obtain ⟨hs,he⟩ := logarithmicTest_integral_series S.a S.eps_pos.ne' S.D_ge S.Q_ge S.P S.separated hr.1.le hr.2 μ
  rw [he,← hs.sum_add_tsum_nat_add N]
  have hlo : (∑ j ∈ Finset.range N, ∫ ξ : Sphere,
      logarithmicTest S.a S.ε (S.P (S.Q^(j+1))) (S.Q^(j+1)) ((r:ℂ) • (ξ:Base)) ∂μ) ≤ -(S.d)*(N:ℝ) := by
    have hh := Finset.sum_le_sum (s := Finset.range N) (g := fun _ => -S.d) (fun j hj =>
      S.negative N j (by simp only [Finset.mem_range] at hj; omega) r ⟨hr.1.le,hr.2.le⟩
        (testRadius_near S.Q_ge S.eta_pos (by linarith [S.eta_lt]) (by simp only [Finset.mem_range] at hj; omega)))
    simpa [mul_comm] using hh
  have htail : (∑' m, ∫ ξ : Sphere,
      logarithmicTest S.a S.ε (S.P (S.Q^(m+N+1))) (S.Q^(m+N+1)) ((r:ℂ) • (ξ:Base)) ∂μ) ≤ ∑' m : ℕ, B*t^(m+1) := by
    apply (hs.comp_injective (fun m n h => Nat.add_right_cancel h)).tsum_le_tsum _ hsum
    intro m
    have hb (ξ : Sphere) : ‖logarithmicTest S.a S.ε (S.P (S.Q^(m+N+1))) (S.Q^(m+N+1)) ((r:ℂ) • (ξ:Base))‖ ≤ B*t^(m+1) :=
      (hBb _ (Nat.one_le_pow _ _ (by have := S.Q_ge; omega)) _ (S.separated (m+N)) r ⟨hr.1.le,hr.2.le⟩ ξ).trans
        (mul_le_mul_of_nonneg_left (testRadius_tail S.Q_ge S.eta_pos (by linarith [S.eta_lt]) N m) hB)
    have hh := norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hb)
    exact (le_abs_self _).trans (by simpa [r,Function.comp_def] using hh)
  exact add_le_add hlo htail

lemma psi_radial_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (ξ : Sphere) :
    psi ((r:ℂ) • (ξ:Base)) ≤ Real.log (1/(1-r)) := by
  have hn : ‖(r:ℂ) • (ξ:Base)‖=r := by simp [norm_smul,abs_of_nonneg hr]
  rw [psi,hn,one_div,Real.log_inv]
  have h1 : 0 < 1-r := by linarith
  have hle : 1-r ≤ 1-r^2 := by nlinarith
  exact neg_le_neg (Real.log_le_log h1 hle)

lemma TestSystem.noMinorant (S : TestSystem) {L : ℝ} (hL : 0 < L)
    (hamp : 5*Real.log S.Q < L*S.d) : noMinorant (basePotential S.P S.a S.ε L S.Q) := by
  obtain ⟨T,hT⟩ := S.series_mean_bound
  rintro ⟨H,C,hH,hminor⟩
  have hbound (N : ℕ) : (N:ℝ)*(L*S.d-5*Real.log S.Q) ≤ C-5*Real.log S.η+L*T-(H 0).re := by
    let μ := densityMeasure (density S.Q S.pr.R S.pr.f S.pr.b S.P N)
    let : IsProbabilityMeasure μ := S.probability N
    let r := testRadius S.Q S.η N
    have hr := testRadius_mem S.Q_ge S.eta_pos (by linarith [S.eta_lt] : S.η < 1) N
    change 0 < r ∧ r < 1 at hr
    have hrc : ‖(r:ℂ)‖ < 1 := by simpa [abs_of_pos hr.1] using hr.2
    have hmap := radial_mem_ball hrc
    have hiH := continuous_integrable (μ := μ) (radial_continuous hH.continuousOn hrc)
    have hseries := testSeries_contDiffOn S.a S.eps_pos.ne' S.D_ge S.Q_ge S.P S.separated
    have his := continuous_integrable (μ := μ) (hseries.continuousOn.comp_continuous ((continuous_subtype_val : Continuous (fun ξ : Sphere => (ξ:Base))).const_smul (r:ℂ)) hmap)
    change Integrable (fun ξ : Sphere => ∑' j, logarithmicTest S.a S.ε (S.P (S.Q^(j+1))) (S.Q^(j+1)) ((r:ℂ) • (ξ:Base))) μ at his
    have hpoint (ξ : Sphere) : (H ((r:ℂ) • (ξ:Base))).re ≤
        C+5*Real.log (1/(1-r))+L*(∑' j, logarithmicTest S.a S.ε (S.P (S.Q^(j+1))) (S.Q^(j+1)) ((r:ℂ) • (ξ:Base))) := by
      have hh := hminor _ (hmap ξ)
      have hp := psi_radial_le hr.1.le hr.2 ξ
      have hn : ‖(r:ℂ) • (ξ:Base)‖=r := by simp [norm_smul,abs_of_pos hr.1]
      rw [hn,basePotential] at hh
      linarith
    have hi := integral_mono hiH.re ((integrable_const _).add (his.const_mul L)) hpoint
    simp only [Pi.add_apply] at hi his
    rw [integral_add (integrable_const _) (his.const_mul L),integral_const_mul] at hi
    have hre := Complex.reCLM.integral_comp_comm hiH
    have hm := (S.representing N).analytic_mean hH hrc
    change (∫ ξ : Sphere, (H ((r:ℂ) • (ξ:Base))).re ∂μ) = _ at hre
    change (∫ ξ : Sphere, (H ((r:ℂ) • (ξ:Base))).re ∂μ) ≤ _ at hi
    change (∫ ξ : Sphere, H ((r:ℂ) • (ξ:Base)) ∂μ) = H 0 at hm
    rw [hre,hm] at hi
    simp only [integral_const] at hi
    simp at hi
    have ht := mul_le_mul_of_nonneg_left (hT N) hL.le
    simp at ht
    have hl := testRadius_log S.Q_ge S.eta_pos N
    change Real.log (1/(1-r))=_ at hl
    simp only [one_div,Real.log_inv] at hl
    linarith
  have hd : 0 < L*S.d-5*Real.log S.Q := by linarith
  obtain ⟨N,hN⟩ := exists_nat_gt ((C-5*Real.log S.η+L*T-(H 0).re)/(L*S.d-5*Real.log S.Q))
  have hh := (div_lt_iff₀ hd).mp hN
  have := hbound N
  linarith

end PinchedHartogs.BaseConstruction

end

end OAI
