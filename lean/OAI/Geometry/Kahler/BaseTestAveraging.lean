import OAI.Geometry.Kahler.BaseShiftAveraging

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff ENNReal
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma correction_sigma_average {k ℓ : ℕ} (hk : 0 < k) (hl : ℓ < k)
    {R E : ℝ} (hER : E < R) {f b : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0) {W V : Base → ℝ}
    (hW : ContDiff ℝ ∞ W) (hV : Continuous V) (hband : PhaseBandwidth W ℓ) (hm : OrbitMeanOne W)
    (hroot : ∀ ξ : Sphere, V ((Circle.exp (2*Real.pi/k):ℂ) • (ξ:Base))=V ξ) (p : Sphere) :
    (∫ ξ : Sphere, V ξ*densityCorrection k R f b W p ξ ∂sigma)=
      ∫ ξ : Sphere, V ξ*densityCorrection k R f b (fun _ => 1) p ξ ∂sigma := by
  have hs := (densityCorrection_smooth hk hER hf hb hW htail p).continuous
  have hsone := (densityCorrection_smooth hk hER hf hb (contDiff_const (c := (1:ℝ))) htail p).continuous
  erw [sigma_phase_average ((hV.mul hs).comp continuous_subtype_val),
    sigma_phase_average ((hV.mul hsone).comp continuous_subtype_val)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun ξ => by
    change (∫ z : Circle, V ((z:ℂ) • (ξ:Base))*densityCorrection k R f b W p ((z:ℂ) • (ξ:Base)) ∂circleMeasure)=_
    apply correction_orbit_averaging hk hl R f b (hW.differentiable (by norm_num)) hband hm p ξ
    · fun_prop
    · intro z
      simpa only [Circle.coe_mul,mul_smul,phaseAction_coe] using hroot (phaseAction z ξ))

lemma logarithmicTest_root (a ε r : ℝ) (P : Finset Sphere) {k : ℕ} (hk : 0 < k) (ξ : Sphere) :
    logarithmicTest a ε P k ((r:ℂ) • ((Circle.exp (2*Real.pi/k):ℂ) • (ξ:Base)))=
    logarithmicTest a ε P k ((r:ℂ) • (ξ:Base)) := by
  have hrt : (Circle.exp (2*Real.pi/k):ℂ)^k=1 := by
    simpa only [phaseChar,zpow_natCast,Circle.coe_pow] using phaseChar_root hk
  rw [smul_comm (r:ℂ),logarithmicTest,peakPolynomial_homogeneous,hrt,one_mul]
  rfl

theorem logarithmicTests_exact_averaging {a ε : ℝ} (p : RadialProfiles a) (he : ε ≠ 0)
    {Q : ℕ} (hQ : 2 ≤ Q) (P : ℕ → Finset Sphere) (j : ℕ) (r : ℝ) :
    (∫ ξ : Sphere, logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) ((r:ℂ) • (ξ:Base))*
      density Q p.R p.f p.b P (j+1) ξ ∂sigma) =
    (∫ ξ : Sphere, logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) ((r:ℂ) • (ξ:Base)) ∂sigma)+
    ∑ v ∈ P (Q^(j+1)), ∫ ξ : Sphere, logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) ((r:ℂ) • (ξ:Base))*
      densityCorrection (Q^(j+1)) p.R p.f p.b (fun _ => 1) v ξ ∂sigma := by
  have hq : 0 < Q := by omega
  have hk := pow_pos hq (j+1)
  let V : Base → ℝ := fun ξ => logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) ((r:ℂ) • ξ)
  let W := density Q p.R p.f p.b P j
  have hV : Continuous V := (logarithmicTest_contDiff a he _ _).continuous.comp (by fun_prop)
  have hW : ContDiff ℝ ∞ W := density_smooth hq p.cutoff_lt p.smooth_f p.smooth_b p.tail P j
  have hband := density_bandwidth hq p.cutoff_lt p.smooth_f p.smooth_b p.tail P j
  have hm := density_orbit_mean hQ p.cutoff_lt p.smooth_f p.smooth_b p.tail P j
  have hgap : densityBandwidth Q j < Q^(j+1) := densityBandwidth_lt hQ j
  have hroot : ∀ ξ : Sphere, V ((Circle.exp (2*Real.pi/(Q^(j+1):ℕ)):ℂ) • (ξ:Base))=V ξ :=
    logarithmicTest_root a ε r _ hk
  have hci : ∀ v : Sphere, Integrable (fun ξ : Sphere => V ξ*densityCorrection (Q^(j+1)) p.R p.f p.b W v ξ) sigma := by
    intro v
    exact compact_continuous_integrable ((hV.mul (densityCorrection_smooth hk p.cutoff_lt p.smooth_f p.smooth_b hW p.tail v).continuous).comp continuous_subtype_val)
  simp only [density,mul_add,Finset.mul_sum]
  change (∫ ξ : Sphere, V ξ*W ξ+∑ v ∈ P (Q^(j+1)), V ξ*densityCorrection (Q^(j+1)) p.R p.f p.b W v ξ ∂sigma)=_
  erw [integral_add (compact_continuous_integrable ((hV.mul hW.continuous).comp continuous_subtype_val)) (integrable_finsetSum (P (Q^(j+1))) (fun v _ => hci v)),integral_finsetSum (P (Q^(j+1))) (fun v _ => hci v)]
  change (∫ ξ : Sphere, V ξ*W ξ ∂sigma)+_=_
  rw [sigma_root_average hk hgap hW.continuous hV hband hm hroot]
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  exact correction_sigma_average hk hgap p.cutoff_lt p.smooth_f p.smooth_b p.tail hW hV hband hm hroot v

end PinchedHartogs.BaseConstruction

end

end OAI
