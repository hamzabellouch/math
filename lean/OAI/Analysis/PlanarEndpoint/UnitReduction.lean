import OAI.Analysis.PlanarEndpoint.Extension
import OAI.Analysis.PlanarEndpoint.Fourier
import OAI.Analysis.PlanarEndpoint.FrequencyWeak
import OAI.Analysis.PlanarEndpoint.GraphReduction
import OAI.Analysis.PlanarEndpoint.GraphScaling
import OAI.Analysis.PlanarEndpoint.GraphSelection
import OAI.Analysis.PlanarEndpoint.GraphTree
import OAI.Analysis.PlanarEndpoint.UnitScaling

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace PlanarEndpoint

def UnitFrequencyGraphEstimate (c₀ C₀ p : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 1 ≤ R →
    ∀ v : Plane → ℂ, ∀ hv : MemLp v 2 volume,
    (∀ᵐ η : Plane ∂volume, η ∉ {η | c₀ ≤ ‖η‖ ∧ ‖η‖ ≤ C₀} → v η = 0) →
    ∀ (x₀ : Plane) (T : Plane → ℝ), Measurable T →
      (∀ X, T X ∈ Icc (0:ℝ) R) → ∀ lam : ℝ, 0 < lam →
      volume (Metric.ball x₀ R ∩ {X | lam < ‖frequencyExtension v X (T X)‖}) ≤
        ENNReal.ofReal (R^2 * (K * R^(-2/3:ℝ) * ‖hv.toLp v‖ / lam)^p)

lemma inverse_smul_ball (x x₀ : Plane) {N : ℝ} (hN : 0 < N) :
    N⁻¹ • x ∈ Metric.ball x₀ 1 ↔ x ∈ Metric.ball (N • x₀) N := by
  have he : dist x (N • x₀) = N * dist (N⁻¹ • x) x₀ := by
    calc
      _ = dist (N • (N⁻¹ • x)) (N • x₀) := by simp [smul_smul,hN.ne']
      _ = _ := by simp [dist_smul₀,Real.norm_eq_abs,abs_of_pos hN]
  simp only [Metric.mem_ball,he]
  exact ⟨fun h => by nlinarith,fun h => (mul_lt_mul_iff_right₀ hN).mp (by simpa using h)⟩

lemma unitGraph_time_range {N t₀ s : ℝ} (hN : 0 < N) (hsN : s ≤ N⁻¹)
    {T : Plane → ℝ} (hT : ∀ x, T x ∈ Icc t₀ (t₀+s)) (X : Plane) :
    N^2*(T (N⁻¹ • X)-t₀) ∈ Icc (0:ℝ) N := by
  have ht := hT (N⁻¹ • X)
  constructor
  · exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr ht.1)
  · have hh : N^2*(T (N⁻¹ • X)-t₀) ≤ N^2*N⁻¹ :=
      mul_le_mul_of_nonneg_left ((by linarith [ht.2] : T (N⁻¹ • X)-t₀ ≤ s).trans hsN)
        (sq_nonneg _)
    have he : N^2*N⁻¹ = N := by field_simp
    simpa only [he] using hh

lemma unitGraph_threshold_identity (f : L2) {N : ℝ} (hN : 0 < N) (t₀ K lam : ℝ) :
    K * N^(-2/3:ℝ) *
        ‖(unitFrequencyInput_memLp f hN t₀).toLp (unitFrequencyInput f N t₀)‖ /
        (lam / (((2*Real.pi)^2)⁻¹*N)) =
      (K/(2*Real.pi)) * N^(1/3:ℝ) * ‖f‖ / lam := by
  rw [unitFrequencyInput_norm f hN t₀]
  have hp : N^(-2/3:ℝ)*N = N^(1/3:ℝ) := by
    calc
      _ = N^(-2/3:ℝ)*N^(1:ℝ) := by rw [Real.rpow_one]
      _ = N^((-2/3:ℝ)+1) := (Real.rpow_add hN _ _).symm
      _ = _ := by norm_num
  rw [← hp]
  field_simp

lemma shortTimeGraphEstimate_of_unitFrequency {c₀ C₀ p : ℝ}
    (hg : UnitFrequencyGraphEstimate c₀ C₀ p) : ShortTimeGraphEstimate c₀ C₀ p := by
  obtain ⟨K,hK,hg⟩ := hg
  refine ⟨K/(2*Real.pi),div_pos hK (by positivity),?_⟩
  intro j f hf x₀ t₀ s hs hsN T hT hr lam hlam
  let N : ℝ := 2^j
  have hN : 0 < N := by positivity
  have hN1 : 1 ≤ N := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
  let v := unitFrequencyInput f N t₀
  let hv := unitFrequencyInput_memLp f hN t₀
  let Q (X : Plane) : ℝ := N^2*(T (N⁻¹ • X)-t₀)
  have hQ : Measurable Q := by
    exact measurable_const.mul ((hT.comp (measurable_const_smul _)).sub measurable_const)
  have hQr : ∀ X, Q X ∈ Icc (0:ℝ) N := unitGraph_time_range hN hsN hr
  let a : ℝ := ((2*Real.pi)^2)⁻¹*N
  have ha : 0 < a := by dsimp [a]; positivity
  let E : Set Plane := Metric.ball x₀ 1 ∩ {x | lam < ‖evolution f x (T x)‖}
  let F : Set Plane := Metric.ball (N • x₀) N ∩
    {X | lam/a < ‖frequencyExtension v X (Q X)‖}
  have hE : MeasurableSet E := Metric.isOpen_ball.measurableSet.inter
    (measurableSet_lt measurable_const (measurable_graph_evolution f hf.integrable hT).norm)
  have hEF : affineScale 0 N⁻¹ ⁻¹' E = F := by
    ext X
    simp only [affineScale,zero_add,mem_preimage,mem_inter_iff,mem_ofPred_eq,E,F]
    rw [inverse_smul_ball X x₀ hN]
    apply and_congr_right'
    rw [norm_evolution_unitFrequency_scaling f (N⁻¹ • X) hN (T (N⁻¹ • X)) t₀]
    simp only [smul_smul,mul_inv_cancel₀ hN.ne',one_smul]
    change lam < a * ‖frequencyExtension v X (Q X)‖ ↔
      lam/a < ‖frequencyExtension v X (Q X)‖
    rw [mul_comm a]
    exact (div_lt_iff₀ ha).symm
  have hb := hg N hN1 v hv (unitFrequencyInput_support hN hf t₀)
    (N • x₀) Q hQ hQr (lam/a) (div_pos hlam ha)
  have hnn : 0 ≤ N^2 * (K*N^(-2/3:ℝ)*‖hv.toLp v‖/(lam/a))^p := by positivity
  have hbR : volume.real F ≤ N^2 * (K*N^(-2/3:ℝ)*‖hv.toLp v‖/(lam/a))^p := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq
      (ENNReal.toReal_ofReal hnn)
  have he := volumeReal_affineScale hE 0 (inv_pos.mpr hN)
  rw [hEF] at he
  have hbfinal : volume.real E ≤ ((K/(2*Real.pi))*N^(1/3:ℝ)*‖f‖/lam)^p := by
    calc
      _ = (N⁻¹)^2 * volume.real F := he
      _ ≤ (N⁻¹)^2 * (N^2*(K*N^(-2/3:ℝ)*‖hv.toLp v‖/(lam/a))^p) :=
        mul_le_mul_of_nonneg_left hbR (sq_nonneg _)
      _ = ((K/(2*Real.pi))*N^(1/3:ℝ)*‖f‖/lam)^p := by
        dsimp [a,hv,v]
        rw [unitGraph_threshold_identity f hN t₀ K lam]
        field_simp
  have hfin : volume E ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ball_lt_top (μ := volume) (x := x₀) (r := 1)).ne (measure_mono inter_subset_left)
  change volume E ≤ _
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal hbfinal

lemma shortTimeWeakEstimate_of_unitFrequency {c₀ C₀ p : ℝ}
    (hg : UnitFrequencyGraphEstimate c₀ C₀ p) : ShortTimeWeakEstimate c₀ C₀ p :=
  shortTimeWeakEstimate_of_graph (shortTimeGraphEstimate_of_unitFrequency hg)

lemma mainConclusion_of_unitFrequencyGraph {p : ℝ} (hp : 2 < p)
    (hg : UnitFrequencyGraphEstimate (1/4) 4 p) {f : L2} (hf : InHThird f) :
    MainConclusion f :=
  mainConclusion_of_shortTime hp (shortTimeWeakEstimate_of_unitFrequency hg) hf

end PlanarEndpoint
end

end OAI
