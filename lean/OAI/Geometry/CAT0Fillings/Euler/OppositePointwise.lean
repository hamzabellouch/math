import Mathlib
import OAI.Geometry.CAT0Fillings.Powers.PolynomialBound
import OAI.Geometry.CAT0Fillings.Radial.ClosedInequality
import OAI.Geometry.CAT0Fillings.Radial.Extension

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def radialPowerIntegrand (o : X) (v : q.Sobolev) (β : ℝ) (w : ℕ × Euc (k+1)) : ℝ :=
  dist o (q.atlasParam w)*((q.inclusion v (q.atlasParam w))^(2+4*β)*
    Real.sqrt (1-‖q.gradient (LipschitzWith.dist_right o) w‖^2)-
    2*β*(q.inclusion v (q.atlasParam w))^(1+4*β)*
      inner ℝ (q.gradient (LipschitzWith.dist_right o) w) (q.closedGradient v w))

lemma radial_power_integral (hz : IsCycle T) (o : X) (v : q.Sobolev) {β : ℝ} (hb : 0 < β)
    (hn : (k+1:ℝ)*β = 1+2*β)
    (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
    (hm : ∀ b : ℝ, 0 < b → MemLp (q.inclusion v) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT))
    (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ R : q.Sobolev,
      (q.inclusion R : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT] (fun x => (q.inclusion v x)^γ) ∧
      (q.closedGradient R : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => (γ*(q.inclusion v (q.atlasParam w))^(γ-1)) • q.closedGradient v w))
    (hr : ∀ (g : X → ℝ) (K : ℝ≥0), LipschitzWith K g →
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → q.radialVariation o g ≤ (k+1:ℝ)*q.sweptMass o g) :
    Integrable (q.radialPowerIntegrand o v β) q.atlasMeasure ∧
      (∫ x, (q.inclusion v x)^(2+4*β) ∂MassMeasure.currentMassMeasure hT) ≤
        ∫ w, q.radialPowerIntegrand o v β w ∂q.atlasMeasure := by
  obtain ⟨ψ,hψ,hDψ⟩ := hpow (2+4*β) (by linarith)
  have hψ0 : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion ψ x := by
    filter_upwards [hψ,hv] with x hx hp
    rw [hx]; exact Real.rpow_nonneg hp _
  have hrad := q.radialDefect_nonpos hz o hr ψ hψ0
  have hp := (Lp.memLp (q.inclusion ψ)).comp_measurePreserving q.atlas_preserving
  have hA := (q.memLp_radialA o).integrable_mul hp
  have hB : Integrable (fun w => inner ℝ (q.radialB o w) (q.closedGradient ψ w)) q.atlasMeasure := by
    apply (L2.integrable_inner (𝕜 := ℝ) ((q.memLp_radialB o).toLp _) (q.closedGradient ψ)).congr
    filter_upwards [(q.memLp_radialB o).coeFn_toLp] with w hw
    rw [hw]
  have hAB : Integrable (fun w => q.radialA o w*q.inclusion ψ (q.atlasParam w)+inner ℝ (q.radialB o w) (q.closedGradient ψ w)) q.atlasMeasure := hA.add hB
  have hu := (ClosedCalculus.power_memLp_two hv hm (a := 2+4*β) (by positivity)).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have huA := q.atlas_preserving.integrable_comp_of_integrable hu
  change Integrable (fun w => (q.inclusion v (q.atlasParam w))^(2+4*β)) q.atlasMeasure at huA
  have he : q.radialPowerIntegrand o v β =ᵐ[q.atlasMeasure]
      (fun w => (q.inclusion v (q.atlasParam w))^(2+4*β)-(k+1:ℝ)⁻¹*
        (q.radialA o w*q.inclusion ψ (q.atlasParam w)+inner ℝ (q.radialB o w) (q.closedGradient ψ w))) := by
    filter_upwards [q.atlas_preserving.quasiMeasurePreserving.ae hψ,hDψ] with w hw hd
    dsimp only [radialPowerIntegrand,radialA,radialB]
    rw [hw,hd,real_inner_smul_left,real_inner_smul_right]
    rw [show (2:ℝ)+4*β-1 = 1+4*β by ring]
    have hn0 : (k+1:ℝ) ≠ 0 := by positivity
    field_simp [hn0]
    have hn' : (k+1:ℝ)*(2*β) = 2+4*β := by nlinarith [hn]
    linear_combination -dist o (q.atlasParam w)*(q.inclusion v (q.atlasParam w))^(1+4*β)*
      inner ℝ (q.gradient (LipschitzWith.dist_right o) w) (q.closedGradient v w)*hn'
  refine ⟨(huA.sub (hAB.const_mul _)).congr he.symm,?_⟩
  have hi := integral_congr_ae he
  rw [integral_sub huA (hAB.const_mul _),integral_const_mul,←q.radialDefect_eq_integral] at hi
  have hAt := integral_map (μ := q.atlasMeasure) (f := (fun x => (q.inclusion v x)^(2+4*β))) q.atlas_preserving.measurable.aemeasurable
    (by rw [q.atlas_preserving.map_eq]; exact hu.aestronglyMeasurable)
  rw [q.atlas_preserving.map_eq] at hAt
  rw [←hAt] at hi
  rw [hi]
  have hnonpos : (k+1:ℝ)⁻¹*q.radialDefect o ψ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hrad
  linarith
end CAT0Fillings.ChartGeometry
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.OppositeAverage

lemma radial_cauchy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R D : E) {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hR : ‖R‖ ≤ 1) :
    A*Real.sqrt (1-‖R‖^2)-C*inner ℝ R D ≤ Real.sqrt (A^2+C^2*‖D‖^2) := by
  have hR2 : ‖R‖^2 ≤ 1 := by nlinarith [norm_nonneg R]
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1-‖R‖^2)
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ A^2+C^2*‖D‖^2)
  have hab := abs_real_inner_le_norm R D
  have hi : -inner ℝ R D ≤ ‖R‖*‖D‖ := (neg_le_abs _).trans hab
  have h1 : A*Real.sqrt (1-‖R‖^2)-C*inner ℝ R D ≤
      A*Real.sqrt (1-‖R‖^2)+C*‖R‖*‖D‖ := by nlinarith [mul_le_mul_of_nonneg_left hi hC]
  apply h1.trans
  have h2 : (A*Real.sqrt (1-‖R‖^2)+C*‖R‖*‖D‖)^2 ≤ A^2+C^2*‖D‖^2 := by
    nlinarith [sq_nonneg (A*‖R‖-C*‖D‖*Real.sqrt (1-‖R‖^2))]
  have hp : 0 ≤ A*Real.sqrt (1-‖R‖^2)+C*‖R‖*‖D‖ := by positivity
  nlinarith [Real.sqrt_nonneg (A^2+C^2*‖D‖^2)]

lemma radial_power_cauchy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R D : E) {u β : ℝ} (hu : 0 ≤ u) (hb : 0 < β) (hR : ‖R‖ ≤ 1) :
    u^(2+4*β)*Real.sqrt (1-‖R‖^2)-2*β*u^(1+4*β)*inner ℝ R D ≤
      u^(1+3*β)*Real.sqrt (u^(2+2*β)+4*β^2*u^(2*β)*‖D‖^2) := by
  have hm : u^(1+3*β)*u^(1+β) = u^(2+4*β) := by
    rw [←Real.rpow_add' hu (by linarith : 1+3*β+(1+β) ≠ 0)]
    congr 1
    ring
  have hm' : u^(1+3*β)*u^β = u^(1+4*β) := by
    rw [←Real.rpow_add' hu (by linarith : 1+3*β+β ≠ 0)]
    congr 1
    ring
  have hsq : (u^(1+β))^2 = u^(2+2*β) := by
    rw [←Real.rpow_mul_natCast hu]
    congr 1
    ring
  have hsq' : (u^β)^2 = u^(2*β) := by
    rw [←Real.rpow_mul_natCast hu]
    congr 1
    ring
  have hh := mul_le_mul_of_nonneg_left (radial_cauchy R D (A := u^(1+β)) (C := 2*β*u^β)
    (Real.rpow_nonneg hu (1+β)) (mul_nonneg (by positivity) (Real.rpow_nonneg hu β)) hR)
    (Real.rpow_nonneg hu (1+3*β))
  rw [hsq,mul_pow,hsq'] at hh
  have he : (2*β)^2 = 4*β^2 := by ring
  rw [he] at hh
  rw [mul_sub,←mul_assoc,hm] at hh
  rw [show u^(1+3*β)*(2*β*u^β*inner ℝ R D) =
    2*β*(u^(1+3*β)*u^β)*inner ℝ R D by ring,hm'] at hh
  exact hh

lemma integral_cauchy_square {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) :
    (∫ x, f x*g x ∂μ)^2 ≤ (∫ x, (f x)^2 ∂μ)*(∫ x, (g x)^2 ∂μ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2)
    (Real.holderConjugate_iff.mpr ⟨by norm_num,by norm_num⟩) hf0 hg0
    (by simpa using hf) (by simpa using hg)
  norm_num only [Real.rpow_two,one_div] at h
  simp only [←Real.sqrt_eq_rpow] at h
  have hi0 : 0 ≤ ∫ x, f x*g x ∂μ := integral_nonneg_of_ae (by
    filter_upwards [hf0,hg0] with x hx hy using mul_nonneg hx hy)
  have h1 : 0 ≤ ∫ x, (f x)^2 ∂μ := integral_nonneg fun point => sq_nonneg (f point)
  have h2 : 0 ≤ ∫ x, (g x)^2 ∂μ := integral_nonneg fun point => sq_nonneg (g point)
  calc
    _ ≤ (Real.sqrt (∫ x, (f x)^2 ∂μ)*Real.sqrt (∫ x, (g x)^2 ∂μ))^2 := by
      exact (sq_le_sq₀ hi0 (by positivity)).mpr h
    _ = _ := by rw [mul_pow,Real.sq_sqrt h1,Real.sq_sqrt h2]
end CAT0Fillings.OppositeAverage
end

end OAI
