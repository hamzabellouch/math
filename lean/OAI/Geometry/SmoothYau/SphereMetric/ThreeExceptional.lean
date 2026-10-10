import Mathlib
import OAI.Geometry.SmoothYau.Estimates.NormPowerVariableWeightControl
import OAI.Geometry.SmoothYau.NodalMeasure.ExistsSupportedBoxNodalQuasimodes

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
local instance threePacketNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threePacketContinuousSMul : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul

def threePacketA : (Fin 3 → ℝ) → ℂ :=
  threeComplexPower (productAxis 0) (productAxis 1) 1 ∘ threeNormalInv ∘ normalWaveEquiv
def threePacketB : (Fin 3 → ℝ) → ℂ :=
  fun y => (threeCouplingRadius:ℂ)*(threeComplexPower (productAxis 0) (productAxis 2) 1 (threeNormalInv (normalWaveEquiv y)))
def threePacketWeight (φ : ThreeManifold → ℝ) (k : ℕ) (y : Fin 3 → ℝ) : ℝ :=
  Real.exp (productWaveFrequency k*φ (threeNormalInv (normalWaveEquiv y)))+‖threePacketA y‖^k+‖threePacketB y‖^k
def threeExceptionalInChart (φ : ThreeManifold → ℝ) (k : ℕ) : Set (Fin 3 → ℝ) :=
  {y | ‖threePacketA y‖^k+‖threePacketB y‖^k ≤ (productWaveFrequency k)^6*
    Real.exp (productWaveFrequency k*φ (threeNormalInv (normalWaveEquiv y)))}
lemma threePacketA_smooth : ContDiff ℝ ∞ threePacketA :=
  ((threeComplexPower_chart_smooth _ _ _ _).comp threeNormalEquiv.contDiff).comp normalWaveEquiv.contDiff
lemma threePacketB_smooth : ContDiff ℝ ∞ threePacketB :=
  contDiff_const.mul (((threeComplexPower_chart_smooth _ _ _ _).comp threeNormalEquiv.contDiff).comp normalWaveEquiv.contDiff)
lemma threePacketA_norm (y : Fin 3 → ℝ) :
    ‖threePacketA y‖=‖productA (threeNormalInv (normalWaveEquiv y)).1‖ := by
  simp only [threePacketA,Function.comp_apply,threeComplexPower,pow_one,norm_mul,Circle.norm_coe,mul_one]
  rfl
lemma threePacketB_norm (y : Fin 3 → ℝ) :
    ‖threePacketB y‖=threeCouplingRadius*‖productB (threeNormalInv (normalWaveEquiv y)).1‖ := by
  simp only [threePacketB,threeComplexPower,pow_one,norm_mul,Circle.norm_coe,mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (show 0<threeCouplingRadius by norm_num [threeCouplingRadius])]
  rfl
lemma threePacketWeight_lower (φ : ThreeManifold → ℝ) (k : ℕ) (y : Fin 3 → ℝ) :
    Real.exp (productWaveFrequency k*φ (threeNormalInv (normalWaveEquiv y))) ≤ threePacketWeight φ k y := by
  dsimp [threePacketWeight]
  nlinarith [pow_nonneg (norm_nonneg (threePacketA y)) k,pow_nonneg (norm_nonneg (threePacketB y)) k]
lemma threePacketWeight_upper (φ : ThreeManifold → ℝ) (k : ℕ) (y : Fin 3 → ℝ)
    (hy : y∈threeExceptionalInChart φ k) :
    threePacketWeight φ k y≤(1+(productWaveFrequency k)^6)*
      Real.exp (productWaveFrequency k*φ (threeNormalInv (normalWaveEquiv y))) := by
  dsimp [threeExceptionalInChart] at hy
  dsimp [threePacketWeight]
  nlinarith
lemma threePacket_radius_bound (k : ℕ) (y : Fin 3 → ℝ) :
    threeGlobalRadius (threeNormalInv (normalWaveEquiv y))^k≤‖threePacketA y‖^k+‖threePacketB y‖^k := by
  rw [threePacketA_norm,threePacketB_norm]
  have hr : 0≤threeCouplingRadius := by norm_num [threeCouplingRadius]
  dsimp [threeGlobalRadius]
  rcases le_total ‖productA (threeNormalInv (normalWaveEquiv y)).1‖
    (threeCouplingRadius*‖productB (threeNormalInv (normalWaveEquiv y)).1‖) with h|h
  · rw [max_eq_right h]
    exact le_add_of_nonneg_left (by positivity)
  · rw [max_eq_left h]
    exact le_add_of_nonneg_right (by positivity)
lemma threePacket_back_eq (k : ℕ) :
    (threeCoupled threeCouplingRadius k ∘ threeNormalInv) ∘ normalWaveEquiv =
      (fun y => (threePacketA y^k).re+(threePacketB y^k).re) := by
  funext y
  exact threeCoupled_split_powers _ _ _
lemma threePacket_background_input_bounds {φ : ThreeManifold → ℝ}
    (hφ : ContDiff ℝ ∞ (φ ∘ threeNormalInv)) {S : Set (Fin 3 → ℝ)} (hS : IsCompact S) :
    ∃ T>0, ∃ H>0, ∀ k : ℕ, 2≤k →
      Differentiable ℝ (threePacketWeight φ k) ∧ (∀ y, 0<threePacketWeight φ k y) ∧
      (∀ y∈S, ∀ j≤2,
        ‖iteratedFDeriv ℝ j ((threeCoupled threeCouplingRadius k ∘ threeNormalInv) ∘ normalWaveEquiv) y‖ ≤
          T*(productWaveFrequency k)^j*threePacketWeight φ k y) ∧
      (∀ y∈S, ‖fderiv ℝ (threePacketWeight φ k) y‖ ≤ H*productWaveFrequency k*threePacketWeight φ k y) := by
  obtain ⟨T,hT,H,hH,hinputs⟩ := two_power_variable_weight_control threePacketA_smooth threePacketB_smooth
    (hφ.comp normalWaveEquiv.contDiff) hS
  refine ⟨T,hT,H,hH,?_⟩
  intro k hk
  rw [threePacket_back_eq]
  exact hinputs k hk

lemma threeCoupled_abs_le_radius (k : ℕ) (p : ThreeManifold) :
    |threeCoupled threeCouplingRadius k p|≤2*threeGlobalRadius p^k := by
  rw [threeCoupled_split_powers]
  have hh (i : Fin 3) : ‖threeComplexPower (productAxis 0) (productAxis i) 1 p‖=‖planarLinear (productAxis 0) (productAxis i) p.1‖ := by
    simp [threeComplexPower]
  have hr : 0≤threeCouplingRadius := by norm_num [threeCouplingRadius]
  have h1 : ‖threeComplexPower (productAxis 0) (productAxis 1) 1 p‖ ≤ threeGlobalRadius p := by
    rw [hh]; exact le_max_left _ _
  have h2 : ‖(threeCouplingRadius:ℂ)*threeComplexPower (productAxis 0) (productAxis 2) 1 p‖≤threeGlobalRadius p := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,hh]
    exact le_max_right _ _
  have hb1 := Complex.abs_re_le_norm ((threeComplexPower (productAxis 0) (productAxis 1) 1 p)^k)
  have hb2 := Complex.abs_re_le_norm (((threeCouplingRadius:ℂ)*threeComplexPower (productAxis 0) (productAxis 2) 1 p)^k)
  rw [norm_pow] at hb1 hb2
  have hp1 := hb1.trans (pow_le_pow_left₀ (norm_nonneg _) h1 k)
  have hp2 := hb2.trans (pow_le_pow_left₀ (norm_nonneg _) h2 k)
  exact (abs_add_le _ _).trans (by linarith)

lemma three_background_sign_small (φ : ThreeManifold → ℝ) {K : Set NormalWaveSpace}
    {δ : ℝ} (hδ : 0<δ) (hgap : ∀ y∈K, threeGlobalLog (threeNormalInv y)+δ≤φ (threeNormalInv y))
    {c : ℝ} (hc : 0<c) :
    ∀ᶠ k : ℕ in atTop, ∀ y∈K, |threeCoupled threeCouplingRadius k (threeNormalInv y)|≤
      c*Real.exp (productWaveFrequency k*φ (threeNormalInv y)) := by
  let ρ := Real.exp (-δ)
  have hρ : 0<ρ := Real.exp_pos _
  have hρ1 : ρ<1 := Real.exp_lt_one_iff.mpr (by linarith)
  have ht : Tendsto (fun k : ℕ => 2*ρ^k) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ.le hρ1).const_mul 2
  filter_upwards [eventually_ge_atTop (1:ℕ),ht.eventually (Iio_mem_nhds hc)] with k hk hsmall
  intro y hy
  have hb := productWaveFrequency_bounds hk
  have hrad := three_positive_envelope_gap (threeNormalInv y) hk (hgap y hy)
  have he : Real.exp (productWaveFrequency k*(φ (threeNormalInv y)-δ))≤
      ρ^k*Real.exp (productWaveFrequency k*φ (threeNormalInv y)) := by
    dsimp [ρ]
    rw [←Real.exp_nat_mul,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hb.1 hδ.le]
  calc
    _ ≤ 2*threeGlobalRadius (threeNormalInv y)^k := threeCoupled_abs_le_radius _ _
    _ ≤ 2*(ρ^k*Real.exp (productWaveFrequency k*φ (threeNormalInv y))) := mul_le_mul_of_nonneg_left (hrad.trans he) (by norm_num)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hsmall.le (Real.exp_pos (productWaveFrequency k*φ (threeNormalInv y))).le]

lemma three_exceptional_eventually_coverage (φ : ThreeManifold → ℝ) {K : Set NormalWaveSpace}
    {δ : ℝ} (hδ : 0<δ)
    (hgap : ∀ y∉K, φ (threeNormalInv y)≤threeGlobalLog (threeNormalInv y)-δ) :
    ∀ᶠ k : ℕ in atTop, threeExceptionalInChart φ k⊆normalWaveEquiv.symm '' K := by
  let ρ := Real.exp (-δ)
  have hρ : 0<ρ := Real.exp_pos _
  have hρ1 : ρ<1 := Real.exp_lt_one_iff.mpr (by linarith)
  have ht : Tendsto (fun k : ℕ => 12800*((k:ℝ)^6*ρ^k)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_const_mul_const_pow_of_lt_one 6 hρ.le hρ1).const_mul 12800
  filter_upwards [eventually_ge_atTop (1:ℕ),ht.eventually (Iio_mem_nhds zero_lt_one)] with k hk hsmall
  intro y hy
  refine ⟨normalWaveEquiv y,?_,normalWaveEquiv.symm_apply_apply y⟩
  by_contra hout
  have hν := productWaveFrequency_bounds hk
  have he := three_negative_envelope_gap (threeNormalInv (normalWaveEquiv y)) hk hδ.le (hgap _ hout)
  have hν0 : 0≤productWaveFrequency k := (Nat.cast_nonneg _).trans hν.1
  have hν6 := pow_le_pow_left₀ hν0 hν.2 6
  have hpos := pow_pos (threeGlobalRadius_pos (threeNormalInv (normalWaveEquiv y))) k
  have hb := (threePacket_radius_bound k y).trans hy
  have hh := hb.trans (mul_le_mul_of_nonneg_left he (pow_nonneg hν0 6))
  have heρ : Real.exp (-(k:ℝ)*δ)=ρ^k := by dsimp [ρ]; rw [←Real.exp_nat_mul]; congr 1; ring
  rw [heρ] at hh
  have hbig : (productWaveFrequency k)^6*(200*threeGlobalRadius (threeNormalInv (normalWaveEquiv y))^k*ρ^k) ≤
      (12800*((k:ℝ)^6*ρ^k))*threeGlobalRadius (threeNormalInv (normalWaveEquiv y))^k := by
    calc
      _ ≤ (2*(k:ℝ))^6*(200*threeGlobalRadius (threeNormalInv (normalWaveEquiv y))^k*ρ^k) :=
        mul_le_mul_of_nonneg_right hν6 (by positivity)
      _ = _ := by ring
  have hbad := hh.trans hbig
  have hs := mul_lt_mul_of_pos_right hsmall hpos
  norm_num at hs
  exact (not_lt_of_ge hbad) hs
end


section
open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal
local instance threeQuasimodeNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeQuasimodeContinuousSMul : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
lemma threeNormalInv_injective : Function.Injective threeNormalInv := by
  intro x y h
  have hh := congrArg (chartAt ThreeModel threeProfileCenter) h
  dsimp [threeNormalInv,Function.comp_def] at hh
  rw [(chartAt ThreeModel threeProfileCenter).right_inv (by rw [three_chart_target]; trivial),
    (chartAt ThreeModel threeProfileCenter).right_inv (by rw [three_chart_target]; trivial)] at hh
  exact threeNormalEquiv.injective hh

theorem exists_three_chart_quasimodes :
    ∃ R : ℝ, 0<R ∧ ThreeCleanBall R ∧ ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
      IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric ∈ N ∧
      ∀ g ∈ N, ∀ a b : ℝ, 0<a → a<b → b<R/2 → ∀ A : ℝ,
      ∃ Φ : ThreeManifold → ℝ, ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ Φ ∧
        ContDiff ℝ ∞ (Φ ∘ threeNormalInv) ∧ ∃ δ>0,
        (∀ y∈closedBall 0 a, threeGlobalLog (threeNormalInv y)+δ<Φ (threeNormalInv y)) ∧
        ∃ I : Box (Fin 3), normalWaveEquiv '' Box.Icc I ⊆ closedBall 0 a ∧
        ∃ partition : TaggedPrepartition I, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
          (∀ J∈partition, 0<ℓ J) ∧ ∃ ε>0,
        ∀ m D : ℕ, ∃ C>0, ∀ᶠ k : ℕ in atTop,
          ∃ u : NormalWaveSpace → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
            tsupport u ⊆ ball 0 ((b+R/2)/2) ∧
            (∀ x : NormalWaveSpace, ∀ j ≤ m,
              ‖iteratedFDeriv ℝ j u x‖ ≤ C*(productWaveFrequency k)^(j+4)*
                Real.exp (productWaveFrequency k*Φ (threeNormalInv x)) ∧
              ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami (threeNormalMetricOf g) u y+
                  productFrequency k*u y) x‖ ≤ C*((productWaveFrequency k)^(D+1))⁻¹*
                Real.exp (productWaveFrequency k*Φ (threeNormalInv x))) ∧
            (∀ y∈threeExceptionalInChart Φ k,
              1/(productWaveFrequency k)^110 ≤ ‖realWaveJet (productWaveFrequency k) (threePacketWeight Φ k y)
                (((threeCoupled threeCouplingRadius k ∘ threeNormalInv)+u) ∘ normalWaveEquiv) y‖) ∧
            ENNReal.ofReal (A*productWaveFrequency k) < SignTests.signCertificate
              (fun z : {J : Box (Fin 3) // J∈partition.boxes} => Box.Ioo z.val)
              (fun z => ε/(productWaveFrequency k*ℓ z.val))
              (((threeCoupled threeCouplingRadius k ∘ threeNormalInv)+u) ∘ normalWaveEquiv) ∧
            ENNReal.ofReal (A*productWaveFrequency k) < 36*Measure.hausdorffMeasure 2
              ((⋃ z : {J : Box (Fin 3) // J∈partition.boxes}, Box.Ioo z.val) ∩
                {x | ((threeCoupled threeCouplingRadius k ∘ threeNormalInv)+u) (normalWaveEquiv x)=0}) := by
  obtain ⟨C₀,R,hR,hclean,N,hN,h0N,hprofiles⟩ := exists_three_robust_global_profile_family
  refine ⟨R,hR,hclean,N,hN,h0N,?_⟩
  intro g hg a b ha hab hbR A
  let G := threeNormalMetricOf g
  let K : Set NormalWaveSpace := closedBall 0 b
  let O : Set NormalWaveSpace := ball 0 ((b+R/2)/2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hO : IsOpen O := isOpen_ball
  have hKO : K⊆O := closedBall_subset_ball (by linarith)
  obtain ⟨ε,hε,hε1,p₀,hp₀,hproduce⟩ :=
    exists_supported_box_nodal_quasimodes_subregions G hK hO hKO
  let c := p₀/(16*ε)
  have hc : 0<c := div_pos hp₀ (mul_pos (by norm_num) hε)
  obtain ⟨δ,hδ,I,hIa,hprofiles⟩ := hprofiles g hg a b ha hab hbR
  obtain ⟨Φ,hΦ,hφ,hsp,hstrict,hin,hout,hmass⟩ := hprofiles (A/c)
  let φ := Φ ∘ threeNormalInv
  have hIK : normalWaveEquiv '' Box.Icc I⊆K :=
    hIa.trans (closedBall_subset_closedBall hab.le)
  obtain ⟨partition,hπ,ℓ,hℓ,hproduce⟩ := hproduce φ hφ
    (fun y hy _ => (hstrict y hy).2)
    (fun y hy hd => ((hstrict y hy).1 ((coordinateMetricGradient_eq_zero_iff G φ y).mpr hd)).elim)
    I hIK
  have hmass' : A<c*(∫ x in Box.Icc I, profileFrequencyScale G φ (normalWaveEquiv x)) :=
    (div_lt_iff₀ hc).mp hmass |>.trans_eq (mul_comm _ _)
  obtain ⟨r,hr⟩ := (hK.image normalWaveEquiv.symm.continuous).isBounded.subset_closedBall (0:Fin 3 → ℝ)
  let S : Set (Fin 3 → ℝ) := closedBall 0 r
  obtain ⟨T,hT,H,hH,hinputs⟩ := threePacket_background_input_bounds hφ (isCompact_closedBall (0:Fin 3 → ℝ) r)
  refine ⟨Φ,hΦ,hφ,δ/2,half_pos hδ,hin,I,hIa,partition,hπ,ℓ,hℓ,ε,hε,?_⟩
  intro m D
  obtain ⟨c₀,hc₀,C,hC,N₀,hN₀,hproduce⟩ := hproduce m D T H hT.le hH.le
  refine ⟨C,hC,?_⟩
  have hfreq := productWaveFrequency_tendsto.eventually (eventually_ge_atTop N₀)
  have hsign := three_background_sign_small Φ (half_pos hδ)
    (K:=normalWaveEquiv '' Box.Icc I) (fun y hy => (hin y (hIa hy)).le) hc₀
  have hexcept := three_exceptional_eventually_coverage Φ hδ (K:=K) (fun y hy =>
    hout (threeNormalInv y) (by
      rintro ⟨x,hx,hxy⟩
      exact hy (threeNormalInv_injective hxy ▸ hx)))
  filter_upwards [hfreq,eventually_ge_atTop (2:ℕ),hsign,hexcept] with k hk hk2 hsign hexcept
  obtain ⟨hW,hW0,hwjet,hlog⟩ := hinputs k hk2
  have hw : ContDiff ℝ ∞ (threeCoupled threeCouplingRadius k ∘ threeNormalInv) :=
    (threeCoupled_chart_smooth _ _ _).comp threeNormalEquiv.contDiff
  obtain ⟨u,hu,huc,hus,hder,hjet,hscore,hnod⟩ := hproduce (productWaveFrequency k) hk S
    (convex_closedBall _ _) (threeExceptionalInChart Φ k) (hexcept.trans hr) hexcept
    (threeCoupled threeCouplingRadius k ∘ threeNormalInv) hw
    (threePacketWeight Φ k) hW hW0 (fun y _ => threePacketWeight_lower Φ k y)
    (fun y hy => threePacketWeight_upper Φ k y hy) hwjet hlog hsign
  have hν : 0<productWaveFrequency k := zero_lt_one.trans_le (hN₀.trans hk)
  have hle : A*productWaveFrequency k ≤ c*productWaveFrequency k*
      (∫ x in Box.Icc I, profileFrequencyScale G φ (normalWaveEquiv x)) := by
    nlinarith [mul_pos (sub_pos.mpr hmass') hν]
  refine ⟨u,hu,huc,hus,?_,hjet,(ENNReal.ofReal_le_ofReal hle).trans_lt hscore,
    (ENNReal.ofReal_le_ofReal hle).trans_lt hnod⟩
  simpa only [productWaveFrequency_equation,G,φ,Function.comp_apply] using hder
end


section
open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal

theorem exists_three_chart_quasimodes_with_gaps :
    ∃ R : ℝ, 0<R ∧ ThreeCleanBall R ∧ ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
      IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric ∈ N ∧
      ∀ g ∈ N, ∀ a b : ℝ, 0<a → a<b → b<R/2 → ∀ A : ℝ,
      ∃ Φ : ThreeManifold → ℝ, ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ Φ ∧
        ContDiff ℝ ∞ (Φ ∘ threeNormalInv) ∧ ∃ δ>0,
        (∀ y∈closedBall 0 a, threeGlobalLog (threeNormalInv y)+δ<Φ (threeNormalInv y)) ∧
        (∀ p ∉ threeNormalInv '' closedBall 0 b, Φ p≤threeGlobalLog p-2*δ) ∧
        ∃ I : Box (Fin 3), normalWaveEquiv '' Box.Icc I ⊆ closedBall 0 a ∧
        ∃ partition : TaggedPrepartition I, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
          (∀ J∈partition, 0<ℓ J) ∧ ∃ ε>0,
        ∀ m D : ℕ, ∃ C>0, ∀ᶠ k : ℕ in atTop,
          ∃ u : NormalWaveSpace → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
            tsupport u ⊆ ball 0 ((b+R/2)/2) ∧
            (∀ x : NormalWaveSpace, ∀ j ≤ m,
              ‖iteratedFDeriv ℝ j u x‖ ≤ C*(productWaveFrequency k)^(j+4)*
                Real.exp (productWaveFrequency k*Φ (threeNormalInv x)) ∧
              ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami (threeNormalMetricOf g) u y+
                  productFrequency k*u y) x‖ ≤ C*((productWaveFrequency k)^(D+1))⁻¹*
                Real.exp (productWaveFrequency k*Φ (threeNormalInv x))) ∧
            (∀ y∈threeExceptionalInChart Φ k,
              1/(productWaveFrequency k)^110 ≤ ‖realWaveJet (productWaveFrequency k) (threePacketWeight Φ k y)
                (((threeCoupled threeCouplingRadius k ∘ threeNormalInv)+u) ∘ normalWaveEquiv) y‖) ∧
            ENNReal.ofReal (A*productWaveFrequency k) < SignTests.signCertificate
              (fun z : {J : Box (Fin 3) // J∈partition.boxes} => Box.Ioo z.val)
              (fun z => ε/(productWaveFrequency k*ℓ z.val))
              (((threeCoupled threeCouplingRadius k ∘ threeNormalInv)+u) ∘ normalWaveEquiv) ∧
            ENNReal.ofReal (A*productWaveFrequency k) < 36*Measure.hausdorffMeasure 2
              ((⋃ z : {J : Box (Fin 3) // J∈partition.boxes}, Box.Ioo z.val) ∩
                {x | ((threeCoupled threeCouplingRadius k ∘ threeNormalInv)+u) (normalWaveEquiv x)=0}) := by
  obtain ⟨C₀,R,hR,hclean,N,hN,h0N,hprofiles⟩ := exists_three_robust_global_profile_family
  refine ⟨R,hR,hclean,N,hN,h0N,?_⟩
  intro g hg a b ha hab hbR A
  let G := threeNormalMetricOf g
  let K : Set NormalWaveSpace := closedBall 0 b
  let O : Set NormalWaveSpace := ball 0 ((b+R/2)/2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hO : IsOpen O := isOpen_ball
  have hKO : K⊆O := closedBall_subset_ball (by linarith)
  obtain ⟨ε,hε,hε1,p₀,hp₀,hproduce⟩ :=
    exists_supported_box_nodal_quasimodes_subregions G hK hO hKO
  let c := p₀/(16*ε)
  have hc : 0<c := div_pos hp₀ (mul_pos (by norm_num) hε)
  obtain ⟨δ,hδ,I,hIa,hprofiles⟩ := hprofiles g hg a b ha hab hbR
  obtain ⟨Φ,hΦ,hφ,hsp,hstrict,hin,hout,hmass⟩ := hprofiles (A/c)
  let φ := Φ ∘ threeNormalInv
  have hIK : normalWaveEquiv '' Box.Icc I⊆K :=
    hIa.trans (closedBall_subset_closedBall hab.le)
  obtain ⟨partition,hπ,ℓ,hℓ,hproduce⟩ := hproduce φ hφ
    (fun y hy _ => (hstrict y hy).2)
    (fun y hy hd => ((hstrict y hy).1 ((coordinateMetricGradient_eq_zero_iff G φ y).mpr hd)).elim)
    I hIK
  have hmass' : A<c*(∫ x in Box.Icc I, profileFrequencyScale G φ (normalWaveEquiv x)) :=
    (div_lt_iff₀ hc).mp hmass |>.trans_eq (mul_comm _ _)
  obtain ⟨r,hr⟩ := (hK.image normalWaveEquiv.symm.continuous).isBounded.subset_closedBall (0:Fin 3 → ℝ)
  let S : Set (Fin 3 → ℝ) := closedBall 0 r
  obtain ⟨T,hT,H,hH,hinputs⟩ := threePacket_background_input_bounds hφ (isCompact_closedBall (0:Fin 3 → ℝ) r)
  refine ⟨Φ,hΦ,hφ,δ/2,half_pos hδ,hin,(by simpa only [mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)] using hout),I,hIa,partition,hπ,ℓ,hℓ,ε,hε,?_⟩
  intro m D
  obtain ⟨c₀,hc₀,C,hC,N₀,hN₀,hproduce⟩ := hproduce m D T H hT.le hH.le
  refine ⟨C,hC,?_⟩
  have hfreq := productWaveFrequency_tendsto.eventually (eventually_ge_atTop N₀)
  have hsign := three_background_sign_small Φ (half_pos hδ)
    (K:=normalWaveEquiv '' Box.Icc I) (fun y hy => (hin y (hIa hy)).le) hc₀
  have hexcept := three_exceptional_eventually_coverage Φ hδ (K:=K) (fun y hy =>
    hout (threeNormalInv y) (by
      rintro ⟨x,hx,hxy⟩
      exact hy (threeNormalInv_injective hxy ▸ hx)))
  filter_upwards [hfreq,eventually_ge_atTop (2:ℕ),hsign,hexcept] with k hk hk2 hsign hexcept
  obtain ⟨hW,hW0,hwjet,hlog⟩ := hinputs k hk2
  have hw : ContDiff ℝ ∞ (threeCoupled threeCouplingRadius k ∘ threeNormalInv) :=
    (threeCoupled_chart_smooth _ _ _).comp threeNormalEquiv.contDiff
  obtain ⟨u,hu,huc,hus,hder,hjet,hscore,hnod⟩ := hproduce (productWaveFrequency k) hk S
    (convex_closedBall _ _) (threeExceptionalInChart Φ k) (hexcept.trans hr) hexcept
    (threeCoupled threeCouplingRadius k ∘ threeNormalInv) hw
    (threePacketWeight Φ k) hW hW0 (fun y _ => threePacketWeight_lower Φ k y)
    (fun y hy => threePacketWeight_upper Φ k y hy) hwjet hlog hsign
  have hν : 0<productWaveFrequency k := zero_lt_one.trans_le (hN₀.trans hk)
  have hle : A*productWaveFrequency k ≤ c*productWaveFrequency k*
      (∫ x in Box.Icc I, profileFrequencyScale G φ (normalWaveEquiv x)) := by
    nlinarith [mul_pos (sub_pos.mpr hmass') hν]
  refine ⟨u,hu,huc,hus,?_,hjet,(ENNReal.ofReal_le_ofReal hle).trans_lt hscore,
    (ENNReal.ofReal_le_ofReal hle).trans_lt hnod⟩
  simpa only [productWaveFrequency_equation,G,φ,Function.comp_apply] using hder
end


open Set Filter Function Manifold Metric
open scoped Topology ContDiff
def threeExceptional (φ : ThreeManifold → ℝ) (k : ℕ) : Set ThreeManifold :=
  {p | productWeight threeCouplingRadius k p ≤ productWaveFrequency k^6*Real.exp (productWaveFrequency k*φ p)}
lemma three_global_radius_weight_bound (k : ℕ) (p : ThreeManifold) :
    threeGlobalRadius p^k≤productWeight threeCouplingRadius k p ∧
    productWeight threeCouplingRadius k p≤2*threeGlobalRadius p^k := by
  have hr : 0≤threeCouplingRadius := by norm_num [threeCouplingRadius]
  have h1 := pow_le_pow_left₀ (norm_nonneg (productA p.1)) (le_max_left ‖productA p.1‖ (threeCouplingRadius*‖productB p.1‖)) k
  have h2 := pow_le_pow_left₀ (mul_nonneg hr (norm_nonneg (productB p.1))) (le_max_right ‖productA p.1‖ (threeCouplingRadius*‖productB p.1‖)) k
  rw [mul_pow] at h2
  constructor
  · dsimp [threeGlobalRadius,productWeight]
    rcases le_total ‖productA p.1‖ (threeCouplingRadius*‖productB p.1‖) with h|h
    · rw [max_eq_right h,mul_pow]; exact le_add_of_nonneg_left (by positivity)
    · rw [max_eq_left h]; exact le_add_of_nonneg_right (by positivity)
  · dsimp [productWeight,threeGlobalRadius] at *; linarith
lemma threeWeight_le_packet (φ : ThreeManifold → ℝ) (k : ℕ) (y : Fin 3 → ℝ) :
    threeWeight φ k (threeNormalInv (normalWaveEquiv y))≤threePacketWeight φ k y := by
  dsimp [threeWeight,threePacketWeight]
  linarith [threePacket_radius_bound k y]
lemma three_packet_productWeight (k : ℕ) (y : Fin 3 → ℝ) :
    ‖threePacketA y‖^k+‖threePacketB y‖^k=productWeight threeCouplingRadius k (threeNormalInv (normalWaveEquiv y)) := by
  rw [threePacketA_norm,threePacketB_norm,mul_pow]; rfl
lemma three_exceptional_chart_iff (φ : ThreeManifold → ℝ) (k : ℕ) (y : Fin 3 → ℝ) :
    y∈threeExceptionalInChart φ k ↔ threeNormalInv (normalWaveEquiv y)∈threeExceptional φ k := by
  dsimp [threeExceptionalInChart,threeExceptional]
  rw [three_packet_productWeight]
lemma three_exceptional_global_coverage (φ : ThreeManifold → ℝ) {K : Set ThreeManifold}
    {δ : ℝ} (hδ : 0<δ)
    (hgap : ∀ y∉K, φ y≤threeGlobalLog y-δ) :
    ∀ᶠ k : ℕ in atTop, threeExceptional φ k⊆K := by
  let ρ := Real.exp (-δ)
  have hρ : 0<ρ := Real.exp_pos _
  have hρ1 : ρ<1 := Real.exp_lt_one_iff.mpr (by linarith)
  have ht : Tendsto (fun k : ℕ => 12800*((k:ℝ)^6*ρ^k)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_const_mul_const_pow_of_lt_one 6 hρ.le hρ1).const_mul 12800
  filter_upwards [eventually_ge_atTop (1:ℕ),ht.eventually (Iio_mem_nhds zero_lt_one)] with k hk hsmall
  intro y hy
  by_contra hout
  have hν := productWaveFrequency_bounds hk
  have he := three_negative_envelope_gap y hk hδ.le (hgap _ hout)
  have hν0 : 0≤productWaveFrequency k := (Nat.cast_nonneg _).trans hν.1
  have hν6 := pow_le_pow_left₀ hν0 hν.2 6
  have hpos := pow_pos (threeGlobalRadius_pos y) k
  have hb := (three_global_radius_weight_bound k y).1.trans hy
  have hh := hb.trans (mul_le_mul_of_nonneg_left he (pow_nonneg hν0 6))
  have heρ : Real.exp (-(k:ℝ)*δ)=ρ^k := by dsimp [ρ]; rw [←Real.exp_nat_mul]; congr 1; ring
  rw [heρ] at hh
  have hbig : (productWaveFrequency k)^6*(200*threeGlobalRadius y^k*ρ^k) ≤
      (12800*((k:ℝ)^6*ρ^k))*threeGlobalRadius y^k := by
    calc
      _ ≤ (2*(k:ℝ))^6*(200*threeGlobalRadius y^k*ρ^k) :=
        mul_le_mul_of_nonneg_right hν6 (by positivity)
      _ = _ := by ring
  have hbad := hh.trans hbig
  have hs := mul_lt_mul_of_pos_right hsmall hpos
  norm_num at hs
  exact (not_lt_of_ge hbad) hs

lemma three_core_exceptional {φ : ThreeManifold → ℝ} {δ : ℝ} (hδ : 0<δ)
    {F : Set ThreeManifold} (hgap : ∀ q∈F, threeGlobalLog q+δ≤φ q) :
    ∀ᶠ k : ℕ in atTop, F⊆threeExceptional φ k := by
  filter_upwards [eventually_ge_atTop (2:ℕ)] with k hk q hq
  have hk1 : 1≤k := by omega
  have hν := productWaveFrequency_bounds hk1
  have hν2 : 2≤productWaveFrequency k := by
    exact (show (2:ℝ)≤k by exact_mod_cast hk).trans hν.1
  have hν6 : 2≤productWaveFrequency k^6 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) hν2 6
    norm_num at hh
    linarith
  have hb := (three_global_radius_weight_bound k q).2
  have he := three_positive_envelope_gap q hk1 (hgap q hq)
  have he' : Real.exp (productWaveFrequency k*(φ q-δ))≤Real.exp (productWaveFrequency k*φ q) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  change productWeight threeCouplingRadius k q≤_
  exact hb.trans ((mul_le_mul_of_nonneg_left (he.trans he') (by norm_num)).trans
    (mul_le_mul_of_nonneg_right hν6 (Real.exp_pos _).le))

end YauCounterexamples
end

end OAI
