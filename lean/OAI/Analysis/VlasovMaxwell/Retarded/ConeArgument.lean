import Mathlib
import OAI.Analysis.VlasovMaxwell.Geometry.Sphere

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology NNReal
open scoped Topology ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

def coneArgument (T ε : ℝ) (x₀ : Vec) (p : ℝ × Vec) : ℝ :=
  ((T-p.1)^2 - ‖p.2-x₀‖^2)/ε

def coneCutoff (T ε : ℝ) (x₀ : Vec) (p : ℝ × Vec) : ℝ :=
  Real.smoothTransition (coneArgument T ε x₀ p)

lemma contDiff_coneArgument (T ε : ℝ) (x₀ : Vec) {k : ℕ∞} :
    ContDiff ℝ k (coneArgument T ε x₀) :=
  ((contDiff_const.sub contDiff_fst).pow 2 |>.sub
    ((contDiff_snd.sub contDiff_const).norm_sq ℝ)).div_const ε

lemma contDiff_coneCutoff (T ε : ℝ) (x₀ : Vec) {k : ℕ∞} :
    ContDiff ℝ k (coneCutoff T ε x₀) :=
  Real.smoothTransition.contDiff.comp (contDiff_coneArgument T ε x₀)

lemma deriv_transition_nonneg (u : ℝ) : 0 ≤ deriv Real.smoothTransition u :=
  Real.smoothTransition.monotone.deriv_nonneg

lemma deriv_transition_zero_neg {u : ℝ} (hu : u < 0) :
    deriv Real.smoothTransition u = 0 := by
  have he : Real.smoothTransition =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
    filter_upwards [gt_mem_nhds hu] with v hv
    exact Real.smoothTransition.zero_of_nonpos hv.le
  rw [he.deriv_eq,deriv_const]

lemma coneArgument_fderiv (T ε : ℝ) (x₀ : Vec) (p v : ℝ × Vec) :
    fderiv ℝ (coneArgument T ε x₀) p v =
      (-2*(T-p.1)*v.1 - 2*⟪p.2-x₀,v.2⟫)/ε := by
  have hd := (((hasFDerivAt_const T p).sub (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).pow 2).sub
    (((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).sub (hasFDerivAt_const x₀ p)).norm_sq)
  have hh := hd.const_smul ε⁻¹
  have he : (fun y => ε⁻¹ • (((T-y.1)^2)-‖y.2-x₀‖^2)) = coneArgument T ε x₀ := by
    ext y
    simp [coneArgument,div_eq_mul_inv,mul_comm]
  change HasFDerivAt (fun y => ε⁻¹ • ((T-y.1)^2-‖y.2-x₀‖^2)) _ p at hh
  rw [he] at hh
  rw [hh.fderiv]
  simp [smul_eq_mul, div_eq_mul_inv, inner_sub_left]
  ring

lemma coneCutoff_fderiv (T ε : ℝ) (x₀ : Vec) (p v : ℝ × Vec) :
    fderiv ℝ (coneCutoff T ε x₀) p v =
      deriv Real.smoothTransition (coneArgument T ε x₀ p) *
        ((-2*(T-p.1)*v.1-2*⟪p.2-x₀,v.2⟫)/ε) := by
  have hθ := (Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)
  have hg := (contDiff_coneArgument T ε x₀ (k := 1)).differentiable (by simp)
  have hh := (hθ (coneArgument T ε x₀ p)).hasDerivAt.comp_hasFDerivAt p (hg p).hasFDerivAt
  change HasFDerivAt (coneCutoff T ε x₀) _ p at hh
  rw [hh.fderiv]
  simpa [smul_eq_mul] using congrArg
    (fun c : ℝ => deriv Real.smoothTransition (coneArgument T ε x₀ p) * c)
    (coneArgument_fderiv T ε x₀ p v)

lemma coneArgument_neg_outside {T ε t : ℝ} (hε : 0 < ε) (ht : t ∈ Icc 0 T)
    {x x₀ : Vec} (hx : x ∉ closedBall x₀ T) : coneArgument T ε x₀ (t,x) < 0 := by
  have hr : T < ‖x-x₀‖ := by simpa [mem_closedBall,dist_eq_norm] using hx
  dsimp [coneArgument]
  apply div_neg_of_neg_of_pos _ hε
  have hR : 0 ≤ T-t := sub_nonneg.mpr ht.2
  have he : T-t < ‖x-x₀‖ := lt_of_le_of_lt (sub_le_self _ ht.1) hr
  nlinarith [sq_lt_sq₀ hR (norm_nonneg (x-x₀)) |>.mpr he]

lemma coneCutoff_zero_outside {T ε t : ℝ} (hε : 0 < ε) (ht : t ∈ Icc 0 T)
    {x x₀ : Vec} (hx : x ∉ closedBall x₀ T) : coneCutoff T ε x₀ (t,x) = 0 :=
  Real.smoothTransition.zero_of_nonpos (coneArgument_neg_outside hε ht hx).le

def coneShellFlux (s : Solution) (T ε : ℝ) (x₀ : Vec) (p : ℝ × Vec) : ℝ :=
  (2/ε)*deriv Real.smoothTransition (coneArgument T ε x₀ p) *
    ((T-p.1)*totalEnergy s p + ⟪p.2-x₀,totalFlux s p⟫)

lemma coneShellFlux_zero_outside (s : Solution) {T ε t : ℝ} (hε : 0 < ε)
    (ht : t ∈ Icc 0 T) {x x₀ : Vec} (hx : x ∉ closedBall x₀ T) :
    coneShellFlux s T ε x₀ (t,x) = 0 := by
  simp [coneShellFlux,deriv_transition_zero_neg (coneArgument_neg_outside hε ht hx)]

lemma coneShellFlux_nonneg {d : Datum} {s : Solution} (hs : Classical d s)
    {T ε t : ℝ} (hε : 0 < ε) (ht : t ∈ Icc 0 T) (x x₀ : Vec) :
    0 ≤ coneShellFlux s T ε x₀ (t,x) := by
  by_cases hr : ‖x-x₀‖ ≤ T-t
  · apply mul_nonneg (mul_nonneg (by positivity) (deriv_transition_nonneg _))
    have hb := classical_total_flux_bound hs ht.1 x
    have he := classical_total_energy_nonneg hs ht.1 x
    have hc := real_inner_le_norm (-(x-x₀)) (totalFlux s (t,x))
    simp only [inner_neg_left,norm_neg] at hc
    nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg (x-x₀)),
      mul_le_mul_of_nonneg_right hr he]
  · have hn : coneArgument T ε x₀ (t,x) < 0 := by
      dsimp [coneArgument]
      apply div_neg_of_neg_of_pos _ hε
      have := norm_nonneg (x-x₀)
      push Not at hr
      have hR : 0 ≤ T-t := sub_nonneg.mpr ht.2
      nlinarith [sq_lt_sq₀ hR (norm_nonneg (x-x₀)) |>.mpr hr]
    simp [coneShellFlux,deriv_transition_zero_neg hn]

lemma deriv_cone_energy {d : Datum} {s : Solution} (hs : Classical d s)
    {T ε t : ℝ} (hε : 0 < ε) (ht : t ∈ Ioo 0 T) (x₀ : Vec) :
    HasDerivAt (fun r => ∫ x : Vec, coneCutoff T ε x₀ (r,x)*totalEnergy s (r,x))
      (-(∫ x : Vec, coneShellFlux s T ε x₀ (t,x))) t := by
  have hh := deriv_moving_energy hs isOpen_Ioo (fun _ h => h.1)
    (isCompact_closedBall x₀ T) (contDiff_coneCutoff T ε x₀ (k := 1)).contDiffOn
    (fun r hr x hx => coneCutoff_zero_outside hε ⟨hr.1.le,hr.2.le⟩ hx) ht
  convert hh using 1
  rw [← integral_neg]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  dsimp only
  rw [coneCutoff_fderiv,coneCutoff_fderiv]
  simp only [inner_zero_right,mul_zero,mul_one,sub_zero,zero_sub]
  dsimp [coneShellFlux]
  ring

lemma classical_particle_flux_continuous_slab {d : Datum} {s : Solution}
    (hs : Classical d s) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (particleFlux s) (Icc 0 T ×ˢ (univ : Set Vec)) := by
  obtain ⟨K,hK,hzero⟩ := hs.2.2.2.2.2.2.1 T hT
  change ContinuousOn (fun p : ℝ × Vec => ∫ v : Vec, s.f (p.1,p.2,v) • v) _
  apply continuousOn_integral_uniform_support
    (F := fun z : (ℝ × Vec) × Vec => s.f (z.1.1,z.1.2,z.2) • z.2) (hK.image continuous_snd)
  · have hf : ContinuousOn (fun z : (ℝ × Vec) × Vec => s.f (z.1.1,z.1.2,z.2))
        ((Icc 0 T ×ˢ univ) ×ˢ univ) := by
      apply hs.1.continuousOn.comp (contDiff_reassociate (k := 1)).continuous.continuousOn
      intro z hz
      exact hz.1.1.1
    exact hf.smul continuous_snd.continuousOn
  · intro p hp v hv
    have hf : s.f (p.1,p.2,v) = 0 := by
      by_contra hn
      exact hv ⟨(p.2,v),hzero p.1 hp.1 (subset_tsupport _ hn),rfl⟩
    simp only [hf,zero_smul]

lemma classical_total_flux_continuous_slab {d : Datum} {s : Solution}
    (hs : Classical d s) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (totalFlux s) (Icc 0 T ×ˢ (univ : Set Vec)) := by
  have hsub : Icc 0 T ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace := fun z hz => hz.1.1
  exact ((contDiff_cross (k := 1)).continuous.comp_continuousOn
    ((hs.2.1.continuousOn.mono hsub).prodMk (hs.2.2.1.continuousOn.mono hsub))).add
      (classical_particle_flux_continuous_slab hs hT)

lemma coneShellFlux_continuous_slab {d : Datum} {s : Solution}
    (hs : Classical d s) {T ε : ℝ} (hT : 0 ≤ T) (x₀ : Vec) :
    ContinuousOn (coneShellFlux s T ε x₀) (Icc 0 T ×ˢ (univ : Set Vec)) := by
  have hθ : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by simp)
  exact ((continuous_const.mul (hθ.comp (contDiff_coneArgument T ε x₀ (k := 1)).continuous)).continuousOn).mul
    (((continuous_const.sub continuous_fst).continuousOn.mul
      (classical_total_energy_continuous_slab hs hT)).add
        ((continuous_snd.sub continuous_const).continuousOn.inner
          (classical_total_flux_continuous_slab hs hT)))

lemma coneShellFlux_integral_continuous {d : Datum} {s : Solution}
    (hs : Classical d s) {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) (x₀ : Vec) :
    ContinuousOn (fun t => ∫ x : Vec, coneShellFlux s T ε x₀ (t,x)) (Icc 0 T) := by
  apply continuousOn_integral_uniform_support (isCompact_closedBall x₀ T)
    (coneShellFlux_continuous_slab hs hT x₀)
  intro t ht x hx
  exact coneShellFlux_zero_outside s hε ht hx

lemma cone_energy_continuous {d : Datum} {s : Solution}
    (hs : Classical d s) {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) (x₀ : Vec) :
    ContinuousOn (fun t => ∫ x : Vec, coneCutoff T ε x₀ (t,x)*totalEnergy s (t,x)) (Icc 0 T) := by
  apply continuousOn_integral_uniform_support (isCompact_closedBall x₀ T)
    ((contDiff_coneCutoff T ε x₀ (k := 1)).continuous.continuousOn.mul
      (classical_total_energy_continuous_slab hs hT))
  intro t ht x hx
  change coneCutoff T ε x₀ (t,x)*totalEnergy s (t,x)=0
  simp only [coneCutoff_zero_outside hε ht hx,zero_mul]

lemma coneShellFlux_bound {d : Datum} {s : Solution} (hs : Classical d s)
    {T ε b : ℝ} (hb : 0 ≤ b) (hbT : b ≤ T) (hε : 0 < ε) (x₀ : Vec) :
    (∫ t in 0..b, ∫ x : Vec, coneShellFlux s T ε x₀ (t,x)) ≤
      ∫ x : Vec, totalEnergy s (0,x) := by
  have hT := hb.trans hbT
  have hsub : Icc (0:ℝ) b ⊆ Icc 0 T := Icc_subset_Icc_right hbT
  have hc := (cone_energy_continuous hs hT hε x₀).mono hsub
  have hi := ((coneShellFlux_integral_continuous hs hT hε x₀).mono hsub).intervalIntegrable_of_Icc (μ := volume) hb
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb hc
    (fun t ht => deriv_cone_energy hs hε ⟨ht.1,ht.2.trans_le hbT⟩ x₀) hi.neg
  rw [intervalIntegral.integral_neg] at hf
  have hbpos : 0 ≤ ∫ x : Vec, coneCutoff T ε x₀ (b,x)*totalEnergy s (b,x) := by
    apply integral_nonneg
    intro x
    exact mul_nonneg (Real.smoothTransition.nonneg _) (classical_total_energy_nonneg hs hb x)
  have hzero : (∫ x : Vec, coneCutoff T ε x₀ (0,x)*totalEnergy s (0,x)) ≤
      ∫ x : Vec, totalEnergy s (0,x) := by
    refine integral_mono ?_ (classical_total_energy_integrable hs le_rfl) ?_
    · apply Continuous.integrable_of_hasCompactSupport
      · apply Continuous.mul ((contDiff_coneCutoff T ε x₀ (k := 1)).continuous.comp
          (continuous_const.prodMk continuous_id))
        apply (classical_total_energy_continuous_slab hs hT).comp_continuous
          (continuous_const.prodMk continuous_id)
        intro x
        exact ⟨⟨le_rfl,hT⟩,mem_univ x⟩
      · apply HasCompactSupport.mul_right
        apply compactSupport_of_zero_off (isCompact_closedBall x₀ T)
        exact fun x hx => coneCutoff_zero_outside hε ⟨le_rfl,hT⟩ hx
    · intro x
      exact mul_le_of_le_one_left (classical_total_energy_nonneg hs le_rfl x)
        (Real.smoothTransition.le_one _)
  linarith

lemma deriv_transition_zero_gt_one {u : ℝ} (hu : 1 < u) :
    deriv Real.smoothTransition u = 0 := by
  have he : Real.smoothTransition =ᶠ[𝓝 u] fun _ => (1 : ℝ) := by
    filter_upwards [lt_mem_nhds hu] with v hv
    exact Real.smoothTransition.one_of_one_le hv.le
  rw [he.deriv_eq,deriv_const]

def radialConeWeight (R ε r : ℝ) : ℝ :=
  (2*r/ε)*deriv Real.smoothTransition ((R^2-r^2)/ε)

lemma continuous_radialConeWeight (R ε : ℝ) : Continuous (radialConeWeight R ε) := by
  have hθ := (Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by simp)
  exact ((continuous_const.mul continuous_id).div_const ε).mul
    (hθ.comp ((continuous_const.sub (continuous_id.pow 2)).div_const ε))

lemma radialConeWeight_nonneg {ε r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) (R : ℝ) :
    0 ≤ radialConeWeight R ε r :=
  mul_nonneg (by positivity) (deriv_transition_nonneg _)

lemma deriv_radial_cone (R ε r : ℝ) :
    HasDerivAt (fun z => Real.smoothTransition ((R^2-z^2)/ε))
      (-radialConeWeight R ε r) r := by
  have hθ := (Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)
  have hh := (hθ _).hasDerivAt.comp r
    (((hasDerivAt_const r (R^2)).sub ((hasDerivAt_id r).pow 2)).div_const ε)
  convert! hh using 1
  simp only [radialConeWeight,Pi.sub_apply,id_eq,Pi.pow_apply,
    Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,zero_sub]
  ring

lemma radialConeWeight_mass {R : ℝ} (hR : 0 ≤ R) (ε : ℝ) :
    (∫ r in 0..R, radialConeWeight R ε r) = Real.smoothTransition (R^2/ε) := by
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR
    (Real.smoothTransition.continuous.comp ((continuous_const.sub (continuous_id.pow 2)).div_const ε)).continuousOn
    (fun r _ => deriv_radial_cone R ε r)
    ((continuous_radialConeWeight R ε).neg.intervalIntegrable 0 R)
  rw [intervalIntegral.integral_neg] at hf
  simp only [Function.comp_def,Pi.sub_apply,Pi.pow_apply,id_eq,sub_self,zero_div,Real.smoothTransition.zero,zero_sub,zero_pow (by norm_num : 2 ≠ 0),sub_zero] at hf
  linarith

lemma radialConeWeight_local {R ε δ r : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (hεδ : ε < R*δ) (hr : r ∈ Icc 0 R) (hfar : δ ≤ R-r) :
    radialConeWeight R ε r = 0 := by
  have ha : 1 < (R^2-r^2)/ε := by
    apply (lt_div_iff₀ hε).mpr
    have hh : ε < R*(R-r) := hεδ.trans_le (mul_le_mul_of_nonneg_left hfar hR.le)
    nlinarith [mul_nonneg hr.1 (sub_nonneg.mpr hr.2)]
  simp [radialConeWeight,deriv_transition_zero_gt_one ha]

lemma radialConeWeight_tendsto {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : ContinuousOn F (Icc 0 R)) :
    Filter.Tendsto (fun ε => ∫ r in 0..R, radialConeWeight R ε r * F r)
      (𝓝[>] (0 : ℝ)) (𝓝 (F R)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨δ,hδ,hclose⟩ := (Metric.continuousWithinAt_iff.mp (hF R ⟨hR.le,le_rfl⟩))
    (η/2) (by positivity)
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < min (R^2) (R*δ) := by
    apply Filter.eventually_of_mem (Ioo_mem_nhdsGT (by positivity : 0 < min (R^2) (R*δ)))
    intro ε hε
    exact hε
  filter_upwards [hev] with ε hε
  have hw : ContinuousOn (radialConeWeight R ε) (Icc 0 R) := (continuous_radialConeWeight R ε).continuousOn
  have hwI := (continuous_radialConeWeight R ε).intervalIntegrable (μ := volume) 0 R
  have hFI : IntervalIntegrable (fun r => radialConeWeight R ε r * F r) volume 0 R :=
    (hw.mul hF).intervalIntegrable_of_Icc (μ := volume) hR.le
  have hm : (∫ r in 0..R, radialConeWeight R ε r) = 1 := by
    rw [radialConeWeight_mass hR.le]
    apply Real.smoothTransition.one_of_one_le
    exact (le_div_iff₀ hε.1).mpr (by simpa using (lt_of_lt_of_le hε.2 (min_le_left _ _)).le)
  have heq : (∫ r in 0..R, radialConeWeight R ε r * F r) - F R =
      ∫ r in 0..R, radialConeWeight R ε r * (F r-F R) := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub hFI (hwI.mul_const _),intervalIntegral.integral_mul_const,hm,one_mul]
  have hb : ‖∫ r in 0..R, radialConeWeight R ε r * (F r-F R)‖ ≤ η/2 := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le hR.le
      (g := fun r => radialConeWeight R ε r * (η/2)) (μ := volume)
      (ae_of_all _ (fun r hr => show ‖radialConeWeight R ε r * (F r-F R)‖ ≤
          radialConeWeight R ε r * (η/2) from by
        have hr' : r ∈ Icc 0 R := ⟨hr.1.le,hr.2⟩
        have hp := radialConeWeight_nonneg hε.1 hr'.1 R
        by_cases hd : δ ≤ R-r
        · rw [radialConeWeight_local hR hε.1 (lt_of_lt_of_le hε.2 (min_le_right _ _)) hr' hd]
          simp
        · have hd' : dist r R < δ := by
            rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hr.2)]
            linarith
          have hc := hclose hr' hd'
          rw [Real.dist_eq] at hc
          simp only [norm_mul,Real.norm_eq_abs,abs_of_nonneg hp]
          exact mul_le_mul_of_nonneg_left hc.le hp)) (hwI.mul_const _)
    simpa only [intervalIntegral.integral_mul_const,hm,one_mul] using hh
  rw [dist_eq_norm,heq]
  exact hb.trans_lt (by linarith)

lemma sphere_norm (n : Sphere) : ‖n.1‖ = 1 := by
  simpa only [mem_sphere,dist_zero_right] using n.2

def radialConeProfile (s : Solution) (t R : ℝ) (x₀ : Vec) (r : ℝ) (n : Sphere) : ℝ :=
  r * (R*totalEnergy s (t,x₀+r • n.1) + r*⟪n.1,totalFlux s (t,x₀+r • n.1)⟫)

lemma continuous_radialConeProfile {d : Datum} {s : Solution} (hs : Classical d s)
    {t : ℝ} (ht : 0 ≤ t) (R : ℝ) (x₀ : Vec) :
    Continuous (fun p : ℝ × Sphere => radialConeProfile s t R x₀ p.1 p.2) := by
  have hU : Continuous (fun x => totalEnergy s (t,x)) := by
    apply (classical_total_energy_continuous_slab hs ht).comp_continuous
      (continuous_const.prodMk continuous_id)
    intro x
    exact ⟨⟨ht,le_rfl⟩,mem_univ x⟩
  have hS : Continuous (fun x => totalFlux s (t,x)) := by
    apply (classical_total_flux_continuous_slab hs ht).comp_continuous
      (continuous_const.prodMk continuous_id)
    intro x
    exact ⟨⟨ht,le_rfl⟩,mem_univ x⟩
  have hx : Continuous (fun p : ℝ × Sphere => x₀ + p.1 • p.2.1) := by fun_prop
  exact continuous_fst.mul ((continuous_const.mul (hU.comp hx)).add
    (continuous_fst.mul ((continuous_subtype_val.comp continuous_snd).inner (hS.comp hx))))

lemma continuous_spherical_radialConeProfile {d : Datum} {s : Solution} (hs : Classical d s)
    {t : ℝ} (ht : 0 ≤ t) (R : ℝ) (x₀ : Vec) :
    Continuous (fun r => ∫ n : Sphere, radialConeProfile s t R x₀ r n ∂sphereMeasure) := by
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (k := univ) isCompact_univ
    (continuous_radialConeProfile hs ht R x₀).continuousOn
  intro r n _ hn
  exact (hn (mem_univ n)).elim

lemma coneShellFlux_polar_kernel (s : Solution) (T ε t r : ℝ) (x₀ : Vec) (n : Sphere) :
    r^2 • coneShellFlux s T ε x₀ (t,x₀+r • n.1) =
      radialConeWeight (T-t) ε r * radialConeProfile s t (T-t) x₀ r n := by
  have hn : ‖r • n.1‖^2 = r^2 := by simp [norm_smul,Real.norm_eq_abs,sq_abs]
  simp only [coneShellFlux,coneArgument,radialConeWeight,radialConeProfile,
    add_sub_cancel_left,hn,inner_smul_left,smul_eq_mul,starRingEnd_apply,star_trivial]
  ring

lemma radialConeWeight_zero_above {R ε r : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) (hr : R < r) :
    radialConeWeight R ε r = 0 := by
  have ha : (R^2-r^2)/ε < 0 := by
    apply div_neg_of_neg_of_pos _ hε
    nlinarith [sq_lt_sq₀ hR (hR.trans hr.le) |>.mpr hr]
  simp [radialConeWeight,deriv_transition_zero_neg ha]

lemma radialConeWeight_integral_Ioi {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (F : ℝ → ℝ) :
    (∫ r in Ioi 0, radialConeWeight R ε r * F r) =
      ∫ r in 0..R, radialConeWeight R ε r * F r := by
  rw [intervalIntegral.integral_of_le hR]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
  intro r hr
  have hrr : R < r := by
    by_contra hn
    exact hr.2 ⟨hr.1,not_lt.mp hn⟩
  rw [radialConeWeight_zero_above hR hε hrr,zero_mul]

lemma coneShellFlux_polar {d : Datum} {s : Solution} (hs : Classical d s)
    {T ε t : ℝ} (ht : t ∈ Icc 0 T) (hε : 0 < ε) (x₀ : Vec) :
    (∫ x : Vec, coneShellFlux s T ε x₀ (t,x)) =
      ∫ r in 0..(T-t), radialConeWeight (T-t) ε r *
        (∫ n : Sphere, radialConeProfile s t (T-t) x₀ r n ∂sphereMeasure) := by
  have hR : 0 ≤ T-t := sub_nonneg.mpr ht.2
  have hC : Continuous (fun x => coneShellFlux s T ε x₀ (t,x₀+x)) := by
    apply (coneShellFlux_continuous_slab hs (ht.1.trans ht.2) x₀).comp_continuous
      (continuous_const.prodMk (continuous_const.add continuous_id))
    intro x
    exact ⟨ht,mem_univ _⟩
  have hK : HasCompactSupport (fun x => coneShellFlux s T ε x₀ (t,x₀+x)) := by
    apply compactSupport_of_zero_off (isCompact_closedBall (0:Vec) T)
    intro x hx
    apply coneShellFlux_zero_outside s hε ht
    simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left,sub_zero] using hx
  have htrans := integral_add_left_eq_self (μ := (volume : Measure Vec))
    (fun x => coneShellFlux s T ε x₀ (t,x)) x₀
  rw [← htrans,integral_polar (hC.integrable_of_hasCompactSupport hK)]
  simp_rw [coneShellFlux_polar_kernel,radialConeWeight_integral_Ioi hR hε]
  have hcont : Continuous (fun p : ℝ × Sphere =>
      radialConeWeight (T-t) ε p.1 * radialConeProfile s t (T-t) x₀ p.1 p.2) :=
    ((continuous_radialConeWeight (T-t) ε).comp continuous_fst).mul
      (continuous_radialConeProfile hs ht.1 (T-t) x₀)
  have hi : Integrable (fun p : ℝ × Sphere => radialConeWeight (T-t) ε p.1 *
      radialConeProfile s t (T-t) x₀ p.1 p.2)
        ((volume.restrict (uIoc 0 (T-t))).prod sphereMeasure) := by
    let : IsFiniteMeasure sphereMeasure := inferInstance
    let : IsFiniteMeasureOnCompacts ((volume : Measure ℝ).prod sphereMeasure) :=
      Measure.prod.instIsFiniteMeasureOnCompacts _ _
    rw [uIoc_of_le hR,Measure.restrict_prod_eq_prod_univ]
    exact (hcont.continuousOn.integrableOn_compact
      (μ := (volume : Measure ℝ).prod sphereMeasure)
      (isCompact_Icc.prod isCompact_univ)).mono_set
      (prod_mono_left Ioc_subset_Icc_self)
  rw [← intervalIntegral_integral_swap hi]
  apply intervalIntegral.integral_congr
  intro r _
  exact integral_const_mul _ _

lemma coneShellFlux_tendsto {d : Datum} {s : Solution} (hs : Classical d s)
    {T t : ℝ} (ht : 0 ≤ t) (htT : t < T) (x₀ : Vec) :
    Filter.Tendsto (fun ε => ∫ x : Vec, coneShellFlux s T ε x₀ (t,x))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ n : Sphere, radialConeProfile s t (T-t) x₀ (T-t) n ∂sphereMeasure)) := by
  have hh := radialConeWeight_tendsto (sub_pos.mpr htT)
    (continuous_spherical_radialConeProfile hs ht (T-t) x₀).continuousOn
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (coneShellFlux_polar hs ⟨ht,htT.le⟩ hε x₀).symm

lemma integral_limit_nonneg_le {μ : Measure ℝ} {G : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hGi : ∀ n, Integrable (G n) μ)
    (hGn : ∀ n, ∀ᵐ t ∂μ, 0 ≤ G n t)
    (hconv : ∀ᵐ t ∂μ, Filter.Tendsto (fun n => G n t) Filter.atTop (𝓝 (F t)))
    (hbound : ∀ n, (∫ t, G n t ∂μ) ≤ C) :
    Integrable F μ ∧ (∫ t, F t ∂μ) ≤ C := by
  have hFn : ∀ᵐ t ∂μ, 0 ≤ F t := by
    filter_upwards [hconv, ae_all_iff.mpr hGn] with t ht hp
    exact ge_of_tendsto' ht hp
  have hnormG (n : ℕ) : (∫ t, ‖G n t‖ ∂μ) = ∫ t, G n t ∂μ := by
    apply integral_congr_ae
    filter_upwards [hGn n] with t ht
    exact Real.norm_of_nonneg ht
  have hb : Filter.liminf (fun n => ∫⁻ t, ‖G n t‖ₑ ∂μ) Filter.atTop ≤ ENNReal.ofReal C := by
    apply Filter.liminf_le_of_frequently_le'
    apply Filter.Frequently.of_forall
    intro n
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hGi n),hnormG]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hi := integrable_of_tendsto hconv (fun n => (hGi n).aestronglyMeasurable)
    (lt_of_le_of_lt hb ENNReal.ofReal_lt_top).ne
  refine ⟨hi, ?_⟩
  have hh := (lintegral_enorm_le_liminf_of_tendsto hconv
    (fun n => (hGi n).aestronglyMeasurable.aemeasurable.enorm)).trans hb
  rw [← ofReal_integral_norm_eq_lintegral_enorm hi,
    ENNReal.ofReal_le_ofReal_iff hC] at hh
  convert! hh using 1
  apply integral_congr_ae
  filter_upwards [hFn] with t ht
  exact (Real.norm_of_nonneg ht).symm

lemma classical_light_cone_flux {d : Datum} {s : Solution} (hs : Classical d s)
    {T : ℝ} (hT : 0 ≤ T) (x₀ : Vec) :
    IntegrableOn (fun t => ∫ n : Sphere,
      radialConeProfile s t (T-t) x₀ (T-t) n ∂sphereMeasure) (Ioo 0 T) ∧
    (∫ t in 0..T, ∫ n : Sphere,
      radialConeProfile s t (T-t) x₀ (T-t) n ∂sphereMeasure) ≤
        ∫ x : Vec, totalEnergy s (0,x) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n:ℝ)+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have heps : Filter.Tendsto ε Filter.atTop (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Filter.Eventually.of_forall hε⟩
  let G : ℕ → ℝ → ℝ := fun n t => ∫ x : Vec, coneShellFlux s T (ε n) x₀ (t,x)
  have hGi (n : ℕ) : Integrable (G n) (volume.restrict (Ioo 0 T)) := by
    exact ((coneShellFlux_integral_continuous hs hT (hε n) x₀).integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hGn (n : ℕ) : ∀ᵐ t ∂volume.restrict (Ioo 0 T), 0 ≤ G n t := by
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro t ht
    apply integral_nonneg
    intro x
    exact coneShellFlux_nonneg hs (hε n) ⟨ht.1.le,ht.2.le⟩ x x₀
  have hconv : ∀ᵐ t ∂volume.restrict (Ioo 0 T),
      Filter.Tendsto (fun n => G n t) Filter.atTop
        (𝓝 (∫ n : Sphere, radialConeProfile s t (T-t) x₀ (T-t) n ∂sphereMeasure)) := by
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro t ht
    exact (coneShellFlux_tendsto hs ht.1.le ht.2 x₀).comp heps
  have hb (n : ℕ) : (∫ t in Ioo 0 T, G n t) ≤ ∫ x : Vec, totalEnergy s (0,x) := by
    rw [restrict_Ioo_eq_restrict_Ioc,← intervalIntegral.integral_of_le hT]
    exact coneShellFlux_bound hs hT le_rfl (hε n) x₀
  obtain ⟨hi,hb⟩ := integral_limit_nonneg_le
    (integral_nonneg (classical_total_energy_nonneg hs le_rfl)) hGi hGn hconv hb
  refine ⟨hi, ?_⟩
  rwa [restrict_Ioo_eq_restrict_Ioc,← intervalIntegral.integral_of_le hT] at hb

end RVM

end

end OAI
