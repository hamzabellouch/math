import Mathlib
import OAI.Analysis.PathSelection.InverseEstimates

namespace OAI

/-! Phase perturbation and vanishing, positive and constant equal-exponent charts. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma arg_mul_near_one {v p : ℂ} (hv : |v.arg|≤Real.pi/2)
    (hp : ‖p-1‖≤1/2) : |(v*p).arg|≤|v.arg|+2*‖p-1‖ := by
  by_cases hv0 : v=0
  · simp only [hv0,zero_mul,Complex.arg_zero,abs_zero,zero_add]
    positivity
  have hp0 : p≠0 := by
    intro he
    rw [he,zero_sub,norm_neg,norm_one] at hp
    norm_num at hp
  have hlog := Complex.norm_log_one_add_half_le_self hp
  have he : 1+(p-1)=p := by ring
  rw [he] at hlog
  have ha : |p.arg|≤(3/2:ℝ)*‖p-1‖ := by
    rw [←Complex.log_im]
    exact (Complex.abs_im_le_norm _).trans hlog
  have hsum : v.arg+p.arg∈Ioc (-Real.pi) Real.pi := by
    have hh : |v.arg+p.arg| < Real.pi := (abs_add_le _ _).trans_lt (by
      calc
        |v.arg|+|p.arg| ≤ Real.pi/2+(3/2:ℝ)*‖p-1‖ := add_le_add hv ha
        _ < Real.pi := by nlinarith [Real.pi_gt_three])
    exact ⟨(abs_lt.mp hh).1,(abs_lt.mp hh).2.le⟩
  rw [Complex.arg_mul hv0 hp0 hsum]
  exact (abs_add_le _ _).trans (add_le_add le_rfl (ha.trans (show (3/2:ℝ)*‖p-1‖≤2*‖p-1‖ by nlinarith [norm_nonneg (p-1)])))

theorem inward_phase_small_perturbation {V F : ℂ → ℂ} {e : ℝ → ℝ}
    (hV0 : ∀ᶠ z in sectorInfinity,V z≠0)
    (hVarg : ∀ᶠ z in sectorInfinity,|(V z).arg|≤|z.arg|)
    (he : Tendsto e atTop (𝓝 0))
    (hclose : ∀ᶠ z in sectorInfinity,‖F z/V z-1‖≤|e ‖z‖|) :
    ∀ᶠ z in sectorInfinity,|(F z).arg|≤|z.arg|+2*|e ‖z‖| := by
  have hs : ∀ᶠ r : ℝ in atTop,|e r|≤1/2 := by
    filter_upwards [(Metric.tendsto_nhds.mp he) (1/2) (by norm_num)] with r hr
    exact (by simpa only [dist_zero_right,Real.norm_eq_abs] using hr.le)
  have ha : ∀ᶠ z in sectorInfinity,|z.arg|≤Real.pi/2 := by
    filter_upwards [SectorEventually.realpart_pos] with z hz
    exact (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)).le
  filter_upwards [hV0,hVarg,hclose,tendsto_norm_sectorInfinity.eventually hs,ha] with z hv harg hc hs ha
  have hh := arg_mul_near_one (harg.trans ha) (hc.trans hs)
  rw [mul_div_cancel₀ _ hv] at hh
  exact hh.trans (add_le_add harg (mul_le_mul_of_nonneg_left hc (by norm_num)))

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

 

theorem comparable_sector_mapping {F : ℂ → ℂ} {f ψ e : ℝ → ℝ}
    (hft : Tendsto f atTop atTop)
    (hfψ : ∀ᶠ r : ℝ in atTop,f r=(2:ℝ)^(ψ (Real.logb 2 r)))
    (hψa : ∀ᶠ x : ℝ in atTop,DifferentiableAt ℝ ψ x)
    (hψd : Tendsto (deriv ψ) atTop (𝓝 1))
    (hmod : ∀ᶠ z in sectorInfinity,f ‖z‖/2 ≤ ‖F z‖ ∧ ‖F z‖ ≤ 2*f ‖z‖)
    (harg : ∀ᶠ z in sectorInfinity,|(F z).arg| ≤ |z.arg|+|e ‖z‖|)
    {χ : ℝ → ℝ} (hχ : AdmissibleAngularLoss χ)
    (he : ∀ᶠ r : ℝ in atTop,|e r| ≤ χ r)
    (ω : ℝ → ℝ) (R : ℝ) (hω : AdmissibleAngularLoss ω) :
    ∃ (η : ℝ → ℝ) (T : ℝ),AdmissibleAngularLoss η ∧
      ∀ z∈lossSector η T,F z∈lossSector ω R := by
  obtain ⟨hN,hNu⟩ := hω.neighboring
  let ν : ℝ → ℝ := fun r => max (baseLoss r) (neighboringLoss ω ((2:ℝ)^(ψ (Real.logb 2 r))))
  have hν : AdmissibleAngularLoss ν := hN.pullback_log_derivative hψa hψd
  have hrad : ∀ᶠ r : ℝ in atTop,0<χ r ∧ |e r|≤χ r ∧
      (∀ s∈Icc (f r/2) (2*f r),ω s≤ν r) ∧ 2*R<f r := by
    filter_upwards [hχ.1,he,hft.eventually hNu,hft.eventually (eventually_gt_atTop (2*R)),hfψ] with r hχ he hu hR hψ
    refine ⟨hχ.1,he,?_,hR⟩
    intro s hs
    exact (hu s hs).trans (by dsimp [ν]; rw [←hψ]; exact le_max_right _ _)
  obtain ⟨κ,S,hκ,hdata⟩ := (hmod.and harg).and (tendsto_norm_sectorInfinity.eventually hrad)
  let η : ℝ → ℝ := fun r => 4*max (κ r) (max (χ r) (ν r))
  have hη : AdmissibleAngularLoss η := (hκ.max (hχ.max hν)).const_mul (by norm_num)
  have hpos : ∀ᶠ r : ℝ in atTop,0<κ r ∧ 0<χ r ∧ 0<ν r := by
    filter_upwards [hκ.1,hχ.1,hν.1] with r hk hc hn
    exact ⟨hk.1,hc.1,hn.1⟩
  obtain ⟨T,hT⟩ := eventually_atTop.mp hpos
  refine ⟨η,max S T,hη,?_⟩
  intro z hz
  have hp := hT ‖z‖ ((le_max_right _ _).trans hz.1.le)
  have hk : κ ‖z‖ ≤ η ‖z‖ := by
    dsimp [η]
    have hh := le_max_left (κ ‖z‖) (max (χ ‖z‖) (ν ‖z‖))
    linarith [hp.1]
  have hzκ : z∈lossSector κ S := ⟨(le_max_left _ _).trans_lt hz.1,
    hz.2.trans_le (sub_le_sub_left hk _)⟩
  obtain ⟨⟨hm,ha⟩,hc,he,hu,hR⟩ := hdata z hzκ
  have hωF := hu ‖F z‖ hm
  have hην : χ ‖z‖+ν ‖z‖ ≤ η ‖z‖ := by
    dsimp [η]
    have hh₁ := (le_max_left (χ ‖z‖) (ν ‖z‖)).trans (le_max_right (κ ‖z‖) (max (χ ‖z‖) (ν ‖z‖)))
    have hh₂ := (le_max_right (χ ‖z‖) (ν ‖z‖)).trans (le_max_right (κ ‖z‖) (max (χ ‖z‖) (ν ‖z‖)))
    linarith [hp.2.1,hp.2.2]
  refine ⟨by linarith [hm.1],?_⟩
  linarith [hz.2]

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

theorem vanishing_equal_exponent_chart {F H J E : ℂ → ℂ} {b ε C : ℝ}
    (hb : 0<b) (hε : 0<ε) (hC : 0≤C)
    (hFa : ∀ᶠ z in stripInfinity,AnalyticAt ℂ F z)
    (hHa : ∀ᶠ z in stripInfinity,AnalyticAt ℂ H z)
    (hF0 : ∀ᶠ z in stripInfinity,F z≠0)
    (hH0 : ∀ᶠ z in stripInfinity,H z≠0)
    (hFr : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0 ∧ 0<(F (t:ℂ)).re)
    (hHr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0 ∧ 0<(H (t:ℂ)).re)
    (hFt : Tendsto (fun t : ℝ => (F (t:ℂ)).re) atTop atTop)
    (hHt : Tendsto (fun t : ℝ => (H (t:ℂ)).re) atTop atTop)
    (hFd : Tendsto (fun z => deriv F z/F z) stripInfinity (𝓝 (b:ℂ)))
    (hHd : Tendsto (fun z => deriv H z/H z) stripInfinity (𝓝 (b:ℂ)))
    (hJa : ∀ᶠ z in stripInfinity,AnalyticAt ℂ J z)
    (hJ0 : ∀ᶠ z in stripInfinity,J z≠0)
    (hJr : ∀ᶠ t : ℝ in atTop,(J (t:ℂ)).im=0 ∧ 0<(J (t:ℂ)).re)
    (hJd : Tendsto (fun z => deriv J z/J z) stripInfinity (𝓝 0))
    (hJdd : Tendsto (fun z => deriv (deriv J) z/deriv J z) stripInfinity (𝓝 0))
    (hJl : Tendsto (fun t : ℝ => (J (t:ℂ)).re) atTop (𝓝 0))
    (hJm : ∃ A : ℝ,MonotoneOn (fun t : ℝ => (J (t:ℂ)).re) (Ici A) ∨
      AntitoneOn (fun t : ℝ => (J (t:ℂ)).re) (Ici A))
    (hqa : ∀ᶠ z in stripInfinity,AnalyticAt ℂ (fun z => deriv J z/J z) z)
    (hqne : ∀ᶠ z in stripInfinity,deriv J z/J z≠0)
    (hqd : Tendsto (fun z => deriv (fun z => deriv J z/J z) z/(deriv J z/J z)) stripInfinity (𝓝 0))
    (hqr : ∀ᶠ t : ℝ in atTop,(deriv J (t:ℂ)/J (t:ℂ)).im=0 ∧ (deriv J (t:ℂ)/J (t:ℂ)).re<0)
    (he : ∀ᶠ z in stripInfinity,‖E z‖≤C*Real.exp (-ε*z.re))
    (hfactor : ∀ᶠ z in stripInfinity,F z/H z=J z*(1+E z)) :
    ∃ (T : ℝ) (x : ℂ → ℂ),0<T ∧
      AnalyticOnNhd ℂ x {w | 0<w.re ∧ T<‖w‖} ∧
      (∀ w : ℂ,0<w.re → T<‖w‖ → H (x w)=w) ∧
      (∀ᶠ t : ℝ in atTop,x (H (t:ℂ))=(t:ℂ)) ∧
      Tendsto x sectorInfinity stripInfinity ∧
      (∀ᶠ r : ℝ in atTop,(x (r:ℂ)).im=0 ∧ (F (x (r:ℂ))).im=0 ∧ 0<(F (x (r:ℂ))).re) ∧
      Tendsto (fun r : ℝ => (F (x (r:ℂ))).re) atTop atTop ∧
      (∀ᶠ w in sectorInfinity,AnalyticAt ℂ (fun z => F (x z)) w) ∧
      ∀ (ω : ℝ → ℝ) (S : ℝ),AdmissibleAngularLoss ω →
        ∃ (η : ℝ → ℝ) (R : ℝ),AdmissibleAngularLoss η ∧
          (∀ w∈lossSector η R,F (x w)∈lossSector ω S) ∧
          (∀ w∈lossSector η R,(F (x (‖w‖:ℂ))).re/2≤‖F (x w)‖ ∧
            ‖F (x w)‖≤2*(F (x (‖w‖:ℂ))).re) ∧
          (∀ δ : ℝ,0<δ → ∃ U : ℝ,∀ w∈lossSector η U,|(F (x w)).re|≤δ*w.re) := by
  obtain ⟨T,x,hT,hxa,hleft,hright,hxr,hxt,hxto,hinc,hxd,V,hphase⟩ :=
    equal_exponent_inward hb hHa hH0 hHr hHt hHd hJa hJ0 hJr hqa hqne hqd hqr
      (hJd.comp tendsto_real_stripInfinity)
  have hxr' : ∀ᶠ r : ℝ in atTop,(x (r:ℂ)).im=0 := (eventually_gt_atTop T).mono fun r hr => hxr r hr
  have hdom : ∀ᶠ w in sectorInfinity,0<w.re ∧ T<‖w‖ :=
    SectorEventually.realpart_pos.and (tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop T))
  have hxa' : ∀ᶠ w in sectorInfinity,AnalyticAt ℂ x w := hdom.mono fun w hw => hxa w hw
  have hi : ∀ δ : ℝ,0<δ → ∀ᶠ w in sectorInfinity,
      ‖x w-x (‖w‖:ℂ)-Complex.I*(w.arg/b:ℝ)‖≤δ*|w.arg| := by
    intro δ hδ
    obtain ⟨U,hU⟩ := hinc δ hδ
    filter_upwards [SectorEventually.realpart_pos,tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop U)] with w hw hUw
    exact hU w hw hUw
  have hi1 : ∃ U : ℝ,∀ w : ℂ,0<w.re → U<‖w‖ →
      ‖x w-x (‖w‖:ℂ)-Complex.I*(w.arg/b:ℝ)‖≤|w.arg| := by
    simpa only [one_mul] using hinc 1 zero_lt_one
  obtain ⟨hGreal,hGft,hGa,hmod,ψ,hψa,hψd,hψ⟩ :=
    inverse_chart_data hb hFa hF0 hFr hFt hFd hxa' hxr' hxt hxto hi hxd
  obtain ⟨D,hD,hEbound⟩ := inverse_strip_exponential_error hb hε hC hxr' hxt hi1 he
  let e : ℝ → ℝ := fun r => D*Real.exp (-ε*(x (r:ℂ)).re)
  have hep (r : ℝ) : 0<e r := mul_pos hD (Real.exp_pos _)
  have het : Tendsto e atTop (𝓝 0) := by
    have hh := (Real.tendsto_exp_atBot.comp (hxt.const_mul_atTop_of_neg (show -ε<0 by linarith))).const_mul D
    simpa only [mul_zero,e,Function.comp_def] using hh
  have hV0 : ∀ᶠ w in sectorInfinity,w*J (x w)≠0 := by
    filter_upwards [SectorEventually.realpart_pos,hxto.eventually hJ0] with w hw hj
    change 0<w.re at hw
    exact mul_ne_zero (fun he => by simp [he] at hw) hj
  have hVarg : ∀ᶠ w in sectorInfinity,|(w*J (x w)).arg|≤|w.arg| := by
    filter_upwards [SectorEventually.realpart_pos,tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop V)] with w hw hwV
    exact hphase w hw hwV
  have hclose : ∀ᶠ w in sectorInfinity,‖F (x w)/(w*J (x w))-1‖≤|e ‖w‖| := by
    filter_upwards [hdom,hxto.eventually hfactor,hxto.eventually hJ0,hEbound] with w hw hf hj he
    rw [hleft w hw.1 hw.2] at hf
    have hw0 : w≠0 := fun hz => by simpa [hz] using hw.1
    have hh : F (x w)/(w*J (x w))-1=E (x w) := by
      have hf' := (div_eq_iff hw0).mp hf
      rw [hf']
      field_simp
      ring
    rw [hh,abs_of_pos (hep ‖w‖)]
    exact he
  have harg := inward_phase_small_perturbation hV0 hVarg het hclose
  have hri : ∀ᶠ r : ℝ in atTop,H ((x (r:ℂ)).re:ℂ)=(r:ℂ) := by
    filter_upwards [hxr',eventually_gt_atTop T] with r hr hrt
    have heq : x (r:ℂ)=((x (r:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using hr)
    rw [←heq]
    exact hleft (r:ℂ) (by simpa using hT.trans hrt)
      (by simpa only [Complex.norm_of_nonneg (hT.trans hrt).le] using hrt)
  have hsmall := inverse_exponential_loss_absorption hb hε
    (tendsto_real_stripInfinity.eventually hHa) hHr (hHd.comp tendsto_real_stripInfinity)
    hxt hri admissible_baseLoss (2*D) 1 zero_lt_one
  have hemajor : ∀ᶠ r : ℝ in atTop,|2*e r|≤baseLoss r := by
    filter_upwards [hsmall] with r hr
    rw [abs_of_pos (mul_pos (by norm_num) (hep r))]
    simpa only [one_mul,mul_assoc,e] using hr
  have harg' : ∀ᶠ w in sectorInfinity,|(F (x w)).arg|≤|w.arg|+|2*e ‖w‖| := by
    filter_upwards [harg] with w hw
    simpa only [abs_mul,abs_of_pos (show (0:ℝ)<2 by norm_num)] using hw
  have hJd0 : ∀ᶠ z in stripInfinity,deriv J z≠0 := hqne.mono fun z hz => (div_ne_zero_iff.mp hz).1
  obtain ⟨θ,hθ,hsep⟩ := equal_exponent_realpart_separation hb hε hC hxr' hxt hi1 hleft
    (tendsto_real_sectorInfinity.eventually hxa') (hxd.comp tendsto_real_sectorInfinity)
    (tendsto_real_stripInfinity.eventually hHa) hHr (hHd.comp tendsto_real_stripInfinity)
    hJa hJ0 hJd (hJr.mono fun _ h => h.1) hJl hJd0 hJdd hJm he hfactor
  refine ⟨T,x,hT,hxa,hleft,hright,hxto,hxr'.and hGreal,hGft,hGa,?_⟩
  intro ω S hω
  obtain ⟨η,R,hη,hmap⟩ := comparable_sector_mapping hGft hψ hψa hψd hmod harg'
    admissible_baseLoss hemajor ω S hω
  obtain ⟨κ,U,hκ,hmod'⟩ := hmod
  refine ⟨fun r => max (η r) (max (κ r) (θ r)),max R U,hη.max (hκ.max hθ),?_,?_,?_⟩
  · intro w hw
    exact hmap w ⟨(le_max_left _ _).trans_lt hw.1,hw.2.trans_le (sub_le_sub_left (le_max_left _ _) _)⟩
  · intro w hw
    exact hmod' w ⟨(le_max_right _ _).trans_lt hw.1,
      hw.2.trans_le (sub_le_sub_left ((le_max_left _ _).trans (le_max_right _ _)) _)⟩
  · intro δ hδ
    obtain ⟨W,hW⟩ := hsep δ hδ
    exact ⟨W,fun w hw => hW w ⟨hw.1,hw.2.trans_le
      (sub_le_sub_left ((le_max_right _ _).trans (le_max_right _ _)) _)⟩⟩

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

theorem inverse_error_absorption {J H x : ℂ → ℂ} {b ε c M : ℝ}
    (hb : 0<b) (hε : 0<ε) (hM : 0<M)
    (hJa : ∀ᶠ z in stripInfinity,AnalyticAt ℂ J z)
    (hJr : ∀ᶠ t : ℝ in atTop,(J (t:ℂ)).im=0)
    (hJd0 : ∀ᶠ z in stripInfinity,deriv J z≠0)
    (hJdd : Tendsto (fun z => deriv (deriv J) z/deriv J z) stripInfinity (𝓝 0))
    (hJl : Tendsto (fun t : ℝ => (J (t:ℂ)).re) atTop (𝓝 c))
    (hJm : ∃ A : ℝ,MonotoneOn (fun t : ℝ => (J (t:ℂ)).re) (Ici A) ∨
      AntitoneOn (fun t : ℝ => (J (t:ℂ)).re) (Ici A))
    (hxa : ∀ᶠ r : ℝ in atTop,AnalyticAt ℂ x (r:ℂ))
    (hxd : Tendsto (fun r : ℝ => (r:ℂ)*deriv x (r:ℂ)) atTop (𝓝 ((b:ℂ)⁻¹)))
    (hHa : ∀ᶠ s : ℝ in atTop,AnalyticAt ℂ H (s:ℂ))
    (hHr : ∀ᶠ s : ℝ in atTop,(H (s:ℂ)).im=0 ∧ 0<(H (s:ℂ)).re)
    (hHd : Tendsto (fun s : ℝ => deriv H (s:ℂ)/H (s:ℂ)) atTop (𝓝 (b:ℂ)))
    (hxt : Tendsto (fun r : ℝ => (x (r:ℂ)).re) atTop atTop)
    (hinv : ∀ᶠ r : ℝ in atTop,H ((x (r:ℂ)).re:ℂ)=(r:ℂ)) :
    ∃ ω : ℝ → ℝ,AdmissibleAngularLoss ω ∧
      ∀ δ : ℝ,0<δ → ∀ᶠ r : ℝ in atTop,
        |M*(‖deriv J ((x (r:ℂ)).re:ℂ)‖+Real.exp (-ε*(x (r:ℂ)).re))|≤δ*ω r := by
  obtain ⟨ω,hω,hds⟩ := inverse_derivative_loss_absorption hb hJa hJr hJd0 hJdd hJl hJm hxa hxd
  have hes := inverse_exponential_loss_absorption hb hε hHa hHr hHd hxt hinv hω M
  refine ⟨ω,hω,?_⟩
  intro δ hδ
  filter_upwards [hds (δ/(2*M)) (by positivity),hes (δ/2) (by positivity)] with r hd he
  rw [abs_of_nonneg (show 0≤M*(‖deriv J ((x (r:ℂ)).re:ℂ)‖+Real.exp (-ε*(x (r:ℂ)).re)) by positivity)]
  have hh := mul_le_mul_of_nonneg_left hd hM.le
  have hkeq : M*(δ/(2*M)*ω r)=δ/2*ω r := by field_simp
  rw [hkeq] at hh
  nlinarith only [hh,he]

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma strict_loss_tendsto_zero {e ω : ℝ → ℝ} (hω : AdmissibleAngularLoss ω)
    (he : ∀ δ : ℝ,0<δ → ∀ᶠ r : ℝ in atTop,|e r|≤δ*ω r) :
    Tendsto e atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun r => norm_nonneg (e r))) _ hω.tendsto_zero
  simpa only [Real.norm_eq_abs,one_mul] using he 1 zero_lt_one

theorem positive_limit_phase {F : ℂ → ℂ} {a e ω : ℝ → ℝ} {c : ℝ}
    (hc : 0<c) (ha : Tendsto a atTop (𝓝 c)) (hω : AdmissibleAngularLoss ω)
    (he : ∀ δ : ℝ,0<δ → ∀ᶠ r : ℝ in atTop,|e r|≤δ*ω r)
    (heq : ∀ᶠ z in sectorInfinity,‖F z/z-(a ‖z‖:ℂ)‖≤|e ‖z‖|) :
    ∀ᶠ z in sectorInfinity,|(F z).arg|≤|z.arg|+ω ‖z‖ := by
  have hap : ∀ᶠ r : ℝ in atTop,c/2<a r := ha.eventually (eventually_gt_nhds (by linarith))
  have hV0 : ∀ᶠ z in sectorInfinity,(a ‖z‖:ℂ)*z≠0 := by
    filter_upwards [tendsto_norm_sectorInfinity.eventually hap,SectorEventually.realpart_pos] with z hz hr
    change 0<z.re at hr
    exact mul_ne_zero (by exact_mod_cast (show 0<a ‖z‖ by linarith).ne') (fun he => by simp [he] at hr)
  have hVarg : ∀ᶠ z in sectorInfinity,|((a ‖z‖:ℂ)*z).arg|≤|z.arg| := by
    filter_upwards [tendsto_norm_sectorInfinity.eventually hap] with z hz
    rw [Complex.arg_real_mul _ (show 0<a ‖z‖ by linarith)]
  let d : ℝ → ℝ := fun r => (2/c)*e r
  have hdt : Tendsto d atTop (𝓝 0) := by
    simpa only [d,mul_zero] using (strict_loss_tendsto_zero hω he).const_mul (2/c)
  have hclose : ∀ᶠ z in sectorInfinity,‖F z/((a ‖z‖:ℂ)*z)-1‖≤|d ‖z‖| := by
    filter_upwards [heq,tendsto_norm_sectorInfinity.eventually hap,SectorEventually.realpart_pos] with z hz ha hr
    change 0<z.re at hr
    have hz0 : z≠0 := fun he => by simp [he] at hr
    have hap : 0<a ‖z‖ := by linarith
    have ha0 : (a ‖z‖:ℂ)≠0 := by exact_mod_cast hap.ne'
    have hid : F z/((a ‖z‖:ℂ)*z)-1=(F z/z-(a ‖z‖:ℂ))/(a ‖z‖:ℂ) := by field_simp
    rw [hid,norm_div,Complex.norm_of_nonneg hap.le]
    have hca : (a ‖z‖)⁻¹≤2/c := by
      rw [inv_eq_one_div]
      apply (div_le_div_iff₀ hap hc).mpr
      linarith
    calc
      ‖F z/z-(a ‖z‖:ℂ)‖/a ‖z‖ ≤ |e ‖z‖|/a ‖z‖ := div_le_div_of_nonneg_right hz hap.le
      _ ≤ (2/c)*|e ‖z‖| := by rw [div_eq_mul_inv]; nlinarith [abs_nonneg (e ‖z‖)]
      _ = |d ‖z‖| := by dsimp [d]; rw [abs_mul,abs_of_pos (show 0<2/c by positivity)]
  have hang := inward_phase_small_perturbation hV0 hVarg hdt hclose
  filter_upwards [hang,tendsto_norm_sectorInfinity.eventually (he (c/4) (by positivity))] with z hz hez
  have hmult := mul_le_mul_of_nonneg_left hez (show 0≤4/c by positivity)
  have hid : (4/c)*(c/4*ω ‖z‖)=ω ‖z‖ := by field_simp
  rw [hid] at hmult
  have hd : 2*|d ‖z‖|=(4/c)*|e ‖z‖| := by
    dsimp [d]
    rw [abs_mul,abs_of_pos (show 0<2/c by positivity)]
    ring
  rw [hd] at hz
  exact hz.trans (add_le_add le_rfl hmult)

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

theorem positive_equal_exponent_chart {F H J E : ℂ → ℂ} {b ε C c : ℝ}
    (hb : 0<b) (hε : 0<ε) (hC : 0≤C) (hc : 0<c)
    (hFa : ∀ᶠ z in stripInfinity,AnalyticAt ℂ F z)
    (hHa : ∀ᶠ z in stripInfinity,AnalyticAt ℂ H z)
    (hF0 : ∀ᶠ z in stripInfinity,F z≠0)
    (hH0 : ∀ᶠ z in stripInfinity,H z≠0)
    (hFr : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0 ∧ 0<(F (t:ℂ)).re)
    (hHr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0 ∧ 0<(H (t:ℂ)).re)
    (hFt : Tendsto (fun t : ℝ => (F (t:ℂ)).re) atTop atTop)
    (hHt : Tendsto (fun t : ℝ => (H (t:ℂ)).re) atTop atTop)
    (hFd : Tendsto (fun z => deriv F z/F z) stripInfinity (𝓝 (b:ℂ)))
    (hHd : Tendsto (fun z => deriv H z/H z) stripInfinity (𝓝 (b:ℂ)))
    (hJa : ∀ᶠ z in stripInfinity,AnalyticAt ℂ J z)
    (hJ0 : ∀ᶠ z in stripInfinity,J z≠0)
    (hJr : ∀ᶠ t : ℝ in atTop,(J (t:ℂ)).im=0)
    (hJd : Tendsto (fun z => deriv J z/J z) stripInfinity (𝓝 0))
    (hJd0 : ∀ᶠ z in stripInfinity,deriv J z≠0)
    (hJdd : Tendsto (fun z => deriv (deriv J) z/deriv J z) stripInfinity (𝓝 0))
    (hJl : Tendsto (fun t : ℝ => (J (t:ℂ)).re) atTop (𝓝 c))
    (hJm : ∃ A : ℝ,MonotoneOn (fun t : ℝ => (J (t:ℂ)).re) (Ici A) ∨
      AntitoneOn (fun t : ℝ => (J (t:ℂ)).re) (Ici A))
    (he : ∀ᶠ z in stripInfinity,‖E z‖≤C*Real.exp (-ε*z.re))
    (hfactor : ∀ᶠ z in stripInfinity,F z/H z=J z*(1+E z)) :
    ∃ (T : ℝ) (x : ℂ → ℂ),0<T ∧
      AnalyticOnNhd ℂ x {w | 0<w.re ∧ T<‖w‖} ∧
      (∀ w : ℂ,0<w.re → T<‖w‖ → H (x w)=w) ∧
      (∀ᶠ t : ℝ in atTop,x (H (t:ℂ))=(t:ℂ)) ∧
      Tendsto x sectorInfinity stripInfinity ∧
      (∀ᶠ r : ℝ in atTop,(x (r:ℂ)).im=0 ∧ (F (x (r:ℂ))).im=0 ∧ 0<(F (x (r:ℂ))).re) ∧
      Tendsto (fun r : ℝ => (F (x (r:ℂ))).re) atTop atTop ∧
      (∀ᶠ w in sectorInfinity,AnalyticAt ℂ (fun z => F (x z)) w) ∧
      ∀ (ω : ℝ → ℝ) (S : ℝ),AdmissibleAngularLoss ω →
        ∃ (η : ℝ → ℝ) (R : ℝ),AdmissibleAngularLoss η ∧
          (∀ w∈lossSector η R,F (x w)∈lossSector ω S) ∧
          (∀ w∈lossSector η R,(F (x (‖w‖:ℂ))).re/2≤‖F (x w)‖ ∧
            ‖F (x w)‖≤2*(F (x (‖w‖:ℂ))).re) := by
  obtain ⟨T,hT,x,hxa,hleft,hright,hxr,hxt,hxto,hinc,hxd⟩ :=
    positive_exponential_inverse_asymptotic hb hHa hH0 hHr hHt hHd
  have hxr' : ∀ᶠ r : ℝ in atTop,(x (r:ℂ)).im=0 := (eventually_gt_atTop T).mono fun r hr => hxr r hr
  have hdom : ∀ᶠ w in sectorInfinity,0<w.re ∧ T<‖w‖ :=
    SectorEventually.realpart_pos.and (tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop T))
  have hxa' : ∀ᶠ w in sectorInfinity,AnalyticAt ℂ x w := hdom.mono fun w hw => hxa w hw
  have hi : ∀ δ : ℝ,0<δ → ∀ᶠ w in sectorInfinity,
      ‖x w-x (‖w‖:ℂ)-Complex.I*(w.arg/b:ℝ)‖≤δ*|w.arg| := by
    intro δ hδ
    obtain ⟨U,hU⟩ := hinc δ hδ
    filter_upwards [SectorEventually.realpart_pos,tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop U)] with w hw hUw
    exact hU w hw hUw
  have hi1 : ∃ U : ℝ,∀ w : ℂ,0<w.re → U<‖w‖ →
      ‖x w-x (‖w‖:ℂ)-Complex.I*(w.arg/b:ℝ)‖≤|w.arg| := by
    simpa only [one_mul] using hinc 1 zero_lt_one
  obtain ⟨hGreal,hGft,hGa,hmod,ψ,hψa,hψd,hψ⟩ :=
    inverse_chart_data hb hFa hF0 hFr hFt hFd hxa' hxr' hxt hxto hi hxd
  have hri : ∀ᶠ r : ℝ in atTop,H ((x (r:ℂ)).re:ℂ)=(r:ℂ) := by
    filter_upwards [hxr',eventually_gt_atTop T] with r hr hrt
    have heq : x (r:ℂ)=((x (r:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using hr)
    rw [←heq]
    exact hleft (r:ℂ) (by simpa using hT.trans hrt)
      (by simpa only [Complex.norm_of_nonneg (hT.trans hrt).le] using hrt)
  obtain ⟨K,U,hK,herror⟩ := equal_exponent_ratio_error hb hε hC hxr' hxt hi1 hleft
    hJa hJ0 hJd hJr hJl hJd0 hJdd he hfactor
  obtain ⟨χ,hχ,hχe⟩ := inverse_error_absorption hb hε hK hJa hJr hJd0 hJdd hJl hJm
    (tendsto_real_sectorInfinity.eventually hxa') (hxd.comp tendsto_real_sectorInfinity)
    (tendsto_real_stripInfinity.eventually hHa) hHr (hHd.comp tendsto_real_stripInfinity) hxt hri
  have hap : ∀ᶠ w in sectorInfinity,‖F (x w)/w-((J ((x (‖w‖:ℂ)).re:ℂ)).re:ℂ)‖ ≤
      |K*(‖deriv J ((x (‖w‖:ℂ)).re:ℂ)‖+Real.exp (-ε*(x (‖w‖:ℂ)).re))| := by
    filter_upwards [SectorEventually.realpart_pos,tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop U)] with w hw hwU
    rw [abs_of_nonneg (show 0≤K*(‖deriv J ((x (‖w‖:ℂ)).re:ℂ)‖+Real.exp (-ε*(x (‖w‖:ℂ)).re)) by positivity)]
    exact herror w hw hwU
  have harg := positive_limit_phase hc (hJl.comp hxt) hχ hχe hap
  have harg' : ∀ᶠ w in sectorInfinity,|(F (x w)).arg|≤|w.arg|+|χ ‖w‖| := by
    filter_upwards [harg,tendsto_norm_sectorInfinity.eventually hχ.1] with w hw hχw
    simpa only [abs_of_pos hχw.1] using hw
  have hχbound : ∀ᶠ r : ℝ in atTop,|χ r|≤χ r := hχ.1.mono fun r hr => (abs_of_pos hr.1).le
  refine ⟨T,x,hT,hxa,hleft,hright,hxto,hxr'.and hGreal,hGft,hGa,?_⟩
  intro ω S hω
  obtain ⟨η,R,hη,hmap⟩ := comparable_sector_mapping hGft hψ hψa hψd hmod harg' hχ hχbound ω S hω
  obtain ⟨κ,V,hκ,hmod'⟩ := hmod
  exact ⟨fun r => max (η r) (κ r),max R V,hη.max hκ,
    fun w hw => hmap w ⟨(le_max_left _ _).trans_lt hw.1,hw.2.trans_le (sub_le_sub_left (le_max_left _ _) _)⟩,
    fun w hw => hmod' w ⟨(le_max_right _ _).trans_lt hw.1,hw.2.trans_le (sub_le_sub_left (le_max_right _ _) _)⟩⟩

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

theorem constant_equal_exponent_chart {F H E : ℂ → ℂ} {b ε C c : ℝ}
    (hb : 0<b) (hε : 0<ε) (hC : 0≤C) (hc : 0<c)
    (hFa : ∀ᶠ z in stripInfinity,AnalyticAt ℂ F z)
    (hHa : ∀ᶠ z in stripInfinity,AnalyticAt ℂ H z)
    (hF0 : ∀ᶠ z in stripInfinity,F z≠0)
    (hH0 : ∀ᶠ z in stripInfinity,H z≠0)
    (hFr : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0 ∧ 0<(F (t:ℂ)).re)
    (hHr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0 ∧ 0<(H (t:ℂ)).re)
    (hFt : Tendsto (fun t : ℝ => (F (t:ℂ)).re) atTop atTop)
    (hHt : Tendsto (fun t : ℝ => (H (t:ℂ)).re) atTop atTop)
    (hFd : Tendsto (fun z => deriv F z/F z) stripInfinity (𝓝 (b:ℂ)))
    (hHd : Tendsto (fun z => deriv H z/H z) stripInfinity (𝓝 (b:ℂ)))
    (he : ∀ᶠ z in stripInfinity,‖E z‖≤C*Real.exp (-ε*z.re))
    (hfactor : ∀ᶠ z in stripInfinity,F z/H z=(c:ℂ)*(1+E z)) :
    ∃ (T : ℝ) (x : ℂ → ℂ),0<T ∧
      AnalyticOnNhd ℂ x {w | 0<w.re ∧ T<‖w‖} ∧
      (∀ w : ℂ,0<w.re → T<‖w‖ → H (x w)=w) ∧
      (∀ᶠ t : ℝ in atTop,x (H (t:ℂ))=(t:ℂ)) ∧
      Tendsto x sectorInfinity stripInfinity ∧
      (∀ᶠ r : ℝ in atTop,(x (r:ℂ)).im=0 ∧ (F (x (r:ℂ))).im=0 ∧ 0<(F (x (r:ℂ))).re) ∧
      Tendsto (fun r : ℝ => (F (x (r:ℂ))).re) atTop atTop ∧
      (∀ᶠ w in sectorInfinity,AnalyticAt ℂ (fun z => F (x z)) w) ∧
      ∀ (ω : ℝ → ℝ) (S : ℝ),AdmissibleAngularLoss ω →
        ∃ (η : ℝ → ℝ) (R : ℝ),AdmissibleAngularLoss η ∧
          (∀ w∈lossSector η R,F (x w)∈lossSector ω S) ∧
          (∀ w∈lossSector η R,(F (x (‖w‖:ℂ))).re/2≤‖F (x w)‖ ∧
            ‖F (x w)‖≤2*(F (x (‖w‖:ℂ))).re) := by
  obtain ⟨T,hT,x,hxa,hleft,hright,hxr,hxt,hxto,hinc,hxd⟩ :=
    positive_exponential_inverse_asymptotic hb hHa hH0 hHr hHt hHd
  have hxr' : ∀ᶠ r : ℝ in atTop,(x (r:ℂ)).im=0 := (eventually_gt_atTop T).mono fun r hr => hxr r hr
  have hdom : ∀ᶠ w in sectorInfinity,0<w.re ∧ T<‖w‖ :=
    SectorEventually.realpart_pos.and (tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop T))
  have hxa' : ∀ᶠ w in sectorInfinity,AnalyticAt ℂ x w := hdom.mono fun w hw => hxa w hw
  have hi : ∀ δ : ℝ,0<δ → ∀ᶠ w in sectorInfinity,
      ‖x w-x (‖w‖:ℂ)-Complex.I*(w.arg/b:ℝ)‖≤δ*|w.arg| := by
    intro δ hδ
    obtain ⟨U,hU⟩ := hinc δ hδ
    filter_upwards [SectorEventually.realpart_pos,tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop U)] with w hw hUw
    exact hU w hw hUw
  have hi1 : ∃ U : ℝ,∀ w : ℂ,0<w.re → U<‖w‖ →
      ‖x w-x (‖w‖:ℂ)-Complex.I*(w.arg/b:ℝ)‖≤|w.arg| := by
    simpa only [one_mul] using hinc 1 zero_lt_one
  obtain ⟨hGreal,hGft,hGa,hmod,ψ,hψa,hψd,hψ⟩ :=
    inverse_chart_data hb hFa hF0 hFr hFt hFd hxa' hxr' hxt hxto hi hxd
  have hri : ∀ᶠ r : ℝ in atTop,H ((x (r:ℂ)).re:ℂ)=(r:ℂ) := by
    filter_upwards [hxr',eventually_gt_atTop T] with r hr hrt
    have heq : x (r:ℂ)=((x (r:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using hr)
    rw [←heq]
    exact hleft (r:ℂ) (by simpa using hT.trans hrt)
      (by simpa only [Complex.norm_of_nonneg (hT.trans hrt).le] using hrt)
  obtain ⟨D,hD,hDe⟩ := inverse_strip_exponential_error hb hε hC hxr' hxt hi1 he
  let e : ℝ → ℝ := fun r => c*D*Real.exp (-ε*(x (r:ℂ)).re)
  have hes : ∀ δ : ℝ,0<δ → ∀ᶠ r : ℝ in atTop,|e r|≤δ*baseLoss r := by
    intro δ hδ
    have hh := inverse_exponential_loss_absorption hb hε
      (tendsto_real_stripInfinity.eventually hHa) hHr (hHd.comp tendsto_real_stripInfinity)
      hxt hri admissible_baseLoss (c*D) δ hδ
    filter_upwards [hh] with r hr
    simpa only [e,abs_of_pos (show 0<c*D*Real.exp (-ε*(x (r:ℂ)).re) by positivity)] using hr
  have hap : ∀ᶠ w in sectorInfinity,‖F (x w)/w-(c:ℂ)‖≤|e ‖w‖| := by
    filter_upwards [hDe,hxto.eventually hfactor,hdom] with w he hf hw
    rw [hleft w hw.1 hw.2] at hf
    rw [hf]
    have hid : (c:ℂ)*(1+E (x w))-(c:ℂ)=(c:ℂ)*E (x w) := by ring
    rw [hid,norm_mul,Complex.norm_of_nonneg hc.le]
    have hh := mul_le_mul_of_nonneg_left he hc.le
    dsimp [e]
    rw [abs_of_pos (show 0<c*D*Real.exp (-ε*(x (‖w‖:ℂ)).re) by positivity)]
    nlinarith only [hh]
  have harg := positive_limit_phase hc (tendsto_const_nhds (x := c)) admissible_baseLoss hes hap
  let χ := baseLoss
  have hχ : AdmissibleAngularLoss χ := admissible_baseLoss
  have harg' : ∀ᶠ w in sectorInfinity,|(F (x w)).arg|≤|w.arg|+|χ ‖w‖| := by
    filter_upwards [harg,tendsto_norm_sectorInfinity.eventually hχ.1] with w hw hχw
    simpa only [abs_of_pos hχw.1] using hw
  have hχbound : ∀ᶠ r : ℝ in atTop,|χ r|≤χ r := hχ.1.mono fun r hr => (abs_of_pos hr.1).le
  refine ⟨T,x,hT,hxa,hleft,hright,hxto,hxr'.and hGreal,hGft,hGa,?_⟩
  intro ω S hω
  obtain ⟨η,R,hη,hmap⟩ := comparable_sector_mapping hGft hψ hψa hψd hmod harg' hχ hχbound ω S hω
  obtain ⟨κ,V,hκ,hmod'⟩ := hmod
  exact ⟨fun r => max (η r) (κ r),max R V,hη.max hκ,
    fun w hw => hmap w ⟨(le_max_left _ _).trans_lt hw.1,hw.2.trans_le (sub_le_sub_left (le_max_left _ _) _)⟩,
    fun w hw => hmod' w ⟨(le_max_right _ _).trans_lt hw.1,hw.2.trans_le (sub_le_sub_left (le_max_right _ _) _)⟩⟩

end DegeneratingTrees.Clock
end

end OAI
