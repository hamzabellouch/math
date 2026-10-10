import Mathlib
import OAI.Analysis.BiholderTransport.Contact.ContactCharts
import OAI.Analysis.BiholderTransport.Contact.LocalCEMS2
import OAI.Analysis.BiholderTransport.Volume.UniformCharts

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Manifold Bundle Metric
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section IntrinsicCEMS
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma exists_uniform_intrinsic_contact_bounds {ell upper : ℝ} (hell : 0<ell)
    (hupper : 0<upper) :
    ∃ chi eta : ℝ, 0<chi ∧ 0<eta ∧ ∀ (v : M → ℝ) (hv : Continuous v)
      (G : Set M), MeasurableSet G → (∀ᵐ x ∂metricVolume n, x∈G) →
      (∀ x∈G, MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x) →
      InjOn (contactSelection hv) G →
      (∀ x∈G, ∃ p A, NormalAlexandrovContact (n := n) v x p A) →
      (∀ B : Set M, MeasurableSet B → B⊆G →
        ENNReal.ofReal ell*metricVolume n B≤ metricVolume n (contactSelection hv '' B) ∧
        metricVolume n (contactSelection hv '' B)≤ENNReal.ofReal upper*metricVolume n B) →
      ∀ᵐ x ∂metricVolume n, ∃ p A,
        NormalAlexandrovContact (n := n) v x p A ∧
        (∀ w, w≠0 → 0 < inner ℝ ((normalHessianOperator x p+A) w) w) ∧
        chi≤expJacobian (n := n) x p*|(normalHessianOperator x p+A).det| ∧
        expJacobian (n := n) x p*|(normalHessianOperator x p+A).det|≤eta := by
  obtain ⟨C,hC,c,d,hc,hd,hcharts⟩ := exists_uniform_volume_charts (n := n) (M := M)
  let ell0 : ℝ := ell/((C:ℝ)^n*(C:ℝ)^n)
  let upper0 : ℝ := (C:ℝ)^n*upper*(C:ℝ)^n
  have hCr : 0<(C:ℝ) := hC
  have hell0 : 0<ell0 := by dsimp [ell0]; positivity
  have hupper0 : 0<upper0 := by dsimp [upper0]; positivity
  refine ⟨ell0*c/d,upper0*d/c,div_pos (mul_pos hell0 hc) hd,
    div_pos (mul_pos hupper0 hd) hc,?_⟩
  intro v hv G hGm hGae hGD hGi hReg hmass
  suffices H : ∀ᵐ x ∂metricVolume n, x∈G → ∃ p A,
      NormalAlexandrovContact (n := n) v x p A ∧
      (∀ w, w≠0 → 0 < inner ℝ ((normalHessianOperator x p+A) w) w) ∧
      ell0*c/d≤expJacobian (n := n) x p*|(normalHessianOperator x p+A).det| ∧
      expJacobian (n := n) x p*|(normalHessianOperator x p+A).det|≤upper0*d/c by
    filter_upwards [H,hGae] with x hx hxG
    exact hx hxG
  apply ae_of_locally_ae
  intro x hx
  let T := contactSelection hv
  obtain ⟨a,U,hUo,hxU,hUs,hda,hdai,hja⟩ := hcharts x
  obtain ⟨b,V,hVo,hTxV,hVs,hdb,hdbi,hjb⟩ := hcharts (T x)
  have hnear : T ⁻¹' V∈𝓝 x :=
    (contactSelection_continuousAt_of_mdifferentiable hv (hGD x hx)).preimage_mem_nhds
      (hVo.mem_nhds hTxV)
  obtain ⟨W,hWs,hWo,hxW⟩ := _root_.mem_nhds_iff.mp hnear
  let B := G∩(U∩W)
  have hBG : B⊆G := inter_subset_left
  have hBU : B⊆U := fun _ hz => hz.2.1
  have hTBV : T '' B⊆V := by
    rintro _ ⟨z,hz,rfl⟩
    exact hWs hz.2.2
  have hBm : MeasurableSet B := hGm.inter (hUo.inter hWo).measurableSet
  have hloc := local_contact_cems_full hv hBm (fun z hz => hGD z (hBG hz))
    (hGi.mono hBG) (fun z hz => hReg z (hBG hz)) a b
    (hBU.trans hUs) (hTBV.trans hVs) hC hC (hda.mono hBU)
    (hdai.mono (image_mono hBU)) (hdb.mono hTBV) (hdbi.mono (image_mono hTBV))
    (ENNReal.ofReal_pos.mpr hell) (fun A hAm hAB => hmass A hAm (hAB.trans hBG))
  have hloc' := (ae_restrict_iff' hBm).mp hloc
  refine ⟨U∩W,hUo.inter hWo,⟨hxU,hxW⟩,?_⟩
  filter_upwards [hloc',hGae] with z hz hzG hzUW
  obtain ⟨p,A,hp,hpd,R,S,hl,hu,heq⟩ := hz ⟨hzG,hzUW⟩
  have hlr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hl
  have hur := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top ENNReal.coe_ne_top) ENNReal.ofReal_ne_top)
        (ENNReal.pow_ne_top ENNReal.coe_ne_top)) hu
  simp only [ENNReal.toReal_div,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.coe_toReal,ENNReal.toReal_ofReal hell.le,ENNReal.toReal_ofReal hupper.le,
    ENNReal.toReal_ofReal (abs_nonneg _)] at hlr hur
  have hbounds := scalar_intrinsic_jacobian_bounds (abs_nonneg _)
    (mul_nonneg (expJacobian_nonneg z p) (abs_nonneg _)) hell0.le hc hd
    (hja z hzUW.1) (hjb (T z) (hWs hzUW.2)) hlr hur heq
  exact ⟨p,A,hp,hpd,hbounds⟩

lemma minimizing_dualPair_uniform_intrinsic_cems {lam cap : ℝ} (hlam : 0<lam)
    (hcap : lam≤cap) :
    ∃ chi eta : ℝ, 0<chi ∧ 0<eta ∧ ∀ (rho0 rho1 : M → ℝ),
      AdmissibleDensity (metricVolume n) lam cap rho0 →
      AdmissibleDensity (metricVolume n) lam cap rho1 →
      ∀ (u v : M →ᵇ ℝ), IsCostDualPair u v →
      (∀ a b : M →ᵇ ℝ, (∀ x y,0≤contactGap a b x y) →
        dualObjective (densityMeasure (metricVolume n) rho0)
          (densityMeasure (metricVolume n) rho1) (u,v) ≤
        dualObjective (densityMeasure (metricVolume n) rho0)
          (densityMeasure (metricVolume n) rho1) (a,b)) →
      ∀ᵐ x ∂metricVolume n, ∃ p A,
        NormalAlexandrovContact (n := n) v x p A ∧
        (∀ w, w≠0 → 0 < inner ℝ ((normalHessianOperator x p+A) w) w) ∧
        chi≤expJacobian (n := n) x p*|(normalHessianOperator x p+A).det| ∧
        expJacobian (n := n) x p*|(normalHessianOperator x p+A).det|≤eta := by
  obtain ⟨chi,eta,hchi,heta,H⟩ := exists_uniform_intrinsic_contact_bounds
    (n := n) (M := M) (div_pos hlam (hlam.trans_le hcap))
      (div_pos (hlam.trans_le hcap) hlam)
  refine ⟨chi,eta,hchi,heta,?_⟩
  intro rho0 rho1 h0 h1 u v huv hmin
  obtain ⟨G,hGm,hGae,hGi,hGD,_hGc,hReg,hmass⟩ :=
    minimizing_dualPair_regular_contact_set hlam hcap h0 h1 huv hmin
  exact H v v.continuous G hGm hGae hGD hGi hReg hmass

end IntrinsicCEMS
end WeakMTWTransport

end

end

end

end OAI
