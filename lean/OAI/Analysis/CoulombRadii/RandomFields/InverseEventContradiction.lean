import Mathlib
import OAI.Analysis.CoulombRadii.Packets.PhysicalRetainedMean

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

lemma inverse_high_mean_contradiction {η h hh B γ κ N a v mean : ℝ}
    (hη : 0 < η) (hηh : η < h) (hhh : h ≤ hh) (hB : 0 ≤ B) (hγ : 0 < γ)
    (hκ : 0 < κ) (hN : 0 ≤ N) (ha : 0 < a) (hv : κ*a^(1+packetExponent) ≤ v)
    (herr : inverseHighMeanError hh B γ κ N a v  <  η/4)
    (hmean : (h-η)/a^4-(((h-η)/a^4)/a^(-699/100:ℝ)+2*(B/v^3)/(γ/a^6))*
      (2*a^(-349/50:ℝ))-2*(N*(2*v/a))*(a^4)⁻¹-(η/4)*a^(-4:ℝ) ≤ mean)
    (hbad : mean ≤ (h-2*η)/a^4) : False := by
  have he := inverseHighMeanError_bound (hη.le.trans ((hηh.le).trans hhh)) hB hγ hκ hN
    ha hv (show 0 ≤ (h-η)/a^4 by positivity)
    (show (h-η)/a^4 ≤ hh/a^4 by gcongr; linarith) (le_refl (2*a^(-349/50:ℝ)))
  have he' := he.trans_lt herr
  have hpow : a^(-4:ℝ)=(a^4)⁻¹ := by rw [Real.rpow_neg ha.le]; norm_num
  rw [hpow] at hmean
  have HH := mul_le_mul_of_nonneg_right (hmean.trans hbad) (pow_nonneg ha.le 4)
  have h4 : a^4≠0 := pow_ne_zero _ ha.ne'
  simp only [sub_mul,div_mul_cancel₀ _ h4,mul_assoc,inv_mul_cancel₀ h4,mul_one] at HH
  simp only [add_mul,mul_assoc,inv_mul_cancel₀ h4,mul_one] at he'
  nlinarith only [HH,he',hη]

lemma inverse_low_mean_contradiction {η h H a mean : ℝ} (hη : 0 < η) (ha : 0 < a)
    (herr : 2*H*a^(1/100:ℝ) < η/4)
    (hmean : mean ≤ (h+η)/a^4+((H/a^4)/a^(-699/100:ℝ))*(2*a^(-349/50:ℝ))+
      (η/4)*a^(-4:ℝ)) (hbad : (h+2*η)/a^4 ≤ mean) : False := by
  have HH := mul_le_mul_of_nonneg_right (hbad.trans hmean) (pow_nonneg ha.le 4)
  have hpow : a^(-4:ℝ)=(a^4)⁻¹ := by rw [Real.rpow_neg ha.le]; norm_num
  rw [hpow] at HH
  have he := inverse_low_mean_scaled (H:=H) ha
  have h4 : a^4≠0 := pow_ne_zero _ ha.ne'
  simp only [add_mul,div_mul_cancel₀ _ h4,mul_assoc,inv_mul_cancel₀ h4,mul_one] at HH
  nlinarith only [HH,he,herr,hη]

theorem physical_retained_inverse_event (g₀ : 𝓢(Position,ℝ))
    (hg : ∀ z, 1 < ‖z‖  →  g₀ z=0) (hm : (∫ z,g₀ z^2)=1)
    (hrad : ∀ z,g₀ z=g₀ (EuclideanSpace.single 0 ‖z‖))
    {D c A κ Λ M V K₀ hl hh η : ℝ}
    (hD : 0 ≤ D) (hc : 0 < c) (hA : 0 < A) (hκ : 0 < κ) (hΛ : 0 ≤ Λ)
    (hM : 0 ≤ M) (hV : 0 ≤ V) (hK₀ : 0 ≤ K₀) (hη : 0 < η) (hηl : η < hl) (hlh : hl ≤ hh) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧
    ∀ {N J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)), FormDomain χ h  →  normSquared χ=1  →
      energy Z ψ g  ≤  energy Z χ h)  →
    ∀ {E : ℝ}, (E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ)  →
    energy Z ψ g ≤ E+D  →  ∀ {r₀ s : ℝ}, 0 < r₀  →  0 < s  →  s < s₀  →
    c*(1+packetExponent)*s^packetExponent ≤ 1/4  →
    ∀ (j : ℕ), r₀*2^j ≤ s  →  ∀ (k : RetainedScales J j) (y : Position) (_ : y≠0),
    r₀ ≤ ‖y‖  →  Coulomb.atomicCellScale y ≤ A*(r₀*2^j)  →
    letI := rawLaw_isProbability hd.2.2.1 hn
    let a := Coulomb.atomicCellScale y
    let w := packetWidth c r₀ s y
    let ell := (r₀*2^k.val.val)^(101/100:ℝ)
    let m := M*a^(-3:ℝ)
    let e₀ := K₀/w^4*(Real.sqrt 3*ell)*m
    let field := fun z : ObservationSample (N+1) J => (Z:ℝ)*coulombKernel y-
      potentialOf (conditionalPacketDensity (observationLaw J (rawLaw ψ)) Prod.fst
        (tailObservation (fun l : Fin J => r₀*2^l.val) j) g₀ c r₀ s
        (tailObservation (fun l : Fin J => r₀*2^l.val) j z)) y
    κ*a^(1+packetExponent) ≤ w  →  w/a ≤ V*s^packetExponent  →
    ell ≤ Λ*a^(101/100:ℝ)  →  ∀ {h : ℝ}, h∈Icc hl hh  →
    ∀ {B : Set (Fin J  →  UnorderedArray (N+1))}, MeasurableSet B  →
    (∀ z∈retainedTailObservation j ⁻¹' B,
      rawCount (Metric.closedBall y (2*w+2*a^(6/5:ℝ)+2*(Real.sqrt 3*ell)))
        (observationArrayPositions k z) ≤ m)  →
    ((∀ z∈retainedTailObservation j ⁻¹' B,
       Coulomb.tfScalarDensity h/a^6-e₀ ≤ ∑ i,packetKernel g₀ c r₀ s (observationArrayPositions k z i) y) ∧
      (∀ᵐ z ∂observationLaw J (rawLaw ψ),
        z∈tailObservation (fun l : Fin J => r₀*2^l.val) j ⁻¹' B  →  field z ≤ (h-2*η)/a^4) ∨
     (∀ z∈retainedTailObservation j ⁻¹' B,
       (∑ i,packetKernel g₀ c r₀ s (observationArrayPositions k z i) y) ≤ Coulomb.tfScalarDensity h/a^6+e₀) ∧
      (∀ᵐ z ∂observationLaw J (rawLaw ψ),
        z∈tailObservation (fun l : Fin J => r₀*2^l.val) j ⁻¹' B  →  (h+2*η)/a^4 ≤ field z))  →
    (observationLaw J (rawLaw ψ)).real
      (tailObservation (fun l : Fin J => r₀*2^l.val) j ⁻¹' B) < (r₀*2^j)^42 := by
  obtain ⟨C,D₁,E₁,F,K,N₁,B₀,hC,hD₁,hE₁,hF,hK,hN₁,hB₀,Hmean⟩ :=
    physical_retained_inverse_means g₀ hg hm hrad
  obtain ⟨s₁,hs₁,hs₁1,Hs₁⟩ := Hmean hD hc hA (show 0 < η/4 by positivity)
  obtain ⟨s₂,hs₂,Hs₂⟩ := inverse_errors_uniform (H:=Coulomb.tfInteriorConstant Coulomb.thomasFermiKineticConstant)
    hD₁.le hF.le hK.le hK₀ hB₀.le hκ hΛ hM hA hV hC.le hE₁.le hc.le hN₁.le hη hηl hlh
  obtain ⟨Kcap,hKcap,Hcap⟩ := master_kernel_estimates g₀ hg hm
  refine ⟨min s₁ s₂,lt_min hs₁ hs₂,(min_le_left _ _).trans hs₁1,?_⟩
  intro N J Z hZ ψ g hd hn hmin E hE hbase r₀ s hr₀ hs hss hscale j hrj k y hy hry hya
  dsimp only
  intro hw hwa hell h hh' B hB hcount hbad
  by_contra hp
  have hp' := le_of_not_gt hp
  have ha := Coulomb.atomicCellScale_pos hy
  let a := Coulomb.atomicCellScale y
  let w := packetWidth c r₀ s y
  let ell := (r₀*2^k.val.val)^(101/100:ℝ)
  let m := M*a^(-3:ℝ)
  let e₀ := K₀/w^4*(Real.sqrt 3*ell)*m
  have hhη : η < h := hηl.trans_le hh'.1
  have hs1 := hss.trans_le (min_le_left _ _)
  have hs2 := hss.trans_le (min_le_right _ _)
  have has : a ≤ A*s := hya.trans (mul_le_mul_of_nonneg_left hrj hA.le)
  have hm0 : 0 ≤ m := by dsimp [m]; positivity
  have he0 : 0 ≤ ell := by dsimp [ell]; positivity
  have Hnum := Hs₂ hs hs2 ha has hw hwa he0 hell hm0 (le_refl m) hh'
  obtain ⟨hthin,hww,hθ,hNw,hP,hhi,hlo,hErr,hErr'⟩ := Hnum
  have hl0 : 0 ≤ (h-η)/a^4 := div_nonneg (sub_nonneg.mpr hhη.le) (pow_nonneg ha.le _)
  have hh0 : 0 < h := hη.trans hhη
  have hu0 : 0 ≤ (h+η)/a^4 := by positivity
  have hq : 0 < a^(-699/100:ℝ) := Real.rpow_pos_of_pos ha _
  have := rawLaw_isProbability hd.2.2.1 hn
  have hgs : HasCompactSupport (g₀ : Position  →  ℝ) := by
    apply HasCompactSupport.intro (K:=Metric.closedBall 0 1) (isCompact_closedBall _ _)
    intro z hz
    exact hg z (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz)
  have hf := (integrable_const ((Z:ℝ)*coulombKernel y)).sub
    (conditionalPacketPotential_integrable (observationLaw J (rawLaw ψ)) (rawLaw ψ)
      (observationLaw_rawProjection _) (measurable_tailObservation (fun l : Fin J =>r₀*2^l.val) j)
      g₀.continuous hgs hm hc hr₀ hs y)
  have hp0 : 0 < (observationLaw J (rawLaw ψ)).real
      (tailObservation (fun l : Fin J =>r₀*2^l.val) j ⁻¹' B) :=
    (pow_pos (show 0 < r₀*2^j by positivity) 42).trans_le hp'
  have hγ : 0 < Coulomb.tfScalarDensity hl/2 := by
    have H := Coulomb.tfScalarDensity_strict (show (0:ℝ) ≤ 0 by rfl) (hη.trans hηl)
    have : 0 < Coulomb.tfScalarDensity hl := by simpa [Coulomb.tfScalarDensity] using H
    positivity
  have htfl : 0 < Coulomb.tfScalarDensity hl := by linarith only [hγ]
  rcases hbad with ⟨hgate,hbad⟩ | ⟨hgate,hbad⟩
  · have hupper (z) (_hz : z∈retainedTailObservation j ⁻¹' B) :
        (∑ i,packetKernel g₀ c r₀ s (observationArrayPositions k z i) y) ≤
          (N+1:ℕ)*(Kcap/w^3) := by
      calc
        _  ≤  ∑ i : Fin (N+1), Kcap/w^3 := Finset.sum_le_sum (fun i _ =>
          (le_abs_self _).trans ((Hcap hc hr₀ hs hscale y).2.1 _))
        _ = _ := by simp
    have Hmeans := Hs₁ Z hZ hd hn hmin hE hbase hr₀ hs hs1 hscale j hrj hB hp' k y hy hry hya
      hthin hww hgate hupper hcount hl0 hu0 hq hθ
    have H := Hmeans.1 (P:=Coulomb.tfScalarDensity hl/(2*a^6)) (by positivity)
      hNw hP hhi
    have Hb := normalized_event_le (hB.preimage (measurable_tailObservation _ j)) hf hp0 hbad
    have HP : Coulomb.tfScalarDensity hl/(2*a^6)=(Coulomb.tfScalarDensity hl/2)/a^6 := by ring
    rw [HP] at H
    exact inverse_high_mean_contradiction hη hhη hh'.2 hB₀.le hγ hκ hN₁.le ha hw hErr H Hb
  · have hlower (z) (_hz : z∈retainedTailObservation j ⁻¹' B) :
        0 ≤ ∑ i,packetKernel g₀ c r₀ s (observationArrayPositions k z i) y :=
      Finset.sum_nonneg (fun i _ => packetKernel_nonneg g₀ hc hr₀ hs _ _)
    have Hmeans := Hs₁ Z hZ hd hn hmin hE hbase hr₀ hs hs1 hscale j hrj hB hp' k y hy hry hya
      hthin hww hlower hgate hcount hl0 hu0 hq hθ
    have H := Hmeans.2 hlo
    have Hb := le_normalized_event (hB.preimage (measurable_tailObservation _ j)) hf hp0 hbad
    exact inverse_low_mean_contradiction hη ha hErr' H Hb
end NeutralAtom
end

end

end OAI
