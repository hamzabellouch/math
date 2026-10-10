import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.ObservationMeanBounds
import OAI.Analysis.CoulombRadii.ThomasFermi.TFResponseMargins
import OAI.Analysis.CoulombRadii.Variational.RetainedMasterTransfer
import OAI.Analysis.CoulombRadii.FormDomain.RetainedPotentialMean
import OAI.Analysis.CoulombRadii.Packets.InverseErrorScale

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
namespace NeutralAtom

theorem physical_retained_inverse_means (g₀ : 𝓢(Position,ℝ))
    (hg : ∀ z, 1<‖z‖ → g₀ z=0) (hm : (∫ z,g₀ z^2)=1)
    (hrad : ∀ z,g₀ z=g₀ (EuclideanSpace.single 0 ‖z‖)) :
    ∃ C D₁ E₁ F K N₁ B₀ : ℝ,
      0<C ∧ 0<D₁ ∧ 0<E₁ ∧ 0<F ∧ 0<K ∧ 0<N₁ ∧ 0<B₀ ∧
    ∀ {D c A ε : ℝ}, 0 ≤ D → 0<c → 0<A → 0<ε →
    ∃ s₀ : ℝ, 0<s₀ ∧ s₀ ≤ 1 ∧
    ∀ {N J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)), FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h) →
    ∀ {E : ℝ}, (E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D → ∀ {r₀ s : ℝ}, 0<r₀ → 0<s → s<s₀ →
    c*(1+packetExponent)*s^packetExponent ≤ 1/4 →
    ∀ (j : ℕ), r₀*2^j ≤ s →
    ∀ {B : Set (Fin J → UnorderedArray (N+1))}, MeasurableSet B →
    (r₀*2^j)^42 ≤ (observationLaw J (rawLaw ψ)).real
      (tailObservation (fun k : Fin J => r₀*2^k.val) j ⁻¹' B) →
    ∀ (k : RetainedScales J j) (y : Position) (_ : y≠0), r₀ ≤ ‖y‖ →
    Coulomb.atomicCellScale y ≤ A*(r₀*2^j) →
    letI := rawLaw_isProbability hd.2.2.1 hn
    let a := Coulomb.atomicCellScale y
    let b := a^(6/5:ℝ)
    let w := packetWidth c r₀ s y
    let ell := (r₀*2^k.val.val)^(101/100:ℝ)
    let θ := C*(2*w/a)
    let δ := E₁*(c*(1+packetExponent)*s^packetExponent)
    let field := fun z : ObservationSample (N+1) J => (Z:ℝ)*coulombKernel y-
      potentialOf (conditionalPacketDensity (observationLaw J (rawLaw ψ)) Prod.fst
        (tailObservation (fun l : Fin J => r₀*2^l.val) j) g₀ c r₀ s
        (tailObservation (fun l : Fin J => r₀*2^l.val) j z)) y
    let event := tailObservation (fun l : Fin J => r₀*2^l.val) j ⁻¹' B
    let fieldMean := ((observationLaw J (rawLaw ψ)).real event)⁻¹*
      ∫ z in event, field z ∂observationLaw J (rawLaw ψ)
    ∀ {M Qlo Qhi q L U : ℝ}, 18*b ≤ a → 2*w ≤ a →
    (∀ z∈retainedTailObservation j ⁻¹' B,
      Qlo ≤ ∑ i,packetKernel g₀ c r₀ s (observationArrayPositions k z i) y) →
    (∀ z∈retainedTailObservation j ⁻¹' B,
      (∑ i,packetKernel g₀ c r₀ s (observationArrayPositions k z i) y) ≤ Qhi) →
    (∀ z∈retainedTailObservation j ⁻¹' B,
      rawCount (Metric.closedBall y (2*w+2*b+2*(Real.sqrt 3*ell)))
        (observationArrayPositions k z) ≤ M) →
    0 ≤ L → 0 ≤ U → 0<q → θ ≤ 1 →
    let e := Real.sqrt ((D₁/w^5)*q)+(F/w^4*(2*b)+K/w^4*(Real.sqrt 3*ell))*M
    (∀ {P : ℝ}, 0<P → N₁*(2*w/a) ≤ 1/2 →
      P ≤ Qlo-(B₀/w^4)*(Real.sqrt 3*ell+2*b)*M →
      Coulomb.tfScalarDensity (L+θ*(a^4)⁻¹)*(1+δ)+e<Qlo →
      L-(L/q+2*(B₀/w^3)/P)*(2*a^(-349/50:ℝ))-
        2*(N₁*(2*w/a))*(a^4)⁻¹-ε*a^(-4:ℝ) ≤ fieldMean) ∧
    (Qhi<Coulomb.tfScalarDensity (U-θ*(a^4)⁻¹)*(1-δ)-e →
      fieldMean ≤ U+((Coulomb.tfInteriorConstant Coulomb.thomasFermiKineticConstant/a^4)/q)*
        (2*a^(-349/50:ℝ))+ε*a^(-4:ℝ)) := by
  obtain ⟨C,D₁,E₁,F,K,N₁,B₀,hC,hD₁,hE₁,hF,hK,hN₁,hB₀,Hmean⟩ :=
    arrayEvent_fresh_field_means g₀ hg hm
  refine ⟨C,D₁,E₁,F,K,N₁,B₀,hC,hD₁,hE₁,hF,hK,hN₁,hB₀,?_⟩
  intro D c A ε hD hc hA hε
  obtain ⟨s₀,hs₀,hs₀1,Htransfer⟩ := physical_retained_master_fresh_transfer hD hc hA hε
  refine ⟨s₀,hs₀,hs₀1,?_⟩
  intro N J Z hZ ψ g hd hn hmin E hE hbase r₀ s hr₀ hs hss hscale j hrs B hB hp k y hy hry hya
  dsimp only
  intro M Qlo Qhi q L U hsmall hw hlo hhi hcount hL hU hq hθ
  let a := Coulomb.atomicCellScale y
  let b := a^(6/5:ℝ)
  let w := packetWidth c r₀ s y
  have ha : 0<a := Coulomb.atomicCellScale_pos hy
  have hb : 0<b := Real.rpow_pos_of_pos ha _
  have := rawLaw_isProbability hd.2.2.1 hn
  obtain ⟨u,hu,hum,hue,hlaw,t,ht,T,hT,ho,hcs,hos,hG,hdel,hFtransfer⟩ :=
    Htransfer Z hZ hd hn hmin hE hbase hr₀ hs hss j hrs hB hp y hy hry hya
  have hTM : T.ensemble.totalMass=1 := by rw [T.mass_eq,hum]
  have hnu : ∀ l,20*a ≤ ‖(Coulomb.atom Z hZ).position l-y‖ :=
    Coulomb.atomic_patch_nucleus_distance (Coulomb.atom Z hZ) (fun _ => rfl) y
  have Hmeans := Hmean hc hr₀ hs hscale
    (fun l : RetainedScales J j => (r₀*2^l.val.val)^(101/100:ℝ))
    (fun _ => Real.rpow_pos_of_pos (by positivity) _) k
    (hB.preimage (measurable_retainedTailObservation j)) ψ u hlaw
    (Coulomb.atom Z hZ) T.ensemble T.law hTM ha hb hsmall ht y hnu hcs hw
    hlo hhi hcount hL hU hq hθ
  have hgs : HasCompactSupport (g₀ : Position → ℝ) := by
    apply HasCompactSupport.intro (K := Metric.closedBall 0 1) (isCompact_closedBall _ _)
    intro z hz
    exact hg z (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz)
  have hp0 := (pow_pos (show 0<r₀*2^j by positivity) 42).trans_le hp
  have Htower := retainedEvent_field_mean hd.2.2.1 hn
    (fun l : Fin J => r₀*2^l.val) (fun _ => by positivity) j hB u hum hlaw hp0
    g₀.continuous hgs hm hc hr₀ hs y ((Z:ℝ)*coulombKernel y)
  have HT := hFtransfer g₀ hm hrad hg
  rw [Htower] at HT
  have hgap : (∑ p,Coulomb.sliceExpectation (T.ensemble.vector p)
      (Coulomb.patchSliceTFGap (Coulomb.atom Z hZ) (T.ensemble.vector p) ha hb ht.2 y hnu)) ≤
      2*a^(-349/50:ℝ) := by
    exact hG
  have hfield : (∑ p,Coulomb.sliceExpectation (T.ensemble.vector p) (fun spin x =>
      Coulomb.patchTFScreenedField (Coulomb.atom Z hZ)
        ((T.ensemble.vector p).coreSlice spin x).normalized ha hb ht.2 y hnu y))=
      Coulomb.atomicPatchMeanField (Coulomb.atom Z hZ) (fun _ => rfl) T.ensemble y hy b hb t ht.2 := rfl
  rw [hfield] at Hmeans
  constructor
  · intro P hP hNw hPm hmargin
    have HI := Hmeans.1 hP hNw hPm hmargin
    have hcoef : 0 ≤ L/q+2*(B₀/w^3)/P := by positivity [packetWidth_pos hc hr₀ hs y]
    have HH := mul_le_mul_of_nonneg_left hgap hcoef
    have HT' := (abs_le.mp HT).1
    dsimp only [a,b,w] at HH HI HT' ⊢
    linarith
  · intro hmargin
    have HI := Hmeans.2 hmargin
    have hcoef : 0 ≤ (Coulomb.tfInteriorConstant Coulomb.thomasFermiKineticConstant/a^4)/q := by
      positivity [Coulomb.tfInteriorConstant_nonneg Coulomb.thomasFermiKineticConstant]
    have HH := mul_le_mul_of_nonneg_left hgap hcoef
    have HT' := (abs_le.mp HT).2
    dsimp only [a,b,w] at HH HI HT' ⊢
    linarith
end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
namespace NeutralAtom

lemma inverse_all_errors_majorized {D F K K₀ B κ Λ M a v ell m : ℝ}
    (hD : 0 ≤ D) (hF : 0 ≤ F) (hK : 0 ≤ K) (hK₀ : 0 ≤ K₀) (hB : 0 ≤ B)
    (hκ : 0<κ) (hΛ : 0 ≤ Λ) (hM : 0 ≤ M) (ha : 0<a)
    (hv : κ*a^(1+packetExponent) ≤ v) (hell : ell ≤ Λ*a^(101/100:ℝ))
    (hm : m ≤ M*a^(-3:ℝ)) (hell0 : 0 ≤ ell) (hm0 : 0 ≤ m) :
    (Real.sqrt (D/v^5*a^(-699/100:ℝ))+
      (F/v^4*(2*a^(6/5:ℝ))+K/v^4*(Real.sqrt 3*ell))*m)+
      (K₀/v^4*(Real.sqrt 3*ell))*m+
      (B/v^4*(Real.sqrt 3*ell+2*a^(6/5:ℝ)))*m ≤
    inverseResponseError D (F+B) (K+K₀+B) κ Λ M a := by
  have H := inverseResponseError_majorizes hD (add_nonneg hF hB)
    (add_nonneg (add_nonneg hK hK₀) hB) hκ hΛ hM ha hv hell hm hell0 hm0
  convert H using 1
  ring

lemma tf_response_margins_scaled {hl hh η : ℝ} (hη : 0<η) (hηl : η<hl)
    (hlh : hl ≤ hh) : ∃ ε : ℝ, 0<ε ∧ ε ≤ 1 ∧
    ∀ {h a θ δ e e₀ : ℝ}, h∈Icc hl hh → 0<a → 0 ≤ θ → θ ≤ ε →
    0 ≤ δ → δ ≤ ε → 0 ≤ e → 0 ≤ e₀ → (e+e₀)*a^6 ≤ ε →
    Coulomb.tfScalarDensity ((h-η)/a^4+θ*(a^4)⁻¹)*(1+δ)+e <
      Coulomb.tfScalarDensity h/a^6-e₀ ∧
    Coulomb.tfScalarDensity h/a^6+e₀ <
      Coulomb.tfScalarDensity ((h+η)/a^4-θ*(a^4)⁻¹)*(1-δ)-e := by
  obtain ⟨ε,hε,hε1,H⟩ := Coulomb.exists_tf_response_margins hη hηl hlh
  refine ⟨ε,hε,hε1,?_⟩
  intro h a θ δ e e₀ hh' ha hθ hθε hδ hδε he he₀ hsum
  obtain ⟨Hlo,Hhi⟩ := H hh' hθ hθε hδ hδε (by positivity) hsum
  have hEq₁ : (h-η)/a^4+θ*(a^4)⁻¹=(h-η+θ)/a^4 := by ring
  have hEq₂ : (h+η)/a^4-θ*(a^4)⁻¹=(h+η-θ)/a^4 := by ring
  rw [hEq₁,hEq₂,Coulomb.tfScalarDensity_scale _ ha,Coulomb.tfScalarDensity_scale _ ha]
  constructor
  · apply (mul_lt_mul_iff_left₀ (pow_pos ha 6)).mp
    field_simp [ha.ne'] at Hlo ⊢
    nlinarith
  · apply (mul_lt_mul_iff_left₀ (pow_pos ha 6)).mp
    field_simp [ha.ne'] at Hhi ⊢
    nlinarith

lemma inverse_low_mean_scaled {H a : ℝ} (ha : 0<a) :
    (((H/a^4)/a^(-699/100:ℝ))*(2*a^(-349/50:ℝ)))*a^4=
      2*H*a^(1/100:ℝ) := by
  have hrat : a^(-349/50:ℝ)/a^(-699/100:ℝ)=a^(1/100:ℝ) := by
    rw [←Real.rpow_sub ha]; norm_num
  field_simp [ha.ne'] at hrat ⊢
  rw [hrat]

theorem inverse_errors_uniform {D F K K₀ B κ Λ M A V C E₁ c N H hl hh η : ℝ}
    (hD : 0 ≤ D) (hF : 0 ≤ F) (hK : 0 ≤ K) (hK₀ : 0 ≤ K₀) (hB : 0 ≤ B)
    (hκ : 0<κ) (hΛ : 0 ≤ Λ) (hM : 0 ≤ M) (hA : 0<A)
    (hV : 0 ≤ V) (hC : 0 ≤ C) (hE₁ : 0 ≤ E₁) (hc : 0 ≤ c) (hN : 0 ≤ N)
    (hη : 0<η) (hηl : η<hl) (hlh : hl ≤ hh) :
    ∃ s₀ : ℝ, 0<s₀ ∧ ∀ {s a v ell m h : ℝ},
    0<s → s<s₀ → 0<a → a ≤ A*s → κ*a^(1+packetExponent) ≤ v →
    v/a ≤ V*s^packetExponent → 0 ≤ ell → ell ≤ Λ*a^(101/100:ℝ) →
    0 ≤ m → m ≤ M*a^(-3:ℝ) → h∈Icc hl hh →
    let θ := C*(2*v/a)
    let δ := E₁*(c*(1+packetExponent)*s^packetExponent)
    let e := Real.sqrt (D/v^5*a^(-699/100:ℝ))+
      (F/v^4*(2*a^(6/5:ℝ))+K/v^4*(Real.sqrt 3*ell))*m
    let e₀ := K₀/v^4*(Real.sqrt 3*ell)*m
    let matchError := (B/v^4*(Real.sqrt 3*ell+2*a^(6/5:ℝ)))*m
    18*a^(6/5:ℝ) ≤ a ∧ 2*v ≤ a ∧ θ ≤ 1 ∧ N*(2*v/a) ≤ 1/2 ∧
    Coulomb.tfScalarDensity hl/(2*a^6) ≤ Coulomb.tfScalarDensity h/a^6-e₀-matchError ∧
    Coulomb.tfScalarDensity ((h-η)/a^4+θ*(a^4)⁻¹)*(1+δ)+e <
      Coulomb.tfScalarDensity h/a^6-e₀ ∧
    Coulomb.tfScalarDensity h/a^6+e₀ <
      Coulomb.tfScalarDensity ((h+η)/a^4-θ*(a^4)⁻¹)*(1-δ)-e ∧
    inverseHighMeanError hh B (Coulomb.tfScalarDensity hl/2) κ N a v < η/4 ∧
    2*H*a^(1/100:ℝ) < η/4 := by
  obtain ⟨ε,hε,hε1,Hmargin⟩ := tf_response_margins_scaled hη hηl hlh
  have hhl : 0<hl := hη.trans hηl
  have htf : 0<Coulomb.tfScalarDensity hl := by
    have h := Coulomb.tfScalarDensity_strict (show (0:ℝ) ≤ 0 by rfl) hhl
    simpa [Coulomb.tfScalarDensity] using h
  have hR := inverseResponseError_scaled_tendsto hD hκ (F+B) (K+K₀+B) Λ M
  obtain ⟨s₁,hs₁,Hs₁⟩ := exists_uniform_inner_scale hR hA
    (lt_min hε (by positivity : 0<Coulomb.tfScalarDensity hl/2))
  have ht := (tendsto_positive_rpow_zero (by norm_num [packetExponent] : 0<packetExponent))
  have hlim : Tendsto (fun s =>
      (2*V+2*C*V+4*N*V+E₁*c*(1+packetExponent))*s^packetExponent) (𝓝[>] 0) (𝓝 0) := by
    simpa using ht.const_mul (2*V+2*C*V+4*N*V+E₁*c*(1+packetExponent))
  obtain ⟨s₂,hs₂,Hs₂⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (hlim.eventually (gt_mem_nhds hε))
  change 0<s₂ at hs₂
  obtain ⟨s₃,hs₃,Hs₃⟩ := inverseHighMeanError_uniform
    (H:=hh) (B:=B) (γ:=Coulomb.tfScalarDensity hl/2) (κ:=κ) (N:=N) (V:=V)
    hA hN (by positivity : 0<η/4)
  obtain ⟨s₄,hs₄,Hs₄⟩ := exists_uniform_inner_scale
    (by simpa using (tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<1/100)).const_mul (2*H))
    hA (by positivity : 0<η/4)
  obtain ⟨s₅,hs₅,Hs₅⟩ := exists_uniform_inner_scale
    (by simpa using (tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<1/5)).const_mul (18:ℝ))
    hA (by norm_num : (0:ℝ)<1)
  refine ⟨min s₁ (min s₂ (min s₃ (min s₄ s₅))),by positivity,?_⟩
  intro s a v ell m h hs hss ha has hv hva hell0 hell hm0 hm hh'
  have hs1 := hss.trans_le (min_le_left _ _)
  have hs2 := hss.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hs3 := hss.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hs4 := hss.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hs5 := hss.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hRsmall := Hs₁ hs hs1 ha has
  have hp := Hs₂ ⟨hs,hs2⟩
  change (2*V+2*C*V+4*N*V+E₁*c*(1+packetExponent))*s^packetExponent<ε at hp
  have hsPow : 0 ≤ s^packetExponent := Real.rpow_nonneg hs.le _
  have hpw : 0<1+packetExponent := by norm_num [packetExponent]
  have hv0 : 0<v := (by positivity : 0<κ*a^(1+packetExponent)).trans_le hv
  have hθ0 : 0 ≤ C*(2*v/a) := by positivity
  have hδ0 : 0 ≤ E₁*(c*(1+packetExponent)*s^packetExponent) := by positivity
  have hθ : C*(2*v/a) ≤ ε := by
    have HH := mul_le_mul_of_nonneg_left hva (show 0 ≤ 2*C by positivity)
    have Hne : 0 ≤ (2*V+4*N*V+E₁*c*(1+packetExponent))*s^packetExponent := by positivity
    have Heq : C*(2*v/a)=2*C*(v/a) := by ring
    rw [Heq]
    linarith only [HH,hp,Hne]
  have hδ : E₁*(c*(1+packetExponent)*s^packetExponent) ≤ ε := by
    have Hne : 0 ≤ (2*V+2*C*V+4*N*V)*s^packetExponent := by positivity
    linarith only [hp,Hne]
  have hvsmall : 2*v ≤ a := by
    have HH := mul_le_mul_of_nonneg_left hva (show (0:ℝ) ≤ 2 by norm_num)
    have Hne : 0 ≤ (2*C*V+4*N*V+E₁*c*(1+packetExponent))*s^packetExponent := by positivity
    have hdiv : 2*(v/a) ≤ 1 := by linarith only [HH,hp,Hne,hε1]
    have Hdiv : (2*v)/a ≤ 1 := by simpa only [mul_div_assoc] using hdiv
    simpa only [one_mul] using (div_le_iff₀ ha).mp Hdiv
  have hNsmall : N*(2*v/a) ≤ 1/2 := by
    have HH := mul_le_mul_of_nonneg_left hva (show 0 ≤ 4*N by positivity)
    have Hne : 0 ≤ (2*V+2*C*V+E₁*c*(1+packetExponent))*s^packetExponent := by positivity
    have Heq : N*(2*v/a)=2*N*(v/a) := by ring
    rw [Heq]
    linarith only [HH,hp,Hne,hε1]
  have hthin : 18*a^(6/5:ℝ) ≤ a := by
    have Hthin := (Hs₅ hs hs5 ha has).le
    have heq : a^(6/5:ℝ)=a^(1/5:ℝ)*a := by
      calc
        _ = a^((1/5:ℝ)+1) := by norm_num
        _ = _ := by rw [Real.rpow_add ha,Real.rpow_one]
    rw [heq]
    nlinarith only [Hthin,ha]
  let e := Real.sqrt (D/v^5*a^(-699/100:ℝ))+
      (F/v^4*(2*a^(6/5:ℝ))+K/v^4*(Real.sqrt 3*ell))*m
  let e₀ := K₀/v^4*(Real.sqrt 3*ell)*m
  let em := (B/v^4*(Real.sqrt 3*ell+2*a^(6/5:ℝ)))*m
  have he : 0 ≤ e := by dsimp [e]; positivity
  have he₀ : 0 ≤ e₀ := by dsimp [e₀]; positivity
  have hem : 0 ≤ em := by dsimp [em]; positivity
  have hbound := inverse_all_errors_majorized hD hF hK hK₀ hB hκ hΛ hM ha hv hell hm hell0 hm0
  change e+e₀+em ≤ inverseResponseError D (F+B) (K+K₀+B) κ Λ M a at hbound
  have hmul := mul_le_mul_of_nonneg_right hbound (pow_nonneg ha.le 6)
  have hsum : (e+e₀)*a^6 ≤ ε := by
    have := hRsmall.trans_le (min_le_left _ _)
    nlinarith only [hmul,this,mul_nonneg hem (pow_nonneg ha.le 6)]
  have hmarg := Hmargin hh' ha hθ0 hθ hδ0 hδ he he₀ hsum
  have hP : Coulomb.tfScalarDensity hl/(2*a^6) ≤ Coulomb.tfScalarDensity h/a^6-e₀-em := by
    have htfl := Coulomb.tfScalarDensity_mono hh'.1
    have hhalf := hRsmall.trans_le (min_le_right _ _)
    apply (mul_le_mul_iff_left₀ (pow_pos ha 6)).mp
    field_simp [ha.ne']
    nlinarith only [hmul,hhalf,htfl,mul_nonneg he (pow_nonneg ha.le 6)]
  exact ⟨hthin,hvsmall,hθ.trans hε1,hNsmall,hP,hmarg.1,hmarg.2,
    Hs₃ hs hs3 ha has hva,by simpa only [one_div] using Hs₄ hs hs4 ha has⟩
end NeutralAtom

end

end OAI
