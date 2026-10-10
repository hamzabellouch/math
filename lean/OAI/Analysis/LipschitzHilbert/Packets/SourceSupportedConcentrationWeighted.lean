import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedLatticeData
import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorConcentrationWeighted
import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedConcentrationNeighborhood
import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorConcentrationCentered
import OAI.Analysis.LipschitzHilbert.Trees.SourceLatticeRawData
import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedRawRescale
import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedCovariantRescale

namespace OAI

/-! The original selector concentration with packetwise length control.
Empty initial scales impose no global top-length assumption; constants are unchanged. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal FourierTransform
namespace LipschitzHilbert.SourceLatticePacket

theorem frozen_jet_top_neighborhood_of_supported (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ Ab Am : ℝ, 0 < Ab ∧ 0 < Am ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι)
      (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
      (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
      (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ), Measurable v →
      ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖ ≤ 1) →
      Monotone d →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
      ∀ (T : SlopeBox) (K : ℝ) (D : ℕ), 0 < K →
      ∀ data : SupportedTopRawPacketData (P.withProfile alt hAlt).family
          (lo/P.topLength) (hi/P.topLength) T K D,
        SupportedTopCovariantData data → ∀ (i : Fin 2) (J L : ℝ),
      let n := topExceptionMoment (topAreaPrefactor K) J L
      ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J*L)*T.area) ∧
        ∀ a b : ℕ, a ≤ b → b ≤ N → ∀ z w, |w| ≤ K*T.width → z ∉ bad →
          ‖planarPacketInterval ((P.frozenProfile c hc).family.mainCoefficient d v g)
            (fun j u k y x => data.raw i j u k y x) a b z.1 ((z.2-T.slope*z.1)+w)‖ ≤
              (P.family.topPacketAmplitude Ab Am D*(n:ℝ)*5^(8*D))*(T.weight K (D:ℝ) z)^8 := by
  obtain ⟨Ab,Am,hAb,hAm,htop⟩ :=
    PlanarPacketFamily.constructed_analyzed_top_neighborhood_of_supported hL hlo hhi
  refine ⟨Ab,Am,hAb,hAm,?_⟩
  intro N κ ι _ _ P c hc alt hAlt d v hv g hg hg1 hd hAlow hAhigh T K D hK data second i J L
  let A := (P.frozenProfile c hc).referencePlanarFamily
  let U := T.horizontalRescale P.topLength P.topLength_pos
  let R := data.horizontalRescale P.topLength P.topLength_pos
  let R2 := second.horizontalRescale P.topLength P.topLength_pos
  let Q := (P.withProfile alt hAlt).family.horizontalRescale P.topLength P.topLength_pos
  have hconstant : Q.constant = A.constant := rfl
  have hlength (j : Fin N) : Q.length j = A.length j := rfl
  have hwidth : Q.width = A.width := rfl
  have hcenterX (j : Fin N) (u : ι j) : Q.centerX j u = A.centerX j u := rfl
  have hcenterZ (j : Fin N) (u : ι j) : Q.centerZ j u = A.centerZ j u := rfl
  have hfrequency : R.frequency = data.frequency := rfl
  have hboundR (e : Fin 2) (y : ℝ) (j : Fin N) (u : ι j) (k : κ) (x : ℝ) :
      ‖R.raw e j u k y x‖ ≤ A.constant*
        (lineEnvelope (A.centerX j u) (A.length j) (3+2*(8*D+1)) x*
          lineEnvelope (A.centerZ j u) A.width (2+2*(8*D+1)) y) := by
    have h := R.bound e y j u k x
    change ‖R.raw e j u k y x‖ ≤ Q.constant*
      (lineEnvelope (Q.centerX j u) (Q.length j) (3+2*(8*D+1)) x*
        lineEnvelope (Q.centerZ j u) Q.width (2+2*(8*D+1)) y) at h
    simpa only [hconstant,hlength,hwidth,hcenterX,hcenterZ] using h
  have hboundR2 (y : ℝ) (j : Fin N) (u : ι j) (k : κ) (x : ℝ) :
      ‖R2.second j u k y x‖ ≤ A.constant*
        (lineEnvelope (A.centerX j u) (A.length j) (3+2*(8*D+1)) x*
          lineEnvelope (A.centerZ j u) A.width (2+2*(8*D+1)) y) := by
    have h := R2.bound y j u k x
    change ‖R2.second j u k y x‖ ≤ Q.constant*
      (lineEnvelope (Q.centerX j u) (Q.length j) (3+2*(8*D+1)) x*
        lineEnvelope (Q.centerZ j u) Q.width (2+2*(8*D+1)) y) at h
    simpa only [hconstant,hlength,hwidth,hcenterX,hcenterZ] using h
  have hderivR (e : Fin 2) (y : ℝ) (j : Fin N) (u : ι j) (k : κ) (x : ℝ) :
      ‖deriv (R.raw e j u k y) x‖ ≤ (A.constant/A.length j)*
        (lineEnvelope (A.centerX j u) (A.length j) (3+2*(8*D+1)) x*
          lineEnvelope (A.centerZ j u) A.width (2+2*(8*D+1)) y) := by
    have h := R.derivative_bound e y j u k x
    change ‖deriv (R.raw e j u k y) x‖ ≤ (Q.constant/Q.length j)*
      (lineEnvelope (Q.centerX j u) (Q.length j) (3+2*(8*D+1)) x*
        lineEnvelope (Q.centerZ j u) Q.width (2+2*(8*D+1)) y) at h
    simpa only [hconstant,hlength,hwidth,hcenterX,hcenterZ] using h
  have hderivR2 (y : ℝ) (j : Fin N) (u : ι j) (k : κ) (x : ℝ) :
      ‖deriv (R2.second j u k y) x‖ ≤ (A.constant/A.length j)*
        (lineEnvelope (A.centerX j u) (A.length j) (3+2*(8*D+1)) x*
          lineEnvelope (A.centerZ j u) A.width (2+2*(8*D+1)) y) := by
    have h := R2.derivative_bound y j u k x
    change ‖deriv (R2.second j u k y) x‖ ≤ (Q.constant/Q.length j)*
      (lineEnvelope (Q.centerX j u) (Q.length j) (3+2*(8*D+1)) x*
        lineEnvelope (Q.centerZ j u) Q.width (2+2*(8*D+1)) y) at h
    simpa only [hconstant,hlength,hwidth,hcenterX,hcenterZ] using h
  let raw : Fin 2 → ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ := fun e =>
    if i=0 then R.raw e else if e=0 then R.raw 1 else R2.second
  let v' := fun z : ℝ×ℝ => v (z.1,P.topLength*z.2)
  let g' := fun z : ℝ×ℝ => g (z.1,P.topLength*z.2)
  have hv' : Measurable v' := hv.comp
    (measurable_fst.prodMk (measurable_const.mul measurable_snd))
  have hg' : Measurable g' := hg.comp
    (measurable_fst.prodMk (measurable_const.mul measurable_snd))
  obtain ⟨hAlow',hAhigh'⟩ := (P.frozenProfile c hc).referencePlanarFamily_cutoffs hAlow hAhigh
  obtain ⟨B,hB,harea,hpoint⟩ := htop N κ ι A d v' hv' g' hg' (fun _ => hg1 _) hd
    (fun y j u k x => (P.frozenProfile c hc).referencePlanarFamily_derivative j u k y x)
    hAlow' hAhigh' raw data.frequency U K D hK
    R.length_le R.width_le R.centerX_le R.centerZ_le
    (by
      intro e y j u k x
      fin_cases i <;> fin_cases e
      · simpa [raw] using hboundR 0 y j u k x
      · simpa [raw] using hboundR 1 y j u k x
      · simpa [raw] using hboundR 1 y j u k x
      · simpa [raw] using hboundR2 y j u k x)
    (by
      intro e y j u k x
      fin_cases i <;> fin_cases e
      · simpa [raw] using hderivR 0 y j u k x
      · simpa [raw] using hderivR 1 y j u k x
      · simpa [raw] using hderivR 1 y j u k x
      · simpa [raw] using hderivR2 y j u k x)
    (by
      intro e y j u k xi hxi
      fin_cases i <;> fin_cases e
      · simpa [raw] using R.low 0 y j u k xi hxi
      · simpa [raw] using R.low 1 y j u k xi hxi
      · simpa [raw] using R.low 1 y j u k xi hxi
      · simpa [raw] using R2.low y j u k xi hxi)
    (by
      intro e y j u k xi hxi
      fin_cases i <;> fin_cases e
      · simpa [raw] using R.high 0 y j u k xi hxi
      · simpa [raw] using R.high 1 y j u k xi hxi
      · simpa [raw] using R.high 1 y j u k xi hxi
      · simpa [raw] using R2.high y j u k xi hxi)
    (by
      intro y j u k x
      fin_cases i
      · simpa [raw,hfrequency] using R.covariant y j u k x
      · have h := R2.covariant y j u k x
        change (4*(K*U.width):ℂ)*(deriv (fun yy => R.raw 1 j u k yy x) y-
          (R.frequency k:ℂ)*Complex.I*R.raw 1 j u k y x) = R2.second j u k y x at h
        rw [hfrequency] at h
        simpa [raw] using h)
    (by
      intro e j u k
      fin_cases i <;> fin_cases e
      · simpa [raw] using R.continuous 0 j u k
      · simpa [raw] using R.continuous 1 j u k
      · simpa [raw] using R.continuous 1 j u k
      · simpa [raw] using R2.continuous j u k)
    (by
      intro j u k x y
      fin_cases i
      · simpa [raw] using R.differentiable j u k x y
      · simpa [raw] using R2.differentiable j u k x y) J L
  let bad := horizontalDilation (P.topLength⁻¹) (inv_ne_zero P.topLength_pos.ne') ⁻¹' B
  have hbad : MeasurableSet bad := hB.preimage
    (horizontalDilation (P.topLength⁻¹) (inv_ne_zero P.topLength_pos.ne')).measurable
  refine ⟨bad,hbad,?_,?_⟩
  · change (volume.prod volume)
      (horizontalDilation (P.topLength⁻¹) (inv_ne_zero P.topLength_pos.ne') ⁻¹' B) ≤ _
    rw [measure_horizontalDilation_preimage _ _ _ hB,inv_inv,abs_of_pos P.topLength_pos]
    apply (mul_le_mul_right harea (ENNReal.ofReal P.topLength)).trans
    rw [← ENNReal.ofReal_mul P.topLength_pos.le]
    apply ENNReal.ofReal_le_ofReal
    change P.topLength*(Real.exp (-J*L)*(T.length/P.topLength*T.width)) ≤ _
    apply le_of_eq
    field_simp [P.topLength_pos.ne']
    rfl
  · intro a b hab hb z w hw hout
    have hout' : (z.1/P.topLength,z.2) ∉ B := by
      intro hz
      apply hout
      change (horizontalDilation (P.topLength⁻¹) (inv_ne_zero P.topLength_pos.ne') z) ∈ B
      simpa only [horizontalDilation_apply,div_eq_mul_inv,mul_comm] using hz
    have hp := hpoint a b hab hb (z.1/P.topLength,z.2) w hw hout'
    have hraw (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
        raw 0 j u k y x = data.raw i j u k y (P.topLength*x) := by
      fin_cases i <;> rfl
    have hcoeff (j : Fin N) (u : ι j) :
        A.mainCoefficient d v' g' j u = (P.frozenProfile c hc).family.mainCoefficient d v g j u := by
      exact (P.frozenProfile c hc).family.horizontalRescale_mainCoefficient
        P.topLength P.topLength_pos d v g j u
    have hinterval (y : ℝ) : planarPacketInterval (A.mainCoefficient d v' g')
        (fun j u k yy xx => raw 0 j u k yy xx) a b (z.1/P.topLength) y =
        planarPacketInterval ((P.frozenProfile c hc).family.mainCoefficient d v g)
          (fun j u k yy xx => data.raw i j u k yy xx) a b z.1 y := by
      ext k
      simp only [planarPacketInterval,bandIntervalSignal,WithLp.ofLp_toLp,scalarBandPartial,
        planarPacketBand,hcoeff,hraw,mul_div_cancel₀ _ P.topLength_pos.ne']
    have hslope : U.slope*(z.1/P.topLength) = T.slope*z.1 := by
      change (P.topLength*T.slope)*(z.1/P.topLength) = _
      field_simp [P.topLength_pos.ne']
    have hweight : U.weight K (D:ℝ) (z.1/P.topLength,z.2) = T.weight K (D:ℝ) z := by
      rw [SlopeBox.horizontalRescale_weight]
      rw [mul_div_cancel₀ _ P.topLength_pos.ne']
    have hamp : A.topPacketAmplitude Ab Am D = P.family.topPacketAmplitude Ab Am D := rfl
    dsimp only at hp ⊢
    simpa only [hslope,hweight,hinterval,hamp] using hp

end LipschitzHilbert.SourceLatticePacket

end

end OAI
