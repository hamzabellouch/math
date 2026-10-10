import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.NearActiveMaximum
import OAI.Analysis.CoulombRadii.ThomasFermi.Rescaling
import OAI.Analysis.CoulombRadii.Packets.PhysicalInverseCap

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace NeutralAtom
lemma tfDensityScalar_eq_scalar (v : ℝ) : tfDensityScalar v = Coulomb.tfScalarDensity v :=
  (tfScalarDensity_eq_kTF v).symm

theorem inverse_density_error_parameters (cap : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ hl hh ξ : ℝ, 0 < ξ ∧ ξ < hl/16 ∧ hl ≤ hh ∧
      ∀ d v : ℝ, 0 ≤ d → v ≤ cap →
      (∀ h∈Icc hl hh,
        (Coulomb.tfScalarDensity h ≤ d → h-ξ ≤ v) ∧
        (d ≤ Coulomb.tfScalarDensity h → v ≤ h+ξ)) →
      |d-tfDensityScalar v| ≤ η := by
  have hz : Coulomb.tfScalarDensity 0 = 0 := by simp [Coulomb.tfScalarDensity]
  have htwo : Tendsto (fun x : ℝ => 2*x) (𝓝[>] 0) (𝓝 0) := by
    simpa using (((tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0)).const_mul (2:ℝ)).mono_left nhdsWithin_le_nhds)
  have hlim : Tendsto (fun x : ℝ => Coulomb.tfScalarDensity (2*x)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [hz, Function.comp_def] using (Coulomb.tfScalarDensity_continuous.tendsto 0).comp htwo
  have hepos : ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < x := self_mem_nhdsWithin
  obtain ⟨hl,hhl,htf⟩ := (hepos.and (hlim.eventually (gt_mem_nhds hη))).exists
  have hhl : 0 < hl := hhl
  let hh := max (max cap 0 + 2) (2*hl)
  have hhcap : cap+2 ≤ hh := by
    have h1 : cap ≤ max cap 0 := le_max_left _ _
    have h2 : max cap 0+2 ≤ hh := le_max_left _ _
    linarith only [h1,h2]
  have hh0 : 0 < hh := (by linarith [le_max_right cap 0] : (0:ℝ) < max cap 0+2).trans_le (le_max_left _ _)
  have hhlhh : hl ≤ hh := (by linarith : hl ≤ 2*hl).trans (le_max_right _ _)
  have hu := (isCompact_Icc : IsCompact (Icc (0:ℝ) hh)).uniformContinuousOn_of_continuous
    Coulomb.tfScalarDensity_continuous.continuousOn
  obtain ⟨δ,hδ,Hδ⟩ := Metric.uniformContinuousOn_iff.mp hu η hη
  let ξ := min (hl/32) (min (δ/2) (1/2))
  have hξ : 0 < ξ := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hξhl : ξ < hl/16 := (min_le_left _ _).trans_lt (by linarith)
  have hξδ : ξ < δ := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hξ1 : ξ ≤ 1/2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨hl,hh,ξ,hξ,hξhl,hhlhh,?_⟩
  intro d v hd hv HI
  rw [tfDensityScalar_eq_scalar]
  have hdhi : d < Coulomb.tfScalarDensity hh := by
    by_contra hh'
    have H := (HI hh ⟨hhlhh,le_rfl⟩).1 (le_of_not_gt hh')
    linarith only [H,hv,hhcap,hξ1]
  by_cases hdlo : d ≤ Coulomb.tfScalarDensity hl
  · have hvlo := (HI hl ⟨le_rfl,hhlhh⟩).2 hdlo
    have hv2 : v ≤ 2*hl := by linarith only [hvlo,hξhl,hhl]
    have hdη : d ≤ η := hdlo.trans ((Coulomb.tfScalarDensity_mono (by linarith : hl ≤ 2*hl)).trans htf.le)
    have hvη : Coulomb.tfScalarDensity v ≤ η := (Coulomb.tfScalarDensity_mono hv2).trans htf.le
    exact abs_le.mpr ⟨by linarith only [hd,hvη],by linarith only [hdη,Coulomb.tfScalarDensity_nonneg v]⟩
  · obtain ⟨t,ht,hdt⟩ := intermediate_value_Icc hhlhh Coulomb.tfScalarDensity_continuous.continuousOn
      ⟨(lt_of_not_ge hdlo).le,hdhi.le⟩
    have HV := HI t ht
    have hvt : |v-t| ≤ ξ := abs_le.mpr ⟨by linarith [HV.1 hdt.le],by linarith [HV.2 hdt.ge]⟩
    have hvp : max v 0 ∈ Icc (0:ℝ) hh := ⟨le_max_right _ _,max_le (hv.trans (by linarith only [hhcap])) hh0.le⟩
    have htp : t ∈ Icc (0:ℝ) hh := ⟨hhl.le.trans ht.1,ht.2⟩
    have hpdist : dist (max v 0) t < δ := by
      rw [Real.dist_eq]
      have H : max v 0 ≤ t+ξ := max_le
        (by linarith [abs_le.mp hvt |>.2]) (by linarith only [htp.1,hξ])
      have H' : t-ξ ≤ max v 0 := (by linarith [abs_le.mp hvt |>.1] : t-ξ ≤ v).trans (le_max_left _ _)
      exact (abs_le.mpr ⟨by linarith only [H'],by linarith only [H]⟩).trans_lt hξδ
    have He := Hδ (max v 0) hvp t htp hpdist
    rw [Real.dist_eq,hdt] at He
    have hmax : Coulomb.tfScalarDensity (max v 0) = Coulomb.tfScalarDensity v := by simp [Coulomb.tfScalarDensity]
    rw [hmax,abs_sub_comm] at He
    exact He.le
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace NeutralAtom

theorem physical_tf_band {q : ℝ} (hq : 2 ≤ q) : ∃ C : ℝ,0 < C ∧
    ∀ D : ℝ,0 ≤ D → ∃ s₀ : ℝ,0 < s₀ ∧ s₀ ≤ 1 ∧
    ∀ {N J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)),FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h) →
    ∀ {E : ℝ},(E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D → ∀ {r₀ s : ℝ},0 < r₀ → 0 < s → s < s₀ →
    ∀ (j : Fin J),r₀*2^j.val ≤ s →
    letI := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    let rs := fun k : Fin J => r₀*2^k.val
    ∃ G : Set (ObservationSample (N+1) J),MeasurableSet G ∧ P.real Gᶜ ≤ C*s^25 ∧
      ∀ o∈G,∀ y : Position,rs j ≤ ‖y‖ → ‖y‖ ≤ 4*q^2*(rs j) →
        let μ := conditionalPacketDensity P Prod.fst (tailObservation rs j.val)
          Coulomb.unitWindow 1 r₀ s (tailObservation rs j.val o)
        screenedField (Z:ℝ) μ y ≤ physicalSpatialCap/‖y‖^4 ∧
        |μ y-tfDensityScalar (screenedField (Z:ℝ) μ y)| ≤ (q^8)⁻¹/‖y‖^6 := by
  have hqpos : 0 < q := by linarith only [hq]
  obtain ⟨hl,hh,ξ,hξ,hξhl,hhlhh,Herror⟩ := inverse_density_error_parameters physicalSpatialCap
    (by positivity : 0 < (q^8)⁻¹)
  obtain ⟨C,hC,H⟩ := physical_simultaneous_inverse_cap Coulomb.unitWindow Coulomb.unitWindow_support
    Coulomb.unitWindow_mass Coulomb.unitWindow_radial (by norm_num : (0:ℝ) < 1)
    (show 1 ≤ q^2 by nlinarith only [hq]) hξ (show ξ < hl from by linarith only [hξhl,hξ]) hhlhh
  refine ⟨C,hC,?_⟩
  intro D hD
  obtain ⟨s₀,hs₀,hs₀1,H⟩ := H D hD
  refine ⟨s₀,hs₀,hs₀1,?_⟩
  intro N J Z hZ ψ g hd hn hmin E hE he r₀ s hr₀ hs hss j hrjs
  have := rawLaw_isProbability hd.2.2.1 hn
  dsimp only
  obtain ⟨G,hG,hp,HG⟩ := H Z hZ hd hn hmin hE he hr₀ hs hss j hrjs
  have hrj : 0 < r₀*2^j.val := mul_pos hr₀ (by positivity)
  refine ⟨G,hG.1,hp.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hrj.le hrjs 25) hC.le),?_⟩
  intro o ho y hy hy'
  have hypos : 0 < ‖y‖ := hrj.trans_le hy
  obtain ⟨hcap,HI⟩ := HG o ho y hy hy'
  let P := observationLaw J (rawLaw ψ)
  let rs := fun k : Fin J => r₀*2^k.val
  let μ := conditionalPacketDensity P Prod.fst (tailObservation rs j.val)
    Coulomb.unitWindow 1 r₀ s (tailObservation rs j.val o)
  have hμ : 0 ≤ μ y := conditionalPacketDensity_nonneg P Prod.fst (tailObservation rs j.val)
    Coulomb.unitWindow (by norm_num) hr₀ hs _ y
  change screenedField (Z:ℝ) μ y ≤ _ ∧ |μ y-tfDensityScalar (screenedField (Z:ℝ) μ y)| ≤ _
  have hc : ‖y‖^4*screenedField (Z:ℝ) μ y ≤ physicalSpatialCap := hcap
  refine ⟨(le_div_iff₀ (pow_pos hypos 4)).mpr (by simpa only [mul_comm] using hc),?_⟩
  have HE := Herror (‖y‖^6*μ y) (‖y‖^4*screenedField (Z:ℝ) μ y)
    (mul_nonneg (pow_nonneg hypos.le 6) hμ) hc HI
  rw [tfDensityScalar_dilate hypos,← mul_sub,abs_mul,abs_of_pos (pow_pos hypos 6)] at HE
  exact (le_div_iff₀ (pow_pos hypos 6)).mpr (by simpa only [mul_comm] using HE)
end NeutralAtom
end

end

end OAI
