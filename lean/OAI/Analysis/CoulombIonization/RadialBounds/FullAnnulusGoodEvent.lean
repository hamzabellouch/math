import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.FullAnnulusBandCover
import OAI.Analysis.CoulombIonization.ThomasFermi.FullAnnulusNormalization
import OAI.Analysis.CoulombIonization.Variational.ContinuousUniversalEvent

namespace OAI

noncomputable section

namespace CoulombAtom
open MeasureTheory Filter Set
open scoped Topology
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local instance] physicalObservationLaw_probability

theorem exists_actual_fullAnnulus_good_constant {B c₁ lo hi xi : ℝ}
    (hB : 1 ≤ B) (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hlh : lo ≤ hi) (hxi : 0 < xi) (hlo : 16*xi < lo) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} {l : Filter ι}
      {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ} {F : ∀ i, fermionGraph (N i)} {δ : ℝ},
      0 ≤ δ → Tendsto s l (𝓝 0) → (∀ᶠ i in l, 0 < r₀ i) →
      (∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
        OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
          (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) →
      ∀ᶠ i in l, ∀ j : Fin (K i), (2:ℝ)^j.val*r₀ i ≤ s i →
        let u := (2:ℝ)^j.val*r₀ i
        ∃ G : Set (Configuration (N i) × (Fin (K i) × (Fin (N i) × Fin 3) → ℝ)),
          MeasurableSet[observationInformation
            (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j] G ∧
          (physicalObservationLaw (graphRawLaw (F i)) (K i)).real Gᶜ ≤ C*u^25 ∧
          ∀ q ∈ G, ∀ y : Space, u ≤ ‖y‖ → ‖y‖ ≤ B*u →
            InverseComparisonAt ‖y‖
              (originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y)
              (originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y)
              (((5/3:ℝ)*tfKinetic)^(3/2:ℝ))⁻¹ lo hi xi
              (100000^4*(16*(tfPatchCapConstant+3))) := by
  have hp : (0:ℝ) < 100000^4 := by norm_num
  obtain ⟨C,hC,hresult⟩ := exists_actual_fullAnnulus_inverse_constant hB hc hcL
    (div_le_div_of_nonneg_right hlh hp.le) (div_pos hxi hp)
    (lo := lo/100000^4) (hi := hi/100000^4)
    (by rw [←mul_div_assoc]; exact (div_lt_div_iff_of_pos_right hp).mpr hlo)
  refine ⟨C,hC,?_⟩
  intro ι l r₀ s Z lam N K F δ hδ hs hr hF
  have he := hresult hδ hs hr hF
  filter_upwards [he,hr,hF,hs.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hie hri hFi hsi
  intro j hjs
  let u := (2:ℝ)^j.val*r₀ i
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := hjs.trans hsi.le
  have hrs : r₀ i ≤ s i := (le_mul_of_one_le_left hri.le (one_le_pow₀ (by norm_num))).trans hjs
  have hsp : 0 < s i := hu.trans_le hjs
  obtain ⟨E,hE,hpE,hqE⟩ := hie j hjs
  let G : Set (Configuration (N i) × (Fin (K i) × (Fin (N i) × Fin 3) → ℝ)) :=
    {q | ∀ y : Space, u ≤ ‖y‖ → ‖y‖ ≤ B*u →
      InverseComparisonAt ‖y‖
        (originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y)
        (originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y)
        (((5/3:ℝ)*tfKinetic)^(3/2:ℝ))⁻¹ lo hi xi
        (100000^4*(16*(tfPatchCapConstant+3)))}
  have hG : MeasurableSet[observationInformation
      (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j] G :=
    original_inverse_fullAnnulus_measurable (F i) (Z i) (lam i) (r₀ i) j hc hri hsp hrs hu
  have hae : Gᶜ ≤ᵐ[physicalObservationLaw (graphRawLaw (F i)) (K i)] E := by
    filter_upwards [hqE] with q hq
    intro hqG
    by_contra hqnot
    apply hqG
    intro y hyl hyh
    have hh := hq hqnot
    exact inverseComparisonAt_of_cell (by linarith) (hh.2 y hyl hyh) (hh.1 y hyl hyh)
  let := graphRawLaw_probability (F i) hFi.2.2.1
  refine ⟨G,hG,?_,fun q hq => hq⟩
  calc
    _ ≤ (physicalObservationLaw (graphRawLaw (F i)) (K i)).real E :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hae)
    _ ≤ C*u^37 := hpE
    _ ≤ C*u^25 := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hu.le hu1 (by norm_num)) hC.le

end CoulombAtom

namespace CoulombBarrier
open MeasureTheory Filter Set Metric
open scoped Topology
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local instance] physicalObservationLaw_probability

lemma own_state_initial_barrier {Z N K : ℕ} {s ε k B c δ G : ℝ}
    (hn : InitialNumerics Z s ε G c δ) (hc : 0 < c) (hc1 : c ≤ 1/2)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hk : 0 ≤ k) (hB : 0 < B)
    (hed : initialDensityConstant*ε^(6/5:ℝ) < 1/20)
    (hq : 4*initialQuadraticConstant k*ε^(3/2:ℝ) ≤ 1/20)
    (hBs : B ≤ ε^3/10) (hsub : 4*Real.pi*k*Real.sqrt B ≤ 19/2)
    (hG : ∀ z, (canonicalRealPacket z)^2 ≤ G)
    (hN : PriceMinimizes (energy Z) (s^(-4:ℝ)) N) {F : fermionGraph N}
    (hF : OwnProbabilityTailTiltState Z (s^(-4:ℝ)) (ε*(Z:ℝ)^(-1/3:ℝ)) K
      (fun j => tinyProbabilityFloor Z ((2:ℝ)^j.val*(ε*(Z:ℝ)^(-1/3:ℝ)))) δ F) :
    ∃ a p : (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → TFSpace → ℝ,
      IsNuclearBarrier (physicalObservationLaw (graphRawLaw F) K)
        (originalQueryDensity F (ε*(Z:ℝ)^(-1/3:ℝ)) 0 c (ε*(Z:ℝ)^(-1/3:ℝ)) s)
        (Z:ℝ) k B (max B (32*ε^3)) (ε*(Z:ℝ)^(-1/3:ℝ)) 2
        (5184*(ε*(Z:ℝ)^(-1/3:ℝ))^32) a p := by
  let r₀ := ε*(Z:ℝ)^(-1/3:ℝ)
  have htail : TailTiltState Z (s^(-4:ℝ)) r₀ K (tailPolynomialThreshold r₀) δ F :=
    hF.to_tailTiltState hn.radius_pos (tailPolynomialThreshold_pos hn.radius_pos)
      (fun _ => tinyProbabilityFloor_le_polynomial (Nat.cast_nonneg Z) (by positivity))
  have hp := tailPolynomialThreshold_zero hn.radius_pos.le hn.radius_le K
  have hb : 3*(Z:ℝ)*s^(-4:ℝ)+
      dyadicUniformEventBudget ((2:ℝ)^(0:Fin (K+1)).val*r₀)
        (tailPolynomialThreshold r₀ (0 : Fin (K+1))) δ ≤ (Z:ℝ)^(7/3:ℝ) := by
    simp only [Fin.val_zero,pow_zero,one_mul,dyadicUniformEventBudget]
    rw [hp]
    dsimp only [r₀]
    linarith only [hn.budget]
  obtain ⟨a,p,hi⟩ := tail_initial_barrier hn.charge (Real.rpow_pos_of_pos hn.scale_pos _)
    hn.radius_pos hn.radius_le hn.scale_pos hn.scale_le hn.radius_scale hc hc1
    hε hε1 hk hB hn.radius_relation hed hq hBs hsub hN htail (0 : Fin (K+1))
    (tailPolynomialThreshold_pos hn.radius_pos 0) hp.le hb hn.interpolation
    canonicalRealPacket_smooth canonicalRealPacket_compact hG canonicalRealPacket_normalized
    canonicalRealPacket_radial canonicalRealPacket_support
  exact ⟨_,_,hi.pullback (originalDatum_measurable _ _)⟩

end CoulombBarrier

open Set Filter MeasureTheory Metric
open scoped Topology
namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma exists_fullAnnulus_outward_calibration {κ B C : ℝ} (hκ : 0 ≤ κ) (hB : 0 < B)
    (hBC : B ≤ C) (hsub : 4*Real.pi*κ*Real.sqrt B ≤ 19/2) :
    ∃ M lam1 lam2 e ξ hl hh : ℝ, OutwardCalibration κ B C M lam1 lam2 e ξ hl hh ∧
      0 < ξ ∧ 16*ξ < hl ∧ hl ≤ hh := by
  let δ := barrierGap B
  have hδ : 0 < δ := barrierGap_pos hB
  let lam1 := δ/2
  let lam2 := δ/4
  have hl2 : 0 < lam2 := by dsimp only [lam2]; positivity
  let M := C/lam2+3
  have hC : 0 ≤ C := hB.le.trans hBC
  have hM : 2 < M := by dsimp only [M]; linarith [div_nonneg hC hl2.le]
  have hM0 : 0 < M := by linarith
  have hM4 : 0 < (2*M)^4 := by positivity
  have hpow : M ≤ M^4 := by
    have h2 : 1 ≤ M^2 := by nlinarith
    have h4 : M^2 ≤ M^4 := by nlinarith [sq_nonneg (M^2-1)]
    nlinarith
  have hcap : C/M^4 < lam2 := by
    apply (div_lt_iff₀ (pow_pos hM0 4)).mpr
    have hCM : C+3*lam2 = M*lam2 := by dsimp only [M]; field_simp
    nlinarith [mul_le_mul_of_nonneg_left hpow hl2.le]
  let e := min (δ/32) (B/(16*(2*M)^4))
  have he : 0 < e := lt_min (by positivity) (by positivity)
  have he1 : e ≤ δ/32 := min_le_left _ _
  have he2 : e*(2*M)^4 ≤ B/16 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 16*(2*M)^4)).mp (min_le_right (δ/32) (B/(16*(2*M)^4)))
    dsimp only [e]
    nlinarith
  refine ⟨M,lam1,lam2,e,δ/512,B/8,2*C,?_,by positivity,?_,by linarith⟩
  swap
  · dsimp [δ,barrierGap]
    norm_num [div_eq_mul_inv]
    linarith
  refine ⟨hκ,hB,hC,hBC,hM,by positivity,?_,?_,?_,?_,he,?_,hcap,?_,?_,hsub⟩
  · dsimp only [lam2]; linarith
  · dsimp only [lam2,lam1]; linarith
  · dsimp only [lam1,δ]; linarith [barrierGap_pos hB]
  · dsimp only [lam1,lam2]; linarith
  · linarith
  · linarith
  · linarith

end CoulombBarrier

end

end OAI
