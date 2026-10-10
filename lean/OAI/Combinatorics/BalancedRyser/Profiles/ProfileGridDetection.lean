import Mathlib.Topology.Order.ProjIcc
import OAI.Combinatorics.BalancedRyser.Incidence.ProfileEmpiricalIncidence
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileContinuity
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileDetectionSource
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileGridDensity

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Balanced.ProfileGridDetection

abbrev BoundedSpace (M : ℝ) := {p : Profile | IsBoundedProfile M p}

def clippedParameter (z : ℝ) : Icc (0 : ℝ) 1 := projIcc 0 1 zero_le_one z

def planeClipped {M : ℝ} (p : BoundedSpace M × ℝ) : ℝ :=
  ∑' ij, p.1.val ij * (clippedParameter p.2).val ^
    ((ij.1 : ℝ) + Real.sqrt 2 * ij.2)

def dClipped {M : ℝ} (p : BoundedSpace M × ℝ) : ℝ :=
  ∑' ij, p.1.val ij * (if ij.1 ≠ 0 then (clippedParameter p.2).val ^
    (((ij.1 - 1 : ℕ) : ℝ) + Real.sqrt 2 * ij.2) else 0)

def cClipped {M : ℝ} (p : BoundedSpace M × ℝ) : ℝ :=
  ∑' ij, p.1.val ij * (if ij.2 ≠ 0 then (clippedParameter p.2).val ^
    ((ij.1 : ℝ) + Real.sqrt 2 * (ij.2 - 1 : ℕ)) else 0)

theorem continuous_clippedParameter : Continuous clippedParameter := by
  exact continuous_projIcc (h := zero_le_one)

theorem continuous_planeClipped (M : ℝ) : Continuous (@planeClipped M) :=
  (ProfileContinuity.continuous_plane_profile_transform
    (fun _ hp => hp.1) (fun _ hp => hp.2.1)).comp
    (continuous_fst.prodMk (continuous_clippedParameter.comp continuous_snd))

theorem continuous_dClipped (M : ℝ) : Continuous (@dClipped M) :=
  (ProfileContinuity.continuous_deletion_profile_transform
    (fun _ hp => hp.1) (fun _ hp => hp.2.1)).comp
    (continuous_fst.prodMk (continuous_clippedParameter.comp continuous_snd))

theorem continuous_cClipped (M : ℝ) : Continuous (@cClipped M) :=
  (ProfileContinuity.continuous_cover_profile_transform
    (fun _ hp => hp.1) (fun _ hp => hp.2.1)).comp
    (continuous_fst.prodMk (continuous_clippedParameter.comp continuous_snd))

theorem planeClipped_eq {M : ℝ} (p : BoundedSpace M) {z : ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1) :
    planeClipped (p,z) = ProfileDetectionBridge.planeTest p.val z := by
  simp only [planeClipped, clippedParameter, projIcc_of_mem zero_le_one hz,
    ProfileDetectionBridge.planeTest]

theorem dClipped_eq {M : ℝ} (p : BoundedSpace M) {z : ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1) (hzero : ∀ j, p.val (0,j) = 0) :
    dClipped (p,z) = ProfileDetectionBridge.dTest p.val z := by
  simp only [dClipped, clippedParameter, projIcc_of_mem zero_le_one hz,
    ProfileDetectionBridge.dTest]
  apply tsum_congr
  rintro ⟨i,j⟩
  by_cases hi : i = 0
  · simp [hi, hzero]
  · simp [hi, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hi)]

theorem cClipped_eq {M : ℝ} (p : BoundedSpace M) {z : ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1) (hzero : ∀ i, p.val (i,0) = 0) :
    cClipped (p,z) = ProfileDetectionBridge.cTest p.val z := by
  simp only [cClipped, clippedParameter, projIcc_of_mem zero_le_one hz,
    ProfileDetectionBridge.cTest]
  apply tsum_congr
  rintro ⟨i,j⟩
  by_cases hj : j = 0
  · simp [hj, hzero]
  · simp [hj, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hj)]

theorem tendsto_comap_boundedProfiles {M : ℝ} (hM : 0 ≤ M)
    {νn : ℕ → FiniteMeasure Profile} {ν : FiniteMeasure Profile}
    (hνn : ∀ n, νn n {p | IsBoundedProfile M p}ᶜ = 0)
    (hν : ν {p | IsBoundedProfile M p}ᶜ = 0)
    (ht : Tendsto νn atTop (𝓝 ν)) :
    Tendsto (fun n => (νn n).comap (Subtype.val : BoundedSpace M → Profile)) atTop
      (𝓝 (ν.comap (Subtype.val : BoundedSpace M → Profile))) := by
  have he := (ProfileAmbientCompactness.isClosed_boundedProfiles M hM).isClosedEmbedding_subtypeVal
  have hc := he.continuousOn_comap_finiteMeasure
  apply (hc ν (by simpa using hν)).tendsto.comp
  exact tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall (fun n => by simpa using hνn n)⟩

theorem prod_comap_real_preimage {M : ℝ} (hM : 0 ≤ M)
    (ν : FiniteMeasure Profile) (hν : ν {p | IsBoundedProfile M p}ᶜ = 0)
    (τ : Measure ℝ) [SFinite τ] {s : Set (Profile × ℝ)} (hs : MeasurableSet s) :
    (((ν.comap (Subtype.val : BoundedSpace M → Profile) : Measure (BoundedSpace M)).prod τ)).real
      ((Prod.map Subtype.val id) ⁻¹' s) = ((ν : Measure Profile).prod τ).real s := by
  have hm := congrArg FiniteMeasure.toMeasure
    (ProfileAmbientCompactness.map_comap_subtype
      (ProfileAmbientCompactness.isClosed_boundedProfiles M hM) ν hν)
  simp only [FiniteMeasure.toMeasure_map] at hm
  have he := Measure.map_prod_map
    (ν.comap (Subtype.val : BoundedSpace M → Profile) : Measure (BoundedSpace M)) τ
    measurable_subtype_coe measurable_id
  rw [Measure.map_id, hm] at he
  rw [Measure.real, Measure.real, he,
    Measure.map_apply (measurable_subtype_coe.prodMap measurable_id) hs]

theorem cutoff_real_eq_comap {M : ℝ} (hM : 0 ≤ M)
    (ν : FiniteMeasure Profile) (hν : ν {p | IsBoundedProfile M p}ᶜ = 0)
    (τ : Measure ℝ) [SFinite τ]
    (B : Profile → Prop) (hB : MeasurableSet {p | B p})
    (hνB : ∀ᵐ p ∂(ν : Measure Profile), B p)
    (f : Profile × ℝ → ℝ) (hf : Measurable f)
    (g : BoundedSpace M × ℝ → ℝ) (_hg : Measurable g)
    (heq : ∀ p : BoundedSpace M, B p.val → ∀ z ∈ Icc (0 : ℝ) 1,
      f (p.val,z) = g (p,z)) (n : ℕ) :
    ((ν : Measure Profile).prod τ).real
      (ProfileDetection.cutoffDetection Prod.snd f n) =
    ((ν.comap (Subtype.val : BoundedSpace M → Profile) : Measure (BoundedSpace M)).prod τ).real
      (ProfileDetection.cutoffDetection Prod.snd g n) := by
  have hs : MeasurableSet (ProfileDetection.cutoffDetection Prod.snd f n) := by
    unfold ProfileDetection.cutoffDetection
    measurability
  rw [← prod_comap_real_preimage hM ν hν τ hs]
  apply congrArg ENNReal.toReal
  apply measure_congr
  have hm := congrArg FiniteMeasure.toMeasure
    (ProfileAmbientCompactness.map_comap_subtype
      (ProfileAmbientCompactness.isClosed_boundedProfiles M hM) ν hν)
  simp only [FiniteMeasure.toMeasure_map] at hm
  have hsub : ∀ᵐ p ∂(ν.comap (Subtype.val : BoundedSpace M → Profile) :
      Measure (BoundedSpace M)), B p.val := by
    apply ae_of_ae_map measurable_subtype_coe.aemeasurable
    rwa [hm]
  have hprod : ∀ᵐ p ∂(ν.comap (Subtype.val : BoundedSpace M → Profile) :
      Measure (BoundedSpace M)).prod τ, B p.1.val := by
    apply (Measure.ae_prod_iff_ae_ae (hB.preimage
      (measurable_subtype_coe.comp measurable_fst))).mpr
    exact hsub.mono fun _ hp => Eventually.of_forall fun _ => hp
  filter_upwards [hprod] with p hp
  apply propext
  change (1 / ((n : ℝ) + 1) < p.2 ∧ p.2 < 1 ∧
      3 / ((n : ℝ) + 1) < |f (p.1.val,p.2)|) ↔
    (1 / ((n : ℝ) + 1) < p.2 ∧ p.2 < 1 ∧
      3 / ((n : ℝ) + 1) < |g p|)
  by_cases hz : 1 / ((n : ℝ) + 1) < p.2 ∧ p.2 < 1
  · rw [heq p.1 hp p.2 ⟨(lt_trans (by positivity) hz.1).le, hz.2.le⟩]
    rfl
  · tauto

theorem profile_rightGrid_real (n : ℕ) (ν : FiniteMeasure Profile)
    {s : Set (Profile × ℝ)} (hs : MeasurableSet s) :
    ((ν : Measure Profile).prod (ProfileParameterGrids.rightGrid n : Measure ℝ)).real s =
      (∑ i ∈ Finset.range (n + 1), (ν : Measure Profile).real
        {p | (p, (((i + 1 : ℕ) : ℝ) / (n + 1))) ∈ s}) / (n + 1) := by
  have h := ProfileParameterGrids.rightGrid_prod_real n ν (measurable_swap hs)
  rw [Measure.real, ← Measure.prod_swap,
    Measure.map_apply measurable_swap hs]
  exact h

theorem profile_powerGrid_real (γ : ℝ) (hγ : 0 ≤ γ) (n : ℕ)
    (ν : FiniteMeasure Profile) {s : Set (Profile × ℝ)} (hs : MeasurableSet s) :
    ((ν : Measure Profile).prod (ProfileParameterGrids.powerGrid γ hγ n : Measure ℝ)).real s =
      (∑ i ∈ Finset.range (n + 1), (ν : Measure Profile).real
        {p | (p, ((((i + 1 : ℕ) : ℝ) / (n + 1)) ^ γ⁻¹)) ∈ s}) / (n + 1) := by
  have h := ProfileParameterGrids.powerGrid_prod_real γ hγ n ν (measurable_swap hs)
  rw [Measure.real, ← Measure.prod_swap,
    Measure.map_apply measurable_swap hs]
  exact h

def clippedDiscrepancy {M : ℝ} (G : BoundedSpace M × ℝ → ℝ)
    (p : BoundedSpace M × (BoundedSpace M × ℝ)) : ℝ :=
  G p.2 - planeClipped (p.1,p.2.2)

theorem continuous_clippedDiscrepancy {M : ℝ}
    {G : BoundedSpace M × ℝ → ℝ} (hG : Continuous G) :
    Continuous (clippedDiscrepancy G) :=
  (hG.comp continuous_snd).sub ((continuous_planeClipped M).comp
    (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))

theorem moving_cutoff_liminf {M : ℝ} (hM : 0 ≤ M)
    (pn : ℕ → BoundedSpace M) (p : BoundedSpace M)
    (hp : Tendsto pn atTop (𝓝 p))
    (νn : ℕ → FiniteMeasure Profile) (ν : FiniteMeasure Profile)
    (hνn : ∀ n, νn n {x | IsBoundedProfile M x}ᶜ = 0)
    (hν : ν {x | IsBoundedProfile M x}ᶜ = 0)
    (hweak : Tendsto νn atTop (𝓝 ν))
    (τn : ℕ → FiniteMeasure ℝ) (τ : FiniteMeasure ℝ)
    (hτ : Tendsto τn atTop (𝓝 τ))
    (B : Profile → Prop) (hB : MeasurableSet {x | B x})
    (hBn : ∀ n, ∀ᵐ x ∂(νn n : Measure Profile), B x)
    (hBν : ∀ᵐ x ∂(ν : Measure Profile), B x)
    (T : Profile × ℝ → ℝ) (hT : Measurable T)
    (G : BoundedSpace M × ℝ → ℝ) (hG : Continuous G)
    (heq : ∀ x : BoundedSpace M, B x.val → ∀ z ∈ Icc (0 : ℝ) 1,
      T (x.val,z) = G (x,z)) (t : ℕ) :
    ((ν : Measure Profile).prod (τ : Measure ℝ)).real
      (ProfileDetection.cutoffDetection Prod.snd
        (fun x => T x - ProfileDetectionBridge.planeTest p.val x.2) t) ≤
    atTop.liminf (fun n => ((νn n : Measure Profile).prod (τn n : Measure ℝ)).real
      (ProfileDetection.cutoffDetection Prod.snd
        (fun x => T x - ProfileDetectionBridge.planeTest (pn n).val x.2) t)) := by
  let : Nonempty (BoundedSpace M) := ⟨p⟩
  have hsub := tendsto_comap_boundedProfiles hM hνn hν hweak
  have hlim := ProfileWeakDetection.le_liminf_moving_product_detection
    hp hsub hτ continuous_snd (continuous_clippedDiscrepancy hG)
    (1 / ((t : ℝ) + 1)) (3 / ((t : ℝ) + 1))
  have hident (a : BoundedSpace M) (ρ : FiniteMeasure Profile)
      (hρ : ρ {x | IsBoundedProfile M x}ᶜ = 0)
      (hρB : ∀ᵐ x ∂(ρ : Measure Profile), B x) (σ : FiniteMeasure ℝ) :
      ((ρ : Measure Profile).prod (σ : Measure ℝ)).real
        (ProfileDetection.cutoffDetection Prod.snd
          (fun x => T x - ProfileDetectionBridge.planeTest a.val x.2) t) =
      ((ρ.comap (Subtype.val : BoundedSpace M → Profile) : Measure (BoundedSpace M)).prod
        (σ : Measure ℝ)).real
        (ProfileWeakDetection.detectionSet Prod.snd
          (fun x => clippedDiscrepancy G (a,x))
          (1 / ((t : ℝ) + 1)) (3 / ((t : ℝ) + 1))) := by
    apply cutoff_real_eq_comap hM ρ hρ (σ : Measure ℝ) B hB hρB
      _ (hT.sub (ProfileParameterLaw.measurable_planeTest.comp
        (measurable_const.prodMk measurable_snd)))
      _ ((continuous_clippedDiscrepancy hG).comp
        (continuous_const.prodMk continuous_id)).measurable
    intro x hx z hz
    dsimp [clippedDiscrepancy]
    rw [heq x hx z hz, planeClipped_eq a hz]
  rw [hident p ν hν hBν τ]
  simp only [FiniteMeasure.toMeasure_prod] at hlim
  have hseq := fun n => hident (pn n) (νn n) (hνn n) (hBn n) (τn n)
  simp_rw [hseq]
  exact hlim

theorem actual_moving_cutoff_liminf
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (k : ℕ) (D C E : ∀ n, Finset (Line (F n)))
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    (P : Profile) (ν : FiniteMeasure Profile)
    (hP : Tendsto (fun n => planeProfile (D n) (C n)) atTop (𝓝 P))
    (hν : Tendsto (fun n => empiricalProfileMeasure (D n) (C n) (E n)) atTop (𝓝 ν))
    (τn : ℕ → FiniteMeasure ℝ) (τ : FiniteMeasure ℝ)
    (hτ : Tendsto τn atTop (𝓝 τ))
    (B : Profile → Prop) (hB : IsClosed {x | B x})
    (hBE : ∀ n l, l ∈ E n → B (lineProfile (D n) (C n) l))
    (T : Profile × ℝ → ℝ) (hT : Measurable T)
    (G : BoundedSpace (2 * (k : ℝ) + 4) × ℝ → ℝ) (hG : Continuous G)
    (heq : ∀ x : BoundedSpace (2 * (k : ℝ) + 4), B x.val →
      ∀ z ∈ Icc (0 : ℝ) 1, T (x.val,z) = G (x,z)) (t : ℕ) :
    ((ν : Measure Profile).prod (τ : Measure ℝ)).real
      (ProfileDetection.cutoffDetection Prod.snd
        (fun x => T x - ProfileDetectionBridge.planeTest P x.2) t) ≤
    atTop.liminf (fun n =>
      ((empiricalProfileMeasure (D n) (C n) (E n) : Measure Profile).prod
        (τn n : Measure ℝ)).real
        (ProfileDetection.cutoffDetection Prod.snd
          (fun x => T x - ProfileDetectionBridge.planeTest (planeProfile (D n) (C n)) x.2) t)) := by
  let M : ℝ := 2 * (k : ℝ) + 4
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hb n : IsBoundedProfile M (planeProfile (D n) (C n)) :=
    planeProfile_isBounded k (D n) (C n) (hpair n).1 (hpair n).2.2
  have hbP := ProfileAmbientCompactness.boundedProfile_of_tendsto hM hb hP
  let pn : ℕ → BoundedSpace M := fun n => ⟨planeProfile (D n) (C n), hb n⟩
  let p : BoundedSpace M := ⟨P,hbP⟩
  have hpn : Tendsto pn atTop (𝓝 p) := tendsto_subtype_rng.mpr hP
  have hs n : empiricalProfileMeasure (D n) (C n) (E n)
      {x | IsBoundedProfile M x}ᶜ = 0 :=
    ProfileEmpiricalSupport.admissible_empirical_bounded_support k (D n) (C n) (E n)
      (hpair n).1 (hpair n).2.2
  have hsν := ProfileAmbientCompactness.boundedProfile_support_of_tendsto hM hs hν
  have hBn n : ∀ᵐ x ∂(empiricalProfileMeasure (D n) (C n) (E n) : Measure Profile), B x := by
    apply ae_iff.mpr
    exact (FiniteMeasure.null_iff_toMeasure_null _ _).mp
      (ProfileEmpiricalSupport.empiricalProfileMeasure_compl_eq_zero
        (D n) (C n) (E n) hB.measurableSet (hBE n))
  have hKB := (ProfileAmbientCompactness.isCompact_boundedProfiles M hM).inter_right hB
  have hνKB := ProfileAmbientCompactness.compact_support_of_tendsto hKB
    (μ := fun n => empiricalProfileMeasure (D n) (C n) (E n))
    (fun n => ProfileEmpiricalSupport.empiricalProfileMeasure_compl_eq_zero
      (D n) (C n) (E n) hKB.measurableSet (fun l hl =>
        ⟨lineProfile_isBounded k (D n) (C n) l (hpair n).1 (hpair n).2.2, hBE n l hl⟩)) hν
  have hBν : ∀ᵐ x ∂(ν : Measure Profile), B x := by
    have ha := ae_iff.mpr ((FiniteMeasure.null_iff_toMeasure_null ν _).mp hνKB)
    exact ha.mono fun _ hx => hx.2
  exact moving_cutoff_liminf hM pn p hpn _ ν hs hsν hν τn τ hτ B hB.measurableSet
    hBn hBν T hT G hG heq t

section ActualGrids

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def dGridCutoffMass (D C : Finset (Line F)) (t : ℕ) : ℝ :=
  (∑ i ∈ Finset.range D.card,
    (empiricalProfileMeasure D C D : Measure Profile).real {x |
      (x, (((i + 1 : ℕ) : ℝ) / D.card)) ∈
        ProfileDetection.cutoffDetection Prod.snd
          (ProfileDetectionLimit.dDiscrepancy (planeProfile D C)) t}) / D.card

def cGridCutoffMass (D C : Finset (Line F)) (t : ℕ) : ℝ :=
  (∑ i ∈ Finset.range C.card,
    (empiricalProfileMeasure D C C : Measure Profile).real {x |
      (x, ((((i + 1 : ℕ) : ℝ) / C.card) ^ (Real.sqrt 2)⁻¹)) ∈
        ProfileDetection.cutoffDetection Prod.snd
          (ProfileDetectionLimit.cDiscrepancy (planeProfile D C)) t}) / C.card

@[simp] theorem cGridCutoffMass_empty (D : Finset (Line F)) (t : ℕ) :
    cGridCutoffMass D ∅ t = 0 := by simp [cGridCutoffMass]

end ActualGrids

theorem dCutoff_le_liminf_actual_grid
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (k : ℕ) (hk : 1 ≤ k) (D C : ∀ n, Finset (Line (F n)))
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop)
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (ht : ProfileSequenceLimit D C c P νD νC) (t : ℕ) :
    ((νD : Measure Profile).prod (ProfileParameterLaw.parameterLaw 1)).real
      (ProfileDetection.cutoffDetection Prod.snd (ProfileDetectionLimit.dDiscrepancy P) t) ≤
    atTop.liminf (fun n => dGridCutoffMass (D n) (C n) t) := by
  have hcard n : Fintype.card (F n) ≤ (D n).card := by
    rw [profile_deletionSet_card k (D n) (hpair n).1]
    have hmul := Nat.mul_le_mul_right (Fintype.card (F n) + 1) hk
    simp only [Nat.one_mul] at hmul
    exact (Nat.le_succ _).trans hmul
  have hpos n : 1 ≤ (D n).card := (Fintype.card_pos (α := F n)).trans_le (hcard n)
  have hcount := tendsto_atTop_mono hcard hq
  have hN := (tendsto_sub_atTop_nat 1).comp hcount
  have hτ := ProbabilityMeasure.toFiniteMeasure_continuous.continuousAt.tendsto.comp
    (ProfileParameterGrids.tendsto_rightGrid.comp hN)
  have hB : IsClosed {x : Profile | ∀ j, x (0,j) = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun j => isClosed_eq (continuous_apply (0,j)) continuous_const
  have h := actual_moving_cutoff_liminf k D C D hpair P νD ht.2.1 ht.2.2.1
    (fun n => (ProfileParameterGrids.rightGrid ((D n).card - 1)).toFiniteMeasure)
    ProfileParameterGrids.unitUniform.toFiniteMeasure hτ
    (fun x => ∀ j, x (0,j) = 0) hB
    (fun n l hl => ProfileEmpiricalSupport.lineProfile_zero_first_of_mem (D n) (C n) l hl)
    (fun x => ProfileDetectionBridge.dTest x.1 x.2) ProfileParameterLaw.measurable_dTest
    dClipped (continuous_dClipped _) (fun x hx z hz => (dClipped_eq x hz hx).symm) t
  simp only [ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    ProfileParameterGrids.unitUniform_eq_parameterLaw_one] at h
  have hgrid n :
      ((empiricalProfileMeasure (D n) (C n) (D n) : Measure Profile).prod
        (ProfileParameterGrids.rightGrid ((D n).card - 1) : Measure ℝ)).real
        (ProfileDetection.cutoffDetection Prod.snd
          (fun x => ProfileDetectionBridge.dTest x.1 x.2 -
            ProfileDetectionBridge.planeTest (planeProfile (D n) (C n)) x.2) t) =
      dGridCutoffMass (D n) (C n) t := by
    have hf := ProfileDetectionLimit.measurable_dDiscrepancy (planeProfile (D n) (C n))
    have hs : MeasurableSet (ProfileDetection.cutoffDetection Prod.snd
        (fun x => ProfileDetectionBridge.dTest x.1 x.2 -
          ProfileDetectionBridge.planeTest (planeProfile (D n) (C n)) x.2) t) := by
      change MeasurableSet (ProfileDetection.cutoffDetection Prod.snd
        (ProfileDetectionLimit.dDiscrepancy (planeProfile (D n) (C n))) t)
      unfold ProfileDetection.cutoffDetection
      measurability
    rw [profile_rightGrid_real _ _ hs]
    have hcast : (((D n).card - 1 : ℕ) : ℝ) + 1 = (D n).card := by
      exact_mod_cast Nat.sub_add_cancel (hpos n)
    simp only [Nat.sub_add_cancel (hpos n), hcast]
    rfl
  simp_rw [hgrid] at h
  exact h

theorem cCutoff_le_liminf_of_card_tendsto
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (k : ℕ) (D C : ∀ n, Finset (Line (F n)))
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    (hcount : Tendsto (fun n => (C n).card) atTop atTop)
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (ht : ProfileSequenceLimit D C c P νD νC) (t : ℕ) :
    ((νC : Measure Profile).prod (ProfileParameterLaw.parameterLaw (Real.sqrt 2))).real
      (ProfileDetection.cutoffDetection Prod.snd (ProfileDetectionLimit.cDiscrepancy P) t) ≤
    atTop.liminf (fun n => cGridCutoffMass (D n) (C n) t) := by
  have hγ : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hγ0 := zero_le_one.trans hγ
  have hN := (tendsto_sub_atTop_nat 1).comp hcount
  have hτ := ProbabilityMeasure.toFiniteMeasure_continuous.continuousAt.tendsto.comp
    ((ProfileParameterGrids.tendsto_powerGrid (Real.sqrt 2) hγ0).comp hN)
  have hB : IsClosed {x : Profile | ∀ i, x (i,0) = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_eq (continuous_apply (i,0)) continuous_const
  have h := actual_moving_cutoff_liminf k D C C hpair P νC ht.2.1 ht.2.2.2
    (fun n => (ProfileParameterGrids.powerGrid (Real.sqrt 2) hγ0 ((C n).card - 1)).toFiniteMeasure)
    (ProfileParameterGrids.powerUniform (Real.sqrt 2) hγ0).toFiniteMeasure hτ
    (fun x => ∀ i, x (i,0) = 0) hB
    (fun n l hl => ProfileEmpiricalSupport.lineProfile_zero_second_of_mem (D n) (C n) l hl)
    (fun x => ProfileDetectionBridge.cTest x.1 x.2) ProfileParameterLaw.measurable_cTest
    cClipped (continuous_cClipped _) (fun x hx z hz => (cClipped_eq x hz hx).symm) t
  simp only [ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    ProfileParameterGrids.powerUniform_eq_parameterLaw hγ] at h
  have hgrid : ∀ᶠ n in atTop,
      ((empiricalProfileMeasure (D n) (C n) (C n) : Measure Profile).prod
        (ProfileParameterGrids.powerGrid (Real.sqrt 2) hγ0 ((C n).card - 1) : Measure ℝ)).real
        (ProfileDetection.cutoffDetection Prod.snd
          (fun x => ProfileDetectionBridge.cTest x.1 x.2 -
            ProfileDetectionBridge.planeTest (planeProfile (D n) (C n)) x.2) t) =
      cGridCutoffMass (D n) (C n) t := by
    filter_upwards [hcount.eventually_ge_atTop 1] with n hn
    have hf := ProfileDetectionLimit.measurable_cDiscrepancy (planeProfile (D n) (C n))
    have hs : MeasurableSet (ProfileDetection.cutoffDetection Prod.snd
        (fun x => ProfileDetectionBridge.cTest x.1 x.2 -
          ProfileDetectionBridge.planeTest (planeProfile (D n) (C n)) x.2) t) := by
      change MeasurableSet (ProfileDetection.cutoffDetection Prod.snd
        (ProfileDetectionLimit.cDiscrepancy (planeProfile (D n) (C n))) t)
      unfold ProfileDetection.cutoffDetection
      measurability
    rw [profile_powerGrid_real _ _ _ _ hs]
    have hcast : (((C n).card - 1 : ℕ) : ℝ) + 1 = (C n).card := by
      exact_mod_cast Nat.sub_add_cancel hn
    simp only [Nat.sub_add_cancel hn, hcast]
    rfl
  rw [liminf_congr hgrid] at h
  exact h

section GridBounds

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem cGridCutoffMass_nonneg (D C : Finset (Line F)) (t : ℕ) :
    0 ≤ cGridCutoffMass D C t := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Finset.sum_nonneg fun _ _ => measureReal_nonneg

theorem cGridCutoffMass_le_one (D C : Finset (Line F))
    (hC : C.card ≤ Fintype.card F) (t : ℕ) : cGridCutoffMass D C t ≤ 1 := by
  by_cases hc : C.card = 0
  · simp [cGridCutoffMass, hc]
  have hcR : (0 : ℝ) < C.card := by exact_mod_cast Nat.pos_of_ne_zero hc
  apply (div_le_iff₀ hcR).mpr
  calc
    _ ≤ ∑ _i ∈ Finset.range C.card, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ ≤ (empiricalProfileMeasure D C C : Measure Profile).real univ :=
          measureReal_mono (subset_univ _)
        _ = (C.card : ℝ) / (Fintype.card F : ℝ) :=
          FiniteProfile.empiricalProfileMeasure_mass D C C
        _ ≤ 1 := (div_le_one (by exact_mod_cast Fintype.card_pos (α := F))).mpr (by exact_mod_cast hC)
    _ = _ := by simp

end GridBounds

theorem cover_limit_mass
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    {D C : ∀ n, Finset (Line (F n))}
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (ht : ProfileSequenceLimit D C c P νD νC) : (νC.mass : ℝ) = c := by
  have hm : Tendsto
      (fun n => ((empiricalProfileMeasure (D n) (C n) (C n)).mass : ℝ))
      atTop (𝓝 (νC.mass : ℝ)) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp ht.2.2.2.mass
  have heq n : ((empiricalProfileMeasure (D n) (C n) (C n)).mass : ℝ) =
      ((C n).card : ℝ) / (Fintype.card (F n) : ℝ) := by
    have h := FiniteProfile.empiricalProfileMeasure_mass (D n) (C n) (C n)
    simpa only [Measure.real, ← FiniteMeasure.ennreal_mass, ENNReal.coe_toReal] using h
  simp_rw [heq] at hm
  exact tendsto_nhds_unique hm ht.1

theorem cCutoff_le_liminf_actual_grid
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (k : ℕ) (D C : ∀ n, Finset (Line (F n)))
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop)
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (ht : ProfileSequenceLimit D C c P νD νC) (t : ℕ) :
    ((νC : Measure Profile).prod (ProfileParameterLaw.parameterLaw (Real.sqrt 2))).real
      (ProfileDetection.cutoffDetection Prod.snd (ProfileDetectionLimit.cDiscrepancy P) t) ≤
    atTop.liminf (fun n => cGridCutoffMass (D n) (C n) t) := by
  have hm := cover_limit_mass ht
  have hc : 0 ≤ c := hm ▸ νC.mass.coe_nonneg
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · have hm0 : νC.mass = 0 := by
      apply NNReal.coe_injective
      simpa only [NNReal.coe_zero, ← hc0] using hm
    have hν : νC = 0 := (FiniteMeasure.mass_zero_iff νC).mp hm0
    simp only [hν, FiniteMeasure.toMeasure_zero, Measure.zero_prod, measureReal_zero]
    have hb : atTop.IsBoundedUnder (· ≤ ·)
        (fun n => cGridCutoffMass (D n) (C n) t) :=
      isBoundedUnder_of ⟨1, fun n => cGridCutoffMass_le_one (D n) (C n) (hpair n).2.2 t⟩
    exact le_liminf_of_le hb.isCoboundedUnder_ge
      (Eventually.of_forall fun n => cGridCutoffMass_nonneg (D n) (C n) t)
  · have hhalf : 0 < c / 2 := half_pos hcpos
    have hratio : ∀ᶠ n in atTop,
        c / 2 ≤ ((C n).card : ℝ) / (Fintype.card (F n) : ℝ) :=
      (ht.1.eventually (eventually_ge_nhds (by linarith : c / 2 < c)))
    have hbound : ∀ᶠ n in atTop,
        c / 2 * (Fintype.card (F n) : ℝ) ≤ (C n).card := by
      filter_upwards [hratio] with n hn
      exact (le_div_iff₀ (by exact_mod_cast Fintype.card_pos (α := F n))).mp hn
    have hqR : Tendsto (fun n => (Fintype.card (F n) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_iff.mpr hq
    have hcountR : Tendsto (fun n => ((C n).card : ℝ)) atTop atTop :=
      tendsto_atTop_mono' atTop hbound (hqR.const_mul_atTop hhalf)
    exact cCutoff_le_liminf_of_card_tendsto k D C hpair
      (tendsto_natCast_atTop_iff.mp hcountR) ht t

section DeletionGridBounds
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem dGridCutoffMass_nonneg (D C : Finset (Line F)) (t : ℕ) :
    0 ≤ dGridCutoffMass D C t := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => measureReal_nonneg) (Nat.cast_nonneg _)

theorem dGridCutoffMass_le_two_mul (D C : Finset (Line F))
    {k : ℕ} (hD : IsDeletionSet k D) (t : ℕ) : dGridCutoffMass D C t ≤ 2 * k := by
  by_cases hd : D.card = 0
  · simp only [dGridCutoffMass, hd, Finset.range_zero, Finset.sum_empty, Nat.cast_zero,
      div_zero]
    positivity
  have hdR : (0 : ℝ) < D.card := by exact_mod_cast Nat.pos_of_ne_zero hd
  apply (div_le_iff₀ hdR).mpr
  calc
    _ ≤ ∑ _i ∈ Finset.range D.card, (2 * k : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ ≤ (empiricalProfileMeasure D C D : Measure Profile).real univ :=
          measureReal_mono (subset_univ _)
        _ = (k : ℝ) + k * (Fintype.card F : ℝ)⁻¹ :=
          FiniteProfile.empiricalProfileMeasure_deletion_mass D C hD
        _ ≤ 2 * k := by
          have hq : (1 : ℝ) ≤ Fintype.card F := by
            exact_mod_cast Fintype.card_pos (α := F)
          have hi := mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hq)
            (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
          linarith
    _ = _ := by simp; ring

end DeletionGridBounds

theorem cutoff_sum_le_liminf_actual_grid
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (k : ℕ) (hk : 1 ≤ k) (D C : ∀ n, Finset (Line (F n)))
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop)
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (ht : ProfileSequenceLimit D C c P νD νC) (t : ℕ) :
    ((νD : Measure Profile).prod (ProfileParameterLaw.parameterLaw 1)).real
      (ProfileDetection.cutoffDetection Prod.snd (ProfileDetectionLimit.dDiscrepancy P) t) +
    ((νC : Measure Profile).prod (ProfileParameterLaw.parameterLaw (Real.sqrt 2))).real
      (ProfileDetection.cutoffDetection Prod.snd (ProfileDetectionLimit.cDiscrepancy P) t) ≤
    atTop.liminf (fun n => dGridCutoffMass (D n) (C n) t +
      cGridCutoffMass (D n) (C n) t) := by
  have hd0 : atTop.IsBoundedUnder (· ≥ ·)
      (fun n => dGridCutoffMass (D n) (C n) t) :=
    isBoundedUnder_of ⟨0, fun n => dGridCutoffMass_nonneg (D n) (C n) t⟩
  have hd1 : atTop.IsBoundedUnder (· ≤ ·)
      (fun n => dGridCutoffMass (D n) (C n) t) :=
    isBoundedUnder_of ⟨2 * (k : ℝ), fun n =>
      dGridCutoffMass_le_two_mul (D n) (C n) (hpair n).1 t⟩
  have hc0 : atTop.IsBoundedUnder (· ≥ ·)
      (fun n => cGridCutoffMass (D n) (C n) t) :=
    isBoundedUnder_of ⟨0, fun n => cGridCutoffMass_nonneg (D n) (C n) t⟩
  have hc1 : atTop.IsBoundedUnder (· ≤ ·)
      (fun n => cGridCutoffMass (D n) (C n) t) :=
    isBoundedUnder_of ⟨1, fun n => cGridCutoffMass_le_one (D n) (C n) (hpair n).2.2 t⟩
  exact (add_le_add (dCutoff_le_liminf_actual_grid k hk D C hpair hq ht t)
    (cCutoff_le_liminf_actual_grid k D C hpair hq ht t)).trans
      (le_liminf_add hd0 hd1 hc0 hc1.isCoboundedUnder_ge)

theorem exists_cutoff_eventually_grid_excess
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (k : ℕ) (hk : 1 ≤ k) (D C : ∀ n, Finset (Line (F n)))
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop)
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (ht : ProfileSequenceLimit D C c P νD νC)
    (hexcess : c < (νD : Measure Profile).real (deletionVisible P) +
      (νC : Measure Profile).real (coverVisible P)) :
    ∃ t : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n in atTop,
      ((C n).card : ℝ) / (Fintype.card (F n) : ℝ) + ε <
        dGridCutoffMass (D n) (C n) t + cGridCutoffMass (D n) (C n) t := by
  obtain ⟨t, htcut⟩ := ProfileDetectionSource.exists_cutoff_of_visible_excess
    k D C hpair ht hexcess
  let S := ((νD : Measure Profile).prod (ProfileParameterLaw.parameterLaw 1)).real
      (ProfileDetection.cutoffDetection Prod.snd (ProfileDetectionLimit.dDiscrepancy P) t) +
    ((νC : Measure Profile).prod (ProfileParameterLaw.parameterLaw (Real.sqrt 2))).real
      (ProfileDetection.cutoffDetection Prod.snd (ProfileDetectionLimit.cDiscrepancy P) t)
  have hS : c < S := htcut
  let ε := (S - c) / 4
  have he : 0 < ε := by dsimp [ε]; linarith
  refine ⟨t, ε, he, ?_⟩
  have hlower := cutoff_sum_le_liminf_actual_grid k hk D C hpair hq ht t
  have hmargin : c + 2 * ε < atTop.liminf
      (fun n => dGridCutoffMass (D n) (C n) t + cGridCutoffMass (D n) (C n) t) := by
    have hsc : c + 2 * ε < S := by dsimp [ε]; linarith
    exact hsc.trans_le hlower
  have hb : atTop.IsBoundedUnder (· ≥ ·)
      (fun n => dGridCutoffMass (D n) (C n) t + cGridCutoffMass (D n) (C n) t) :=
    isBoundedUnder_of ⟨0, fun n => add_nonneg (dGridCutoffMass_nonneg (D n) (C n) t)
      (cGridCutoffMass_nonneg (D n) (C n) t)⟩
  have hg := eventually_lt_of_lt_liminf hmargin hb
  have hr := ht.1.eventually (eventually_lt_nhds (show c < c + ε by linarith))
  filter_upwards [hg, hr] with n hn hrn
  linarith

end Balanced.ProfileGridDetection

end

end OAI
