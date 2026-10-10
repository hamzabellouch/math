import Mathlib
import OAI.Probability.SKFluctuations.ResidualUniformCurvature
import OAI.Probability.SKFluctuations.ScalarGapFourth
import OAI.Probability.SKFluctuations.VariableMassClock

namespace OAI

/-! Rescaled Profile Test Continuity. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open Filter Set
open scoped Topology NNReal

noncomputable def rescaledBoundedProfile {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) : boundedMassProfiles :=
  ⟨fun s => α.val (s/T), (fun s => α.property.1 (s/T)),
    α.property.2.comp (monotone_id.div_const hT.le)⟩

theorem continuous_rescaledBoundedProfile {T : ℝ} (hT : 0 < T) :
    Continuous (rescaledBoundedProfile hT) := by
  have hh : Continuous (fun α : boundedMassProfiles => fun s : ℝ => α.val (s/T)) :=
    continuous_pi fun s => (continuous_apply (s/T)).comp continuous_subtype_val
  exact hh.subtype_mk _

theorem boundedNonnegativeProfile_rescaled {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) :
    boundedNonnegativeProfile (rescaledBoundedProfile hT α) = rescaledMassProfile α hT := rfl

theorem continuous_rescaledProfile_test {n : ℕ} (J : HeatJet n)
    {T : ℝ} (hT : 0 < T) (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) :
    Continuous (fun α : boundedMassProfiles =>
      J.nonnegativeProfileTest (rescaledMassProfile α hT) l t x) := by
  have hh := (continuous_boundedProfile_test J l t x).comp (continuous_rescaledBoundedProfile hT)
  simpa only [Function.comp_def,boundedNonnegativeProfile_rescaled] using hh

theorem prefixGridProfile_rescaled_test_tendsto {n : ℕ} (J : HeatJet n)
    {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) {q : ℝ} (hq : 0 ≤ q)
    (hc : ∀ x ∈ Ico (0:ℝ) q, ContinuousWithinAt α.val (Ici x) x)
    {h ε : ℕ → ℝ} (hh : ∀ N, 0 < h N) (hε : ∀ N, 0 ≤ ε N)
    (hεq : ∀ N, ε N ≤ α.val q) (ht : Tendsto h atTop (𝓝 0))
    (hεt : Tendsto ε atTop (𝓝 0)) (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) :
    Tendsto (fun N => J.nonnegativeProfileTest
      (rescaledMassProfile (prefixGridProfile α hq (hh N) (hε N) (hεq N)) hT) l t x)
      atTop (𝓝 (J.nonnegativeProfileTest (rescaledMassProfile α hT) l t x)) :=
  (continuous_rescaledProfile_test J hT l t x).continuousAt.tendsto.comp
    (prefixGridProfile_tendsto α hq hc hh hε hεq ht hεt)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set Scalar
open scoped Topology NNReal

theorem scalarPrefixResidualApproximation {T q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hq : 0 < q) (hq1 : q ≤ 1) (hm : 0 < α.val q)
    (hc : ∀ x ∈ Ico (0:ℝ) q, ContinuousWithinAt α.val (Ici x) x) :
    ∃ R : ℕ → GaussianResidual,
      (∀ N, (R N).variance=T*q) ∧ (∀ N, (R N).residual.Cone) ∧
      (∀ N x, |(R N).residual.jet 1 x| ≤ 1) ∧
      (∀ N, (∫ x, (R N).plantedDensity
        (fun y => (scalarTailJet hT α q).F (fun _ => y)) (α.val q) x)=1) ∧
      (∀ A (hA : BddSmooth 2 A),
        Tendsto (fun N => ∫ x, (R N).plantedDensity
          (fun y => (scalarTailJet hT α q).F (fun _ => y)) (α.val q) x*A (fun _ => x))
        atTop (𝓝 (((scalarTailJet hT α q).withTest A hA).nonnegativeProfileTest
          (rescaledMassProfile α hT) 0 (Real.toNNReal (T*q)) 0))) := by
  let h := fun N : ℕ => q/((N+1:ℕ):ℝ)
  let ε := fun N : ℕ => α.val q/((N+1:ℕ):ℝ)
  have hh (N) : 0 < h N := div_pos hq (by positivity)
  have hε (N) : 0 < ε N := div_pos hm (by positivity)
  have hεq (N) : ε N ≤ α.val q := by
    apply (div_le_iff₀ (show (0:ℝ) < ((N+1:ℕ):ℝ) by positivity)).mpr
    have hn : (1:ℝ) ≤ ((N+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    nlinarith
  let β := fun N => prefixGridProfile α hq.le (hh N) (hε N).le (hεq N)
  have ht : Tendsto h atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat q).comp (tendsto_add_atTop_nat 1)
  have hεt : Tendsto ε atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (α.val q)).comp (tendsto_add_atTop_nat 1)
  have hex (N) := prefixGridProfile_uniform_density hT α hq hq1 (hh N) (hε N)
    (hεq N) N (by dsimp only [h]; field_simp)
  choose R hv hR hd hg _he using hex
  have hF (N) : (scalarTailJet hT (β N) q).F=(scalarTailJet hT α q).F :=
    scalarTailJet_congr hT hq1 (fun u hu =>
      prefixGridProfile_tail α hq.le (hh N) (hε N).le (hεq N) hu.1.le)
  refine ⟨R,hv,hR,(fun N x => (hg N x).trans (α.property.1 q).2),?_,?_⟩
  · intro N
    have hn := (hd N).integral hT
    change (∫ x, (R N).plantedDensity (fun y => (scalarTailJet hT (β N) q).F (fun _ => y)) (α.val q) x)=1 at hn
    rwa [hF N] at hn
  · intro A hA
    let J := (scalarTailJet hT α q).withTest A hA
    have hcJ := prefixGridProfile_rescaled_test_tendsto J hT α hq.le hc hh
      (fun N => (hε N).le) hεq ht hεt 0 (Real.toNNReal (T*q)) 0
    have he (N) : J.nonnegativeProfileTest (rescaledMassProfile (β N) hT) 0 (Real.toNNReal (T*q)) 0 =
        ∫ x, (R N).plantedDensity (fun y => (scalarTailJet hT α q).F (fun _ => y)) (α.val q) x*A (fun _ => x) := by
      have hj := congrFun (HeatJet.nonnegativeProfileTest_congr J
        ((scalarTailJet hT (β N) q).withTest A hA) (hF N).symm rfl
        (rescaledMassProfile (β N) hT) 0 (Real.toNNReal (T*q))) 0
      rw [hj,hd N A hA]
      rw [hF N]
    simpa only [← he] using hcJ

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set Scalar
open scoped Topology NNReal

noncomputable def scalarPrefixRootSecond {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (q : ℝ) (hm : 0 < α.val q) : ℝ :=
  ((scalarTailJet hT α q).withTest
    (scalarRootSecond (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2)
      (T*q) (Real.toNNReal (T*(1-q))) (α.val q) 0)
    (scalarRootSecond_bddSmooth (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2)
      (T*q) (Real.toNNReal (T*(1-q))) hm 0 2)).nonnegativeProfileTest
    (rescaledMassProfile α hT) 0 (Real.toNNReal (T*q)) 0

noncomputable def scalarPrefixRootThird {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (q : ℝ) (hm : 0 < α.val q) : ℝ :=
  ((scalarTailJet hT α q).withTest
    (scalarRootThird (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2)
      (T*q) (Real.toNNReal (T*(1-q))) (α.val q) 0)
    (scalarRootThird_bddSmooth (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2)
      (T*q) (Real.toNNReal (T*(1-q))) hm 0 2)).nonnegativeProfileTest
    (rescaledMassProfile α hT) 0 (Real.toNNReal (T*q)) 0

theorem scalarPrefixRoot_transversality {T q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hq : 0 < q) (hq1 : q ≤ 1) (hm : 0 < α.val q)
    (hc : ∀ x ∈ Ico (0:ℝ) q, ContinuousWithinAt α.val (Ici x) x)
    (hz : scalarPrefixRootSecond hT α q hm=0) :
    0 < scalarPrefixRootThird hT α q hm := by
  let β := rescaledMassProfile α hT
  have hb : ∀ s, β.mass s ≤ 1 := fun s => (α.property.1 (s/T)).2
  let t := Real.toNNReal (T*(1-q))
  have hmq : α.val q ≤ β.mass (T*q) := by
    change α.val q ≤ α.val ((T*q)/T)
    rw [mul_div_cancel_left₀ _ hT.ne']
  have hF : scalarClockProfileJet β hb (T*q) t (α.val q) 0 0=
      fun y => (scalarTailJet hT α q).F (fun _ => y) := by
    funext y
    exact scalarClockProfileJet_zero_clock β hb (T*q) t hm y
  obtain ⟨R,hv,hR,hg,hn,ht⟩ := scalarPrefixResidualApproximation hT α hq hq1 hm hc
  have hM := ht (scalarRootSecond β hb (T*q) t (α.val q) 0)
    (scalarRootSecond_bddSmooth β hb (T*q) t hm 0 2)
  have hL := ht (scalarRootThird β hb (T*q) t (α.val q) 0)
    (scalarRootThird_bddSmooth β hb (T*q) t hm 0 2)
  change Tendsto _ atTop (𝓝 (scalarPrefixRootSecond hT α q hm)) at hM
  change Tendsto _ atTop (𝓝 (scalarPrefixRootThird hT α q hm)) at hL
  rw [hz] at hM
  rw [← hF] at hn hM hL
  exact scalarClockProfile_residual_test_sequence_root β hb (T*q) t hm hmq 0 R
    (mul_pos hT hq) hv hR hg hn hM hL

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal

theorem realSpatialJet_congr_slice {f g : ℝ × ℝ → ℝ} {s t : ℝ}
    (h : ∀ x, f (s,x)=g (t,x)) (k : ℕ) (x : ℝ) :
    realSpatialJet f k (s,x)=realSpatialJet g k (t,x) := by
  induction k generalizing x with
  | zero => exact h x
  | succ k ih =>
    change deriv (fun y => realSpatialJet f k (s,y)) x=deriv (fun y => realSpatialJet g k (t,y)) x
    rw [show (fun y => realSpatialJet f k (s,y))=(fun y => realSpatialJet g k (t,y)) from funext ih]

theorem HeatJet.scalarClockJet_zero_congr {J K : HeatJet 0} {m t : ℝ} (hm : 0 < m)
    (hF : K.F=(J.evolve hm t).F) (k : ℕ) (y : Fin 1 → ℝ) :
    K.scalarClockJet m k 0 y=J.scalarClockJet m k t y := by
  apply realSpatialJet_congr_slice
  intro x
  change clockContinuation m K.F 0 (fun _ => x)=clockContinuation m J.F t (fun _ => x)
  rw [clockContinuation_zero hm.ne']
  exact congrFun hF (fun _ => x)

theorem scalarPlateau_test_concat {T p q r m : ℝ} (hT : 0 < T)
    (hp : 0 ≤ p) (hpq : p < q) (hqr : q < r) (hr : r ≤ 1)
    (α : boundedMassProfiles) (hm : 0 < m) (hm1 : m ≤ 1)
    (hf : ∀ u ∈ Ioo p r, α.val u=m)
    (A : (Fin 1 → ℝ) → ℝ) (hA : BddSmooth 2 A)
    (B : HeatJet 0)
    (hBF : B.F=((scalarTailJet hT α r).evolve hm (T*(r-p))).F)
    (hBA : B.A=clockTest m ((scalarTailJet hT α r).evolve hm (T*(r-q))).F A (T*(q-p))) :
    ((scalarTailJet hT α q).withTest A hA).nonnegativeProfileTest
      (rescaledMassProfile α hT) 0 (Real.toNNReal (T*q)) 0 =
    B.nonnegativeProfileTest (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p)) 0 := by
  let J := scalarTailJet hT α r
  let K := (scalarTailJet hT α q).withTest A hA
  have hs : 0 < T*(q-p) := mul_pos hT (sub_pos.mpr hpq)
  have ht : 0 ≤ T*p := mul_nonneg hT.le hp
  have hq : 0 ≤ T*q := mul_nonneg hT.le (hp.trans hpq.le)
  have hd : 0 ≤ T*(r-q) := mul_nonneg hT.le (sub_nonneg.mpr hqr.le)
  have he : Real.toNNReal (T*p)+Real.toNNReal (T*(q-p))=Real.toNNReal (T*q) := by
    apply NNReal.eq
    simp only [NNReal.coe_add,Real.coe_toNNReal _ ht,Real.coe_toNNReal _ hs.le,Real.coe_toNNReal _ hq]
    ring
  have hh := K.nonnegativeProfileTest_clock_concat (rescaledMassProfile α hT)
    (fun u => (α.property.1 (u/T)).2) hm hm1 0
    (Real.toNNReal (T*p)) (Real.toNNReal (T*(q-p))) (by rwa [Real.coe_toNNReal _ hs.le]) (by
      intro u hu
      change α.val (u/T)=m
      apply hf
      simp only [zero_add,Real.coe_toNNReal _ ht,Real.coe_toNNReal _ hs.le] at hu
      exact ⟨(lt_div_iff₀ hT).mpr (by nlinarith [hu.1]),
        (div_lt_iff₀ hT).mpr (by nlinarith [hu.2])⟩) 0
  rw [he] at hh
  change K.nonnegativeProfileTest _ _ _ _ = _
  rw [hh]
  have hF : K.F=(J.evolve hm (T*(r-q))).F :=
    scalarTailJet_plateau_evolve hT hqr hr α hm (fun u hu => hf u ⟨hpq.trans hu.1,hu.2⟩)
  apply congrFun (HeatJet.nonnegativeProfileTest_congr _ _ ?_ ?_ _ _ _) 0
  · rw [hBF]
    change clockContinuation m K.F (Real.toNNReal (T*(q-p)))=clockContinuation m J.F (T*(r-p))
    rw [Real.coe_toNNReal _ hs.le,hF]
    funext x
    change clockContinuation m (clockContinuation m J.F (T*(r-q))) (T*(q-p)) x = _
    rw [clockContinuation_add J.lipschitz hm.ne' hs.le hd]
    congr 1
    ring
  · rw [hBA]
    change clockTest m K.F A (Real.toNNReal (T*(q-p)))=clockTest m _ A _
    rw [Real.coe_toNNReal _ hs.le,hF]

end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal

section
variable {T p q r m : ℝ} (hT : 0 < T) (hp : 0 ≤ p) (hpq : p < q) (hqr : q < r)
    (hr : r ≤ 1) (α : boundedMassProfiles) (hm : 0 < m) (hm1 : m ≤ 1)
    (hf : ∀ u ∈ Ioo p r, α.val u=m)

include hpq hqr hr hf hm
private theorem ScalarPlateauRoot_plateauRoot_jet (k : ℕ) (y : Fin 1 → ℝ) :
    scalarClockProfileJet (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2)
      (T*q) (Real.toNNReal (T*(1-q))) (α.val q) 0 k (y 0)=
      (scalarTailJet hT α r).scalarClockJet m k (T*(r-q)) y := by
  rw [hf q ⟨hpq,hqr⟩]
  have hy : (fun _ : Fin 1 => y 0)=y := by ext i; rw [Fin.eq_zero i]
  change (scalarTailJet hT α q).scalarClockJet m k 0 (fun _ => y 0)=_
  rw [hy]
  exact HeatJet.scalarClockJet_zero_congr hm
    (scalarTailJet_plateau_evolve hT hqr hr α hm (fun u hu => hf u ⟨hpq.trans hu.1,hu.2⟩)) k y

include hp hm1 in
theorem scalarPrefixRootSecond_plateau (hmq : 0 < α.val q) :
    scalarPrefixRootSecond hT α q hmq=
      (((scalarTailJet hT α r).profileGapCurvatureJet (scalarTailJet_G_smooth hT α r)
        hm (T*(r-p)) (T*(q-p))).nonnegativeProfileTest
          (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p)) 0) := by
  unfold scalarPrefixRootSecond
  apply scalarPlateau_test_concat hT hp hpq hqr hr α hm hm1 hf
  · exact (scalarTailJet hT α r).profileGapCurvatureJet_F _ hm _ _
  · rw [HeatJet.profileGapCurvatureJet_A]
    unfold HeatJet.scalarGapCurvature
    have hd : T*(r-p)-T*(q-p)=T*(r-q) := by ring
    rw [hd]
    have ht : scalarRootSecond (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2)
        (T*q) (Real.toNNReal (T*(1-q))) (α.val q) 0 =
        (fun y => (scalarTailJet hT α r).scalarClockJet m 3 (T*(r-q)) y ^ 2-
          2*m*(scalarTailJet hT α r).scalarClockJet m 2 (T*(r-q)) y ^ 3) := by
      funext y
      dsimp only [scalarRootSecond]
      rw [ScalarPlateauRoot_plateauRoot_jet hT hpq hqr hr α hm hf 3 y,
        ScalarPlateauRoot_plateauRoot_jet hT hpq hqr hr α hm hf 2 y,hf q ⟨hpq,hqr⟩]
    rw [ht]
    rfl

include hp hm1 in
theorem scalarPrefixRootThird_plateau (hmq : 0 < α.val q) :
    scalarPrefixRootThird hT α q hmq=
      (((scalarTailJet hT α r).profileGapThirdJet (scalarTailJet_G_smooth hT α r)
        hm (T*(r-p)) (T*(q-p))).nonnegativeProfileTest
          (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p)) 0) := by
  unfold scalarPrefixRootThird
  apply scalarPlateau_test_concat hT hp hpq hqr hr α hm hm1 hf
  · exact (scalarTailJet hT α r).profileGapThirdJet_F _ hm _ _
  · rw [HeatJet.profileGapThirdJet_A]
    unfold HeatJet.scalarGapThird
    have hd : T*(r-p)-T*(q-p)=T*(r-q) := by ring
    rw [hd]
    have ht : scalarRootThird (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2)
        (T*q) (Real.toNNReal (T*(1-q))) (α.val q) 0 =
        (fun y => (scalarTailJet hT α r).scalarClockJet m 4 (T*(r-q)) y ^ 2-
          12*m*((scalarTailJet hT α r).scalarClockJet m 2 (T*(r-q)) y *
            (scalarTailJet hT α r).scalarClockJet m 3 (T*(r-q)) y ^ 2)+
          6*m^2*(scalarTailJet hT α r).scalarClockJet m 2 (T*(r-q)) y ^ 4) := by
      funext y
      dsimp only [scalarRootThird]
      rw [ScalarPlateauRoot_plateauRoot_jet hT hpq hqr hr α hm hf 4 y,
        ScalarPlateauRoot_plateauRoot_jet hT hpq hqr hr α hm hf 3 y,
        ScalarPlateauRoot_plateauRoot_jet hT hpq hqr hr α hm hf 2 y,hf q ⟨hpq,hqr⟩]
      ring
    rw [ht]
    rfl

include hp hm1 in
theorem scalarPlateau_root_transversality
    (hc : ∀ x ∈ Ico (0:ℝ) q, ContinuousWithinAt α.val (Ici x) x)
    (hz : (((scalarTailJet hT α r).profileGapCurvatureJet (scalarTailJet_G_smooth hT α r)
        hm (T*(r-p)) (T*(q-p))).nonnegativeProfileTest
          (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p)) 0)=0) :
    0 < (((scalarTailJet hT α r).profileGapThirdJet (scalarTailJet_G_smooth hT α r)
        hm (T*(r-p)) (T*(q-p))).nonnegativeProfileTest
          (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p)) 0) := by
  have hmq : 0 < α.val q := by rw [hf q ⟨hpq,hqr⟩]; exact hm
  rw [← scalarPrefixRootThird_plateau hT hp hpq hqr hr α hm hm1 hf hmq]
  apply scalarPrefixRoot_transversality hT α (hp.trans_lt hpq) (hqr.le.trans hr) hmq hc
  rwa [scalarPrefixRootSecond_plateau hT hp hpq hqr hr α hm hm1 hf hmq]

end
end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

noncomputable def scalarTailSpatialJet {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles)
    (k : ℕ) (q : ℝ) (y : Fin 1 → ℝ) : ℝ :=
  scalarProfileJet (rescaledMassProfile α hT) (T*q) (Real.toNNReal (T*(1-q))) k (y 0)

theorem scalarTailSpatialJet_continuous {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (k : ℕ) :
    Continuous (fun p : ℝ × (Fin 1 → ℝ) => scalarTailSpatialJet hT α k p.1 p.2) :=
  scalarTailJet_spatial_continuous hT α k

theorem scalarTailSpatialJet_bounded {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (k : ℕ) :
    AbsBounded (fun p : ℝ × (Fin 1 → ℝ) => scalarTailSpatialJet hT α (k+1) p.1 p.2) :=
  ⟨(ReplicaTree.attachmentCount 1 k:ℝ),by positivity,fun p =>
    scalarProfileJet_bound _ (fun s => (α.property.1 (s/T)).2) _ _ k (p.2 0)⟩

theorem scalarTailSpatialJet_smooth {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (k : ℕ) (q : ℝ) :
    BddSmooth 0 (scalarTailSpatialJet hT α (k+1) q) :=
  scalarProfileJet_bddSmooth _ (fun s => (α.property.1 (s/T)).2) _ _ k

theorem scalarTailSpatialJet_line {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (k : ℕ) (q : ℝ) (x v : Fin 1 → ℝ) (s : ℝ) :
    HasDerivAt (fun r => scalarTailSpatialJet hT α k q (x+r • v))
      (∑ i, v i*scalarTailSpatialJet hT α (k+1) q (x+s • v)) s :=
  scalarProfileJet_line _ (fun s => (α.property.1 (s/T)).2) _ _ k x v s

theorem scalarTailSpatialJet_coord {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (k : ℕ) (q : ℝ) (i : Fin 1) (x : Fin 1 → ℝ) (s : ℝ) :
    HasDerivAt (fun r => scalarTailSpatialJet hT α k q (x+r • Pi.single i 1))
      (scalarTailSpatialJet hT α (k+1) q (x+s • Pi.single i 1)) s :=
  scalarProfileJet_coord _ (fun s => (α.property.1 (s/T)).2) _ _ k i x s

noncomputable def scalarTailTestJet {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles)
    (k : ℕ) (q : ℝ) : HeatJet 0 :=
  { scalarTailJet hT α q with
    A := scalarTailSpatialJet hT α (k+1) q
    A₁ := fun _ => scalarTailSpatialJet hT α (k+2) q
    A₂ := fun _ => scalarTailSpatialJet hT α (k+3) q
    smoothA := scalarTailSpatialJet_smooth hT α k q
    smoothA₁ := fun _ => scalarTailSpatialJet_smooth hT α (k+1) q
    smoothA₂ := fun _ => scalarTailSpatialJet_smooth hT α (k+2) q
    derivA := scalarTailSpatialJet_line hT α (k+1) q
    derivA₁ := scalarTailSpatialJet_coord hT α (k+2) q }

noncomputable def scalarTailTestFamily {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles)
    (k : ℕ) : HeatJetFamily 0 :=
  { scalarTailJetFamily hT α with
    J := scalarTailTestJet hT α k
    continuousA := scalarTailSpatialJet_continuous hT α (k+1)
    continuousA₁ := fun _ => scalarTailSpatialJet_continuous hT α (k+2)
    continuousA₂ := fun _ => scalarTailSpatialJet_continuous hT α (k+3)
    boundedA := scalarTailSpatialJet_bounded hT α k
    boundedA₁ := fun _ => scalarTailSpatialJet_bounded hT α (k+1)
    boundedA₂ := fun _ => scalarTailSpatialJet_bounded hT α (k+2) }

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem HeatJet.H_congr_F {J K : HeatJet 0} (he : J.F=K.F) : J.H 0=K.H 0 := by
  have hg := HeatJet.G_congr_F he
  funext x
  have hJ := J.derivG 0 x 0
  have hK := K.derivG 0 x 0
  simp only [zero_smul,add_zero] at hJ hK
  rw [hg] at hJ
  exact hJ.unique hK

noncomputable def scalarPlantedCurvature {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (q : ℝ) : ℝ :=
  ((scalarTailJet hT α q).withTest (fun y => ((scalarTailJet hT α q).H 0 y)^2)
    ((scalarTailJet_H_smooth hT α q 2 0).pow 2)).nonnegativeProfileTest
      (rescaledMassProfile α hT) 0 (Real.toNNReal (T*q)) 0

theorem scalarPlantedCurvature_plateau {T p q r m : ℝ} (hT : 0 < T)
    (hp : 0 ≤ p) (hpq : p < q) (hqr : q < r) (hr : r ≤ 1)
    (α : boundedMassProfiles) (hm : 0 < m) (hm1 : m ≤ 1)
    (hf : ∀ u ∈ Ioo p r, α.val u=m) :
    scalarPlantedCurvature hT α q=
      ((scalarTailJet hT α r).profileGapEnergyJet (scalarTailJet_G_smooth hT α r)
        hm (T*(r-p)) (T*(q-p))).nonnegativeProfileTest
          (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p)) 0 := by
  unfold scalarPlantedCurvature
  apply scalarPlateau_test_concat hT hp hpq hqr hr α hm hm1 hf
  · exact (scalarTailJet hT α r).profileGapEnergyJet_F _ hm _ _
  · rw [HeatJet.profileGapEnergyJet_A]
    unfold HeatJet.scalarGapEnergy
    have hd : T*(r-p)-T*(q-p)=T*(r-q) := by ring
    rw [hd]
    have ht : (fun y => (scalarTailJet hT α r).scalarClockJet m 2 (T*(r-q)) y ^ 2) =
        (fun y => ((scalarTailJet hT α q).H 0 y)^2) := by
      funext y
      congr 1
      rw [HeatJet.scalarClockJet_two _ hm]
      exact (congrFun (HeatJet.H_congr_F
        (scalarTailJet_plateau_evolve hT hqr hr α hm
          (fun u hu => hf u ⟨hpq.trans hu.1,hu.2⟩))) y).symm
    rw [ht]
    rfl

theorem scalarPlantedEnergy_derivative_plateau {T p q r m : ℝ} (hT : 0 < T)
    (hp : 0 ≤ p) (hq : q ∈ Ioo p r) (hr : r ≤ 1)
    (α : boundedMassProfiles) (hm : 0 < m) (hm1 : m ≤ 1)
    (hf : ∀ u ∈ Ioo p r, α.val u=m) :
    HasDerivAt (scalarPlantedEnergy hT α) (T*scalarPlantedCurvature hT α q) q := by
  rw [scalarPlantedCurvature_plateau hT hp hq.1 hq.2 hr α hm hm1 hf,mul_comm T]
  exact scalarPlantedEnergy_hasDerivAt_plateau hT hp hq hr α hm hm1 hf

theorem scalarPlantedCurvature_derivative_plateau {T p q r m : ℝ} (hT : 0 < T)
    (hp : 0 ≤ p) (hq : q ∈ Ioo p r) (hr : r ≤ 1)
    (α : boundedMassProfiles) (hm : 0 < m) (hm1 : m ≤ 1)
    (hf : ∀ u ∈ Ioo p r, α.val u=m) (hmq : 0 < α.val q) :
    HasDerivAt (scalarPlantedCurvature hT α) (T*scalarPrefixRootSecond hT α q hmq) q := by
  have hs : T*(q-p) ∈ Ioo (0:ℝ) (T*(r-p)) :=
    ⟨mul_pos hT (sub_pos.mpr hq.1),mul_lt_mul_of_pos_left (by linarith [hq.2]) hT⟩
  have hh := (scalarTailJet hT α r).profileGapEnergy_hasDerivAt
    (scalarTailJet_G_smooth hT α r) hm (scalarTailJet_H_smooth hT α r)
    hs (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2)
    0 (Real.toNNReal (T*p)) 0
  have hd : HasDerivAt (fun u : ℝ => T*(u-p)) T q := by
    simpa only [mul_one,id_eq] using ((hasDerivAt_id q).sub_const p).const_mul T
  rw [scalarPrefixRootSecond_plateau hT hp hq.1 hq.2 hr α hm hm1 hf hmq,mul_comm T]
  apply (hh.comp q hd).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hq.1 hq.2] with u hu
  exact scalarPlantedCurvature_plateau hT hp hu.1 hu.2 hr α hm hm1 hf

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem boundedProfile_L1_tendsto {α : ℕ → boundedMassProfiles} {β : boundedMassProfiles}
    (hα : Tendsto α atTop (𝓝 β)) (a b : ℝ) :
    Tendsto (fun n => ∫ s in a..b, |(α n).val s-β.val s|) atTop (𝓝 0) := by
  have hp (s : ℝ) := ((continuous_apply s).comp continuous_subtype_val).tendsto β |>.comp hα
  have hh := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (F := fun n s => |(α n).val s-β.val s|) (f:=fun _ => (0:ℝ))
    (μ:=volume) (a:=a) (b:=b) (fun _ => (1:ℝ))
    (Eventually.of_forall (fun n =>
      ((α n).property.2.measurable.sub β.property.2.measurable).abs.aestronglyMeasurable))
    (Eventually.of_forall (fun n => Filter.Eventually.of_forall (fun s _ => by
      have ha := (α n).property.1 s
      have hb := β.property.1 s
      simp only [Real.norm_eq_abs,abs_abs]
      exact abs_le.mpr ⟨by linarith [ha.1,hb.2],by linarith [ha.2,hb.1]⟩)))
    intervalIntegrable_const
    (Filter.Eventually.of_forall (fun s _ => by
      simpa only [Function.comp_apply,sub_self,abs_zero] using ((hp s).sub_const (β.val s)).abs))
  simpa only [intervalIntegral.integral_zero] using hh

theorem HeatJet.profile_parameter_tendstoUniformly {n : ℕ} (J : HeatJet n)
    {α : ℕ → boundedMassProfiles} {β : boundedMassProfiles}
    (hα : Tendsto α atTop (𝓝 β)) (l : ℝ) (t : ℝ≥0) :
    TendstoUniformly (fun k => J.nonnegativeProfileValue (boundedNonnegativeProfile (α k)) l t)
      (J.nonnegativeProfileValue (boundedNonnegativeProfile β) l t) atTop := by
  choose D _ hD using fun i => (J.smoothG i).bound
  have he := (boundedProfile_L1_tendsto hα l (l+t)).const_mul ((∑ i, (D i)^2)/2)
  simp only [mul_zero] at he
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [he.eventually (gt_mem_nhds hε)] with k hk x
  have hh := J.nonnegativeProfileValue_L1_comparison D hD
    (boundedNonnegativeProfile (α k)) (boundedNonnegativeProfile β) l t x
  simpa only [Real.dist_eq,abs_sub_comm] using hh.trans_lt hk

theorem scalarProfileJet_parameter_tendsto {α : ℕ → boundedMassProfiles}
    {β : boundedMassProfiles} (hα : Tendsto α atTop (𝓝 β))
    (l : ℝ) (t : ℝ≥0) (k : ℕ) :
    TendstoUniformly (fun n => scalarProfileJet (boundedNonnegativeProfile (α n)) l t k)
      (scalarProfileJet (boundedNonnegativeProfile β) l t k) atTop := by
  apply jet_tendstoUniformly_of_limit
    (fun n j => scalarProfileJet (boundedNonnegativeProfile (α n)) l t j)
    (scalarProfileJet (boundedNonnegativeProfile β) l t)
    (fun n j x => scalarProfileJet_hasDerivAt _ (fun s => ((α n).property.1 s).2) l t j x)
    (fun j => ⟨(ReplicaTree.attachmentCount 1 j:ℝ),fun n x =>
      scalarProfileJet_bound _ (fun s => ((α n).property.1 s).2) l t j x⟩)
    (scalarProfileJet_hasDerivAt _ (fun s => (β.property.1 s).2) l t)
  have hh := scalarTerminal.profile_parameter_tendstoUniformly hα l t
  rw [Metric.tendstoUniformly_iff] at hh ⊢
  intro ε hε
  filter_upwards [hh ε hε] with n hn x
  rw [scalarProfileJet_zero (boundedNonnegativeProfile β) (fun s => (β.property.1 s).2),
    scalarProfileJet_zero (boundedNonnegativeProfile (α n)) (fun s => ((α n).property.1 s).2)]
  exact hn (fun _ => x)

theorem scalarTailSpatialJet_parameter_tendsto {T : ℝ} (hT : 0 < T)
    {α : ℕ → boundedMassProfiles} {β : boundedMassProfiles}
    (hα : Tendsto α atTop (𝓝 β)) (q : ℝ) (k : ℕ) :
    TendstoUniformly (fun n => scalarTailSpatialJet hT (α n) k q)
      (scalarTailSpatialJet hT β k q) atTop := by
  have hr := (continuous_rescaledBoundedProfile hT).tendsto β |>.comp hα
  have hh := scalarProfileJet_parameter_tendsto hr (T*q) (Real.toNNReal (T*(1-q))) k
  rw [Metric.tendstoUniformly_iff] at hh ⊢
  intro ε hε
  filter_upwards [hh ε hε] with n hn x
  exact hn (x 0)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem tendstoUniformly_squared_unit {X : Type*} {f : ℕ → X → ℝ} {g : X → ℝ}
    (hf : ∀ n x, |f n x| ≤ 1) (hg : ∀ x, |g x| ≤ 1)
    (ht : TendstoUniformly f g atTop) :
    TendstoUniformly (fun n x => (f n x)^2) (fun x => (g x)^2) atTop := by
  rw [Metric.tendstoUniformly_iff] at ht ⊢
  intro ε hε
  filter_upwards [ht (ε/2) (by positivity)] with n hn x
  have hd : |f n x-g x| < ε/2 := by
    simpa only [Real.dist_eq,abs_sub_comm] using hn x
  have he : |f n x+g x| ≤ 2 := (abs_add_le _ _).trans (by linarith [hf n x,hg x])
  rw [Real.dist_eq,abs_sub_comm,sq_sub_sq,abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left he (abs_nonneg (f n x-g x))]

theorem scalarTailJet_H_abs_le {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles)
    (q : ℝ) (x : Fin 1 → ℝ) : |(scalarTailJet hT α q).H 0 x| ≤ 1 := by
  rw [abs_of_nonneg (scalarTailJet_admissible hT α q x).1]
  exact (scalarTailJet_admissible hT α q).curvature x

theorem scalarPlantedCurvature_bounds {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (q : ℝ) :
    0 ≤ scalarPlantedCurvature hT α q ∧ scalarPlantedCurvature hT α q ≤ 1 := by
  let J := (scalarTailJet hT α q).withTest (fun y => ((scalarTailJet hT α q).H 0 y)^2)
    ((scalarTailJet_H_smooth hT α q 2 0).pow 2)
  constructor
  · exact J.nonnegativeProfileTest_nonneg (fun y => sq_nonneg _)
      (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2) 0 _ 0
  · apply (le_abs_self _).trans
    apply J.nonnegativeProfileTest_abs_le _ (rescaledMassProfile α hT)
      (fun s => (α.property.1 (s/T)).2) 0 _ 0
    intro y
    change |((scalarTailJet hT α q).H 0 y)^2| ≤ 1
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_one_iff_abs_le_one _).mpr (scalarTailJet_H_abs_le hT α q y)

theorem scalarTailSpatialJet_window_tendsto {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) {q : ℕ → ℝ} {r : ℝ}
    (hq : Tendsto q atTop (𝓝 r)) (k : ℕ) :
    TendstoUniformly (fun n => scalarTailSpatialJet hT α k (q n))
      (scalarTailSpatialJet hT α k r) atTop := by
  have hl := hq.const_mul T
  have ht := continuous_real_toNNReal.tendsto (T*(1-r)) |>.comp
    ((tendsto_const_nhds.sub hq).const_mul T)
  have hh := scalarProfileJet_window_tendsto (rescaledMassProfile α hT)
    (fun s => (α.property.1 (s/T)).2) hl ht k
  rw [Metric.tendstoUniformly_iff] at hh ⊢
  intro ε hε
  filter_upwards [hh ε hε] with n hn x
  exact hn (x 0)

theorem scalarPlantedCurvature_continuous {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) :
    Continuous (scalarPlantedCurvature hT α) := by
  rw [continuous_iff_seqContinuous]
  intro q r hq
  let J (u : ℝ) := (scalarTailJet hT α u).withTest (fun y => ((scalarTailJet hT α u).H 0 y)^2)
    ((scalarTailJet_H_smooth hT α u 2 0).pow 2)
  have hA : TendstoUniformly (fun n => (J (q n)).A) (J r).A atTop :=
    tendstoUniformly_squared_unit (fun n => scalarTailJet_H_abs_le hT α (q n))
      (scalarTailJet_H_abs_le hT α r) (scalarTailSpatialJet_window_tendsto hT α hq 2)
  have hm := HeatJet.nonnegativeProfileTest_terminal_tendsto
    (fun n => J (q n)) (J r) (scalarTailJet_F_tendsto hT α hq) hA
    (fun _ => rescaledMassProfile α hT) (fun _ s => (α.property.1 (s/T)).2)
    (fun _ => 0) (fun n => Real.toNNReal (T*q n))
  have hl := ((J r).nonnegativeProfileTest_window_continuous (rescaledMassProfile α hT)
    (fun s => (α.property.1 (s/T)).2) 0).tendsto (0,Real.toNNReal (T*r)) |>.comp
      (tendsto_const_nhds.prodMk_nhds
        (continuous_real_toNNReal.tendsto (T*r) |>.comp (hq.const_mul T)))
  have hh := (hm.tendsto_at 0).add hl
  simpa only [Function.comp_def,sub_add_cancel,zero_add,scalarPlantedCurvature,J] using hh

theorem scalarPlantedCurvature_parameter_tendsto {T : ℝ} (hT : 0 < T)
    {α : ℕ → boundedMassProfiles} {β : boundedMassProfiles}
    (hα : Tendsto α atTop (𝓝 β)) (q : ℝ) :
    Tendsto (fun n => scalarPlantedCurvature hT (α n) q) atTop
      (𝓝 (scalarPlantedCurvature hT β q)) := by
  let J (γ : boundedMassProfiles) := (scalarTailJet hT γ q).withTest
    (fun y => ((scalarTailJet hT γ q).H 0 y)^2)
    ((scalarTailJet_H_smooth hT γ q 2 0).pow 2)
  have hA : TendstoUniformly (fun n => (J (α n)).A) (J β).A atTop :=
    tendstoUniformly_squared_unit (fun n => scalarTailJet_H_abs_le hT (α n) q)
      (scalarTailJet_H_abs_le hT β q) (scalarTailSpatialJet_parameter_tendsto hT hα q 2)
  have hm := HeatJet.nonnegativeProfileTest_terminal_tendsto (fun n => J (α n)) (J β)
    (scalarTailSpatialJet_parameter_tendsto hT hα q 0) hA
    (fun n => rescaledMassProfile (α n) hT) (fun n s => ((α n).property.1 (s/T)).2)
    (fun _ => 0) (fun _ => Real.toNNReal (T*q))
  have hl := (continuous_rescaledProfile_test (J β) hT 0 (Real.toNNReal (T*q)) 0).tendsto β |>.comp hα
  have hh := (hm.tendsto_at 0).add hl
  simpa only [Function.comp_def,sub_add_cancel,zero_add,scalarPlantedCurvature,J] using hh

theorem scalarPlantedEnergy_parameter_tendsto {T : ℝ} (hT : 0 < T)
    {α : ℕ → boundedMassProfiles} {β : boundedMassProfiles}
    (hα : Tendsto α atTop (𝓝 β)) (q : ℝ) :
    Tendsto (fun n => scalarPlantedEnergy hT (α n) q) atTop
      (𝓝 (scalarPlantedEnergy hT β q)) := by
  have hA : TendstoUniformly (fun n => (scalarTailJet hT (α n) q).square.A)
      (scalarTailJet hT β q).square.A atTop :=
    tendstoUniformly_squared_unit (fun n => scalarTailJet_G_bound hT (α n) q 0)
      (scalarTailJet_G_bound hT β q 0) (scalarTailSpatialJet_parameter_tendsto hT hα q 1)
  have hm := HeatJet.nonnegativeProfileTest_terminal_tendsto
    (fun n => (scalarTailJet hT (α n) q).square) (scalarTailJet hT β q).square
    (scalarTailSpatialJet_parameter_tendsto hT hα q 0) hA
    (fun n => rescaledMassProfile (α n) hT) (fun n s => ((α n).property.1 (s/T)).2)
    (fun _ => 0) (fun _ => Real.toNNReal (T*q))
  have hl := (continuous_rescaledProfile_test (scalarTailJet hT β q).square hT 0
    (Real.toNNReal (T*q)) 0).tendsto β |>.comp hα
  have hh := (hm.tendsto_at 0).add hl
  simpa only [Function.comp_def,sub_add_cancel,zero_add,scalarPlantedEnergy] using hh

end SKFluctuations.Hierarchy

end

end OAI
