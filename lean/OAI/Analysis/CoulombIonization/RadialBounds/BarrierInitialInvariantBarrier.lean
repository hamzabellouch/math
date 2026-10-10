import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierInitialCapsBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierInitializationBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierNuclearScaleBarrier

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierInitialInvariant_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

structure IsNuclearBarrier {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → TFSpace → ℝ) (Z k B C r T η : ℝ)
    (a p : Ω → TFSpace → ℝ) : Prop where
  measurable_offset : Measurable (Function.uncurry a)
  uniform_lipschitz_offset : DeterministicLocalLipschitz a
  bound_offset : DeterministicLocalBound a
  measurable_error : Measurable (Function.uncurry p)
  nonneg_error : ∀ sample x, 0 ≤ p sample x
  bounded_error : ∃ L : ℝ, ∀ sample x, p sample x ≤ L
  support_error : ∀ sample x, r < ‖x‖ → p sample x = 0
  weak : ∀ᵐ sample ∂P, WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+a sample x)
    (fun x => innerSource r (μ sample) (p sample) x+
      outerCoefficient r x*reaction k (nuclearField Z x+a sample x))
  lower : ∀ sample x, r ≤ ‖x‖ → outerBarrier B r x ≤ nuclearField Z x+a sample x
  upper : ∀ sample x, r ≤ ‖x‖ → nuclearField Z x+a sample x ≤ C/‖x‖^4
  tail : ∀ sample x, T*r < ‖x‖ → nuclearField Z x+a sample x = outerBarrier B r x
  mass : (∫ sample, (∫ x, p sample x) ∂P) ≤ η

lemma IsNuclearBarrier.locallyLipschitz_offset {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {μ a p : Ω → TFSpace → ℝ} {Z k B C r T η : ℝ}
    (h : IsNuclearBarrier P μ Z k B C r T η a p) (sample : Ω) :
    LocallyLipschitz (a sample) := h.uniform_lipschitz_offset.locallyLipschitz sample

lemma initial_error_mass_power {n Z r ε : ℝ} (hn : 0 ≤ n) (hcount : n ≤ 3*Z)
    (hr : 0 < r) (hr1 : r ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hrel : Z*r^3 = ε^3) {p : ℝ} (hp : p ≤ 1728*r^37) :
    n*p ≤ 5184*r^32 := by
  have he : Z*r^37 = ε^3*r^34 := by
    calc
      _ = (Z*r^3)*r^34 := by ring
      _ = _ := by rw [hrel]
  have hε3 : ε^3 ≤ 1 := pow_le_one₀ hε.le hε1
  have hrp : r^34 ≤ r^32 := pow_le_pow_of_le_one hr.le hr1 (by norm_num)
  calc
    n*p ≤ n*(1728*r^37) := mul_le_mul_of_nonneg_left hp hn
    _ ≤ (3*Z)*(1728*r^37) := mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = 5184*(ε^3*r^34) := by rw [show (3*Z)*(1728*r^37) = 5184*(Z*r^37) by ring,he]
    _ ≤ 5184*((1:ℝ)*r^32) := by gcongr
    _ = _ := by ring

theorem initial_barrier_invariant {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {A : Set Ω} (hA : MeasurableSet A)
    {μ : Ω → TFSpace → ℝ} (hm : Measurable (Function.uncurry μ))
    {M n Z B r ε k : ℝ} (hM : 0 ≤ M) (hn : 0 ≤ n)
    (hZ : 0 < Z) (hB : 0 < B) (hr : 0 < r) (hr1 : r ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hk : 0 ≤ k)
    (hrel : Z*r^3 = ε^3) (hquad : 4*initialQuadraticConstant k*ε^(3/2:ℝ) ≤ 1/20)
    (hBsmall : B ≤ ε^3/10) (hsub : 4*Real.pi*k*Real.sqrt B ≤ 19/2)
    (hμn : ∀ sample x, 0 ≤ μ sample x) (hμb : ∀ sample x, μ sample x ≤ M)
    (hμi : ∀ sample, Integrable (μ sample)) (hμc : ∀ sample, ∫ x, μ sample x ≤ n)
    (hcount : n ≤ 3*Z)
    (hgood : ∀ sample ∈ A, ∀ x : TFSpace, ‖x‖ ≤ (11/10)*r → innerPotential r (μ sample) x ≤ Z/(10*r))
    (hbad : P.real Aᶜ ≤ 1728*r^37) :
    IsNuclearBarrier P μ Z k B (max B (32*ε^3)) r 2 (5184*r^32)
      (fun sample => initializedOffset Z B r (initialQuadratic (initialQuadraticConstant k) Z r)
        (initialCharge A r μ sample)) (initialError A r μ) := by
  let a := initialQuadratic (initialQuadraticConstant k) Z r
  have ha : 0 ≤ a := mul_nonneg (initialQuadraticConstant_pos hk).le (Real.rpow_nonneg (by positivity) _)
  have hq : 4*a*r^2 ≤ Z/(20*r) := initialQuadratic_small hZ hr hε hrel hquad
  have hreact : reaction k (2*(Z/r)) ≤ 6*a := initialQuadratic_reaction hZ hr
  have hBs : B ≤ Z*r^3/10 := by rwa [hrel]
  have hρm := initialCharge_measurable hA r hm
  have hρn := initialCharge_nonneg (A := A) (r := r) hμn
  have hρb := initialCharge_bound (A := A) (r := r) hμn hμb
  have hρs := initialCharge_support A r μ
  have hρg := initialCharge_good hZ.le hr.le hgood
  have hmω (sample : Ω) : Measurable (μ sample) := hm.comp (measurable_const.prodMk measurable_id)
  have hρmω (sample : Ω) : Measurable (initialCharge A r μ sample) :=
    hρm.comp (measurable_const.prodMk measurable_id)
  refine ⟨initializedOffset_joint_measurable hρm Z B a hr,?_,
    initializedOffset_deterministicBound hρmω hM hr hρn hρb hρs Z B a,
    initialCharge_measurable hA.compl r hm,initialCharge_nonneg hμn,
    ⟨M,initialCharge_bound hμn hμb⟩,?_,?_,?_,?_,?_,?_⟩
  · exact initializedOffset_deterministicLip hZ hr ha hM hB.le hq hBs hρmω hρn hρb hρs hρg
  · intro sample x hx
    exact truncated_density_exterior (initialCharge_support Aᶜ r μ sample) hx.le
  · exact ae_of_all _ (fun sample => (initial_barrier_with_error hZ hB hr ha hk hq hreact hBs hsub
      hmω hμn hμb hgood sample).2)
  · intro sample x hx
    exact initializedBarrier_lower hx
  · intro sample x hx
    exact initializedBarrier_cap hZ hr hB.le ha hq (le_max_left _ _)
      (by rw [mul_assoc,hrel]; exact le_max_right _ _) (hρn sample) hx
  · intro sample x hx
    exact initializedBarrier_tail hZ hr hB.le ha hq (hρn sample) (by linarith)
  · exact (initialError_expected_mass hA hm hμn hμb hμi hμc).trans
      (initial_error_mass_power hn hcount hr hr1 hε hε1 hrel hbad)

end Work_BarrierInitialInvariant_barrier_scope

open Set Filter MeasureTheory Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

lemma nonneg_bounded_deterministicBound {Ω : Type*} {p : Ω → TFSpace → ℝ}
    (hn : ∀ sample x, 0 ≤ p sample x) {L : ℝ} (hb : ∀ sample x, p sample x ≤ L) :
    DeterministicLocalBound p := fun _ _ => ⟨L,fun sample x _ => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (hn sample x)] using hb sample x⟩

lemma nonneg_bounded_locallyIntegrable {p : TFSpace → ℝ} (hm : Measurable p)
    (hn : ∀ x, 0 ≤ p x) {L : ℝ} (hb : ∀ x, p x ≤ L) : LocallyIntegrable p :=
  deterministicBound_locallyIntegrable hm (nonneg_bounded_deterministicBound (fun _ : Unit => hn) (fun _ => hb))

lemma expected_mass_add {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {p q : Ω → TFSpace → ℝ} (hpm : Measurable (Function.uncurry p))
    (hqm : Measurable (Function.uncurry q)) (hpb : DeterministicLocalBound p) (hqb : DeterministicLocalBound q)
    {R S : ℝ} (hps : ∀ sample x, R < ‖x‖ → p sample x = 0) (hqs : ∀ sample x, S < ‖x‖ → q sample x = 0) :
    (∫ sample, (∫ x, p sample x+q sample x) ∂P) = (∫ sample, (∫ x, p sample x) ∂P)+(∫ sample, (∫ x, q sample x) ∂P) := by
  have hpi := compactBound_integrable_prod (P := P) hpm hpb hps
  have hqi := compactBound_integrable_prod (P := P) hqm hqb hqs
  calc
    _ = ∫ z, p z.1 z.2+q z.1 z.2 ∂P.prod volume :=
      (integral_prod (fun z => p z.1 z.2+q z.1 z.2) (hpi.add hqi)).symm
    _ = (∫ z, p z.1 z.2 ∂P.prod volume)+(∫ z, q z.1 z.2 ∂P.prod volume) := integral_add hpi hqi
    _ = _ := congrArg₂ (·+·) (integral_prod (fun z => p z.1 z.2) hpi) (integral_prod (fun z => q z.1 z.2) hqi)

theorem outward_barrier_invariant {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (good : Ω → Prop) [DecidablePred good] (hgood : MeasurableSet {sample | good sample})
    {Z B C R M κ lam1 lam2 e ξ Cinv hl hh T η : ℝ}
    (cal : OutwardCalibration κ B C M lam1 lam2 e ξ hl hh) (hR : 0 < R)
    {a h μ p : Ω → TFSpace → ℝ}
    (old : IsNuclearBarrier P μ Z κ B C (R/2) T η a p)
    (hm : Measurable (Function.uncurry h)) (hhl : DeterministicLocalLipschitz h)
    (hhb : DeterministicLocalBound h)
    (hμm : Measurable (Function.uncurry μ)) (hμn : ∀ sample x, 0 ≤ μ sample x)
    {D : ℝ} (hD : 0 ≤ D) (hμb : ∀ sample x, μ sample x ≤ D)
    (hhcap : ∀ sample, good sample → ∀ x, R/2 ≤ ‖x‖ → ‖x‖ < 2*M*R → nuclearField Z x+h sample x ≤ C/‖x‖^4)
    (hinv : ∀ sample, good sample → ∀ x, R/2 ≤ ‖x‖ → ‖x‖ < 2*M*R →
      InverseComparisonAt ‖x‖ (nuclearField Z x+h sample x) (μ sample x) κ hl hh ξ Cinv)
    (hwh : ∀ᵐ sample ∂P, good sample → WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+h sample x) (fun x => 4*Real.pi*μ sample x)) :
    IsNuclearBarrier P μ Z κ B C R M
      (η+∫ sample, (∫ x, addedError (good sample) R (μ sample) (fun _ => 0) x) ∂P)
      (fun sample => outwardOffset (good sample) (a sample) (h sample) Z B R M lam1 lam2)
      (fun sample => addedError (good sample) R (μ sample) (p sample)) := by
  obtain ⟨L,hpL⟩ := old.bounded_error
  have hpm := old.measurable_error
  have hpb := nonneg_bounded_deterministicBound old.nonneg_error hpL
  have hps := old.support_error
  have hpn := old.nonneg_error
  have hqm := addedError_measurable good hgood (p := fun _ _ => 0) hμm measurable_const R
  have hqb := nonneg_bounded_deterministicBound
    (fun sample x => addedError_nonneg (good sample) (R := R) (hμn sample) (fun _ => le_refl 0) x)
    (fun sample x => addedError_le (good sample) (R := R) hD (hμb sample) (fun _ => le_refl 0) x)
  have hqs : ∀ sample x, R < ‖x‖ → addedError (good sample) R (μ sample) (fun _ => 0) x = 0 :=
    fun sample x hx => addedError_support (good sample) hR.le (fun _ _ => rfl) hx
  refine ⟨outwardOffset_measurable good hgood old.measurable_offset hm Z B M lam1 lam2 hR,?_,
    outwardOffset_deterministicBound good old.bound_offset hhb Z B M lam1 lam2 hR,
    addedError_measurable good hgood hμm hpm R,
    (fun sample x => addedError_nonneg (good sample) (hμn sample) (hpn sample) x),
    ⟨L+D,fun sample x => addedError_le (good sample) hD (hμb sample) (hpL sample) x⟩,?_,?_,?_,?_,?_,?_⟩
  · exact outwardOffset_deterministicLip cal.B_pos.le cal.C_nonneg hR cal.M_large cal.shift_order cal.cap_shift
      cal.shift_small good old.uniform_lipschitz_offset hhl old.lower old.upper
      (fun sample hg x hx hx' => hhcap sample hg x (by nlinarith [cal.M_large]) hx')
  · exact fun sample x hx => addedError_support (good sample) hR.le (hps sample) hx
  · filter_upwards [old.weak,hwh] with sample hwa hwh
    have hmω := hμm.comp ((measurable_const (a := sample)).prodMk measurable_id)
    have hpω := hpm.comp ((measurable_const (a := sample)).prodMk measurable_id)
    exact outwardOffset_weak (good sample) cal hR (old.locallyLipschitz_offset sample).continuous
      (hhl.locallyLipschitz sample).continuous (nonneg_bounded_locallyIntegrable hmω (hμn sample) (hμb sample))
      (nonneg_bounded_locallyIntegrable hpω (hpn sample) (hpL sample))
      (hμn sample) (hpn sample) (old.lower sample) (old.upper sample) (hhcap sample) (hinv sample) hwa hwh
  · exact fun sample x hx => outwardOffset_lower cal.B_pos.le hR cal.shift_small (good sample) (old.lower sample) hx
  · exact fun sample x hx => outwardOffset_cap cal.B_pos.le hR cal.M_large cal.shift_order (good sample)
      cal.B_le_C (cal.xi_nonneg.trans cal.low_shift.le) (old.upper sample) (hhcap sample) hx
  · exact fun sample x hx => outwardOffset_tail cal.B_pos.le cal.C_nonneg hR cal.M_large cal.shift_order cal.cap_shift
      (good sample) (old.upper sample) (fun hg y hy hy' => hhcap sample hg y (by nlinarith [cal.M_large]) hy') hx
  · have hmass := expected_mass_add (P := P)
      (q := fun sample => addedError (good sample) R (μ sample) (fun _ => 0)) hpm hqm hpb hqb hps hqs
    simp only [addedError,zero_add] at hmass ⊢
    rw [hmass]
    linarith [old.mass]

end CoulombBarrier

end

end OAI
