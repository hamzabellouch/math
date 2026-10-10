import OAI.NumberTheory.DirichletL.Foundation
import OAI.NumberTheory.DirichletL.Detector.GramLatticeDecay
import OAI.NumberTheory.DirichletL.Detector.GramAnnularLattice

namespace OAI

noncomputable section
open Filter Set
open scoped Classical SchwartzMap ContDiff Topology

namespace ProbeGramJointConstruction
open ProbeGramLatticeDecay EisensteinSchwartzPoisson

def q1 (z : Joint) : ℝ := ‖z.fst‖^2
def q2 (z : Joint) : ℝ := ‖z.snd‖^2

lemma q1_smooth : ContDiff ℝ ∞ q1 :=
  (WithLp.fstL 2 ℝ ℂ ℂ).contDiff.norm_sq ℂ
lemma q2_smooth : ContDiff ℝ ∞ q2 :=
  (WithLp.sndL 2 ℝ ℂ ℂ).contDiff.norm_sq ℂ

lemma norm_sq_eq (z : Joint) : ‖z‖^2 = q1 z + q2 z :=
  WithLp.prod_norm_sq_eq_of_L2 z

def log1 (a b : ℝ) (ha : 0<a) (z : Joint) : ℝ :=
  CompletedHeight.patchedLog a b ha (q1 z)
def log2 (a b : ℝ) (ha : 0<a) (z : Joint) : ℝ :=
  CompletedHeight.patchedLog a b ha (q2 z)
def phase (a b : ℝ) (ha : 0<a) (z : Joint) : ℝ :=
  log1 a b ha z - log2 a b ha z
def rootScale (a b : ℝ) (ha : 0<a) (z : Joint) : ℝ :=
  Real.exp (-(log1 a b ha z + log2 a b ha z)/2)
def amplitude (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (z : Joint) : ℂ :=
  W (q1 z)*star (W (q2 z))*Complex.exp (-((log1 a b ha z+log2 a b ha z):ℂ))

lemma patchedLog_smooth (a b : ℝ) (ha : 0<a) :
    ContDiff ℝ ∞ (CompletedHeight.patchedLog a b ha) :=
  contDiff_id.add (CompletedHeight.logCorrection_smooth a b ha)
lemma log1_smooth (a b : ℝ) (ha : 0<a) : ContDiff ℝ ∞ (log1 a b ha) :=
  (patchedLog_smooth a b ha).comp q1_smooth
lemma log2_smooth (a b : ℝ) (ha : 0<a) : ContDiff ℝ ∞ (log2 a b ha) :=
  (patchedLog_smooth a b ha).comp q2_smooth
lemma phase_smooth (a b : ℝ) (ha : 0<a) : ContDiff ℝ ∞ (phase a b ha) :=
  (log1_smooth a b ha).sub (log2_smooth a b ha)
lemma rootScale_smooth (a b : ℝ) (ha : 0<a) : ContDiff ℝ ∞ (rootScale a b ha) :=
  (((log1_smooth a b ha).add (log2_smooth a b ha)).neg.div_const 2).exp
lemma rootScale_pos (a b : ℝ) (ha : 0<a) (z : Joint) : 0<rootScale a b ha z :=
  Real.exp_pos _
lemma amplitude_smooth (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (a b : ℝ) (ha : 0<a) :
    ContDiff ℝ ∞ (amplitude W a b ha) := by
  unfold amplitude
  have h1 := hW.comp q1_smooth
  have h2 := hW.comp q2_smooth
  have hl := (log1_smooth a b ha).add (log2_smooth a b ha)
  simpa only [Function.comp_apply, Complex.ofRealCLM_apply, Complex.ofReal_add, Complex.conjCLE_apply, Complex.star_def] using
    (h1.mul (Complex.conjCLE.contDiff.comp h2)).mul
      ((Complex.ofRealCLM.contDiff.comp hl).neg.cexp)

def rawProfile (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (v T : ℝ) (z : Joint) : ℂ :=
  (W (q1 z)*(q1 z:ℂ)^(-1+(v:ℂ)*Complex.I))*
    star (W (q2 z)*(q2 z:ℂ)^(-1+(v:ℂ)*Complex.I))*
    paperRadialFourier U (T/(q1 z*q2 z))

def patchedProfile (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (v T : ℝ) (z : Joint) : ℂ :=
  amplitude W a b ha z * FourierBridge.logPhase (v/(2*Real.pi)) (phase a b ha z) *
    paperFourierRayCLM U (Real.sqrt T*rootScale a b ha z)

lemma patchedProfile_smooth (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (v T : ℝ) :
    ContDiff ℝ ∞ (patchedProfile W U a b ha v T) := by
  have h1 := amplitude_smooth W hW a b ha
  have h2 := phase_smooth a b ha
  have h3 := rootScale_smooth a b ha
  have h4 := (paperFourierRayCLM U).smooth (⊤ : ℕ∞)
  have hp : ContDiff ℝ ∞ (fun z => FourierBridge.logPhase (v/(2*Real.pi)) (phase a b ha z)) := by
    unfold FourierBridge.logPhase
    exact ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul h2)).mul contDiff_const).cexp
  exact (h1.mul hp).mul (h4.comp (contDiff_const.mul h3))

lemma rawProfile_zero_left (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (v T : ℝ) (z : Joint)
    (hz : W (q1 z)=0) : rawProfile W U v T z=0 := by simp [rawProfile,hz]
lemma rawProfile_zero_right (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (v T : ℝ) (z : Joint)
    (hz : W (q2 z)=0) : rawProfile W U v T z=0 := by simp [rawProfile,hz]
lemma patchedProfile_zero_left (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (v T : ℝ) (z : Joint) (hz : W (q1 z)=0) : patchedProfile W U a b ha v T z=0 := by
  simp [patchedProfile,amplitude,hz]
lemma patchedProfile_zero_right (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (v T : ℝ) (z : Joint) (hz : W (q2 z)=0) : patchedProfile W U a b ha v T z=0 := by
  simp [patchedProfile,amplitude,hz]

def sourceCompact (b : ℝ) : Set Joint := Metric.closedBall 0 (1+2*b)
lemma sourceCompact_isCompact (b : ℝ) : IsCompact (sourceCompact b) :=
  isCompact_closedBall _ _

lemma support_amplitude (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) :
    Function.support (amplitude W a b ha)⊆{z | a≤q1 z ∧ q1 z≤b ∧ a≤q2 z ∧ q2 z≤b} := by
  intro z hz
  have h1 : W (q1 z)≠0 := fun h => hz (by simp [amplitude,h])
  have h2 : W (q2 z)≠0 := fun h => hz (by simp [amplitude,h])
  exact ⟨(hs h1).1,(hs h1).2,(hs h2).1,(hs h2).2⟩

lemma annulus_subset_sourceCompact (a b : ℝ) (ha : 0<a) (hab : a<b) :
    {z : Joint | a≤q1 z ∧ q1 z≤b ∧ a≤q2 z ∧ q2 z≤b}⊆sourceCompact b := by
  intro z hz
  change dist z 0≤1+2*b
  rw [dist_zero_right]
  have hn := norm_sq_eq z
  have hb : 0<b := ha.trans hab
  nlinarith [norm_nonneg z, sq_nonneg (‖z‖-1),hz.2.1,hz.2.2.2]

lemma tsupport_amplitude_subset (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) :
    tsupport (amplitude W a b ha)⊆sourceCompact b := by
  exact closure_minimal ((support_amplitude W a b ha hs).trans
    (annulus_subset_sourceCompact a b ha hab)) Metric.isClosed_closedBall

lemma amplitude_hasCompactSupport (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) : HasCompactSupport (amplitude W a b ha) :=
  HasCompactSupport.of_support_subset_isCompact (sourceCompact_isCompact b)
    ((support_amplitude W a b ha hs).trans (annulus_subset_sourceCompact a b ha hab))

lemma patchedProfile_hasCompactSupport (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hab : a<b) (hs : Function.support W⊆Icc a b) (v T : ℝ) :
    HasCompactSupport (patchedProfile W U a b ha v T) :=
  ((amplitude_hasCompactSupport W a b ha hab hs).mul_right).mul_right

lemma norm_power_pair (v x y : ℝ) (hx : 0<x) (hy : 0<y) :
    (x:ℂ)^(-1+(v:ℂ)*Complex.I)*star ((y:ℂ)^(-1+(v:ℂ)*Complex.I)) =
      Complex.exp (-((Real.log x+Real.log y):ℂ))*
        FourierBridge.logPhase (v/(2*Real.pi)) (Real.log x-Real.log y) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne')]
  rw [←Complex.ofReal_log hx.le,←Complex.ofReal_log hy.le]
  simp only [Complex.star_def,←Complex.exp_conj,map_mul,map_add,map_neg,map_one,
    Complex.conj_ofReal,Complex.conj_I]
  unfold FourierBridge.logPhase
  rw [←Complex.exp_add,←Complex.exp_add]
  congr 1
  push_cast
  have hpi : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

lemma sqrt_reciprocal_product (T x y : ℝ) (hT : 0≤T) (hx : 0<x) (hy : 0<y) :
    Real.sqrt (T/(x*y))=Real.sqrt T*Real.exp (-(Real.log x+Real.log y)/2) := by
  have he : Real.exp (-(Real.log x+Real.log y)/2)^2=(x*y)⁻¹ := by
    rw [←Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2:ℝ)*(-(Real.log x+Real.log y)/2)=-(Real.log x+Real.log y) by ring,
      Real.exp_neg,Real.exp_add,Real.exp_log hx,Real.exp_log hy]
  have hl := Real.sq_sqrt (div_nonneg hT (mul_pos hx hy).le)
  have hr : (Real.sqrt T*Real.exp (-(Real.log x+Real.log y)/2))^2=T/(x*y) := by
    rw [mul_pow,Real.sq_sqrt hT,he,div_eq_mul_inv]
  nlinarith [Real.sqrt_nonneg (T/(x*y)),Real.sqrt_nonneg T,
    Real.exp_pos (-(Real.log x+Real.log y)/2),mul_nonneg (Real.sqrt_nonneg T)
      (Real.exp_pos (-(Real.log x+Real.log y)/2)).le]

theorem rawProfile_eq_patchedProfile (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Icc a b)
    (v T : ℝ) (hT : 0≤T) (z : Joint) :
    rawProfile W U v T z=patchedProfile W U a b ha v T z := by
  by_cases h1 : W (q1 z)=0
  · rw [rawProfile_zero_left W U v T z h1,patchedProfile_zero_left W U a b ha v T z h1]
  by_cases h2 : W (q2 z)=0
  · rw [rawProfile_zero_right W U v T z h2,patchedProfile_zero_right W U a b ha v T z h2]
  have hx := ha.trans_le (hs h1).1
  have hy := ha.trans_le (hs h2).1
  have hl1 : log1 a b ha z=Real.log (q1 z) := CompletedHeight.patchedLog_eq_log a b ha _ (hs h1)
  have hl2 : log2 a b ha z=Real.log (q2 z) := CompletedHeight.patchedLog_eq_log a b ha _ (hs h2)
  have hker : paperRadialFourier U (T/(q1 z*q2 z)) =
      paperFourierRayCLM U (Real.sqrt T*rootScale a b ha z) := by
    rw [paperRadialFourier_eq_ray]
    change paperFourierRayCLM U (Real.sqrt (T/(q1 z*q2 z))) = _
    rw [sqrt_reciprocal_product T _ _ hT hx hy]
    simp only [rootScale,hl1,hl2]
  unfold rawProfile patchedProfile amplitude phase
  rw [hker,hl1,hl2]
  simp only [star_mul]
  calc
    _ = (W (q1 z)*star (W (q2 z)))*
        ((q1 z:ℂ)^(-1+(v:ℂ)*Complex.I)*star ((q2 z:ℂ)^(-1+(v:ℂ)*Complex.I)))*
        paperFourierRayCLM U (Real.sqrt T*rootScale a b ha z) := by ring
    _ = _ := by rw [norm_power_pair v _ _ hx hy];ring

def amplitudeSchwartz (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) : 𝓢(Joint,ℂ) :=
  (amplitude_hasCompactSupport W a b ha hab hs).toSchwartzMap (amplitude_smooth W hW a b ha)

@[simp] lemma amplitudeSchwartz_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (z : Joint) :
    amplitudeSchwartz W a b ha hab hs hW z=amplitude W a b ha z := rfl

lemma rawProfile_smooth (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤T) : ContDiff ℝ ∞ (rawProfile W U v T) := by
  have he : rawProfile W U v T=patchedProfile W U a b ha v T :=
    funext (rawProfile_eq_patchedProfile W U a b ha hs v T hT)
  rw [he]
  exact patchedProfile_smooth W hW U a b ha v T

lemma support_rawProfile (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (hs : Function.support W⊆Icc a b) (v T : ℝ) :
    Function.support (rawProfile W U v T)⊆{z | a≤q1 z ∧ q1 z≤b ∧ a≤q2 z ∧ q2 z≤b} := by
  intro z hz
  have h1 : W (q1 z)≠0 := fun h => hz (rawProfile_zero_left W U v T z h)
  have h2 : W (q2 z)≠0 := fun h => hz (rawProfile_zero_right W U v T z h)
  exact ⟨(hs h1).1,(hs h1).2,(hs h2).1,(hs h2).2⟩

lemma rawProfile_hasCompactSupport (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hab : a<b) (hs : Function.support W⊆Icc a b) (v T : ℝ) :
    HasCompactSupport (rawProfile W U v T) :=
  HasCompactSupport.of_support_subset_isCompact (sourceCompact_isCompact b)
    ((support_rawProfile W U a b hs v T).trans (annulus_subset_sourceCompact a b ha hab))

def jointProfile (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤T) : 𝓢(Joint,ℂ) :=
  (rawProfile_hasCompactSupport W U a b ha hab hs v T).toSchwartzMap
    (rawProfile_smooth W U a b ha hs hW v T hT)

@[simp] theorem jointProfile_apply (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤T) (z : Joint) :
    jointProfile W U a b ha hab hs hW v T hT z=rawProfile W U v T z := rfl

theorem jointProfile_factorization (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤T) (z : Joint) :
    jointProfile W U a b ha hab hs hW v T hT z=
      amplitude W a b ha z * FourierBridge.logPhase (v/(2*Real.pi)) (phase a b ha z) *
        paperFourierRayCLM U (Real.sqrt T*rootScale a b ha z) :=
  rawProfile_eq_patchedProfile W U a b ha hs v T hT z

theorem jointProfile_annularSupport (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤T) :
    ProbeGramAnnularLattice.AnnularSupport a b (jointProfile W U a b ha hab hs hW v T hT) :=
  support_rawProfile W U a b hs v T

lemma jointProfile_zero_scale (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (v : ℝ) (z : Joint) :
    jointProfile W U a b ha hab hs hW v 0 (by positivity) z=
      (W (q1 z)*(q1 z:ℂ)^(-1+(v:ℂ)*Complex.I))*
        star (W (q2 z)*(q2 z:ℂ)^(-1+(v:ℂ)*Complex.I))*paperRadialFourier U 0 := by
  simp only [jointProfile_apply,rawProfile,zero_div]

lemma jointProfile_zero_of_left_small (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤T) (z : Joint) (hz : q1 z<a) :
    jointProfile W U a b ha hab hs hW v T hT z=0 := by
  apply rawProfile_zero_left
  by_contra h
  exact (not_le.mpr hz) (hs h).1

lemma jointProfile_zero_of_right_small (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤T) (z : Joint) (hz : q2 z<a) :
    jointProfile W U a b ha hab hs hW v T hT z=0 := by
  apply rawProfile_zero_right
  by_contra h
  exact (not_le.mpr hz) (hs h).1

end ProbeGramJointConstruction

end

end OAI
