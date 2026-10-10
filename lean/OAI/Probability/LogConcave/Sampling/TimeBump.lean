import Mathlib
import OAI.Probability.LogConcave.Sampling.ProbabilityVelocity
import OAI.Probability.LogConcave.Dynamics.VariationalField

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function Filter Metric
open scoped Topology NNReal

def timeBump {T : ℝ} (hT0 : 0≤T) (hT1 : T<1) : ContDiffBump (T/2) :=
  ⟨(T+1)/4,(3-T)/4,by linarith,by linarith⟩
def smoothTimeClip {T : ℝ} (hT0 : 0≤T) (hT1 : T<1) (t : ℝ) : ℝ :=
  T/2+timeBump hT0 hT1 t*(t-T/2)
lemma smoothTimeClip_contDiff {T : ℝ} (hT0 : 0≤T) (hT1 : T<1) (n : ℕ) :
    ContDiff ℝ (n:WithTop ℕ∞) (smoothTimeClip hT0 hT1) :=
  contDiff_const.add ((timeBump hT0 hT1).contDiff.mul (contDiff_id.sub contDiff_const))
lemma smoothTimeClip_eq {T t : ℝ} (hT0 : 0≤T) (hT1 : T<1) (ht : t∈Icc 0 T) :
    smoothTimeClip hT0 hT1 t=t := by
  have hh : timeBump hT0 hT1 t=1 := by
    apply (timeBump hT0 hT1).one_of_mem_closedBall
    rw [mem_closedBall,Real.dist_eq,abs_le]
    change -((T+1)/4)≤t-T/2 ∧ t-T/2≤(T+1)/4
    constructor <;> linarith [ht.1,ht.2]
  simp [smoothTimeClip,hh]
lemma smoothTimeClip_sq_lt {T : ℝ} (hT0 : 0≤T) (hT1 : T<1) (t : ℝ) :
    (smoothTimeClip hT0 hT1 t)^2<1 := by
  have hb : |timeBump hT0 hT1 t*(t-T/2)|≤(3-T)/4 := by
    by_cases ht : (3-T)/4≤dist t (T/2)
    · rw [(timeBump hT0 hT1).zero_of_le_dist ht,zero_mul,abs_zero]
      linarith
    · have hd : |t-T/2|≤(3-T)/4 := by simpa only [Real.dist_eq] using (le_of_lt (lt_of_not_ge ht))
      rw [abs_mul,abs_of_nonneg (timeBump hT0 hT1).nonneg]
      exact (mul_le_of_le_one_left (abs_nonneg _) (timeBump hT0 hT1).le_one).trans hd
  have hh := abs_le.mp hb
  dsimp [smoothTimeClip]
  have h1 : -1<T/2+timeBump hT0 hT1 t*(t-T/2) := by linarith [hh.1]
  have h2 : T/2+timeBump hT0 hT1 t*(t-T/2)<1 := by linarith [hh.2]
  nlinarith

def smoothProbabilityVelocity {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ)
    {T : ℝ} (hT0 : 0≤T) (hT1 : T<1) (t : ℝ) (y : Point d) : Point d :=
  probabilityVelocity F x r (smoothTimeClip hT0 hT1 t) y

lemma smoothProbabilityVelocity_contDiff {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (n : ℕ) :
    ContDiff ℝ (n:WithTop ℕ∞) (uncurry (smoothProbabilityVelocity F x r hT0 hT1)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hv : ContDiffAt ℝ (n:WithTop ℕ∞) (uncurry (probabilityVelocity F x r))
      (smoothTimeClip hT0 hT1 p.1,p.2) :=
    (probabilityVelocity_joint_smooth hF x hr (by linarith)
      (smoothTimeClip hT0 hT1 p.1,p.2) (smoothTimeClip_sq_lt hT0 hT1 p.1)).of_le (WithTop.coe_le_coe.mpr le_top)
  exact hv.comp (f:=fun q : ℝ × Point d => (smoothTimeClip hT0 hT1 q.1,q.2)) p
    (((smoothTimeClip_contDiff hT0 hT1 n).comp contDiff_fst).prodMk contDiff_snd).contDiffAt

def probabilityTransport {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (s t : Icc (0:ℝ) T) (z : Point d) : Point d :=
  GlobalODE.flow (fun u _ => clampedProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 u)
    (clampedProbabilityVelocity_continuous hF x hr hl hT0 hT1) s z t

lemma probabilityTransport_contDiff {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (s t : Icc (0:ℝ) T) (n : ℕ) :
    ContDiff ℝ (n:WithTop ℕ∞) (probabilityTransport hF x hr hl hT0 hT1 s t) := by
  let f := smoothProbabilityVelocity F x r hT0 hT1
  have hf := smoothProbabilityVelocity_contDiff hF x hr hl hT0 hT1 n
  have hL : ∀u∈Icc 0 T,LipschitzWith ⟨(Real.pi^2/2)*(lam:ℝ)*r^2,by positivity⟩ (f u) := by
    intro u hu
    change LipschitzWith _ (fun y => probabilityVelocity F x r (smoothTimeClip hT0 hT1 u) y)
    rw [smoothTimeClip_eq hT0 hT1 hu]
    exact probabilityVelocity_lipschitz hF x hr hl hu hT1
  have he : probabilityTransport hF x hr hl hT0 hT1 s t=
      (fun z => GlobalODE.flow hL hf.continuous s z t) := by
    funext z
    apply GlobalODE.flow_congr
    intro u hu y
    rw [clampedProbabilityVelocity_eq F x r T hT0 hu]
    dsimp [f,smoothProbabilityVelocity]
    rw [smoothTimeClip_eq hT0 hT1 hu]
  rw [he]
  exact GlobalODE.smooth_flow hf hL hT0 s t
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Function
open scoped NNReal Topology

lemma conditionalFieldMean_neg_time {d : ℕ} (F : Point d → ℝ) (x : Point d) (r t : ℝ) (y : Point d) :
    conditionalFieldMean F x r (-t) y=conditionalFieldMean F x r t (-y) := by
  have he : conditionalPotential F x r (-t) y = conditionalPotential F x r t (-y) := by
    funext z
    simp [conditionalPotential, neg_smul, smul_neg]
  simp only [conditionalFieldMean, he]
lemma probabilityVelocity_neg_time {d : ℕ} (F : Point d → ℝ) (x : Point d) (r t : ℝ) (y : Point d) :
    probabilityVelocity F x r (-t) y=probabilityVelocity F x r t (-y) := by
  simp only [probabilityVelocity,conditionalFieldMean_neg_time]

lemma probabilityVelocity_lipschitz_signed {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ : ρ^2<1) :
    LipschitzWith ⟨(Real.pi^2/2)*(lam:ℝ)*r^2,by positivity⟩ (probabilityVelocity F x r ρ) := by
  by_cases hp : 0≤ρ
  · exact probabilityVelocity_lipschitz hF x hr hl ⟨hp,le_rfl⟩ (by nlinarith)
  · have hn : 0≤-ρ := by linarith
    have hL := probabilityVelocity_lipschitz hF x hr hl ⟨hn,le_rfl⟩ (by nlinarith : -ρ<1)
    have he : probabilityVelocity F x r ρ=fun y => probabilityVelocity F x r (-ρ) (-y) := by
      funext y
      simpa only [neg_neg] using probabilityVelocity_neg_time F x r (-ρ) y
    rw [he]
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [dist_neg_neg] using hL.dist_le_mul (-y) (-z)

lemma smoothProbabilityVelocity_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (t : ℝ) :
    LipschitzWith ⟨(Real.pi^2/2)*(lam:ℝ)*r^2,by positivity⟩
      (smoothProbabilityVelocity F x r hT0 hT1 t) :=
  probabilityVelocity_lipschitz_signed hF x hr hl (smoothTimeClip_sq_lt hT0 hT1 t)

lemma smoothProbabilityVelocity_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    ContDiff ℝ (⊤:ℕ∞) (uncurry (smoothProbabilityVelocity F x r hT0 hT1)) :=
  contDiff_infty.mpr (smoothProbabilityVelocity_contDiff hF x hr hl hT0 hT1)
end LogConcaveSampling

end

end

end

end OAI
