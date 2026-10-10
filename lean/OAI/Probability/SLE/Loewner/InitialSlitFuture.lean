import OAI.Probability.SLE.Loewner.InitialForwardChart
import Mathlib.Topology.Order.ProjIcc

namespace OAI

/-! The physical future of an initial simple slit, with an exact real
offset parameter and no choice of conformal chart. -/
noncomputable section
open Set Filter Function
open scoped Topology

namespace SLEExactGauge

def slitFutureParameter (s : unitInterval) (r : ℝ) : unitInterval :=
  projIcc 0 1 zero_le_one ((s:ℝ)+r)

lemma slitFutureParameter_continuous (s : unitInterval) :
    Continuous (slitFutureParameter s) :=
  continuous_projIcc.comp (continuous_const.add continuous_id)

@[simp] lemma slitFutureParameter_zero (s : unitInterval) :
    slitFutureParameter s 0=s := by
  simp only [slitFutureParameter,add_zero,projIcc_val]

lemma slitFutureParameter_coe (s : unitInterval) {r : ℝ}
    (hr : r∈Ioo 0 (1-(s:ℝ))) :
    (slitFutureParameter s r:ℝ)=(s:ℝ)+r := by
  exact congrArg Subtype.val (projIcc_of_mem zero_le_one
    (show (s:ℝ)+r∈Icc (0:ℝ) 1 from ⟨by linarith [s.property.1,hr.1],by linarith [hr.2]⟩))

lemma slitFuturePoint_mem_domain (p : C(unitInterval,ℂ)) (hi : Injective p)
    (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (s : unitInterval) {r : ℝ} (hr : r∈Ioo 0 (1-(s:ℝ))) :
    p (slitFutureParameter s r)∈upperHalfPlane \ range (initialSubarc p s) := by
  have he := slitFutureParameter_coe s hr
  have hlt : s<slitFutureParameter s r := by
    change (s:ℝ)<(slitFutureParameter s r:ℝ)
    rw [he]
    linarith [hr.1]
  refine ⟨hH _ (ne_of_gt (lt_of_le_of_lt bot_le hlt)),?_⟩
  rw [initialSubarc_range]
  rintro ⟨u,hu,heq⟩
  exact (not_le_of_gt hlt) (hi heq ▸ hu.2)

lemma slit_tip_not_mem_domain (p : C(unitInterval,ℂ)) (s : unitInterval) :
    p s∉upperHalfPlane \ range (initialSubarc p s) := by
  intro h
  apply h.2
  exact ⟨1,by simp only [initialSubarc_apply,mul_one]⟩

end SLEExactGauge

end

end OAI
