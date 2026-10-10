import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspWindowCore
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaIncomingSmooth
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSmoothTests

namespace OAI

/-! The difference of incoming cutoffs at heights one and two is a
literal compact smooth automorphic section. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff MatrixGroups
namespace CubicFirstMoment

def cubicThetaIncomingWindowCutoff (v : ℝ) : ℂ :=
  cubicThetaCuspCutoff v-cubicThetaCuspCutoff (v/2)

lemma cubicThetaIncomingWindowCutoff_smooth :
    ContDiff ℝ ∞ cubicThetaIncomingWindowCutoff :=
  cubicThetaCuspCutoff_smooth.sub
    (cubicThetaCuspCutoff_smooth.comp (contDiff_id.div_const 2))

lemma cubicThetaIncomingWindowCutoff_low {v : ℝ} (hv : v≤1) :
    cubicThetaIncomingWindowCutoff v=0 := by
  rw [cubicThetaIncomingWindowCutoff,cubicThetaCuspCutoff_zero hv,
    cubicThetaCuspCutoff_zero (by linarith : v/2≤1),sub_self]

lemma cubicThetaIncomingWindowCutoff_high {v : ℝ} (hv : 4≤v) :
    cubicThetaIncomingWindowCutoff v=0 := by
  rw [cubicThetaIncomingWindowCutoff,cubicThetaCuspCutoff_one (by linarith : 2≤v),
    cubicThetaCuspCutoff_one (by linarith : 2≤v/2),sub_self]

def cubicThetaIncomingWindowTerm (r : CubicThetaBottomRow) (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  cubicThetaIncomingWindowCutoff (r.height p)*cubicThetaEisensteinTerm r p s

def cubicThetaIncomingWindow (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  ∑' r : CubicThetaBottomRow, cubicThetaIncomingWindowTerm r p s

lemma cubicThetaIncomingWindowTerm_translate (r : CubicThetaBottomRow)
    (g : cubicThetaPrincipalGroup) {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    cubicThetaIncomingWindowTerm r (cubicThetaMobius (cubicThetaPrincipalComplex g) p) s=
      cubicThetaKubotaValue g*cubicThetaIncomingWindowTerm (r.rightMul g) p s := by
  rw [cubicThetaIncomingWindowTerm,cubicThetaIncomingWindowTerm,
    ← CubicThetaBottomRow.height_rightMul r g hp,cubicThetaEisensteinTerm_translate r g hp s]
  ring

theorem cubicThetaIncomingWindow_automorphy (g : cubicThetaPrincipalGroup)
    {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    cubicThetaIncomingWindow (cubicThetaMobius (cubicThetaPrincipalComplex g) p) s=
      cubicThetaKubotaValue g*cubicThetaIncomingWindow p s := by
  unfold cubicThetaIncomingWindow
  simp_rw [cubicThetaIncomingWindowTerm_translate _ g hp s]
  rw [tsum_mul_left]
  congr 1
  exact (CubicThetaBottomRow.rightMulEquiv g).tsum_eq
    (fun r => cubicThetaIncomingWindowTerm r p s)

theorem cubicThetaIncomingWindow_compact_sum {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hpos : ∀ p∈K, 0<p.2) :
    ∃ S : Finset CubicThetaBottomRow, ∀ p∈K, ∀ s : ℂ,
      cubicThetaIncomingWindow p s=∑ r∈S, cubicThetaIncomingWindowTerm r p s := by
  obtain ⟨S,hS⟩ := cubicThetaIncomingRows_compact hK hpos
  refine ⟨S,fun p hp s => ?_⟩
  apply tsum_eq_sum
  intro r hr
  unfold cubicThetaIncomingWindowTerm
  rw [cubicThetaIncomingWindowCutoff_low (hS p hp r hr).le,zero_mul]

lemma cubicThetaIncomingWindowTerm_contDiffAt (r : CubicThetaBottomRow) (s : ℂ)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContDiffAt ℝ ∞ (fun q => cubicThetaIncomingWindowTerm r q s) p := by
  have hh := r.height_contDiffAt hp
  have hc := cubicThetaIncomingWindowCutoff_smooth.contDiffAt.comp p hh
  have hpow := (cubicThetaHeightPower_analytic s (r.height_pos hp)).contDiffAt.comp p hh
  exact hc.mul (contDiffAt_const.mul hpow)

theorem cubicThetaIncomingWindow_contDiffOn (s : ℂ) :
    ContDiffOn ℝ ∞ (fun p => cubicThetaIncomingWindow p s) {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  obtain ⟨K,hKn,hK,hKpos⟩ := cubicThetaPositive_compact_neighborhood hp
  obtain ⟨S,hS⟩ := cubicThetaIncomingWindow_compact_sum hK hKpos
  have he : (fun q => cubicThetaIncomingWindow q s) =ᶠ[𝓝 p]
      (fun q => ∑ r∈S, cubicThetaIncomingWindowTerm r q s) := by
    filter_upwards [hKn] with q hq
    exact hS q hq s
  have hd : ContDiffAt ℝ ∞ (fun q => ∑ r∈S, cubicThetaIncomingWindowTerm r q s) p :=
    ContDiffAt.sum (fun r _ => cubicThetaIncomingWindowTerm_contDiffAt r s hp)
  exact (hd.congr_of_eventuallyEq he).contDiffWithinAt

theorem cubicThetaIncomingWindow_core :
    ∃ S : Finset SL(2,Eisenstein), ∀ (s : ℂ) (p : CubicThetaPoint),
      cubicThetaQuotientMap p∉cubicThetaQuotientCore S 4 →
        cubicThetaIncomingWindow p.val s=0 := by
  obtain ⟨S,hS⟩ := cubicThetaCuspWindow_core
  refine ⟨S,fun s p hp => ?_⟩
  suffices hz : ∀ r, cubicThetaIncomingWindowTerm r p.val s=0 by
    simp only [cubicThetaIncomingWindow,hz,tsum_zero]
  intro r
  by_cases hlo : r.height p.val≤1
  · exact mul_eq_zero_of_left (cubicThetaIncomingWindowCutoff_low hlo) _
  by_cases hhi : 4≤r.height p.val
  · exact mul_eq_zero_of_left (cubicThetaIncomingWindowCutoff_high hhi) _
  have he : cubicThetaPointHeight (r.completion • p)=r.height p.val := by
    change (cubicThetaBottomRow r.completion).height p.val=_
    rw [r.completion_row]
  have hq := hS 1 (r.completion • p) (by rw [he]; linarith) (by rw [he]; linarith)
  rw [one_smul,cubicThetaQuotient_covering.map_smul] at hq
  exact False.elim (hp hq)

def cubicThetaIncomingWindowSection (s : ℂ) : CubicThetaSection :=
  ⟨⟨fun p => cubicThetaIncomingWindow p.val s,by
      apply continuous_iff_continuousAt.mpr
      intro p
      have h := (cubicThetaIncomingWindow_contDiffOn s).contDiffAt
        ((isOpen_lt continuous_const continuous_snd).mem_nhds p.property)
      exact h.continuousAt.comp continuous_subtype_val.continuousAt⟩,by
    intro g p
    exact cubicThetaIncomingWindow_automorphy g p.property s⟩

lemma cubicThetaIncomingWindowSection_compact (s : ℂ) :
    HasCompactSupport (cubicThetaSectionNorm (cubicThetaIncomingWindowSection s)) := by
  obtain ⟨S,hS⟩ := cubicThetaIncomingWindow_core
  apply HasCompactSupport.of_support_subset_isCompact (cubicThetaQuotientCore_compact S 4)
  intro q hq
  by_contra h
  have hz := hS s (cubicThetaQuotientLift q) (by rwa [cubicThetaQuotientLift_map])
  apply hq
  change ‖cubicThetaIncomingWindow (cubicThetaQuotientLift q).val s‖=0
  rw [hz,norm_zero]

def cubicThetaIncomingWindowTest (s : ℂ) : cubicThetaSmoothTests :=
  ⟨cubicThetaIncomingWindowSection s,by
    refine ⟨?_,cubicThetaIncomingWindowSection_compact s⟩
    apply (cubicThetaIncomingWindow_contDiffOn s).congr
    intro y hy
    change cubicThetaIncomingWindow (cubicThetaPointInclusion.symm y).val s=
      cubicThetaIncomingWindow y s
    have he := cubicThetaPointInclusion.right_inv (show y∈cubicThetaPointInclusion.target by
      rwa [cubicThetaPointInclusion_target])
    change (cubicThetaPointInclusion.symm y).val=y at he
    exact congrArg (fun p => cubicThetaIncomingWindow p s) he⟩

end CubicFirstMoment

end

end OAI
