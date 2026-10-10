import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHeightBandCore
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaIncomingSmooth
import Mathlib.Topology.ContinuousMap.CompactlySupported
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspStripReduction

namespace OAI

/-! Compact radial profiles give actual automorphic sections by a locally finite
Poincaré sum. No spectral input is used. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups CompactlySupported
namespace CubicFirstMoment


def cubicThetaRadialProfileTerm (r : CubicThetaBottomRow) (p : ℂ × ℝ) (W : C_c(ℝ,ℂ)) : ℂ :=
  star r.phase*W (r.height p)

def cubicThetaRadialProfileSeries (p : ℂ × ℝ) (W : C_c(ℝ,ℂ)) : ℂ :=
  ∑' r : CubicThetaBottomRow, cubicThetaRadialProfileTerm r p W

lemma cubicThetaRadialProfileTerm_translate (r : CubicThetaBottomRow)
    (g : cubicThetaPrincipalGroup) {p : ℂ × ℝ} (hp : 0<p.2) (W : C_c(ℝ,ℂ)) :
    cubicThetaRadialProfileTerm r (cubicThetaMobius (cubicThetaPrincipalComplex g) p) W=
      cubicThetaKubotaValue g*cubicThetaRadialProfileTerm (r.rightMul g) p W := by
  have hu : cubicThetaKubotaValue g*star (cubicThetaKubotaValue g)=1 := by
    calc
      _ = (‖cubicThetaKubotaValue g‖:ℂ)^2 := Complex.mul_conj' _
      _ = 1 := by rw [cubicThetaKubotaValue_norm]; norm_num
  rw [cubicThetaRadialProfileTerm,cubicThetaRadialProfileTerm,
    CubicThetaBottomRow.height_rightMul r g hp,CubicThetaBottomRow.phase_rightMul,star_mul]
  calc
    _ = (cubicThetaKubotaValue g*star (cubicThetaKubotaValue g))*
        (star r.phase*W
          (r.height (cubicThetaMobius (cubicThetaPrincipalComplex g) p))) := by rw [hu,one_mul]
    _ = _ := by ring

theorem cubicThetaRadialProfileSeries_automorphy (g : cubicThetaPrincipalGroup)
    {p : ℂ × ℝ} (hp : 0<p.2) (W : C_c(ℝ,ℂ)) :
    cubicThetaRadialProfileSeries (cubicThetaMobius (cubicThetaPrincipalComplex g) p) W=
      cubicThetaKubotaValue g*cubicThetaRadialProfileSeries p W := by
  unfold cubicThetaRadialProfileSeries
  simp_rw [cubicThetaRadialProfileTerm_translate _ g hp W]
  rw [tsum_mul_left]
  congr 1
  exact (CubicThetaBottomRow.rightMulEquiv g).tsum_eq (fun r => cubicThetaRadialProfileTerm r p W)

theorem cubicThetaRadialProfileSeries_compact_sum (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ), W v=0) {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hpos : ∀ p∈K, 0<p.2) :
    ∃ S : Finset CubicThetaBottomRow, ∀ p∈K,
      cubicThetaRadialProfileSeries p W=∑ r∈S, cubicThetaRadialProfileTerm r p W := by
  obtain ⟨S,hS⟩ := cubicThetaIncomingRows_compact hK hpos
  refine ⟨S,fun p hp => ?_⟩
  apply tsum_eq_sum
  intro r hr
  exact mul_eq_zero_of_right _ (hW _ (hS p hp r hr).le)

lemma cubicThetaRadialProfileSeries_continuousOn (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ), W v=0) :
    ContinuousOn (fun p => cubicThetaRadialProfileSeries p W) {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  obtain ⟨K,hKn,hK,hKpos⟩ := cubicThetaPositive_compact_neighborhood hp
  obtain ⟨S,hS⟩ := cubicThetaRadialProfileSeries_compact_sum W hW hK hKpos
  have he : (fun q => cubicThetaRadialProfileSeries q W) =ᶠ[𝓝 p]
      (fun q => ∑ r∈S, cubicThetaRadialProfileTerm r q W) := by
    filter_upwards [hKn] with q hq
    exact hS q hq
  have hd : ContinuousAt (fun q => ∑ r∈S, cubicThetaRadialProfileTerm r q W) p := by
    clear hS he
    classical
    induction S using Finset.induction_on with
    | empty => simpa using (continuousAt_const (x:=p) (y:=(0:ℂ)))
    | @insert r S hr ih =>
      simp only [Finset.sum_insert hr]
      exact (continuousAt_const.mul (W.continuous.continuousAt.comp
        (r.height_contDiffAt hp).continuousAt)).add ih
  exact (hd.congr_of_eventuallyEq he).continuousWithinAt

theorem cubicThetaRadialProfileSeries_core (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ), W v=0) :
    ∃ (H : ℝ) (S : Finset SL(2,Eisenstein)),
      ∀ p : CubicThetaPoint, cubicThetaQuotientMap p∉cubicThetaQuotientCore S H →
        cubicThetaRadialProfileSeries p.val W=0 := by
  obtain ⟨B,hB⟩ := W.hasCompactSupport.isCompact.bddAbove_image continuous_id.continuousOn
  let H := max 1 B
  obtain ⟨S,hS⟩ := cubicThetaHeightBand_core (le_max_left 1 B)
  refine ⟨H,S,fun p hp => ?_⟩
  suffices hz : ∀ r, cubicThetaRadialProfileTerm r p.val W=0 by
    simp only [cubicThetaRadialProfileSeries,hz,tsum_zero]
  intro r
  by_cases hlo : r.height p.val≤1
  · exact mul_eq_zero_of_right _ (hW _ hlo)
  by_cases hz : W (r.height p.val)=0
  · exact mul_eq_zero_of_right _ hz
  have hhi : r.height p.val≤H :=
    (hB (mem_image_of_mem id (subset_closure hz))).trans (le_max_right 1 B)
  have he : cubicThetaPointHeight (r.completion • p)=r.height p.val := by
    change (cubicThetaBottomRow r.completion).height p.val=_
    rw [r.completion_row]
  have hq := hS 1 (r.completion • p) (by rw [he]; linarith) (by rw [he]; exact hhi)
  rw [one_smul,cubicThetaQuotient_covering.map_smul] at hq
  exact False.elim (hp hq)

def cubicThetaRadialProfileSection (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ), W v=0) : CubicThetaSection :=
  ⟨⟨fun p => cubicThetaRadialProfileSeries p.val W,by
      apply continuous_iff_continuousAt.mpr
      intro p
      have h := (cubicThetaRadialProfileSeries_continuousOn W hW).continuousAt
        ((isOpen_lt continuous_const continuous_snd).mem_nhds p.property)
      exact h.comp continuous_subtype_val.continuousAt⟩,by
    intro g p
    exact cubicThetaRadialProfileSeries_automorphy g p.property W⟩

lemma cubicThetaRadialProfileSection_compact (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ), W v=0) :
    HasCompactSupport (cubicThetaSectionNorm (cubicThetaRadialProfileSection W hW)) := by
  obtain ⟨H,S,hS⟩ := cubicThetaRadialProfileSeries_core W hW
  apply HasCompactSupport.of_support_subset_isCompact (cubicThetaQuotientCore_compact S H)
  intro q hq
  by_contra h
  have hz := hS (cubicThetaQuotientLift q) (by rwa [cubicThetaQuotientLift_map])
  apply hq
  change ‖cubicThetaRadialProfileSeries (cubicThetaQuotientLift q).val W‖=0
  rw [hz,norm_zero]

lemma cubicThetaRadialProfileSeries_high (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ), W v=0) {p : ℂ × ℝ} (hp : 1<p.2) :
    cubicThetaRadialProfileSeries p W=W p.2 := by
  have he : cubicThetaRadialProfileSeries p W=cubicThetaRadialProfileTerm cubicThetaZeroRow p W := by
    apply tsum_eq_single
    intro r hr
    by_contra hn
    have hh : 1<r.height p := by
      by_contra ht
      exact hn (mul_eq_zero_of_right _ (hW _ (le_of_not_gt ht)))
    have hc := r.high_height_c_zero hp hh
    exact hr ((CubicThetaBottomRow.c_zero_iff r).mp hc)
  rw [he]
  simp [cubicThetaRadialProfileTerm,CubicThetaBottomRow.height,CubicThetaBottomRow.phase,
    cubicThetaZeroRow,norm,cubicSymbol_one_lower]

end CubicFirstMoment

end

end OAI
