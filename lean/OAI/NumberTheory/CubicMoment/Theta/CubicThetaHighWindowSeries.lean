import OAI.NumberTheory.CubicMoment.Theta.CubicThetaWindowProfile
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspStripReduction

namespace OAI

/-! The high defect is an actual compact automorphic section supported
in the single principal cusp above height two. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaHighWindowTerm (r : CubicThetaBottomRow) (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  star r.phase*cubicThetaHighWindowForcing s (r.height p)

def cubicThetaHighWindowSeries (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  ∑' r : CubicThetaBottomRow, cubicThetaHighWindowTerm r p s

lemma cubicThetaHighWindowTerm_translate (r : CubicThetaBottomRow)
    (g : cubicThetaPrincipalGroup) {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    cubicThetaHighWindowTerm r (cubicThetaMobius (cubicThetaPrincipalComplex g) p) s=
      cubicThetaKubotaValue g*cubicThetaHighWindowTerm (r.rightMul g) p s := by
  have hu : cubicThetaKubotaValue g*star (cubicThetaKubotaValue g)=1 := by
    calc
      _ = (‖cubicThetaKubotaValue g‖:ℂ)^2 := Complex.mul_conj' _
      _ = 1 := by rw [cubicThetaKubotaValue_norm]; norm_num
  rw [cubicThetaHighWindowTerm,cubicThetaHighWindowTerm,
    CubicThetaBottomRow.height_rightMul r g hp,CubicThetaBottomRow.phase_rightMul,star_mul]
  calc
    _ = (cubicThetaKubotaValue g*star (cubicThetaKubotaValue g))*
        (star r.phase*cubicThetaHighWindowForcing s
          (r.height (cubicThetaMobius (cubicThetaPrincipalComplex g) p))) := by rw [hu,one_mul]
    _ = _ := by ring

theorem cubicThetaHighWindowSeries_automorphy (g : cubicThetaPrincipalGroup)
    {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    cubicThetaHighWindowSeries (cubicThetaMobius (cubicThetaPrincipalComplex g) p) s=
      cubicThetaKubotaValue g*cubicThetaHighWindowSeries p s := by
  unfold cubicThetaHighWindowSeries
  simp_rw [cubicThetaHighWindowTerm_translate _ g hp s]
  rw [tsum_mul_left]
  congr 1
  exact (CubicThetaBottomRow.rightMulEquiv g).tsum_eq (fun r => cubicThetaHighWindowTerm r p s)

theorem cubicThetaHighWindowSeries_compact_sum {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hpos : ∀ p∈K, 0<p.2) :
    ∃ S : Finset CubicThetaBottomRow, ∀ p∈K, ∀ s : ℂ,
      cubicThetaHighWindowSeries p s=∑ r∈S, cubicThetaHighWindowTerm r p s := by
  obtain ⟨S,hS⟩ := cubicThetaIncomingRows_compact hK hpos
  refine ⟨S,fun p hp s => ?_⟩
  apply tsum_eq_sum
  intro r hr
  unfold cubicThetaHighWindowTerm
  rw [cubicThetaHighWindowForcing_low s (by linarith [hS p hp r hr]),mul_zero]

lemma cubicThetaHighWindowSeries_continuousOn (s : ℂ) :
    ContinuousOn (fun p => cubicThetaHighWindowSeries p s) {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  obtain ⟨K,hKn,hK,hKpos⟩ := cubicThetaPositive_compact_neighborhood hp
  obtain ⟨S,hS⟩ := cubicThetaHighWindowSeries_compact_sum hK hKpos
  have he : (fun q => cubicThetaHighWindowSeries q s) =ᶠ[𝓝 p]
      (fun q => ∑ r∈S, cubicThetaHighWindowTerm r q s) := by
    filter_upwards [hKn] with q hq
    exact hS q hq s
  have hd : ContinuousAt (fun q => ∑ r∈S, cubicThetaHighWindowTerm r q s) p := by
    clear hS he
    classical
    induction S using Finset.induction_on with
    | empty => simpa using (continuousAt_const (x:=p) (y:=(0:ℂ)))
    | @insert r S hr ih =>
      simp only [Finset.sum_insert hr]
      exact (continuousAt_const.mul ((cubicThetaHighWindowForcing_continuous s).continuousAt.comp
        (r.height_contDiffAt hp).continuousAt)).add ih
  exact (hd.congr_of_eventuallyEq he).continuousWithinAt

theorem cubicThetaHighWindowSeries_core :
    ∃ S : Finset SL(2,Eisenstein), ∀ (s : ℂ) (p : CubicThetaPoint),
      cubicThetaQuotientMap p∉cubicThetaQuotientCore S 4 →
        cubicThetaHighWindowSeries p.val s=0 := by
  obtain ⟨S,hS⟩ := cubicThetaCuspWindow_core
  refine ⟨S,fun s p hp => ?_⟩
  suffices hz : ∀ r, cubicThetaHighWindowTerm r p.val s=0 by
    simp only [cubicThetaHighWindowSeries,hz,tsum_zero]
  intro r
  by_cases hlo : r.height p.val≤2
  · exact mul_eq_zero_of_right _ (cubicThetaHighWindowForcing_low s hlo)
  by_cases hhi : 4≤r.height p.val
  · exact mul_eq_zero_of_right _ (cubicThetaHighWindowForcing_high s hhi)
  have he : cubicThetaPointHeight (r.completion • p)=r.height p.val := by
    change (cubicThetaBottomRow r.completion).height p.val=_
    rw [r.completion_row]
  have hq := hS 1 (r.completion • p) (by rw [he]; linarith) (by rw [he]; linarith)
  rw [one_smul,cubicThetaQuotient_covering.map_smul] at hq
  exact False.elim (hp hq)

def cubicThetaHighWindowSection (s : ℂ) : CubicThetaSection :=
  ⟨⟨fun p => cubicThetaHighWindowSeries p.val s,by
      apply continuous_iff_continuousAt.mpr
      intro p
      have h := (cubicThetaHighWindowSeries_continuousOn s).continuousAt
        ((isOpen_lt continuous_const continuous_snd).mem_nhds p.property)
      exact h.comp continuous_subtype_val.continuousAt⟩,by
    intro g p
    exact cubicThetaHighWindowSeries_automorphy g p.property s⟩

lemma cubicThetaHighWindowSection_compact (s : ℂ) :
    HasCompactSupport (cubicThetaSectionNorm (cubicThetaHighWindowSection s)) := by
  obtain ⟨S,hS⟩ := cubicThetaHighWindowSeries_core
  apply HasCompactSupport.of_support_subset_isCompact (cubicThetaQuotientCore_compact S 4)
  intro q hq
  by_contra h
  have hz := hS s (cubicThetaQuotientLift q) (by rwa [cubicThetaQuotientLift_map])
  apply hq
  change ‖cubicThetaHighWindowSeries (cubicThetaQuotientLift q).val s‖=0
  rw [hz,norm_zero]

lemma cubicThetaHighWindowSeries_high {p : ℂ × ℝ} (hp : 1<p.2) (s : ℂ) :
    cubicThetaHighWindowSeries p s=cubicThetaHighWindowForcing s p.2 := by
  have he : cubicThetaHighWindowSeries p s=cubicThetaHighWindowTerm cubicThetaZeroRow p s := by
    apply tsum_eq_single
    intro r hr
    by_contra hn
    have hh : 1<r.height p := by
      by_contra ht
      exact hn (mul_eq_zero_of_right _ (cubicThetaHighWindowForcing_low s (by linarith)))
    have hc := r.high_height_c_zero hp hh
    exact hr ((CubicThetaBottomRow.c_zero_iff r).mp hc)
  rw [he]
  simp [cubicThetaHighWindowTerm,CubicThetaBottomRow.height,CubicThetaBottomRow.phase,
    cubicThetaZeroRow,norm,cubicSymbol_one_lower]

end CubicFirstMoment

end

end OAI
