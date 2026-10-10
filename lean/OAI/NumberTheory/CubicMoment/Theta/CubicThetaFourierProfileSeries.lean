import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowCompletionTranslation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialProfileSeries
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalFourierIntegrability

namespace OAI

/-! Compact Poincare profiles with an actual nonzero horizontal character.
The completion phase is independent of the chosen primitive-row completion. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups CompactlySupported
namespace CubicFirstMoment

def cubicThetaFourierProfileTerm (h : Eisenstein) (r : CubicThetaBottomRow)
    (p : ℂ × ℝ) (W : C_c(ℝ,ℂ)) : ℂ :=
  cubicThetaRadialProfileTerm r p W*
    cubicThetaHorizontalCharacter h (cubicThetaMobius (cubicThetaPrincipalComplex r.completion) p).1

def cubicThetaFourierProfileSeries (h : Eisenstein) (p : ℂ × ℝ) (W : C_c(ℝ,ℂ)) : ℂ :=
  ∑' r : CubicThetaBottomRow,cubicThetaFourierProfileTerm h r p W

lemma cubicThetaFourierProfileTerm_translate (h : Eisenstein) (r : CubicThetaBottomRow)
    (g : cubicThetaPrincipalGroup) {p : ℂ × ℝ} (hp : 0<p.2) (W : C_c(ℝ,ℂ)) :
    cubicThetaFourierProfileTerm h r (cubicThetaMobius (cubicThetaPrincipalComplex g) p) W=
      cubicThetaKubotaValue g*cubicThetaFourierProfileTerm h (r.rightMul g) p W := by
  have hrow : cubicThetaBottomRow (r.completion*g)=cubicThetaBottomRow (r.rightMul g).completion := by
    rw [(r.rightMul g).completion_row]
    rfl
  have hc := cubicThetaHorizontalCharacter_completion h (r.completion*g)
    (r.rightMul g).completion hrow (⟨p,hp⟩:CubicThetaPoint)
  change cubicThetaHorizontalCharacter h
    (cubicThetaMobius (cubicThetaPrincipalComplex (r.completion*g)) p).1=
    cubicThetaHorizontalCharacter h
      (cubicThetaMobius (cubicThetaPrincipalComplex (r.rightMul g).completion) p).1 at hc
  rw [map_mul,←cubicThetaMobius_comp _ _ hp] at hc
  change cubicThetaHorizontalCharacter h
    (cubicThetaMobius (cubicThetaPrincipalComplex r.completion)
      (cubicThetaMobius (cubicThetaPrincipalComplex g) p)).1=
    cubicThetaHorizontalCharacter h
      (cubicThetaMobius (cubicThetaPrincipalComplex (r.rightMul g).completion) p).1 at hc
  unfold cubicThetaFourierProfileTerm
  rw [cubicThetaRadialProfileTerm_translate r g hp W,hc]
  ring

theorem cubicThetaFourierProfileSeries_automorphy (h : Eisenstein)
    (g : cubicThetaPrincipalGroup) {p : ℂ × ℝ} (hp : 0<p.2) (W : C_c(ℝ,ℂ)) :
    cubicThetaFourierProfileSeries h (cubicThetaMobius (cubicThetaPrincipalComplex g) p) W=
      cubicThetaKubotaValue g*cubicThetaFourierProfileSeries h p W := by
  unfold cubicThetaFourierProfileSeries
  simp_rw [cubicThetaFourierProfileTerm_translate h _ g hp W]
  rw [tsum_mul_left]
  congr 1
  exact (CubicThetaBottomRow.rightMulEquiv g).tsum_eq (fun r => cubicThetaFourierProfileTerm h r p W)

lemma cubicThetaFourierProfileTerm_zero (h : Eisenstein) (r : CubicThetaBottomRow)
    (p : ℂ × ℝ) (W : C_c(ℝ,ℂ)) (hz : W (r.height p)=0) :
    cubicThetaFourierProfileTerm h r p W=0 := by
  simp only [cubicThetaFourierProfileTerm,cubicThetaRadialProfileTerm,hz,mul_zero,zero_mul]

theorem cubicThetaFourierProfileSeries_compact_sum (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ),W v=0) {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hpos : ∀ p∈K,0<p.2) :
    ∃ S : Finset CubicThetaBottomRow,∀ p∈K,
      cubicThetaFourierProfileSeries h p W=∑ r∈S,cubicThetaFourierProfileTerm h r p W := by
  obtain ⟨S,hS⟩ := cubicThetaIncomingRows_compact hK hpos
  refine ⟨S,fun p hp => ?_⟩
  apply tsum_eq_sum
  intro r hr
  exact cubicThetaFourierProfileTerm_zero h r p W (hW _ (hS p hp r hr).le)

lemma cubicThetaFourierProfileTerm_continuousAt (h : Eisenstein) (r : CubicThetaBottomRow)
    (W : C_c(ℝ,ℂ)) {p : ℂ × ℝ} (hp : 0<p.2) :
    ContinuousAt (fun q => cubicThetaFourierProfileTerm h r q W) p := by
  have hr := r.height_contDiffAt hp
  have hm := cubicThetaMobius_continuousAt (cubicThetaPrincipalComplex r.completion) hp
  exact (continuousAt_const.mul (W.continuous.continuousAt.comp hr.continuousAt)).mul
    ((cubicThetaHorizontalCharacter_continuous h).continuousAt.comp
      (continuousAt_fst.comp hm))

lemma cubicThetaFourierProfileSeries_continuousOn (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ),W v=0) :
    ContinuousOn (fun p => cubicThetaFourierProfileSeries h p W) {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  obtain ⟨K,hKn,hK,hKpos⟩ := cubicThetaPositive_compact_neighborhood hp
  obtain ⟨S,hS⟩ := cubicThetaFourierProfileSeries_compact_sum h W hW hK hKpos
  have he : (fun q => cubicThetaFourierProfileSeries h q W)=ᶠ[𝓝 p]
      (fun q => ∑ r∈S,cubicThetaFourierProfileTerm h r q W) := by
    filter_upwards [hKn] with q hq
    exact hS q hq
  have hd : ContinuousAt (fun q => ∑ r∈S,cubicThetaFourierProfileTerm h r q W) p := by
    clear hS he
    classical
    induction S using Finset.induction_on with
    | empty => simpa using (continuousAt_const (x:=p) (y:=(0:ℂ)))
    | @insert r S hr ih =>
      simp only [Finset.sum_insert hr]
      exact (cubicThetaFourierProfileTerm_continuousAt h r W hp).add ih
  exact (hd.congr_of_eventuallyEq he).continuousWithinAt

end CubicFirstMoment

end

end OAI
