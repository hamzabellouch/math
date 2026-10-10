import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKloostermanPeriodization
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalUnfold

namespace OAI

/-! Exact integration of the periodized row: its finite Kloosterman sum
multiplies one common archimedean inversion integral. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported ContDiff SchwartzMap
namespace CubicFirstMoment

lemma cubicThetaGramKernel_period_integrable (h k : Eisenstein) (V : C_c(ℝ,ℂ))
    (hsm : ContDiff ℝ ∞ (V : ℝ → ℂ)) {c : ℂ} (hc : c≠0) {δ v : ℝ}
    (hδ : 0<δ) (hv : 0<v) (hV : ∀ t≤δ,V t=0) (a : ℂ) :
    IntegrableOn (fun z => ∑' m : Eisenstein,
      cubicThetaGramInversionKernel h k V c (z+a+3*(m:ℂ)) v)
      cubicThetaHorizontalCell := by
  let F := cubicThetaGramKernelSchwartz h k V hsm hc hδ hv hV
  have hs (z : ℂ) : Summable (fun m : Eisenstein => F (z+a+3*(m:ℂ))) :=
    schwartz_summable_eisenstein_coset F 3 (by norm_num) (z+a)
  have hf : Integrable (fun z => F (z+a)) :=
    (measurePreserving_add_right volume a).integrable_comp_of_integrable F.integrable
  have he : (fun z => ∑' m : Eisenstein,F (z+a+3*(m:ℂ)))=
      (fun z => ∑' g : CubicThetaPeriodGroup,F (g • z+a)) := by
    funext z
    change (∑' m : Eisenstein,F (z+a+3*(m:ℂ)))=
      ∑' m : Eisenstein,F ((z+3*(m:ℂ))+a)
    congr 1
    funext m
    congr 1
    ring
  change IntegrableOn (fun z => ∑' m : Eisenstein,F (z+a+3*(m:ℂ))) _
  rw [he]
  apply cubicThetaHorizontal_periodized_integrable (F.continuous.comp (continuous_id.add continuous_const)) hf
  intro z
  change Summable (fun m : Eisenstein => F ((z+3*(m:ℂ))+a))
  simpa only [add_assoc,add_comm,add_left_comm] using hs z

lemma cubicThetaGramKernel_period_integral (h k : Eisenstein) (V : C_c(ℝ,ℂ))
    (hsm : ContDiff ℝ ∞ (V : ℝ → ℂ)) {c : ℂ} (hc : c≠0) {δ v : ℝ}
    (hδ : 0<δ) (hv : 0<v) (hV : ∀ t≤δ,V t=0) (a : ℂ) :
    (∫ z in cubicThetaHorizontalCell,∑' m : Eisenstein,
      cubicThetaGramInversionKernel h k V c (z+a+3*(m:ℂ)) v)=
      ∫ z,cubicThetaGramInversionKernel h k V c z v := by
  let F := cubicThetaGramKernelSchwartz h k V hsm hc hδ hv hV
  have hf : Integrable (fun z => F (z+a)) :=
    (measurePreserving_add_right volume a).integrable_comp_of_integrable F.integrable
  calc
    _ = ∫ z in cubicThetaHorizontalCell,∑' g : CubicThetaPeriodGroup,F (g • z+a) := by
      apply setIntegral_congr_fun cubicThetaHorizontalCell_measurable
      intro z _
      change (∑' m : Eisenstein,F (z+a+3*(m:ℂ)))=
        ∑' m : Eisenstein,F ((z+3*(m:ℂ))+a)
      congr 1
      funext m
      congr 1
      ring
    _ = ∫ z,F (z+a) := cubicThetaHorizontal_integral_tsum hf
    _ = ∫ z,F z := integral_add_right_eq_self F a
    _ = _ := rfl

lemma cubicThetaKloostermanRow_integrable (h k : Eisenstein) {c : Eisenstein}
    (hc : (3:Eisenstein)∣c) (hc0 : c≠0) (V : C_c(ℝ,ℂ))
    (hsm : ContDiff ℝ ∞ (V : ℝ → ℂ)) {δ v : ℝ} (hδ : 0<δ) (hv : 0<v)
    (hV : ∀ t≤δ,V t=0) :
    IntegrableOn (cubicThetaKloostermanRow h k c hc V v) cubicThetaHorizontalCell := by
  classical
  let : Finite (Residues (3*c)) := finite_residues (mul_ne_zero (by norm_num) hc0)
  let : Fintype (Residues (3*c)) := Fintype.ofFinite _
  have hcC : (c:ℂ)≠0 := fun hz => hc0 (Subtype.ext hz)
  change IntegrableOn (fun z => cubicThetaKloostermanRow h k c hc V v z) _
  simp_rw [cubicThetaKloostermanRow_periodized h k hc hc0 V hsm hδ hv hV,tsum_fintype]
  exact integrable_finsetSum _ (fun x _ =>
    (cubicThetaGramKernel_period_integrable h k V hsm hcC hδ hv hV _).const_mul _)

theorem cubicThetaKloostermanRow_integral (h k : Eisenstein) {c : Eisenstein}
    (hc : (3:Eisenstein)∣c) (hc0 : c≠0) (V : C_c(ℝ,ℂ))
    (hsm : ContDiff ℝ ∞ (V : ℝ → ℂ)) {δ v : ℝ} (hδ : 0<δ) (hv : 0<v)
    (hV : ∀ t≤δ,V t=0) :
    (∫ z in cubicThetaHorizontalCell,cubicThetaKloostermanRow h k c hc V v z)=
      cubicThetaKloostermanSum h k c hc*
        ∫ z,cubicThetaGramInversionKernel h k V (c:ℂ) z v := by
  classical
  let : Finite (Residues (3*c)) := finite_residues (mul_ne_zero (by norm_num) hc0)
  let : Fintype (Residues (3*c)) := Fintype.ofFinite _
  have hcC : (c:ℂ)≠0 := fun hz => hc0 (Subtype.ext hz)
  simp_rw [cubicThetaKloostermanRow_periodized h k hc hc0 V hsm hδ hv hV,tsum_fintype]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul,cubicThetaGramKernel_period_integral h k V hsm hcC hδ hv hV]
    rw [←Finset.sum_mul]
    simp only [cubicThetaKloostermanSum,tsum_fintype]
  · intro x _
    exact (cubicThetaGramKernel_period_integrable h k V hsm hcC hδ hv hV _).const_mul _

end CubicFirstMoment

end

end OAI
