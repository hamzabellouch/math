import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierStepBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierStepGeometryBarrier

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierStepBounds_barrier_scope
open Set Filter MeasureTheory Metric
open scoped Topology
open CoulombAtom CoulombAnalysis
variable {Z B C R M lam1 lam2 : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
  (hR : 0 < R) (hM : 2 < M) (hshifts : lam2 ≤ lam1)
  (hshift : C/M^4 < lam2) (hsmall : lam1 < barrierGap B)

include hB hC hR hM hshifts hshift hsmall in
lemma outwardOffset_deterministicLip {Ω : Type*} (good : Ω → Prop) [DecidablePred good]
    {a h : Ω → TFSpace → ℝ} (ha : DeterministicLocalLipschitz a)
    (hh : DeterministicLocalLipschitz h)
    (hlo : ∀ sample x, R/2 ≤ ‖x‖ → outerBarrier B (R/2) x ≤ nuclearField Z x+a sample x)
    (hhi : ∀ sample x, R/2 ≤ ‖x‖ → nuclearField Z x+a sample x ≤ C/‖x‖^4)
    (hhcap : ∀ sample, good sample → ∀ x, M*R < ‖x‖ → ‖x‖ < 2*M*R → nuclearField Z x+h sample x ≤ C/‖x‖^4) :
    DeterministicLocalLipschitz (fun sample => outwardOffset (good sample) (a sample) (h sample) Z B R M lam1 lam2) := by
  apply cutMaximum_deterministicLip (t := (27/25)*R) (L := M*R)
    (by linarith) (by nlinarith) (by nlinarith)
  · intro sample x hx hx'
    exact outward_lower_overlap (good sample) hB hR hsmall (hlo sample) (by linarith) hx'
  · exact fun sample x hx hx' => outward_upper_overlap (good sample) hB hC hR hM hshifts hshift
      (hhi sample) (hhcap sample) hx hx'
  · exact shiftedCandidates_deterministicLip good ha hh R lam1 lam2
  · exact deterministicLip_spatial (outerOffset_locallyLipschitz Z B hR)

include hB hR hsmall in
lemma outwardOffset_lower (good : Prop) [Decidable good] {a h : TFSpace → ℝ}
    (hlo : ∀ x, R/2 ≤ ‖x‖ → outerBarrier B (R/2) x ≤ nuclearField Z x+a x)
    {x : TFSpace} (hx : R ≤ ‖x‖) :
    outerBarrier B R x ≤ nuclearField Z x+outwardOffset good a h Z B R M lam1 lam2 x := by
  rw [←nuclear_outerOffset_eq (Z := Z) hx]
  apply add_le_add_right
  unfold outwardOffset cutMaximum
  split_ifs with h1 h2
  · exact outward_lower_overlap good hB hR hsmall hlo hx (by linarith)
  · exact le_max_right _ _
  · exact le_refl _

include hB hR hM hshifts in
lemma outwardOffset_cap (good : Prop) [Decidable good] {a h : TFSpace → ℝ}
    (hBC : B ≤ C) (hl2 : 0 ≤ lam2)
    (hhi : ∀ x, R/2 ≤ ‖x‖ → nuclearField Z x+a x ≤ C/‖x‖^4)
    (hhcap : good → ∀ x, R/2 ≤ ‖x‖ → ‖x‖ < 2*M*R → nuclearField Z x+h x ≤ C/‖x‖^4)
    {x : TFSpace} (hx : R ≤ ‖x‖) :
    nuclearField Z x+outwardOffset good a h Z B R M lam1 lam2 x ≤ C/‖x‖^4 := by
  have hb : nuclearField Z x+outerOffset Z B R x ≤ C/‖x‖^4 := by
    rw [nuclear_outerOffset_eq hx]
    exact (outerBarrier_bounds hB hR hx).2.trans
      (div_le_div_of_nonneg_right hBC (pow_nonneg (norm_nonneg _) 4))
  have hv (hx' : ‖x‖ < 2*M*R) :
      nuclearField Z x+shiftedCandidates good a h R lam1 lam2 x ≤ C/‖x‖^4 := by
    have h1 := hhi x (by linarith)
    have hl1 : 0 ≤ lam1/R^4 := div_nonneg (hl2.trans hshifts) (pow_nonneg hR.le _)
    have hl2' : 0 ≤ lam2/R^4 := div_nonneg hl2 (pow_nonneg hR.le _)
    unfold shiftedCandidates
    split_ifs with hg
    · rw [add_max]
      apply max_le
      · linarith
      · have ht := hhcap hg x (by linarith) hx'; linarith
    · linarith
  unfold outwardOffset cutMaximum
  split_ifs with h1 h2
  · exact hv (by nlinarith)
  · rw [add_max]; exact max_le (hv h2) hb
  · exact hb

include hB hC hR hM hshifts hshift in
lemma outwardOffset_tail (good : Prop) [Decidable good] {a h : TFSpace → ℝ}
    (hhi : ∀ x, R/2 ≤ ‖x‖ → nuclearField Z x+a x ≤ C/‖x‖^4)
    (hhcap : good → ∀ x, M*R < ‖x‖ → ‖x‖ < 2*M*R → nuclearField Z x+h x ≤ C/‖x‖^4)
    {x : TFSpace} (hx : M*R < ‖x‖) :
    nuclearField Z x+outwardOffset good a h Z B R M lam1 lam2 x = outerBarrier B R x := by
  have he := cutMaximum_outer (r := (26/25)*R) (t := (27/25)*R)
    (R := 2*M*R) (L := M*R) (by linarith) (by nlinarith)
    (fun y hy hy' => outward_upper_overlap good hB hC hR hM hshifts hshift hhi hhcap hy hy') hx
  unfold outwardOffset
  rw [he,nuclear_outerOffset_eq (by nlinarith : R ≤ ‖x‖)]

end Work_BarrierStepBounds_barrier_scope

open Set Filter MeasureTheory Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

lemma innerSource_locallyIntegrable {μ p : TFSpace → ℝ}
    (hμ : LocallyIntegrable μ) (hp : LocallyIntegrable p) (R : ℝ) :
    LocallyIntegrable (innerSource R μ p) := by
  have hi := hμ.indicator (s := {x : TFSpace | ‖x‖ < R})
    (isOpen_lt continuous_norm continuous_const).measurableSet
  exact (hi.sub hp).smul (4*Real.pi)

lemma addedError_locallyIntegrable (good : Prop) [Decidable good]
    {μ p : TFSpace → ℝ} (hμ : LocallyIntegrable μ) (hp : LocallyIntegrable p) (R : ℝ) :
    LocallyIntegrable (addedError good R μ p) := by
  unfold addedError
  split_ifs with hg
  · simpa only [add_zero] using hp
  · have hi := hμ.indicator (s := {x : TFSpace | R/2 ≤ ‖x‖} ∩ {x : TFSpace | ‖x‖ < R})
      ((isClosed_le continuous_const continuous_norm).measurableSet.inter
      (isOpen_lt continuous_norm continuous_const).measurableSet)
    have he : (({x : TFSpace | R/2 ≤ ‖x‖} ∩ {x : TFSpace | ‖x‖ < R}).indicator μ) =
        (fun x => if R/2 ≤ ‖x‖ ∧ ‖x‖ < R then μ x else 0) := by
      funext x
      simp only [indicator_apply, mem_inter_iff, mem_ofPred_eq]
    rw [he] at hi
    exact hp.add hi

lemma old_branch_height {Z B C R hl hh : ℝ} (hB : 0 < B) (hR : 0 < R)
    (hhl : hl < B/4) (hhh : C < hh) {a : TFSpace → ℝ}
    (hlo : ∀ x, R/2 ≤ ‖x‖ → outerBarrier B (R/2) x ≤ nuclearField Z x+a x)
    (hhi : ∀ x, R/2 ≤ ‖x‖ → nuclearField Z x+a x ≤ C/‖x‖^4)
    {x : TFSpace} (hx : R/2 ≤ ‖x‖) :
    0 ≤ nuclearField Z x+a x ∧ ‖x‖^4*(nuclearField Z x+a x) ∈ Icc hl hh := by
  have hd : 0 < ‖x‖ := (by linarith : 0 < R/2).trans_le hx
  have hd4 := pow_pos hd 4
  have hlow := (outerBarrier_bounds hB.le (by linarith : 0 < R/2) hx).1.trans (hlo x hx)
  have hlow' := (div_le_iff₀ hd4).mp hlow
  have hhigh := (le_div_iff₀ hd4).mp (hhi x hx)
  refine ⟨(by positivity : 0 ≤ (7*B/8)/‖x‖^4).trans hlow,?_,?_⟩ <;> nlinarith

lemma outward_old_retained_dom (good : Prop) [Decidable good]
    {Z B C R κ lam1 lam2 e ξ Cinv hl hh : ℝ}
    (hB : 0 < B) (hR : 0 < R) (hκ : 0 ≤ κ) (hlam : 0 ≤ lam1) (hξ : 0 ≤ ξ)
    (hgap : 16*ξ+2*e < lam1-lam2) (hhl : hl < B/4) (hhh : C < hh)
    {a h μ p : TFSpace → ℝ}
    (hlo : ∀ x, R/2 ≤ ‖x‖ → outerBarrier B (R/2) x ≤ nuclearField Z x+a x)
    (hhi : ∀ x, R/2 ≤ ‖x‖ → nuclearField Z x+a x ≤ C/‖x‖^4)
    (hinv : good → ∀ x, R/2 ≤ ‖x‖ → ‖x‖ < R →
      InverseComparisonAt ‖x‖ (nuclearField Z x+h x) (μ x) κ hl hh ξ Cinv)
    {x : TFSpace} {w : ℝ} (hcand : good → h x-lam2/R^4 ≤ w)
    (hnear : w-(a x-lam1/R^4) < 2*(e/R^4)) :
    innerSource R μ (addedError good R μ p) x+
      outerCoefficient R x*reaction κ (nuclearField Z x+(a x-lam1/R^4)) ≤
    innerSource (R/2) μ p x+outerCoefficient (R/2) x*reaction κ (nuclearField Z x+a x) := by
  have hh' := outward_old_source good hR hκ hlam hξ hgap hinv
    (u := fun y => nuclearField Z y+a y) (w := fun _ => nuclearField Z x+w)
    (H := fun y => nuclearField Z y+h y) (p := p) (x := x)
    (fun hx _ => old_branch_height hB hR hhl hhh hlo hhi hx)
    (fun hg => by linarith [hcand hg]) (by convert hnear using 1 <;> ring)
  simpa only [add_sub_assoc] using hh'

lemma outward_field_retained_dom (good : Prop) [Decidable good]
    {Z B C R M κ lam2 e ξ Cinv hl hh : ℝ}
    (hB : 0 < B) (hR : 0 < R) (he : 0 < e) (hξ : 0 ≤ ξ)
    (hshift : ξ < lam2) (hlam : 0 ≤ lam2) (hhl : hl < B/4) (hhh : C < hh)
    (hsmall : 2*e*(2*M)^4 < B/4)
    {h μ p : TFSpace → ℝ} (hp : ∀ x, 0 ≤ p x) (hμ : ∀ x, 0 ≤ μ x)
    {x : TFSpace} {w : ℝ} (hd : ‖x‖ < 2*M*R)
    (hinv : R ≤ ‖x‖ → InverseComparisonAt ‖x‖ (nuclearField Z x+h x) (μ x) κ hl hh ξ Cinv)
    (hcap : R ≤ ‖x‖ → nuclearField Z x+h x ≤ C/‖x‖^4)
    (hlo : R ≤ ‖x‖ → outerBarrier B R x ≤ nuclearField Z x+w)
    (hnear : w-(h x-lam2/R^4) < 2*(e/R^4)) :
    innerSource R μ (addedError good R μ p) x+
      outerCoefficient R x*reaction κ (nuclearField Z x+(h x-lam2/R^4)) ≤ 4*Real.pi*μ x := by
  have hh' := outward_field_source good hR hξ hshift hp hμ
    (H := fun y => nuclearField Z y+h y) (x := x) hinv (fun hx => by
    apply retained_field_height hB hR he hx hd.le hhl hhh hsmall hlam rfl
      (w := nuclearField Z x+w) (H := nuclearField Z x+h x)
    · exact (outerBarrier_bounds hB.le hR hx).1.trans (hlo hx)
    · have hd4 := pow_pos (hR.trans_le hx) 4
      have hb := (le_div_iff₀ hd4).mp (hcap hx)
      nlinarith
    · convert hnear using 1 <;> ring)
  simpa only [add_sub_assoc] using hh'

end CoulombBarrier

end

end OAI
