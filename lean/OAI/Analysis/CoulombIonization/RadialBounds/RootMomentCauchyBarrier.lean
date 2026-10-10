import Mathlib
import OAI.Analysis.CoulombIonization.Variational.WeightedCauchy
import OAI.Analysis.CoulombIonization.RadialBounds.RadialSelectedCounts
import OAI.Analysis.CoulombIonization.RadialBounds.CoreHistoryCountsBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_RootMomentCauchy_barrier_scope

open MeasureTheory Filter
open scoped BigOperators

lemma integrable_sqrt_mul_sqrt {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) :
    Integrable (fun x => Real.sqrt (f x)*Real.sqrt (g x)) μ := by
  apply (hf.add hg).mono'
    ((Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable).mul
      (Real.continuous_sqrt.comp_aestronglyMeasurable hg.aestronglyMeasurable))
  apply ae_of_all
  intro x
  change ‖Real.sqrt (f x)*Real.sqrt (g x)‖ ≤ f x+g x
  rw [Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  nlinarith [sq_nonneg (Real.sqrt (f x)-Real.sqrt (g x)),
    Real.sq_sqrt (hfn x),Real.sq_sqrt (hgn x)]

lemma sum_integral_sqrt_mul_sqrt_le {ι : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    (f g : ∀ i, X i → ℝ) (hf : ∀ i, Integrable (f i) (μ i))
    (hg : ∀ i, Integrable (g i) (μ i)) (hfn : ∀ i x, 0 ≤ f i x) (hgn : ∀ i x, 0 ≤ g i x) :
    (∑ i, ∫ x, Real.sqrt (f i x)*Real.sqrt (g i x) ∂μ i) ≤
      Real.sqrt (∑ i, ∫ x, f i x ∂μ i)*Real.sqrt (∑ i, ∫ x, g i x ∂μ i) := by
  have hh := weighted_sum_integral_cauchy μ (fun _ _ => 1)
    (fun i x => Real.sqrt (f i x)) (fun i x => Real.sqrt (g i x))
    (fun _ _ => zero_le_one)
    (fun i => by simpa only [mul_one,Real.sq_sqrt (hfn i _)] using hf i)
    (fun i => by simpa only [mul_one,Real.sq_sqrt (hgn i _)] using hg i)
    (fun i => by simpa only [mul_one] using integrable_sqrt_mul_sqrt (hf i) (hg i) (hfn i) (hgn i))
  simpa only [mul_one,Real.sq_sqrt (hfn _ _),Real.sq_sqrt (hgn _ _)] using hh

end Work_RootMomentCauchy_barrier_scope

section Work_CoreHistoryIMS_barrier_scope

open MeasureTheory Filter Set
open scoped BigOperators

lemma rawFormPair_integrable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {g : Configuration N → ℝ} (hg : Measurable g) {B : ℝ}
    (hB : ∀ x, ‖g x‖ ≤ B) (s : Spins N) : Integrable (fun x => g x*‖ψ.value s x‖^2) :=
  ((hψ.1 s).norm.integrable_sq).bdd_mul hg.aestronglyMeasurable (ae_of_all _ hB)

lemma rawBallFirst_le_sqrt_count {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) (R : ℝ) :
    rawFormPair ψ (rawBallCount y R) ≤ Real.sqrt (rawCountMoment ψ y R)*Real.sqrt (formMass ψ) := by
  have hc := weighted_sum_integral_cauchy (fun _ : Spins N => volume)
    (fun s x => ‖ψ.value s x‖^2) (fun _ => rawBallCount y R) (fun _ _ => 1)
    (fun _ _ => sq_nonneg _)
    (fun s => rawFormPair_integrable hψ ((rawBallCount_measurable y R).pow_const 2)
      (fun x => norm_sq_le_of_nonneg (rawBallCount_nonneg _ _ _) (rawBallCount_le _ _ _)) s)
    (fun s => by simpa only [one_pow,one_mul] using (hψ.1 s).norm.integrable_sq)
    (fun s => by
      simpa only [mul_one] using (rawFormPair_integrable hψ (rawBallCount_measurable y R)
        (fun x => by rw [Real.norm_of_nonneg (rawBallCount_nonneg _ _ _)]; exact rawBallCount_le _ _ _) s))
  simpa only [mul_one,one_pow,one_mul,rawFormPair,rawCountMoment,formMass] using hc

lemma collar_count_le_rawBallFirst {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) {t b R : ℝ} (hR : t+b < R) :
    weightedParticleCount ψ (fun z => if t ≤ ‖z-y‖ ∧ ‖z-y‖ ≤ t+b then 1 else 0) ≤
      rawFormPair ψ (rawBallCount y R) := by
  let w : Space → ℝ := fun z => if t ≤ ‖z-y‖ ∧ ‖z-y‖ ≤ t+b then 1 else 0
  have hw : Measurable w := measurable_const.ite
    (((isClosed_le continuous_const ((continuous_id.sub continuous_const).norm)).inter
      (isClosed_le ((continuous_id.sub continuous_const).norm) continuous_const)).measurableSet) measurable_const
  have hB : ∀ z, ‖w z‖ ≤ 1 := by intro z; unfold w; split_ifs <;> norm_num
  have hg : Measurable (fun x : Configuration N => ∑ i, w (x i)) :=
    Finset.measurable_sum _ (fun i _ => hw.comp (measurable_pi_apply i))
  have hgB (x : Configuration N) : ‖∑ i, w (x i)‖ ≤ (N:ℝ) := by
    calc
      _ ≤ ∑ i, ‖w (x i)‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Fin N, (1:ℝ) := Finset.sum_le_sum (fun i _ => hB (x i))
      _ = _ := by simp
  change weightedParticleCount ψ w ≤ _
  rw [weightedParticleCount_eq_rawLaw hψ hw hB,←rawFormPair_eq_integral hψ hg hgB]
  unfold rawFormPair
  apply Finset.sum_le_sum
  intro s _
  apply integral_mono (rawFormPair_integrable hψ hg hgB s)
    (rawFormPair_integrable hψ (rawBallCount_measurable y R)
      (fun x => by rw [Real.norm_of_nonneg (rawBallCount_nonneg _ _ _)]; exact rawBallCount_le _ _ _) s)
  intro x
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  unfold rawBallCount
  apply Finset.sum_le_sum
  intro i _
  dsimp only [w]
  split_ifs with h h' h'
  · norm_num
  · exfalso; exact h' (lt_of_le_of_lt h.2 hR)
  · norm_num
  · norm_num

lemma radial_ims_le_sqrt_count {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) {t b R : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hR : t+b < R) :
    (1/2:ℝ)*weightedParticleCount ψ (spatialErrorWeight (coreFirstRadialCut y ht hb)) ≤
      ((3/2:ℝ)*(Real.pi*smoothTransitionBound/b)^2)*
        (Real.sqrt (rawCountMoment ψ y R)*Real.sqrt (formMass ψ)) := by
  exact (radial_fresh_ims_bound hψ y ht hb).trans (mul_le_mul_of_nonneg_left
    ((collar_count_le_rawBallFirst hψ y hR).trans (rawBallFirst_le_sqrt_count hψ y R)) (by positivity))

end Work_CoreHistoryIMS_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators

 def localCellRadius (y : Space) : ℝ := ‖y‖/100000
 def localOffsetMass (D : ℝ) (y : Space) : ℝ :=
    max (1/(localCellRadius y)^3) 1+Real.sqrt (D*localCellRadius y)

lemma localCellRadius_pos {y : Space} (hy : y ≠ 0) : 0 < localCellRadius y := by
  unfold localCellRadius
  exact div_pos (norm_pos_iff.mpr hy) (by norm_num)
lemma localOffsetMass_one_le (D : ℝ) (y : Space) : 1 ≤ localOffsetMass D y := by
  unfold localOffsetMass
  linarith [le_max_right (1/localCellRadius y^3) 1,Real.sqrt_nonneg (D*localCellRadius y)]

lemma exists_localCountStencil : ∃ T : Finset Space,
    (∀ v ∈ T, ‖v‖ ≤ 32) ∧ ∀ x : Space, ‖x‖ ≤ 32 → ∃ v ∈ T, ‖x-v‖ < 1/4 := by
  classical
  let S := closedBall (0 : Space) 32
  have hc : S ⊆ ⋃ v : S, ball (v : Space) (1/4) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,by simp⟩
  obtain ⟨t,ht⟩ := (isCompact_closedBall (0 : Space) (32:ℝ)).elim_finite_subcover
    (fun v : S => ball (v : Space) (1/4)) (fun _ => isOpen_ball) hc
  refine ⟨t.image (fun v : S => (v : Space)),?_,?_⟩
  · intro v hv
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hv
    simpa only [S,mem_closedBall_iff_norm,sub_zero] using w.property
  · intro x hx
    have hxs : x ∈ S := by simpa only [S,mem_closedBall_iff_norm,sub_zero] using hx
    obtain ⟨v,hv,hxv⟩ := mem_iUnion₂.mp (ht hxs)
    exact ⟨v,Finset.mem_image.mpr ⟨v,hv,rfl⟩,mem_ball_iff_norm.mp hxv⟩

 def localCountStencil : Finset Space := Classical.choose exists_localCountStencil
lemma localCountStencil_norm {v : Space} (hv : v ∈ localCountStencil) : ‖v‖ ≤ 32 :=
  (Classical.choose_spec exists_localCountStencil).1 v hv
lemma localCountStencil_cover {x : Space} (hx : ‖x‖ ≤ 32) :
    ∃ v ∈ localCountStencil, ‖x-v‖ < 1/4 :=
  (Classical.choose_spec exists_localCountStencil).2 x hx

lemma localCellRadius_near {y v : Space} (hy : y ≠ 0) (hv : ‖v‖ ≤ 32) :
    localCellRadius y/2 ≤ localCellRadius (y+localCellRadius y • v) ∧
      localCellRadius (y+localCellRadius y • v) ≤ 2*localCellRadius y := by
  have ha := (localCellRadius_pos hy).le
  have hv' : ‖localCellRadius y • v‖ ≤ 32*localCellRadius y := by
    rw [norm_smul,Real.norm_of_nonneg ha]
    nlinarith
  have hu := norm_add_le y (localCellRadius y • v)
  have hl : ‖y‖ ≤ ‖y+localCellRadius y • v‖+‖localCellRadius y • v‖ := by
    calc ‖y‖ = ‖(y+localCellRadius y • v)-localCellRadius y • v‖ := by rw [add_sub_cancel_right]
         _ ≤ _ := norm_sub_le _ _
  unfold localCellRadius at *
  constructor <;> linarith

lemma localOffsetMass_near {D : ℝ} (hD : 0 ≤ D) {y v : Space}
    (hy : y ≠ 0) (hv : ‖v‖ ≤ 32) :
    localOffsetMass D (y+localCellRadius y • v) ≤ 8*localOffsetMass D y := by
  let a := localCellRadius y
  let z := y+a • v
  have ha : 0 < a := localCellRadius_pos hy
  have hnear := localCellRadius_near hy hv
  have hz : 0 < localCellRadius z := lt_of_lt_of_le (show 0 < a/2 by positivity) hnear.1
  have hc : 1/(localCellRadius z)^3 ≤ 8/a^3 := by
    calc 1/(localCellRadius z)^3 ≤ 1/(a/2)^3 :=
          one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hnear.1 3)
         _ = _ := by ring
  have hm : max (1/(localCellRadius z)^3) 1 ≤ 8*max (1/a^3) 1 := by
    apply max_le
    · exact hc.trans (by convert mul_le_mul_of_nonneg_left (le_max_left (1/a^3) 1) (by norm_num : (0:ℝ) ≤ 8) using 1; ring)
    · nlinarith [le_max_right (1/a^3) 1]
  have hs : Real.sqrt (D*localCellRadius z) ≤ 2*Real.sqrt (D*a) := by
    have hDs : 0 ≤ D*localCellRadius z := mul_nonneg hD hz.le
    have hDa : 0 ≤ D*a := mul_nonneg hD ha.le
    have hmul := mul_le_mul_of_nonneg_left hnear.2 hD
    nlinarith [Real.sq_sqrt hDs,Real.sq_sqrt hDa,
      Real.sqrt_nonneg (D*localCellRadius z),Real.sqrt_nonneg (D*a)]
  change max (1/(localCellRadius z)^3) 1+Real.sqrt (D*localCellRadius z) ≤
    8*(max (1/a^3) 1+Real.sqrt (D*a))
  linarith [Real.sqrt_nonneg (D*a)]

lemma localCountStencil_scaled_cover {y : Space} (hy : y ≠ 0) {x : Space}
    (hx : ‖x-y‖ < 32*localCellRadius y) :
    ∃ v ∈ localCountStencil, ‖x-(y+localCellRadius y • v)‖ <
      localCellRadius (y+localCellRadius y • v) := by
  let a := localCellRadius y
  have ha : 0 < a := localCellRadius_pos hy
  let u := a⁻¹ • (x-y)
  have hun : ‖u‖ = ‖x-y‖/a := by
    dsimp [u]
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr ha.le)]
    ring
  have hu : ‖u‖ ≤ 32 := by rw [hun]; exact (div_le_iff₀ ha).mpr (by linarith)
  obtain ⟨v,hv,hv'⟩ := localCountStencil_cover hu
  refine ⟨v,hv,?_⟩
  have he : a • u = x-y := by dsimp [u]; rw [smul_smul,mul_inv_cancel₀ ha.ne',one_smul]
  have he' : x-(y+a • v) = a • (u-v) := by rw [smul_sub,he]; abel
  rw [show localCellRadius y = a from rfl,he',norm_smul,Real.norm_of_nonneg ha.le]
  have hn := (localCellRadius_near hy (localCountStencil_norm hv)).1
  nlinarith

lemma rawBallCount_le_cover {N : ℕ} (x : Configuration N) (y : Space) (R : ℝ)
    (T : Finset Space) (r : Space → ℝ)
    (hcover : ∀ z : Space, ‖z-y‖ < R → ∃ v ∈ T, ‖z-v‖ < r v) :
    rawBallCount y R x ≤ ∑ v ∈ T, rawBallCount v (r v) x := by
  classical
  unfold rawBallCount
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  by_cases hx : ‖x i-y‖ < R
  · rw [ite_eq_left hx]
    obtain ⟨v,hv,hiv⟩ := hcover (x i) hx
    have hh := Finset.single_le_sum (f := fun w => if ‖x i-w‖ < r w then (1:ℝ) else 0)
      (fun _ _ => by split_ifs <;> norm_num) hv
    simpa only [ite_eq_left hiv] using hh
  · rw [ite_eq_right hx]
    exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

lemma rawCountMoment_le_cover {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) (R : ℝ) (T : Finset Space) (r : Space → ℝ)
    (hcover : ∀ z : Space, ‖z-y‖ < R → ∃ v ∈ T, ‖z-v‖ < r v) :
    rawCountMoment ψ y R ≤ (T.card:ℝ)*∑ v ∈ T, rawCountMoment ψ v (r v) := by
  classical
  have hb (z : Space) (s : ℝ) (t : Spins N) :
      Integrable (fun x => rawBallCount z s x^2*‖ψ.value t x‖^2) :=
    rawFormPair_integrable hψ ((rawBallCount_measurable z s).pow_const 2)
      (fun _ => norm_sq_le_of_nonneg (rawBallCount_nonneg _ _ _) (rawBallCount_le _ _ _)) t
  have hpoint (x : Configuration N) : rawBallCount y R x^2 ≤
      (T.card:ℝ)*∑ v ∈ T, rawBallCount v (r v) x^2 := by
    calc _ ≤ (∑ v ∈ T, rawBallCount v (r v) x)^2 :=
           pow_le_pow_left₀ (rawBallCount_nonneg _ _ _) (rawBallCount_le_cover x y R T r hcover) 2
         _ ≤ _ := sq_sum_le_card_mul_sum_sq
  unfold rawCountMoment rawFormPair
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  calc
    _ ≤ ∫ x, (T.card:ℝ)*(∑ v ∈ T, rawBallCount v (r v) x^2)*‖ψ.value t x‖^2 := by
      apply integral_mono (hb y R t)
      · simp only [mul_assoc,Finset.sum_mul]
        exact (integrable_finsetSum _ (fun v _ => hb v (r v) t)).const_mul _
      · intro x
        exact mul_le_mul_of_nonneg_right (hpoint x) (sq_nonneg _)
    _ = _ := by
      simp only [mul_assoc,Finset.sum_mul,integral_const_mul]
      rw [integral_finsetSum _ (fun v _ => hb v (r v) t)]

end CoulombAtom

end

end OAI
