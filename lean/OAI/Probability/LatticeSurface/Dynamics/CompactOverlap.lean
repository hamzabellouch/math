import Mathlib
import OAI.Probability.LatticeSurface.Convexity.USCProduct

namespace OAI

open Set Filter

open scoped Topology

noncomputable section

namespace Overlap

end Overlap

namespace Overlap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

def kernel (p : E → ℝ) (x χ : E) : ℝ := Real.sqrt (p (x+χ)*p (x-χ))

def shifts (l : E →L[ℝ] ℝ) (t R : ℝ) : Set E :=
  Metric.closedBall 0 R ∩ l ⁻¹' {t}

def overlap (p : E → ℝ) (l : E →L[ℝ] ℝ) (t R : ℝ) (x : E) : ℝ :=
  max 0 (sSup (kernel p x '' shifts l t R))

lemma compact_shifts (l : E →L[ℝ] ℝ) (t R : ℝ) : IsCompact (shifts l t R) :=
  (isCompact_closedBall 0 R).inter_right (isClosed_singleton.preimage l.continuous)

omit [NormedSpace ℝ E] [ProperSpace E] in
lemma usc_kernel {p : E → ℝ} (hp : UpperSemicontinuous p) (hp0 : ∀ x,0≤p x) :
    UpperSemicontinuous (fun z : E × E => kernel p z.1 z.2) := by
  exact usc_sqrt (usc_mul (hp.comp (continuous_fst.add continuous_snd))
    (hp.comp (continuous_fst.sub continuous_snd)) (fun z => hp0 _) (fun z => hp0 _))

lemma usc_overlap {p : E → ℝ} (hp : UpperSemicontinuous p) (hp0 : ∀ x,0≤p x)
    (l : E →L[ℝ] ℝ) (t R : ℝ) : UpperSemicontinuous (overlap p l t R) :=
  upperSemicontinuous_const.sup (usc_sup_compact (compact_shifts l t R) (usc_kernel hp hp0))

omit [ProperSpace E] in
lemma overlap_nonneg (p : E → ℝ) (l : E →L[ℝ] ℝ) (t R : ℝ) (x : E) :
    0≤overlap p l t R x := le_max_left _ _

omit [ProperSpace E] in
lemma overlap_le {p : E → ℝ} {l : E →L[ℝ] ℝ} {t R : ℝ} {x : E} {b : ℝ}
    (hb : 0≤b) (h : ∀ χ∈shifts l t R,kernel p x χ≤b) : overlap p l t R x≤b := by
  apply max_le hb
  by_cases hne : (shifts l t R).Nonempty
  · exact csSup_le (hne.image _) (by rintro _ ⟨χ,hχ,rfl⟩;exact h χ hχ)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne,Set.image_empty,Real.sSup_empty]
    exact hb

lemma kernel_le_overlap {p : E → ℝ} (hp : UpperSemicontinuous p) (hp0 : ∀ x,0≤p x)
    (l : E →L[ℝ] ℝ) (t R : ℝ) (x : E) {χ : E} (hχ : χ∈shifts l t R) :
    kernel p x χ≤overlap p l t R x := by
  apply le_trans _ (le_max_right _ _)
  exact le_csSup (((usc_kernel hp hp0).comp (continuous_const.prodMk continuous_id)).upperSemicontinuousOn _
    |>.bddAbove_of_isCompact (compact_shifts l t R)) (mem_image_of_mem _ hχ)

omit [ProperSpace E] in
lemma midpoint_norms {x χ : E} {R : ℝ} (hplus : ‖x+χ‖≤R) (hminus : ‖x-χ‖≤R) :
    ‖x‖≤R ∧ ‖χ‖≤R := by
  have hxa : (x+χ)+(x-χ)=(2:ℝ) • x := by module
  have hχa : (x+χ)-(x-χ)=(2:ℝ) • χ := by module
  have hx := norm_add_le (x+χ) (x-χ)
  have hχ := norm_sub_le (x+χ) (x-χ)
  rw [hxa,norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)] at hx
  rw [hχa,norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)] at hχ
  constructor <;> linarith

omit [ProperSpace E] in
lemma kernel_support {p : E → ℝ} {R : ℝ} (hpK : ∀ z,R<‖z‖ → p z=0)
    {x χ : E} (h : kernel p x χ≠0) : ‖x‖≤R ∧ ‖χ‖≤R := by
  have hp : p (x+χ)≠0 ∧ p (x-χ)≠0 := by
    constructor
    · intro hz;apply h;simp [kernel,hz]
    · intro hz;apply h;simp [kernel,hz]
  apply midpoint_norms
  · exact le_of_not_gt (fun hx => hp.1 (hpK _ hx))
  · exact le_of_not_gt (fun hx => hp.2 (hpK _ hx))

omit [ProperSpace E] in
lemma overlap_support {p : E → ℝ} {l : E →L[ℝ] ℝ} {t R : ℝ}
    (hpK : ∀ z,R<‖z‖ → p z=0) {x : E} (hx : R<‖x‖) : overlap p l t R x=0 := by
  apply le_antisymm _ (overlap_nonneg _ _ _ _ _)
  apply overlap_le le_rfl
  intro χ hχ
  have hz : kernel p x χ=0 := by
    by_contra hn
    exact (not_lt_of_ge (kernel_support hpK hn).1) hx
  exact hz.le

lemma kernel_le_overlap_all {p : E → ℝ} (hp : UpperSemicontinuous p) (hp0 : ∀ x,0≤p x)
    {l : E →L[ℝ] ℝ} {t R : ℝ} (hpK : ∀ z,R<‖z‖ → p z=0)
    (x χ : E) (hχ : l χ=t) : kernel p x χ≤overlap p l t R x := by
  by_cases hz : kernel p x χ=0
  · rw [hz];exact overlap_nonneg _ _ _ _ _
  · apply kernel_le_overlap hp hp0 l t R x
    exact ⟨by simpa [Metric.mem_closedBall,dist_zero_right] using (kernel_support hpK hz).2,hχ⟩

lemma overlap_eq_sup {p : E → ℝ} (hp : UpperSemicontinuous p) (hp0 : ∀ x,0≤p x)
    {l : E →L[ℝ] ℝ} {t R : ℝ} (hpK : ∀ z,R<‖z‖ → p z=0)
    (hne : (l ⁻¹' {t}).Nonempty) (x : E) :
    overlap p l t R x=sSup (kernel p x '' (l ⁻¹' {t})) := by
  have hbd : BddAbove (kernel p x '' (l ⁻¹' {t})) := ⟨overlap p l t R x,by
    rintro _ ⟨χ,hχ,rfl⟩;exact kernel_le_overlap_all hp hp0 hpK x χ hχ⟩
  apply le_antisymm
  · apply overlap_le
    · obtain ⟨χ,hχ⟩ := hne
      exact (Real.sqrt_nonneg _).trans (le_csSup hbd (mem_image_of_mem _ hχ))
    · intro χ hχ
      exact le_csSup hbd (mem_image_of_mem _ hχ.2)
  · apply csSup_le (hne.image _)
    rintro _ ⟨χ,hχ,rfl⟩
    exact kernel_le_overlap_all hp hp0 hpK x χ hχ

end Overlap

end

end OAI
