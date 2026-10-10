import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.TfInfiniteFieldDominatesDilation
import OAI.Analysis.CoulombIonization.FieldAnalysis.WeakExteriorDecayBarrier
import OAI.Analysis.CoulombIonization.ThomasFermi.WeakSommerfeldAsymptoticBarrier

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_WeakSingularProfile_barrier_scope

open MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Topology

open CoulombPDE

structure WeakSingularProfile (d : ℝ) (F : Space → ℝ) : Prop where
  continuous : ContinuousOn F {0}ᶜ
  equation : PuncturedPoisson F (fun x => reaction d (F x))
  decay : ∀ ε > 0, ∃ R > 0, ∀ x, R ≤ ‖x‖ → |F x| < ε
  bounds : ∃ c > 0, ∃ C > 0, ∃ R > 0,
    (∀ x, x ≠ 0 → ‖x‖ ≤ R → c * radialPower (-2) x ≤ F x) ∧
    (∀ x, x ≠ 0 → ‖x‖ ≤ R → F x ≤ C * radialPower (-2) x)

lemma WeakSingularProfile.of_classical {d : ℝ} {F : Space → ℝ}
    (h : SingularProfile d F) : WeakSingularProfile d F :=
  ⟨fun x hx => (h.regular x hx).continuousAt.continuousWithinAt,
    (PuncturedPoisson.of_classical h.regular).congr_source (fun x hx => h.equation x hx),
    h.decay,h.bounds⟩

lemma WeakSingularProfile.asymptotic {d : ℝ} {F : Space → ℝ}
    (h : WeakSingularProfile d F) (hd : 0 < d) :
    Tendsto (fun x => ‖x‖ ^ 4 * F x) (𝓝[≠] (0 : Space))
      (𝓝 (sommerfeldCoefficient d)) := by
  obtain ⟨c,hc,C,hC,R,hR,hl,hu⟩ := h.bounds
  exact weak_sommerfeld_asymptotic hd hc hC.le hR h.continuous h.equation hl hu

lemma WeakSingularProfile.scaled_comparison {d α δ : ℝ} {F₁ F₂ : Space → ℝ}
    (h₁ : WeakSingularProfile d F₁) (h₂ : WeakSingularProfile d F₂)
    (hd : 0 < d) (hα : 1 < α) (hδ : 0 < δ) :
    ∀ x, x ≠ 0 → F₂ x ≤ α * F₁ x + δ := by
  let G : Space → ℝ := fun x => α * F₁ x + δ
  have hGc : ContinuousOn G {0}ᶜ :=
    (continuousOn_const.mul h₁.continuous).add continuousOn_const
  have hG : PuncturedPoisson G (fun x => α*reaction d (F₁ x)) :=
    (h₁.equation.const_mul α).add_const
      (continuousOn_const.mul h₁.continuous)
      (continuousOn_const.mul ((reaction_continuous d).comp_continuousOn h₁.continuous)) δ
  have hdiff := h₂.equation.sub hG h₂.continuous hGc
    ((reaction_continuous d).comp_continuousOn h₂.continuous)
    (continuousOn_const.mul ((reaction_continuous d).comp_continuousOn h₁.continuous))
  have hnear : ∀ᶠ x in 𝓝[≠] (0 : Space), F₂ x - G x ≤ 0 := by
    have ht : Tendsto (fun x : Space => ‖x‖ ^ 4 * (α * F₁ x - F₂ x))
        (𝓝[≠] (0 : Space)) (𝓝 ((α - 1) * sommerfeldCoefficient d)) := by
      convert ((h₁.asymptotic hd).const_mul α).sub (h₂.asymptotic hd) using 1 <;> (try funext x) <;> ring_nf
    have hp : 0 < (α - 1) * sommerfeldCoefficient d :=
      mul_pos (sub_pos.mpr hα) (sommerfeldCoefficient_pos hd)
    filter_upwards [ht.eventually (eventually_gt_nhds hp), self_mem_nhdsWithin] with x hx hxn
    have hn : 0 < ‖x‖ ^ 4 := pow_pos (norm_pos_iff.mpr hxn) _
    have hu : 0 < α * F₁ x - F₂ x := (mul_pos_iff_of_pos_left hn).mp hx
    dsimp [G]
    linarith
  have hfar : ∃ R > 0, ∀ x, R ≤ ‖x‖ → F₂ x - G x ≤ 0 := by
    let ε := δ / (2 * (α + 1))
    have he : 0 < ε := div_pos hδ (by linarith)
    have heq : ε * (2 * (α + 1)) = δ := by
      exact div_mul_cancel₀ _ (by linarith)
    obtain ⟨R₁, hR₁, hb₁⟩ := h₁.decay ε he
    obtain ⟨R₂, _hR₂, hb₂⟩ := h₂.decay ε he
    refine ⟨max R₁ R₂, hR₁.trans_le (le_max_left _ _), ?_⟩
    intro x hx
    have h1 := (abs_lt.mp (hb₁ x ((le_max_left _ _).trans hx))).1
    have h2 := (abs_lt.mp (hb₂ x ((le_max_right _ _).trans hx))).2
    dsimp [G]
    nlinarith [mul_nonneg (show 0 ≤ α by linarith) (show 0 ≤ F₁ x + ε by linarith)]
  have hm := weak_global_punctured_maximum
    (u := F₂-G) (h₂.continuous.sub hGc)
    (fun g hg hcg hs hgn => hdiff.nonneg_on_positive (fun x _hx hp => ?_) hg hcg hs hgn)
    (deleted_eventually_to_small_ball hnear) hfar
  · exact fun x hx => sub_nonpos.mp (hm x hx)
  · have hmon := reaction_monotone hd.le (le_of_lt (sub_pos.mp hp))
    have hsuper := reaction_superlinear (v := F₁ x) hd.le hα.le hδ.le
    change 0 ≤ reaction d (F₂ x)-α*reaction d (F₁ x)
    dsimp [G] at hmon
    linarith

theorem weak_singular_profile_unique {d : ℝ} {F₁ F₂ : Space → ℝ}
    (hd : 0 < d) (h₁ : WeakSingularProfile d F₁) (h₂ : WeakSingularProfile d F₂) :
    EqOn F₁ F₂ ({0}ᶜ) := by
  have hle {F G : Space → ℝ} (hF : WeakSingularProfile d F) (hG : WeakSingularProfile d G)
      (x : Space) (hx : x ≠ 0) : G x ≤ F x := by
    have hscaled (α : ℝ) (hα : 1 < α) : G x ≤ α * F x := by
      apply le_of_forall_pos_le_add
      intro δ hδ
      exact hF.scaled_comparison hG hd hα hδ x hx
    have ht : Tendsto (fun t : ℝ => (1 + t) * F x) (𝓝[>] 0) (𝓝 (F x)) := by
      have h : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
      simpa using (h.const_add 1).mul_const (F x)
    apply le_of_tendsto_of_tendsto tendsto_const_nhds ht
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hscaled (1 + t) (by change 0 < t at ht; linarith)
  intro x hx
  exact le_antisymm (hle h₂ h₁ x hx) (hle h₁ h₂ x hx)

theorem weak_profile_eq_tfInfiniteField {F : Space → ℝ}
    (h : WeakSingularProfile tfReactionCoefficient F) :
    EqOn F tfInfiniteField {0}ᶜ :=
  weak_singular_profile_unique tfReactionCoefficient_pos h
    (WeakSingularProfile.of_classical tfInfiniteField_singularProfile)

theorem weak_profile_classical {F : Space → ℝ}
    (h : WeakSingularProfile tfReactionCoefficient F) :
    SingularProfile tfReactionCoefficient F := by
  have he := weak_profile_eq_tfInfiniteField h
  have heq (x : Space) (hx : x ≠ 0) : F =ᶠ[𝓝 x] tfInfiniteField := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
    exact he hy
  refine ⟨?_,?_,h.decay,h.bounds⟩
  · intro x hx
    exact (tfInfiniteField_singularProfile.regular x hx).congr_of_eventuallyEq (heq x hx)
  · intro x hx
    rw [(laplacian_congr_nhds (heq x hx)).eq_of_nhds,
      tfInfiniteField_singularProfile.equation x hx,he hx]

end Work_WeakSingularProfile_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom CoulombPDE

lemma weak_profile_of_cap_barrier {F : CoulombAtom.Space → ℝ} {d B C : ℝ}
    (hc : ContinuousOn F {0}ᶜ)
    (he : PuncturedPoisson F (fun x => reaction d (F x)))
    (hB : 0 < B) (hC : 0 ≤ C)
    (hl : ∀ x, x ≠ 0 → B/‖x‖^4 ≤ F x)
    (hu : ∀ x, x ≠ 0 → F x ≤ 1+C/‖x‖^4)
    (hd : ∀ ε > 0, ∃ R > 0, ∀ x : CoulombAtom.Space, R ≤ ‖x‖ → |F x| < ε) :
    WeakSingularProfile d F := by
  refine ⟨hc,he,hd,B,hB,C+1,by linarith,1,zero_lt_one,?_,?_⟩
  · intro x hx _
    have hm := norm_four_mul_radialPower hx
    have hn : ‖x‖^4 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
    have heq : B/‖x‖^4 = B*radialPower (-2) x := by
      apply (div_eq_iff hn).mpr
      nlinarith
    simpa only [heq] using hl x hx
  · intro x hx hr
    have hm := norm_four_mul_radialPower hx
    have hn : ‖x‖^4 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
    have hp := radialPower_pos (-2) hx
    have hpow : ‖x‖^4 ≤ 1 := pow_le_one₀ (norm_nonneg x) hr
    have hrp : 1 ≤ radialPower (-2) x := by nlinarith
    have heq : C/‖x‖^4 = C*radialPower (-2) x := by
      apply (div_eq_iff hn).mpr
      nlinarith
    have hh := hu x hx
    rw [heq] at hh
    nlinarith

lemma tfInfiniteRadial_exterior {r : ℝ} (hr : tfSupportRadius ≤ r) :
    tfInfiniteRadial r = tfResidualCharge/r := by
  have hr0 : 0 < r := (zero_lt_one.trans tfSupportRadius_gt_one).trans_le hr
  apply tendsto_nhds_unique (tfRealRadial_tendsto hr0)
  apply (tf_unit_deficit_tendsto.div_const r).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with Z hZ
  rw [tfRealRadial,tfUnitDeficit,dite_eq_left hZ,dite_eq_left hZ]
  exact ((tfUnitData Z hZ).exterior_field hZ hr).symm

lemma tfInfiniteField_exterior {x : CoulombAtom.Space} (hx : tfSupportRadius ≤ ‖x‖) :
    tfInfiniteField x = tfResidualCharge/‖x‖ := tfInfiniteRadial_exterior hx

lemma tfInfiniteField_sphereMean (p : CoulombAtom.Space) : sphereMean tfInfiniteField p = tfInfiniteRadial ‖p‖ := by
  unfold sphereMean tfInfiniteField
  simp only [(rotate _).norm_map,integral_const,probReal_univ,smul_eq_mul,one_mul]

theorem weak_profile_charge_eq {F : CoulombAtom.Space → ℝ} {q R : ℝ}
    (h : WeakSingularProfile tfReactionCoefficient F)
    (hm : ∀ p : CoulombAtom.Space, R < ‖p‖ → sphereMean F p = q/‖p‖) :
    q = tfResidualCharge := by
  let r := max R tfSupportRadius+1
  have hr : 0 < r := by
    have hh := le_max_right R tfSupportRadius
    have hh' := zero_lt_one.trans tfSupportRadius_gt_one
    dsimp [r]
    linarith
  let p : CoulombAtom.Space := r • radialAxis
  have hpn : ‖p‖ = r := TFUnitData.ray_norm hr
  have he : sphereMean F p = sphereMean tfInfiniteField p := by
    unfold sphereMean
    apply integral_congr_ae
    exact ae_of_all _ (fun g => weak_profile_eq_tfInfiniteField h
      (rotate_ne_zero g (TFUnitData.ray_ne_zero hr)))
  rw [hm p (by rw [hpn]; dsimp [r]; linarith [le_max_left R tfSupportRadius]),
    tfInfiniteField_sphereMean,hpn,tfInfiniteRadial_exterior (by
      dsimp [r]; linarith [le_max_right R tfSupportRadius])] at he
  exact (div_left_inj' hr.ne').mp he

theorem weak_limit_identification {F : CoulombAtom.Space → ℝ} {q R B C : ℝ}
    (hR : 0 < R) (hB : 0 < B) (hC : 0 ≤ C)
    (hc : ContinuousOn F {0}ᶜ)
    (he : PuncturedPoisson F (fun x => reaction tfReactionCoefficient (F x)))
    (hh : ∀ g : CoulombAtom.Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ {x | R < ‖x‖} → (∫ x, F x*Laplacian.laplacian g x) = 0)
    (hm : ∀ p : CoulombAtom.Space, R < ‖p‖ → sphereMean F p = q/‖p‖)
    (hl : ∀ x, x ≠ 0 → B/‖x‖^4 ≤ F x)
    (hu : ∀ x, x ≠ 0 → F x ≤ 1+C/‖x‖^4) :
    EqOn F tfInfiniteField {0}ᶜ ∧ q = tfResidualCharge := by
  have hb : ∀ x : CoulombAtom.Space, R ≤ ‖x‖ → F x ≤ 1+C/R^4 := by
    intro x hx
    have hp : 0 < ‖x‖ := hR.trans_le hx
    apply (hu x (norm_pos_iff.mp hp)).trans
    exact add_le_add_right (div_le_div_of_nonneg_left hC (pow_pos hR 4)
      (pow_le_pow_left₀ hR.le hx 4)) 1
  have hd := weak_exterior_mean_uniform_decay hR hc hh hb hm
  have hp := weak_profile_of_cap_barrier hc he hB hC hl hu hd
  exact ⟨weak_profile_eq_tfInfiniteField hp,weak_profile_charge_eq hp hm⟩

end CoulombAnalysis

end

end OAI
