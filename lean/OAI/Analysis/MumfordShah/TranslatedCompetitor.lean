import Mathlib
import OAI.Analysis.MumfordShah.EnergyLimits
import OAI.Analysis.MumfordShah.SobolevAlgebra

namespace OAI

/-! MumfordShah translated competitor. -/

noncomputable section
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
namespace MumfordShah
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Set MeasureTheory Topology InnerProductSpace
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology Filter
open scoped ContDiff
open Set MeasureTheory Topology InnerProductSpace
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Filter
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff

open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff

lemma ae_zero_compl_essentialSupport (f : ℂ → ℝ) :
    f =ᵐ[volume.restrict (essentialSupport f)ᶜ] 0 := by
  classical
  have hloc (x : ↥((essentialSupport f)ᶜ)) :
      ∃ r : ℝ, 0 < r ∧ ∀ᵐ y ∂volume.restrict (ball (x : ℂ) r), f y = 0 := by
    have hx := x.property
    change ¬ (∀ r : ℝ, 0 < r → ¬ (∀ᵐ y ∂volume.restrict (ball (x : ℂ) r), f y = 0)) at hx
    push Not at hx
    exact hx
  choose r hr hz using hloc
  obtain ⟨c,hc,hcov⟩ := (HereditarilyLindelofSpace.isLindelof (essentialSupport f)ᶜ).elim_countable_subcover
    (fun x : ↥((essentialSupport f)ᶜ) => ball (x : ℂ) (r x)) (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩, mem_ball_self (hr ⟨x,hx⟩)⟩)
  apply ae_restrict_of_ae_restrict_of_subset hcov
  exact (ae_restrict_biUnion_iff _ hc _).mpr (fun x _ => hz x)

lemma isClosed_essentialSupport (f : ℂ → ℝ) : IsClosed (essentialSupport f) := by
  apply isOpen_compl_iff.mp
  rw [Metric.isOpen_iff]
  intro x hx
  change ¬ (∀ r : ℝ, 0 < r → ¬ (∀ᵐ y ∂volume.restrict (ball x r), f y = 0)) at hx
  push Not at hx
  obtain ⟨r,hr,hz⟩ := hx
  refine ⟨r,hr,?_⟩
  intro y hy
  change ¬ (∀ s : ℝ, 0 < s → ¬ (∀ᵐ z ∂volume.restrict (ball y s), f z = 0))
  intro h
  have hs : 0 < r - dist y x := sub_pos.mpr hy
  apply h (r - dist y x) hs
  apply ae_restrict_of_ae_restrict_of_subset (ball_subset_ball' (by linarith)) hz

lemma compact_support_weak_gradient {A : Set ℂ} {h : ℂ → ℝ} {e : ℂ → ℂ}
    (hA : IsCompact A) (hh : SobolevOn h e Aᶜ)
    (hc : IsCompact (essentialSupport h)) :
    ∃ R : ℝ, 0 < R ∧ ∀ᵐ x ∂volume, R < ‖x‖ → e x = 0 := by
  obtain ⟨R,hR,hb⟩ := (hA.union hc).isBounded.exists_pos_norm_lt
  let O : Set ℂ := {x | R < ‖x‖}
  have hO : IsOpen O := isOpen_lt continuous_const continuous_norm
  have hsub : O ⊆ Aᶜ := fun x hx hxA => (not_lt_of_ge (le_of_lt (hb x (Or.inl hxA)))) hx
  have hesub : O ⊆ (essentialSupport h)ᶜ :=
    fun x hx hxs => (not_lt_of_ge (le_of_lt (hb x (Or.inr hxs)))) hx
  have he := weak_gradient_zero_on (hh.mono hsub) hO
    (ae_restrict_of_ae_restrict_of_subset hesub (ae_zero_compl_essentialSupport h))
  exact ⟨R,hR,(ae_restrict_iff' hO.measurableSet).mp he⟩

lemma local_sobolev_translate {u : ℂ → ℝ} {m : ℂ → ℂ}
    (hu : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → SobolevOn u m S) (t : ℂ)
    {U : Set ℂ} (hU : IsOpen U) (hb : Bornology.IsBounded U) :
    SobolevOn (fun x => u (x-t)) (fun x => m (x-t)) U := by
  let S := (fun x : ℂ => x+t) ⁻¹' U
  have hs : IsOpen S := hU.preimage (continuous_id.add continuous_const)
  have heq : S = (fun x : ℂ => x-t) '' U := by
    ext x
    constructor
    · intro hx
      exact ⟨x+t,hx,add_sub_cancel_right _ _⟩
    · rintro ⟨y,hy,rfl⟩
      simpa [S] using hy
  have hsb : Bornology.IsBounded S := by
    rw [heq]
    simpa only [sub_eq_add_neg] using (isometry_add_right (-t)).lipschitzWith.isBounded_image hb
  have hd : (fun x : ℂ => x-t) ⁻¹' S = U := by
    ext x
    simp [S]
  simpa only [hd] using (hu S hs hsb).translate hs.measurableSet t

def translatedCompetitor (B A : Set ℂ) (f h k φ ψ : ℂ → ℝ)
    (G e d w z : ℂ → ℂ) (η : ℂ → ℝ) (t : ℂ) (σ : ℝ) : Pair where
  K := B ∪ (fun x => x+t) '' A
  u x := f x+h (x-t)+σ*k (x-t)-φ x -
    η x*(φ (x-t)+σ*ψ (x-t)-φ x)
  grad x := G x+e (x-t)+σ • d (x-t)-w x -
    (η x • (w (x-t)+σ • z (x-t)-w x) +
      (φ (x-t)+σ*ψ (x-t)-φ x) • gradient η x)

lemma translated_competitor_sobolev {A B U : Set ℂ}
    (hA : IsClosed A) (hU : IsOpen U) (hb : Bornology.IsBounded U)
    {f h k φ ψ : ℂ → ℝ} {G e d w z : ℂ → ℂ}
    (hf : SobolevOn f G (U \ B)) (hh : SobolevOn h e Aᶜ) (hk : SobolevOn k d Aᶜ)
    (hφ : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → SobolevOn φ w S)
    (hψ : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → SobolevOn ψ z S)
    {η : ℂ → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (t : ℂ) (σ : ℝ) :
    SobolevOn (translatedCompetitor B A f h k φ ψ G e d w z η t σ).u
      (translatedCompetitor B A f h k φ ψ G e d w z η t σ).grad
      (U \ (translatedCompetitor B A f h k φ ψ G e d w z η t σ).K) := by
  let J := B ∪ (fun x => x+t) '' A
  have hsub : U \ J ⊆ U \ B := fun x hx => ⟨hx.1,fun h => hx.2 (Or.inl h)⟩
  have hat : U \ J ⊆ (fun x => x-t) ⁻¹' Aᶜ := by
    intro x hx ha
    exact hx.2 (Or.inr ⟨x-t,ha,sub_add_cancel _ _⟩)
  have hhT := (hh.translate hA.measurableSet.compl t).mono hat
  have hkT := (hk.translate hA.measurableSet.compl t).mono hat
  have hφT := (local_sobolev_translate hφ t hU hb).mono (sdiff_subset (t := J))
  have hψT := (local_sobolev_translate hψ t hU hb).mono (sdiff_subset (t := J))
  have hφU := (hφ U hU hb).mono (sdiff_subset (t := J))
  exact ((((hf.mono hsub).add hhT).add (hkT.const_smul σ)).sub hφU).sub
    (((hφT.add (hψT.const_smul σ)).sub hφU).mul_smooth hη hc)

lemma compact_piece_length_finite {H A : Set ℂ}
    (hH : ∀ R : ℝ, 0 < R → lengthMeasure (H ∩ ball (0:ℂ) R) < ⊤)
    (hA : IsCompact A) (ha : A ⊆ H) : lengthMeasure A < ⊤ := by
  obtain ⟨R,hR,hb⟩ := hA.isBounded.exists_pos_norm_lt
  apply lt_of_le_of_lt (measure_mono (t := H ∩ ball (0:ℂ) R) ?_) (hH R hR)
  intro x hx
  exact ⟨ha hx,by simpa using hb x hx⟩

theorem translated_competitor_admissible {p : Pair} (hp : GlobalAdmissible p)
    {A B : Set ℂ} (hA : IsCompact A) (hB : IsClosed B) (hH : p.K = A ∪ B)
    {f h k φ ψ : ℂ → ℝ} {G e d w z : ℂ → ℂ}
    (hf : ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U → SobolevOn f G (U \ B))
    (hh : SobolevOn h e Aᶜ) (hk : SobolevOn k d Aᶜ)
    (hφ : ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U → SobolevOn φ w U)
    (hψ : ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U → SobolevOn ψ z U)
    {η : ℂ → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (t : ℂ) (σ : ℝ) :
    GlobalAdmissible (translatedCompetitor B A f h k φ ψ G e d w z η t σ) := by
  have ha : A ⊆ p.K := by rw [hH]; exact subset_union_left
  have hb : B ⊆ p.K := by rw [hH]; exact subset_union_right
  have hAl : lengthMeasure A < ⊤ := compact_piece_length_finite hp.2.2.1 hA ha
  refine ⟨hB.union ((hA.image (continuous_id.add continuous_const)).isClosed),
    (hp.2.1.mono hb).union ((hp.2.1.mono ha).translate t),?_,?_⟩
  · intro R hR
    change lengthMeasure ((B ∪ (fun x => x+t) '' A) ∩ ball 0 R) < ⊤
    rw [union_inter_distrib_right]
    apply lt_of_le_of_lt (measure_union_le _ _)
    apply ENNReal.add_lt_top.mpr
    constructor
    · exact lt_of_le_of_lt (measure_mono (inter_subset_inter_left _ hb)) (hp.2.2.1 R hR)
    · apply lt_of_le_of_lt (measure_mono inter_subset_left)
      rwa [translated_length]
  · intro U hU hbU
    exact translated_competitor_sobolev hA.isClosed hU hbU (hf U hU hbU) hh hk hφ hψ hη hc t σ

lemma essentialSupport_subset_closed_of_ae_zero {u : ℂ → ℝ} {S : Set ℂ}
    (hS : IsClosed S) (hu : ∀ᵐ x ∂volume, x ∉ S → u x = 0) :
    essentialSupport u ⊆ S := by
  intro x hx
  by_contra hxn
  obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp hS.isOpen_compl x hxn
  apply hx r hr
  apply (ae_restrict_iff' isOpen_ball.measurableSet).mpr
  filter_upwards [hu] with y hy hyr
  exact hy (hsub hyr)

lemma ae_zero_outside_essentialSupport (u : ℂ → ℝ) :
    ∀ᵐ x ∂volume, x ∉ essentialSupport u → u x = 0 := by
  exact (ae_restrict_iff' (isClosed_essentialSupport u).measurableSet.compl).mp
    (ae_zero_compl_essentialSupport u)

lemma translated_competitor_compact_comparison {p : Pair}
    {A B S V : Set ℂ} (hH : p.K = A ∪ B) (hS : IsCompact S) (hSV : S ⊆ V)
    {f h k φ ψ : ℂ → ℝ} {G e d w z : ℂ → ℂ} {η : ℂ → ℝ} {t : ℂ} {σ : ℝ}
    (heq : p.u =ᵐ[volume] fun x => f x+h x-φ x)
    (hA : A ⊆ S) (hAt : (fun x => x+t) '' A ⊆ S)
    (hh : essentialSupport h ⊆ S)
    (hhT : (fun x => x+t) '' essentialSupport h ⊆ S)
    (hkT : (fun x => x+t) '' essentialSupport k ⊆ S) (hη : tsupport η ⊆ S) :
    IsCompactComparison p (translatedCompetitor B A f h k φ ψ G e d w z η t σ) V := by
  have hhs := ae_zero_outside_essentialSupport h
  have hks := ae_zero_outside_essentialSupport k
  have hmeasure := measurePreserving_sub_right (volume : Measure ℂ) t
  have hht := hmeasure.quasiMeasurePreserving.ae hhs
  have hkt := hmeasure.quasiMeasurePreserving.ae hks
  have hchange : essentialSupport (fun x =>
      (translatedCompetitor B A f h k φ ψ G e d w z η t σ).u x-p.u x) ⊆ S := by
    apply essentialSupport_subset_closed_of_ae_zero hS.isClosed
    filter_upwards [heq,hhs,hht,hkt] with x hx hhx hhtx hktx hxn
    have hh0 : h x = 0 := hhx (fun hn => hxn (hh hn))
    have hhT0 : h (x-t) = 0 := hhtx (fun hn => hxn (hhT ⟨x-t,hn,sub_add_cancel _ _⟩))
    have hkT0 : k (x-t) = 0 := hktx (fun hn => hxn (hkT ⟨x-t,hn,sub_add_cancel _ _⟩))
    have hη0 : η x = 0 := image_eq_zero_of_notMem_tsupport (fun hn => hxn (hη hn))
    simp only [translatedCompetitor, hx, hh0, hhT0, hkT0, hη0]
    ring
  have hsets : (translatedCompetitor B A f h k φ ψ G e d w z η t σ).K ∆ p.K ⊆ S := by
    rw [hH]
    intro x hx
    rcases hx with ⟨hx,hn⟩ | ⟨hx,hn⟩
    · rcases hx with hb | ha
      · exact False.elim (hn (Or.inr hb))
      · exact hAt ha
    · rcases hx with ha | hb
      · exact hA ha
      · exact False.elim (hn (Or.inl hb))
  have hcsub : closure ((translatedCompetitor B A f h k φ ψ G e d w z η t σ).K ∆ p.K ∪
      essentialSupport (fun x => (translatedCompetitor B A f h k φ ψ G e d w z η t σ).u x-p.u x)) ⊆ S :=
    closure_minimal (union_subset hsets hchange) hS.isClosed
  exact ⟨hS.of_isClosed_subset isClosed_closure hcsub,hcsub.trans hSV⟩

lemma translated_length_cancel {A B V : Set ℂ} (hA : IsCompact A)
    (hAB : Disjoint A B) {t : ℂ} (hAtB : Disjoint ((fun x => x+t) '' A) B)
    (hAV : A ⊆ V) (hAtV : (fun x => x+t) '' A ⊆ V) :
    lengthMeasure ((B ∪ (fun x => x+t) '' A) ∩ V) = lengthMeasure ((A ∪ B) ∩ V) := by
  rw [union_inter_distrib_right, inter_eq_left.mpr hAtV,
    measure_union (hAtB.symm.mono_left inter_subset_left)
      (hA.image (continuous_id.add continuous_const)).isClosed.measurableSet,
    translated_length, union_inter_distrib_right, inter_eq_left.mpr hAV,
    union_comm, measure_union (hAB.symm.mono_left inter_subset_left) hA.isClosed.measurableSet]

lemma global_minimizer_equal_length_energy {p q : Pair} (hp : GlobalAbsoluteMinimizer p)
    (hq : GlobalAdmissible q) {R : ℝ} (hR : 0 < R)
    (hc : IsCompactComparison p q (ball 0 R))
    (hlen : lengthMeasure (q.K ∩ ball 0 R) = lengthMeasure (p.K ∩ ball 0 R)) :
    (∫ x in ball (0:ℂ) R, ‖p.grad x‖^2) ≤ ∫ x in ball (0:ℂ) R, ‖q.grad x‖^2 := by
  have hpμ := restrict_diff_null_set (U := ball (0:ℂ) R)
    (volume_eq_zero_of_locally_finite_length hp.1.2.2.1)
  have hqμ := restrict_diff_null_set (U := ball (0:ℂ) R)
    (volume_eq_zero_of_locally_finite_length hq.2.2.1)
  have hpl : MemLp p.grad 2 (volume.restrict (ball (0:ℂ) R)) := by
    rw [← hpμ]; exact (hp.1.2.2.2 _ isOpen_ball isBounded_ball).2.1
  have hql : MemLp q.grad 2 (volume.restrict (ball (0:ℂ) R)) := by
    rw [← hqμ]; exact (hq.2.2.2 _ isOpen_ball isBounded_ball).2.1
  have hpi := hpl.integrable_norm_pow (show 2 ≠ 0 by norm_num)
  have hqi := hql.integrable_norm_pow (show 2 ≠ 0 by norm_num)
  have hcomp := hp.2 (ball 0 R) isOpen_ball isBounded_ball q hq hc
  change (_+lengthMeasure (p.K ∩ ball 0 R)) ≤ (_+lengthMeasure (q.K ∩ ball 0 R)) at hcomp
  rw [hlen] at hcomp
  have he := (ENNReal.add_le_add_iff_right (hp.1.2.2.1 R hR).ne).mp hcomp
  rw [hpμ,hqμ,← ofReal_integral_eq_lintegral_ofReal hpi (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hqi (Filter.Eventually.of_forall (fun _ => sq_nonneg _))] at he
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun _ => sq_nonneg _))).mp he

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff

theorem translated_comparison_limit {v : Pair} (hv : GlobalAbsoluteMinimizer v)
    {A B : Set ℂ} (hA : IsCompact A) (hB : IsClosed B) (hH : v.K = A ∪ B)
    (hAB : Disjoint A B) {t : ℂ} (hAtB : Disjoint ((fun x => x+t) '' A) B)
    {f h k φ ψ : ℂ → ℝ} {G e d w z : ℂ → ℂ} (σ : ℝ)
    (hf : ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U → SobolevOn f G (U \ B))
    (hh : SobolevOn h e Aᶜ) (hk : SobolevOn k d Aᶜ)
    (hhc : IsCompact (essentialSupport h)) (hkc : IsCompact (essentialSupport k))
    (hφ : ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U → SobolevOn φ w U)
    (hψ : ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U → SobolevOn ψ z U)
    (heq : v.u =ᵐ[volume] fun x => f x+h x-φ x)
    (hgeq : v.grad =ᵐ[volume] fun x => G x+(e x-w x))
    (hp : MemLp (fun x => e x-w x) 2 volume)
    (hq : MemLp (fun x => (e (x-t)-w (x-t))+σ • (d (x-t)-z (x-t))) 2 volume)
    (hip : Integrable (fun x => inner ℝ (G x) (e x-w x)) volume)
    (hiq : Integrable (fun x => inner ℝ (G x) ((e (x-t)-w (x-t))+σ • (d (x-t)-z (x-t)))) volume)
    {C D R : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hR : 1 ≤ R)
    (hgrowth : ∀ T : ℝ, 1 ≤ T → (∫ x in ball (0:ℂ) T, ‖G x‖^2) ≤ C*(1+T))
    (haD : ∀ᵐ x ∂volume, R ≤ ‖x‖ → |φ x-φ (x-t)-σ*ψ (x-t)| ≤ D/‖x‖) :
    0 ≤ 2*((∫ x : ℂ, inner ℝ (G x) ((e (x-t)-w (x-t))+σ • (d (x-t)-z (x-t))))-
      (∫ x : ℂ, inner ℝ (G x) (e x-w x)))+
      (∫ x : ℂ, ‖(e (x-t)-w (x-t))+σ • (d (x-t)-z (x-t))‖^2)-
      (∫ x : ℂ, ‖e x-w x‖^2) := by
  have hH0 := volume_eq_zero_of_locally_finite_length hv.1.2.2.1
  have hB0 : volume B = 0 := measure_mono_null (by rw [hH]; exact subset_union_right) hH0
  have hG : ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U → MemLp G 2 (volume.restrict U) := by
    intro U hU hb
    have hGU := (hf U hU hb).2.1
    rwa [restrict_diff_null_set hB0] at hGU
  have ha : ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U →
      MemLp (fun x => φ x-φ (x-t)-σ*ψ (x-t)) 2 (volume.restrict U) := by
    intro U hU hb
    exact (((hφ U hU hb).sub (local_sobolev_translate hφ t hU hb)).sub
      ((local_sobolev_translate hψ t hU hb).const_smul σ)).1
  obtain ⟨Re,hRe,he⟩ := compact_support_weak_gradient hA hh hhc
  obtain ⟨Rd,hRd,hd⟩ := compact_support_weak_gradient hA hk hkc
  let R' := max R (max (Re+‖t‖+1) (Rd+‖t‖+1))
  have hRR : R ≤ R' := le_max_left _ _
  have hR' : 1 ≤ R' := hR.trans hRR
  have heR : Re+‖t‖+1 ≤ R' := (le_max_left _ _).trans (le_max_right _ _)
  have hdR : Rd+‖t‖+1 ≤ R' := (le_max_right _ _).trans (le_max_right _ _)
  have haD' : ∀ᵐ x ∂volume, R' ≤ ‖x‖ → |φ x-φ (x-t)-σ*ψ (x-t)| ≤ D/‖x‖ :=
    haD.mono (fun x hx hxx => hx (hRR.trans hxx))
  obtain ⟨χ,M,hM,hχ,hfamily⟩ := exists_scaled_cutoff_family
  let r (n : ℕ) := (4:ℝ)^n*R'
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hRr (n : ℕ) : R' ≤ r n := by
    dsimp [r]
    exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 4))
  let η (n : ℕ) := scaledCutoff χ (r n)
  have hη (n : ℕ) := hfamily (r n) (hr n)
  have hηs (n : ℕ) : ContDiff ℝ ∞ (η n) := scaledCutoff_smooth hχ _
  let p := fun x => e x-w x
  let q := fun x => (e (x-t)-w (x-t))+σ • (d (x-t)-z (x-t))
  let a := fun x => φ x-φ (x-t)-σ*ψ (x-t)
  let rn (n : ℕ) (x : ℂ) := (1-η n x) • p x+η n x • q x+a x • gradient (η n) x
  obtain ⟨hrn,hlim⟩ := cutoff_field_tendsto_L2 hp hq ha hD hR' haD' hM hηs
    (fun n => (hη n).1) (fun n => (hη n).2.1) (fun n => (hη n).2.2.1)
    (fun n => (hη n).2.2.2.1) (fun n => (hη n).2.2.2.2.1)
  obtain ⟨hri,hlimi⟩ := cutoff_field_interaction_limit hip hiq ha hG hC hD hR' hgrowth haD' hM hηs
    (fun n => (hη n).1) (fun n => (hη n).2.1) (fun n => (hη n).2.2.1)
    (fun n => (hη n).2.2.2.1) (fun n => (hη n).2.2.2.2.1)
  apply finite_energy_limit_inequality hp hq hrn hlim (fun T => hG _ isOpen_ball isBounded_ball) hip hri hlimi
  intro n
  let c := translatedCompetitor B A f h k φ ψ G e d w z (η n) t σ
  have hca : GlobalAdmissible c := translated_competitor_admissible hv.1 hA hB hH hf hh hk hφ hψ (hηs n) (hη n).1 t σ
  have hcg : c.grad =ᵐ[volume] fun x => G x+rn n x := by
    have hem := (measurePreserving_sub_right (volume : Measure ℂ) t).quasiMeasurePreserving.ae he
    have hdm := (measurePreserving_sub_right (volume : Measure ℂ) t).quasiMeasurePreserving.ae hd
    filter_upwards [he,hem,hdm] with x hex hetx hdtx
    dsimp [c,translatedCompetitor,rn,p,q,a]
    by_cases hx : η n x = 1
    · rw [hx]; simp only [Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_one]; ring
    · have hxr : r n < ‖x‖ := lt_of_not_ge (fun hn => hx ((hη n).2.2.1 x hn))
      have hxt := norm_le_norm_sub_add x t
      have he0 : e x = 0 := hex (by linarith [hRr n,norm_nonneg t])
      have het0 : e (x-t) = 0 := hetx (by linarith [hRr n])
      have hdt0 : d (x-t) = 0 := hdtx (by linarith [hRr n])
      rw [he0,het0,hdt0]; simp only [Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_one]; ring
  let S := A ∪ ((fun x => x+t) '' A) ∪ essentialSupport h ∪
    ((fun x => x+t) '' essentialSupport h) ∪ ((fun x => x+t) '' essentialSupport k) ∪ tsupport (η n)
  have hS : IsCompact S := (((((hA.union (hA.image (continuous_id.add continuous_const))).union hhc).union
    (hhc.image (continuous_id.add continuous_const))).union (hkc.image (continuous_id.add continuous_const))).union (hη n).1)
  obtain ⟨T,hT,hST⟩ := hS.isBounded.exists_pos_norm_lt
  have hSV : S ⊆ ball (0:ℂ) T := fun x hx => by simpa using hST x hx
  have hAS : A ⊆ S := by intro x hx; simp only [S,mem_union]; tauto
  have hAtS : (fun x => x+t) '' A ⊆ S := by intro x hx; simp only [S,mem_union]; tauto
  have hhS : essentialSupport h ⊆ S := by intro x hx; simp only [S,mem_union]; tauto
  have hhtS : (fun x => x+t) '' essentialSupport h ⊆ S := by intro x hx; simp only [S,mem_union]; tauto
  have hktS : (fun x => x+t) '' essentialSupport k ⊆ S := by intro x hx; simp only [S,mem_union]; tauto
  have hηS : tsupport (η n) ⊆ S := by intro x hx; simp only [S,mem_union]; tauto
  have hcc : IsCompactComparison v c (ball 0 T) := translated_competitor_compact_comparison hH hS hSV
    heq hAS hAtS hhS hhtS hktS hηS
  have hlen : lengthMeasure (c.K ∩ ball 0 T) = lengthMeasure (v.K ∩ ball 0 T) := by
    rw [hH]; exact translated_length_cancel hA hAB hAtB (hAS.trans hSV) (hAtS.trans hSV)
  refine ⟨T,?_,?_⟩
  · filter_upwards with x hx
    have hxn : x ∉ tsupport (η n) := fun hn => hx (hSV (hηS hn))
    have hz := image_eq_zero_of_notMem_tsupport hxn
    have hgz : gradient (η n) x = 0 := by rw [gradient,fderiv_of_notMem_tsupport ℝ hxn,map_zero]
    dsimp [rn]
    rw [hz,hgz]; simp
  · have hcomp := global_minimizer_equal_length_energy hv hca hT hcc hlen
    convert hcomp using 1
    · apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hgeq] with x hx
      rw [hx]
    · apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hcg] with x hx
      rw [hx]

end MumfordShah
end

end OAI
