import Mathlib
import OAI.Analysis.MumfordShah.Decomposition

namespace OAI

/-! MumfordShah jump interaction. -/

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
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set Metric Topology InnerProductSpace Complex MeasureTheory
open scoped ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff

open Set MeasureTheory Metric Topology Filter InnerProductSpace

lemma norm_sub_sq_le_two (z w : ℂ) : ‖z-w‖^2 ≤ 2*‖z‖^2+2*‖w‖^2 := by
  have h0 := norm_nonneg (z-w)
  have h := norm_sub_le z w
  have h' := sq_nonneg (‖z‖-‖w‖)
  nlinarith [norm_nonneg z,norm_nonneg w]

lemma subtract_L2_preserves_linear_growth {m q : ℂ → ℂ}
    (hm : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → MemLp m 2 (volume.restrict S))
    (hq : MemLp q 2 volume) {C : ℝ}
    (hg : ∀ R : ℝ, 1 ≤ R → (∫ x in ball (0:ℂ) R, ‖m x‖^2) ≤ C*(1+R)) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ R : ℝ, 1 ≤ R →
      (∫ x in ball (0 : ℂ) R, ‖m x - q x‖^2) ≤ C'*(1+R) := by
  let Q := ∫ x : ℂ, ‖q x‖^2
  have hQ : 0 ≤ Q := integral_nonneg (fun _ => sq_nonneg _)
  refine ⟨2*(|C|+Q+1),by positivity,?_⟩
  intro R hR
  have hmL := hm (ball 0 R) isOpen_ball isBounded_ball
  have hqL := hq.restrict (ball (0:ℂ) R)
  have hi := (hmL.sub hqL).integrable_norm_pow (p := 2) (by norm_num)
  have hj := (hmL.integrable_norm_pow (p := 2) (by norm_num)).const_mul 2
  have hk := (hqL.integrable_norm_pow (p := 2) (by norm_num)).const_mul 2
  have hbound := integral_mono hi (hj.add hk) (fun x => norm_sub_sq_le_two (m x) (q x))
  simp only [Pi.add_apply, Pi.sub_apply] at hbound
  rw [integral_add hj hk,integral_const_mul,integral_const_mul] at hbound
  have hqbound : (∫ x in ball (0:ℂ) R, ‖q x‖^2) ≤ Q :=
    setIntegral_le_integral (hq.integrable_norm_pow (by norm_num))
      (Eventually.of_forall (fun _ => sq_nonneg _))
  have hC := le_abs_self C
  have hCR : C*(1+R) ≤ |C| * (1+R) := mul_le_mul_of_nonneg_right hC (by linarith)
  have hQQ : Q ≤ Q*(1+R) := by nlinarith
  have hn := abs_nonneg C
  nlinarith [hg R hR]

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff

def CompactPotential {e : ℂ → ℂ} (he : MemLp e 2 volume) (φ : ℂ → ℝ) : Prop :=
  (∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U →
    SobolevOn φ (compactGradientProjection (he.toLp e)) U) ∧
  CompactDivergenceTestable φ (compactGradientProjection (he.toLp e)) ∧
  HasInversePowerDecay φ 1 ∧
  HasInversePowerDecay (fun x => compactGradientProjection (he.toLp e) x) 2

lemma compact_potential_exists {A : Set ℂ} (hA : IsCompact A) (hA0 : volume A = 0)
    {h : ℂ → ℝ} {e : ℂ → ℂ} (hh : SobolevOn h e Aᶜ) (hc : IsCompact (essentialSupport h)) :
    ∃ he : MemLp e 2 volume, ∃ φ : ℂ → ℝ, CompactPotential he φ := by
  obtain ⟨he,φ,F,R,hR,hφ,_,_,_,_,_,_,_,hT,hg,hd⟩ := testable_compact_projection_sobolev hA hA0 hh hc
  exact ⟨he,φ,hφ,hT,normalized_potential_decay hd,normalized_potential_gradient_decay hd hg⟩

lemma compact_sobolev_gradient_decay {A : Set ℂ} (hA : IsCompact A)
    {h : ℂ → ℝ} {e : ℂ → ℂ} (hh : SobolevOn h e Aᶜ) (hc : IsCompact (essentialSupport h)) :
    HasInversePowerDecay e 2 := by
  obtain ⟨R,_,he⟩ := compact_support_weak_gradient hA hh hc
  exact hasInversePowerDecay_of_compact_support_ae he 2

theorem minimizer_compact_jump_interactions {v : Pair} (hv : GlobalAbsoluteMinimizer v)
    {A B : Set ℂ} (hA : IsCompact A) (hB : IsClosed B) (hH : v.K = A ∪ B) (hAB : Disjoint A B)
    {f h φ : ℂ → ℝ} {G e : ℂ → ℂ} (he : MemLp e 2 volume)
    (hf : ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U → SobolevOn f G (U \ B))
    (hfh : HarmonicOnNhd f Bᶜ) (hGeq : ∀ᵐ x ∂volume, x ∉ B → G x = gradient f x)
    (hh : SobolevOn h e Aᶜ) (hhc : IsCompact (essentialSupport h)) (hht : essentialSupport h ⊆ Bᶜ)
    (hpot : CompactPotential he φ)
    (heq : v.u =ᵐ[volume] fun x => f x+h x-φ x)
    (hgeq : v.grad =ᵐ[volume] fun x => G x+(e x-compactGradientProjection (he.toLp e) x))
    (hdiv : ∀ η : ℂ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      (∫ x : ℂ, inner ℝ (G x) (gradient η x)) = 0)
    {C : ℝ} (hC : 0 ≤ C)
    (hgrowth : ∀ R : ℝ, 1 ≤ R → (∫ x in ball (0:ℂ) R, ‖G x‖^2) ≤ C*(1+R)) :
    ∃ r : ℝ, 0 < r ∧
      ∀ k : ℂ → ℝ, ∀ d : ℂ → ℂ, SobolevOn k d Aᶜ → IsCompact (essentialSupport k) →
        ∃ hd : MemLp d 2 volume, ∃ ψ : ℂ → ℝ, CompactPotential hd ψ ∧
          ∀ t ∈ ball (0:ℂ) r,
            (∫ x : ℂ, inner ℝ (G x) (d (x-t))) =
              -(∫ x : ℂ, inner ℝ (e x-compactGradientProjection (he.toLp e) x)
                (d x-compactGradientProjection (hd.toLp d) x)) := by
  let w := compactGradientProjection (he.toLp e)
  have hH0 := volume_eq_zero_of_locally_finite_length hv.1.2.2.1
  have hA0 : volume A = 0 := measure_mono_null (by rw [hH]; exact subset_union_left) hH0
  have hB0 : volume B = 0 := measure_mono_null (by rw [hH]; exact subset_union_right) hH0
  have hG : ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U → MemLp G 2 (volume.restrict U) := by
    intro U hU hb
    have h := (hf U hU hb).2.1
    rwa [restrict_diff_null_set hB0] at h
  have heD := compact_sobolev_gradient_decay hA hh hhc
  have hpD := heD.sub hpot.2.2.2
  have hp : MemLp (fun x => e x-w x) 2 volume := he.sub (Lp.memLp w)
  have hK : IsCompact (A ∪ essentialSupport h) := hA.union hhc
  obtain ⟨r,hr,htube⟩ := compact_tube_inside hK hB.isOpen_compl (by
    intro x hx
    rcases hx with hx | hx
    · exact Set.disjoint_left.mp hAB hx
    · exact hht hx)
  have hAtB (t : ℂ) (ht : t ∈ ball (0:ℂ) r) : Disjoint ((fun x => x+t) '' A) B := by
    apply Set.disjoint_left.mpr
    rintro x ⟨y,hy,rfl⟩ hx
    exact htube y (Or.inl hy) t (ball_subset_closedBall ht) hx
  have hrem (t : ℂ) : (∫ x : ℂ, inner ℝ (G x) (e (x-t)-w (x-t))) =
      (∫ x : ℂ, inner ℝ (G x) (e (x-t))) :=
    remove_testable_projection_interaction hpot.2.1 (fun U hU hb => (hpot.1 U hU hb).1)
      hG hdiv he heD hpot.2.2.1 hpot.2.2.2 hC hgrowth t
  have hharm := harmonic_translated_compact_source hK hfh hGeq he
    (weak_gradient_zero_off_compact_support hA hh hhc) htube
  have hIp : HarmonicOnNhd (fun t => ∫ x : ℂ, inner ℝ (G x) (e (x-t)-w (x-t))) (ball (0:ℂ) r) := by
    intro t ht
    exact (harmonicAt_congr_nhds (Eventually.of_forall hrem)).mpr (hharm t ht)
  refine ⟨r,hr,?_⟩
  intro k d hk hkc
  obtain ⟨hd,ψ,hψ⟩ := compact_potential_exists hA hA0 hk hkc
  let z := compactGradientProjection (hd.toLp d)
  have hdD := compact_sobolev_gradient_decay hA hk hkc
  have hqD := hdD.sub hψ.2.2.2
  have hq : MemLp (fun x => d x-z x) 2 volume := hd.sub (Lp.memLp z)
  have hc := translated_energy_forces_constant_interactions (Ip := fun t => ∫ x : ℂ, inner ℝ (G x) (e (x-t)-w (x-t)))
    (Iq := fun t => ∫ x : ℂ, inner ℝ (G x) (d (x-t)-z (x-t)))
    (pq := ∫ x : ℂ, inner ℝ (e x-w x) (d x-z x)) (qq := ∫ x : ℂ, ‖d x-z x‖^2) hr hIp (by
      intro t ht σ
      simpa only [sub_zero] using translated_quadratic_comparison hv hA hB hH hAB (hAtB t ht) σ
        hf hh hk hhc hkc hpot.1 hψ.1 heq hgeq hp hq hpD hqD hpot.2.2.1 hψ.2.2.1 hC hgrowth)
  refine ⟨hd,ψ,hψ,?_⟩
  intro t ht
  have hrem' := remove_testable_projection_interaction hψ.2.1 (fun U hU hb => (hψ.1 U hU hb).1)
    hG hdiv hd hdD hψ.2.2.1 hψ.2.2.2 hC hgrowth t
  exact hrem'.symm.trans (hc.2 t ht)

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff

theorem minimizer_decomposition_with_jump_interactions {v : Pair}
    (hv : GlobalAbsoluteMinimizer v) {A B : Set ℂ}
    (hA : IsCompact A) (hB : IsClosed B) (hAB : Disjoint A B) (hH : v.K = A ∪ B)
    {C : ℝ} (hm : ∀ R : ℝ, 1 ≤ R →
      (∫ x in ball (0:ℂ) R, ‖v.grad x‖^2) ≤ C*(1+R)) :
    ∃ h : ℂ → ℝ, ∃ e : ℂ → ℂ, ∃ he : MemLp e 2 volume,
      ∃ φ f : ℂ → ℝ, ∃ G : ℂ → ℂ, ∃ C' r : ℝ,
      SobolevOn h e Aᶜ ∧ IsCompact (essentialSupport h) ∧ essentialSupport h ⊆ Bᶜ ∧
      CompactPotential he φ ∧ HarmonicOnNhd f Bᶜ ∧
      (∀ᵐ x ∂volume, x ∉ B → G x = gradient f x) ∧
      v.u =ᵐ[volume] (fun x => f x+h x-φ x) ∧
      v.grad =ᵐ[volume] (fun x => G x+(e x-compactGradientProjection (he.toLp e) x)) ∧
      (∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U → MemLp G 2 (volume.restrict U)) ∧
      0 < C' ∧ (∀ R : ℝ, 1 ≤ R → (∫ x in ball (0:ℂ) R, ‖G x‖^2) ≤ C'*(1+R)) ∧
      0 < r ∧ ∀ k : ℂ → ℝ, ∀ d : ℂ → ℂ, SobolevOn k d Aᶜ →
        IsCompact (essentialSupport k) →
        ∃ hd : MemLp d 2 volume, ∃ ψ : ℂ → ℝ, CompactPotential hd ψ ∧
          ∀ t ∈ ball (0:ℂ) r, (∫ x : ℂ, inner ℝ (G x) (d (x-t))) =
            -(∫ x : ℂ, inner ℝ (e x-compactGradientProjection (he.toLp e) x)
              (d x-compactGradientProjection (hd.toLp d) x)) := by
  obtain ⟨h,e,he,φ,F,f,R,hh,hhc,hht,hR,hφ,hFeq,_,_,_,_,_,_,_,hfh,hf,hGeq,heq,hdiv,hT,hφg,hφd⟩ :=
    minimizer_testable_harmonic_decomposition hv hA hB hAB hH
  let G := fun x => v.grad x-compactJumpField (he.toLp e) x
  have hpot : CompactPotential he φ :=
    ⟨hφ,hT,normalized_potential_decay hφd,normalized_potential_gradient_decay hφd hφg⟩
  have hH0 := volume_eq_zero_of_locally_finite_length hv.1.2.2.1
  have hB0 : volume B = 0 := measure_mono_null (by rw [hH]; exact subset_union_right) hH0
  have hmL : ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U → MemLp v.grad 2 (volume.restrict U) := by
    intro U hU hb
    have ht := (hv.1.2.2.2 U hU hb).2.1
    rwa [restrict_diff_null_set hH0] at ht
  have hGL : ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U → MemLp G 2 (volume.restrict U) := by
    intro U hU hb
    exact (hmL U hU hb).sub ((Lp.memLp (compactJumpField (he.toLp e))).restrict U)
  obtain ⟨C',hC',hg⟩ := subtract_L2_preserves_linear_growth hmL
    (Lp.memLp (compactJumpField (he.toLp e))) hm
  have heq' : v.u =ᵐ[volume] (fun x => f x+h x-φ x) := by
    filter_upwards [heq,hFeq] with x hx hy
    simpa only [Pi.add_apply,Pi.sub_apply,hy,add_sub_assoc] using hx
  have hgeq : v.grad =ᵐ[volume] (fun x => G x+(e x-compactGradientProjection (he.toLp e) x)) := by
    filter_upwards [MemLp.coeFn_toLp he, Lp.coeFn_sub (he.toLp e) (compactGradientProjection (he.toLp e))] with x hx hy
    change (he.toLp e) x = e x at hx
    simp only [G,compactJumpField,hy,Pi.sub_apply,hx]
    abel
  obtain ⟨r,hr,htests⟩ := minimizer_compact_jump_interactions hv hA hB hH hAB he hf hfh
    (by filter_upwards [hGeq] with x hx using fun hb => (hx hb).symm)
    hh hhc hht hpot heq' hgeq hdiv hC'.le hg
  exact ⟨h,e,he,φ,f,G,C',r,hh,hhc,hht,hpot,hfh,
    by filter_upwards [hGeq] with x hx using fun hb => (hx hb).symm,
    heq',hgeq,hGL,hC',hg,hr,htests⟩

end MumfordShah
end

end OAI
