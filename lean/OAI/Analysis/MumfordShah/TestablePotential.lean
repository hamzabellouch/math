import Mathlib
import OAI.Analysis.MumfordShah.LocalPotential

namespace OAI

/-! MumfordShah testable potential. -/

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

lemma local_memLp_on_bounded {E : Type*} [NormedAddCommGroup E] {G : ℂ → E}
    (hG : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → MemLp G 2 (volume.restrict S))
    {S : Set ℂ} (hS : Bornology.IsBounded S) : MemLp G 2 (volume.restrict S) := by
  obtain ⟨R,hR⟩ := hS.subset_ball (0 : ℂ)
  exact (hG _ isOpen_ball isBounded_ball).mono_measure (Measure.restrict_mono hR le_rfl)

lemma memLp_local_test_smul {G : ℂ → ℂ}
    (hG : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → MemLp G 2 (volume.restrict S))
    {χ : ℂ → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    MemLp (fun x => χ x • G x) 2 volume := by
  have hGi : MemLp ((tsupport χ).indicator G) 2 volume :=
    (memLp_indicator_iff_restrict (isClosed_tsupport χ).measurableSet).mpr
      (local_memLp_on_bounded hG hc.isBounded)
  have hh : MemLp χ ∞ volume := hχ.memLp_of_hasCompactSupport hc
  have hm : MemLp (χ • (tsupport χ).indicator G) 2 volume := hh.smul hGi
  apply hm.ae_eq
  filter_upwards with x
  by_cases hx : x ∈ tsupport χ
  · simp [hx]
  · simp [hx, image_eq_zero_of_notMem_tsupport hx]

lemma memLp_inner_test {G d : ℂ → ℂ} {μ : Measure ℂ}
    (hG : MemLp G 2 μ) (hd : MemLp d ∞ μ) :
    MemLp (fun x => inner ℝ (G x) (d x)) 2 μ := by
  have hb : MemLp (fun x => ‖G x‖ * ‖d x‖) 2 μ := by
    simpa only [mul_comm] using hG.norm.fun_mul (r := 2) hd.norm
  apply hb.mono' (hG.aestronglyMeasurable.inner hd.aestronglyMeasurable)
  exact Eventually.of_forall (fun x => norm_inner_le_norm (G x) (d x))

lemma integrable_inner_memLp_measure {μ : Measure ℂ} {a b : ℂ → ℂ}
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    Integrable (fun x => inner ℝ (a x) (b x)) μ := by
  have h := L2.integrable_inner (𝕜 := ℝ) (ha.toLp a) (hb.toLp b)
  apply h.congr
  filter_upwards [ha.coeFn_toLp,hb.coeFn_toLp] with x hx hy
  rw [hx,hy]

lemma gradient_mul_smooth {f g : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (x : ℂ) :
    gradient (f * g) x = f x • gradient g x + g x • gradient f x := by
  simp only [gradient, fderiv_mul (hf.differentiable (by norm_num) x)
    (hg.differentiable (by norm_num) x), map_add, map_smul]

def CompactDivergenceTestable (φ : ℂ → ℝ) (w : PlaneL2) : Prop :=
  ∀ G : ℂ → ℂ,
    (∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → MemLp G 2 (volume.restrict S)) →
    (∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : ℂ, inner ℝ (G x) (gradient ψ x)) = 0) →
    ∀ χ : ℂ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      (∫ x : ℂ, χ x * inner ℝ (G x) (w x)) =
        -(∫ x : ℂ, φ x * inner ℝ (G x) (gradient χ x))

lemma compact_divergence_testable_of_approximation
    {u : ℕ → ℂ → ℝ} (hu : ∀ k, ContDiff ℝ ∞ (u k))
    {q : ℕ → PlaneL2} (hq : ∀ k, (q k : ℂ → ℂ) =ᵐ[volume] gradient (u k))
    {w : PlaneL2} (hlim : Tendsto q atTop (𝓝 w))
    {U : (n : ℕ) → Lp ℝ 2 (volume.restrict (complexSquare (n+1 : ℝ)))}
    (hU : ∀ n : ℕ, Tendsto (fun k => smoothPotentialLp (hu k).continuous (n+1 : ℝ)) atTop (𝓝 (U n)))
    {φ : ℂ → ℝ} (hφ : ∀ n : ℕ, φ =ᵐ[volume.restrict (complexSquare (n+1 : ℝ))] U n) :
    CompactDivergenceTestable φ w := by
  intro G hG hdiv χ hχ hc
  obtain ⟨n,hn⟩ := bounded_subset_complexSquare hc.isBounded
  let S := complexSquare (n+1 : ℝ)
  let μ := volume.restrict S
  have hgs : MemLp G 2 μ := local_memLp_on_bounded hG (isCompact_complexSquare _).isBounded
  have hχG := memLp_local_test_smul hG hχ.continuous hc
  let a : PlaneL2 := hχG.toLp (fun x => χ x • G x)
  have hd : MemLp (fun x => inner ℝ (G x) (gradient χ x)) 2 μ :=
    memLp_inner_test hgs ((continuous_gradient_of_smooth hχ).memLp_of_hasCompactSupport
      (compactSupport_gradient hc))
  let b : Lp ℝ 2 μ := hd.toLp (fun x => inner ℝ (G x) (gradient χ x))
  have hleft := (tendsto_const_nhds (x := a)).inner hlim (𝕜 := ℝ)
  have hright := ((hU n).inner (tendsto_const_nhds (x := b)) (𝕜 := ℝ)).neg
  have hgrad (k : ℕ) : gradient (normalizedPotential (u k)) = gradient (u k) := by
    funext x
    change (toDual ℝ ℂ).symm (fderiv ℝ (fun y => u k y - unitMean (u k)) x) = _
    rw [fderiv_sub_const]
    rfl
  have hsmooth (k : ℕ) : ContDiff ℝ ∞ (normalizedPotential (u k)) := (hu k).sub contDiff_const
  have hzero (x : ℂ) (hx : x ∉ S) : gradient χ x = 0 := by
    simp [gradient, fderiv_of_notMem_tsupport ℝ (fun ht => hx (hn ht))]
  have heq (k : ℕ) : inner ℝ a (q k) = -inner ℝ (smoothPotentialLp (hu k).continuous (n+1 : ℝ)) b := by
    have hl : inner ℝ a (q k) = ∫ x : ℂ, χ x * inner ℝ (G x) (gradient (u k) x) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hχG.coeFn_toLp, hq k] with x hx hy
      rw [hx,hy,real_inner_smul_left]
    have hr : inner ℝ (smoothPotentialLp (hu k).continuous (n+1 : ℝ)) b =
        ∫ x : ℂ, normalizedPotential (u k) x * inner ℝ (G x) (gradient χ x) := by
      rw [lp_inner_real_test _ hd]
      change (∫ x in S, (smoothPotentialLp (hu k).continuous (n+1 : ℝ)) x * _) = _
      rw [show (∫ x in S, (smoothPotentialLp (hu k).continuous (n+1 : ℝ)) x *
          inner ℝ (G x) (gradient χ x)) =
          ∫ x in S, normalizedPotential (u k) x * inner ℝ (G x) (gradient χ x) from
        integral_congr_ae (by
          filter_upwards [(memLp_normalizedPotential (hu k).continuous _).coeFn_toLp] with x hx
          change (smoothPotentialLp (hu k).continuous (n+1 : ℝ)) x = _ at hx
          rw [hx])]
      exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hzero x hx])
    rw [hl,hr]
    have hid := hdiv (χ * normalizedPotential (u k)) (hχ.mul (hsmooth k)) hc.mul_right
    simp_rw [gradient_mul_smooth hχ (hsmooth k),hgrad k,inner_add_right,
      real_inner_smul_right] at hid
    have hi := integrable_inner_memLp_measure hχG (Lp.memLp (q k))
    have hi' : Integrable (fun x => χ x * inner ℝ (G x) (gradient (u k) x)) volume := by
      apply hi.congr
      filter_upwards [hq k] with x hx
      rw [hx,real_inner_smul_left]
    have hj : Integrable (fun x => normalizedPotential (u k) x * inner ℝ (G x) (gradient χ x)) volume := by
      apply IntegrableOn.integrable_of_forall_notMem_eq_zero (s := S)
      · exact (memLp_normalizedPotential (hu k).continuous _).integrable_mul hd
      · intro x hx
        simp [hzero x hx]
    rw [integral_add hi' hj] at hid
    linarith
  have hfinal := tendsto_nhds_unique (by simpa only [heq] using hleft) hright
  have hl : inner ℝ a w = ∫ x : ℂ, χ x * inner ℝ (G x) (w x) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hχG.coeFn_toLp] with x hx
    rw [hx,real_inner_smul_left]
  have hr : inner ℝ (U n) b = ∫ x : ℂ, φ x * inner ℝ (G x) (gradient χ x) := by
    rw [lp_inner_real_test _ hd]
    change (∫ x in S, U n x * _) = _
    rw [show (∫ x in S, U n x * inner ℝ (G x) (gradient χ x)) =
        ∫ x in S, φ x * inner ℝ (G x) (gradient χ x) from
      integral_congr_ae (by filter_upwards [hφ n] with x hx; rw [hx])]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hzero x hx])
  rwa [hl,hr] at hfinal

theorem gradient_closure_has_testable_local_potential {w : PlaneL2}
    (hw : w ∈ compactGradientClosure) :
    ∃ φ : ℂ → ℝ, CompactDivergenceTestable φ w ∧
      ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → SobolevOn φ w S := by
  obtain ⟨u, q, hu, _huc, hq, hlim⟩ := gradient_closure_approximation hw
  have hex : ∀ n : ℕ, ∃ U : Lp ℝ 2 (volume.restrict (complexSquare (n + 1 : ℝ))),
      Tendsto (fun k => smoothPotentialLp (hu k).continuous (n + 1 : ℝ)) atTop (𝓝 U) :=
    fun n => exists_localLp_limit_of_gradient_limit hu hq hlim (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  choose U hU using hex
  have hcompat : ∀ n m (h : n ≤ m),
      restrictLp (complexSquare_mono (by exact_mod_cast Nat.add_le_add_right h 1)) (U m) = U n := by
    intro n m hnm
    exact localLp_limits_compatible (fun k => (hu k).continuous)
      (by exact_mod_cast Nat.add_le_add_right hnm 1) (hU n) (hU m)
  obtain ⟨φ, hφ⟩ := glue_localLp U hcompat
  refine ⟨φ, compact_divergence_testable_of_approximation hu hq hlim hU hφ,
    fun S _hSo hSb => ?_⟩
  obtain ⟨n, hn⟩ := bounded_subset_complexSquare hSb
  have hφLp : MemLp φ 2 (volume.restrict (complexSquare (n + 1 : ℝ))) :=
    (memLp_congr_ae (hφ n)).mpr (Lp.memLp (U n))
  refine ⟨hφLp.mono_measure (Measure.restrict_mono hn (le_refl volume)),
    (Lp.memLp w).restrict S, ?_⟩
  intro ψ hψ hψc hψS a
  have hψR : tsupport ψ ⊆ complexSquare (n + 1 : ℝ) := hψS.trans hn
  have hd0 (T : Set ℂ) (hT : tsupport ψ ⊆ T) :
      ∀ x, x ∉ T → φ x * fderiv ℝ ψ x a = 0 := by
    intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hT h))]
    simp
  calc
    (∫ x in S, φ x * fderiv ℝ ψ x a) = ∫ x : ℂ, φ x * fderiv ℝ ψ x a :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (hd0 S hψS)
    _ = ∫ x in complexSquare (n + 1 : ℝ), φ x * fderiv ℝ ψ x a :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (hd0 _ hψR)).symm
    _ = ∫ x in complexSquare (n + 1 : ℝ), U n x * fderiv ℝ ψ x a := by
      apply integral_congr_ae
      filter_upwards [hφ n] with x hx
      rw [hx]
    _ = -(∫ x : ℂ, inner ℝ (w x) a * ψ x) :=
      localLp_limit_weak_gradient hu hq hlim (hU n) hψ hψc hψR a
    _ = -(∫ x in S, inner ℝ (w x) a * ψ x) := by
      congr 1
      apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hψS h)), mul_zero]

lemma CompactDivergenceTestable.congr_ae {φ v : ℂ → ℝ} {w : PlaneL2}
    (h : CompactDivergenceTestable φ w) (hv : φ =ᵐ[volume] v) :
    CompactDivergenceTestable v w := by
  intro G hG hd χ hs hc
  rw [h G hG hd χ hs hc]
  congr 1
  apply integral_congr_ae
  filter_upwards [hv] with x hx
  rw [hx]

lemma CompactDivergenceTestable.sub_const {φ : ℂ → ℝ} {w : PlaneL2}
    (h : CompactDivergenceTestable φ w)
    (hφ : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → MemLp φ 2 (volume.restrict S))
    (c : ℝ) : CompactDivergenceTestable (fun x => φ x - c) w := by
  intro G hG hd χ hs hc
  rw [h G hG hd χ hs hc]
  congr 1
  have hφgrad : Integrable (fun x => φ x * inner ℝ (G x) (gradient χ x)) volume := by
    let S := tsupport χ
    have hS : Bornology.IsBounded S := hc.isBounded
    have hGi := local_memLp_on_bounded hG hS
    have hdG := memLp_inner_test hGi
      ((continuous_gradient_of_smooth hs).memLp_of_hasCompactSupport (compactSupport_gradient hc))
    apply IntegrableOn.integrable_of_forall_notMem_eq_zero (s := S)
    · exact (local_memLp_on_bounded hφ hS).integrable_mul hdG
    · intro x hx
      simp [gradient, fderiv_of_notMem_tsupport ℝ hx]
  have hgrad : Integrable (fun x => inner ℝ (G x) (gradient χ x)) volume := by
    
    let S := tsupport χ
    apply IntegrableOn.integrable_of_forall_notMem_eq_zero (s := S)
    · exact integrable_inner_memLp_measure (local_memLp_on_bounded hG hc.isBounded)
        (((continuous_gradient_of_smooth hs).memLp_of_hasCompactSupport
          (compactSupport_gradient hc)).restrict S)
    · intro x hx
      simp [gradient, fderiv_of_notMem_tsupport ℝ hx]
  simp_rw [sub_mul]
  rw [integral_sub hφgrad (hgrad.const_mul c),integral_const_mul,hd χ hs hc,mul_zero,sub_zero]

end MumfordShah
end

end OAI
