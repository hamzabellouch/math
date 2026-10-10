import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Interpolation.CompressionRanks
import OAI.AlgebraicGeometry.Seshadri.Jets.JetVanishing

namespace OAI


                                                    
section
namespace MaximalSeshadri.ActualInterpolation
noncomputable section
open scoped Topology
open Filter
open MaximalSeshadri.AnalyticCoordinates

lemma absolute_of_derivativeSummable {c : Exponent → ℂ} {R : ℝ}
    (h : DerivativeSummable c R) : AbsolutelyConvergentAt c R := by
  have hh := h 0 0
  change Summable (fun e : Exponent => ‖c e‖ *
    ((e.1.descFactorial 0 : ℝ) * R^(e.1-0)) *
    ((e.2.descFactorial 0 : ℝ) * R^(e.2-0))) at hh
  simpa [AbsolutelyConvergentAt, mul_assoc, pow_add] using hh

def seriesValueMap (V : Submodule ℂ (Exponent → ℂ)) (R : ℝ)
    (hs : ∀ c ∈ V, DerivativeSummable c R) (p : ℂ × ℂ)
    (hx : ‖p.1‖ ≤ R) (hz : ‖p.2‖ ≤ R) : V →ₗ[ℂ] ℂ where
  toFun c := seriesEval c p.1 p.2
  map_add' c d := seriesEval_add (absolute_of_derivativeSummable (hs c c.property))
    (absolute_of_derivativeSummable (hs d d.property)) hx hz
  map_smul' a c := by
    change (∑' e : Exponent, (a * (c : Exponent → ℂ) e) * p.1^e.1 * p.2^e.2) =
      a * ∑' e : Exponent, (c : Exponent → ℂ) e * p.1^e.1 * p.2^e.2
    simp only [mul_assoc]
    exact tsum_mul_left

theorem exists_common_representation (V : Submodule ℂ (Exponent → ℂ))
    [FiniteDimensional ℂ V] (φ : V →ₗ[ℂ] (ℂ × ℂ → ℂ)) (R : ℝ) (hR : 0 < R)
    (hs : ∀ c ∈ V, DerivativeSummable c R)
    (hrep : ∀ c : V, φ c =ᶠ[𝓝 0] (fun p => seriesEval c p.1 p.2)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ R ∧ ∀ p : ℂ × ℂ, ‖p‖ < ε →
      ∀ c : V, φ c p = seriesEval c p.1 p.2 := by
  classical
  let b := Module.Basis.ofVectorSpace ℂ V
  have hh : ∀ᶠ p : ℂ × ℂ in 𝓝 0, ∀ i, φ (b i) p = seriesEval (b i) p.1 p.2 :=
    Filter.eventually_all.mpr (fun i => hrep (b i))
  obtain ⟨ε, hε, heq⟩ := Metric.eventually_nhds_iff.mp hh
  refine ⟨min ε R, lt_min hε hR, min_le_right _ _, ?_⟩
  intro p hp c
  have hεp : dist p 0 < ε := by
    simpa only [dist_zero_right] using lt_of_lt_of_le hp (min_le_left _ _)
  have hpR : ‖p‖ < R := lt_of_lt_of_le hp (min_le_right _ _)
  have hx : ‖p.1‖ ≤ R := (norm_fst_le p).trans hpR.le
  have hz : ‖p.2‖ ≤ R := (norm_snd_le p).trans hpR.le
  have hm : (LinearMap.proj p).comp φ = seriesValueMap V R hs p hx hz := by
    apply b.ext
    intro i
    exact heq hεp i
  exact LinearMap.congr_fun hm c

lemma mixedDeriv_congr_on_ball (f g : ℂ × ℂ → ℂ) (ε : ℝ)
    (hfg : ∀ q : ℂ × ℂ, ‖q‖ < ε → f q = g q)
    (p : ℂ × ℂ) (hp : ‖p‖ < ε) (i j : ℕ) :
    iteratedDeriv j (fun z => iteratedDeriv i (fun x => f (x,z)) p.1) p.2 =
      iteratedDeriv j (fun z => iteratedDeriv i (fun x => g (x,z)) p.1) p.2 := by
  have hh : (fun z => f (p + z)) =ᶠ[𝓝 0] (fun z => g (p + z)) := by
    have hn : ∀ᶠ z : ℂ × ℂ in 𝓝 0, ‖p + z‖ < ε := by
      exact (continuous_const.add continuous_id).continuousAt.norm.eventually_lt_const
        (by simpa using hp)
    exact hn.mono (fun z hz => hfg (p + z) hz)
  have hd := mixedDeriv_congr_germ _ _ hh i j
  rw [MaximalSeshadri.AlgebraicJets.mixedDeriv_shift,
    MaximalSeshadri.AlgebraicJets.mixedDeriv_shift] at hd
  exact hd

variable {A M : Type*} [CommRing A] [Algebra ℂ A]
  [AddCommGroup M] [Module ℂ M]

def germCoefficients (coord : M →ₗ[ℂ] A)
    (q : (ℂ × ℂ) → (A →ₐ[ℂ] ℂ))
    (hq : ∀ a, AnalyticAt ℂ (fun z => q z a) 0) : M →ₗ[ℂ] (Exponent → ℂ) :=
  analyticCoefficientLinear.comp ((analyticPullback q hq).toLinearMap.comp coord)

theorem idealPower_test_of_series_test
    (coord : M →ₗ[ℂ] A) (q : (ℂ × ℂ) → (A →ₐ[ℂ] ℂ))
    (hq : ∀ a, AnalyticAt ℂ (fun z => q z a) 0)
    (hinj : Function.Injective (germCoefficients coord q hq))
    [FiniteDimensional ℂ (LinearMap.range (germCoefficients coord q hq))]
    (U : Set (ℂ × ℂ)) (hU : IsOpen U) (h0 : 0 ∈ U) (hqinj : Set.InjOn q U)
    (hqat : ∀ p ∈ U, ∀ a, AnalyticAt ℂ (fun z => q (p + z) a) 0)
    (r m : ℕ) (R : ℝ) (hR : 0 < R)
    (hs : ∀ c ∈ LinearMap.range (germCoefficients coord q hq), DerivativeSummable c R)
    (htest : ∀ ε : ℝ, 0 < ε → ∃ p : Fin r → ℂ × ℂ, Function.Injective p ∧
      (∀ i, ‖(p i).1‖ < min ε R ∧ ‖(p i).2‖ < min ε R) ∧
      Function.Injective (fun c : LinearMap.range (germCoefficients coord q hq) =>
        Interpolation.finiteJetColumn r m p (seriesEval c))) :
    ∃ p : Fin r → A →ₐ[ℂ] ℂ, Function.Injective p ∧
      (∀ i, ∃ z ∈ U, p i = q z) ∧
      ∀ s : M, (∀ i, coord s ∈ (RingHom.ker (p i))^m) → s = 0 := by
  classical
  let C := germCoefficients coord q hq
  let e : M ≃ₗ[ℂ] LinearMap.range C := LinearEquiv.ofInjective C hinj
  let ev : A →ₗ[ℂ] (ℂ × ℂ → ℂ) := LinearMap.pi (fun p => (q p).toLinearMap)
  let φ : LinearMap.range C →ₗ[ℂ] (ℂ × ℂ → ℂ) := ev.comp (coord.comp e.symm.toLinearMap)
  have hrep : ∀ c : LinearMap.range C,
      φ c =ᶠ[𝓝 0] (fun p => seriesEval c p.1 p.2) := by
    intro c
    have hc : C (e.symm c) = (c : Exponent → ℂ) :=
      congrArg Subtype.val (e.apply_symm_apply c)
    have hh := (analyticCoefficients_spec (analyticPullback q hq (coord (e.symm c)))).2
    change (fun p => q p (coord (e.symm c))) =ᶠ[𝓝 0]
      (fun p => seriesEval (C (e.symm c)) p.1 p.2) at hh
    change (fun p => q p (coord (e.symm c))) =ᶠ[𝓝 0] _
    simpa only [hc] using hh
  obtain ⟨ε, hε, _, hεrep⟩ := exists_common_representation
    (LinearMap.range C) φ R hR hs hrep
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  obtain ⟨p, hp, hpn, hpjet⟩ := htest (min ε δ) (lt_min hε hδ)
  have hpe (i : Fin r) : ‖p i‖ < ε := by
    rw [Prod.norm_def]
    exact max_lt ((hpn i).1.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
      ((hpn i).2.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
  have hpU (i : Fin r) : p i ∈ U := by
    apply hδU
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def]
    exact max_lt ((hpn i).1.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
      ((hpn i).2.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  refine ⟨fun i => q (p i), fun i j hij => hp (hqinj (hpU i) (hpU j) hij),
    fun i => ⟨p i, hpU i, rfl⟩, ?_⟩
  intro s hs0
  apply e.injective
  apply hpjet
  funext j
  simp only [Interpolation.finiteJetColumn]
  split_ifs with hj
  · have hd := AlgebraicJets.mixedDeriv_zero_at_of_ideal_power q (p j.1)
      (hqat (p j.1) (hpU j.1)) m (coord s) (hs0 j.1) j.2.1 j.2.2 hj
    have heq := mixedDeriv_congr_on_ball (φ (e s))
      (fun z => seriesEval (e s) z.1 z.2) ε
      (fun z hz => hεrep z hz (e s)) (p j.1) (hpe j.1) j.2.1 j.2.2
    have hφ : φ (e s) = (fun z => q z (coord s)) := by
      change ev (coord (e.symm (e s))) = _
      rw [e.symm_apply_apply]
      rfl
    rw [hφ] at heq
    rw [← heq, hd]
    have he0 : (e 0 : Exponent → ℂ) = 0 := by simp
    rw [he0]
    simp [seriesEval]
  · rfl

end
end MaximalSeshadri.ActualInterpolation

end



end OAI
