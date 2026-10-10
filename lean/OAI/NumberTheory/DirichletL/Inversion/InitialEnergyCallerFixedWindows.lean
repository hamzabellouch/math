import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerWindows

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerFixedWindows
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns
open InverseSecondChildWindows InverseSecondProfileUniform
local notation "Eis"=>ActualEisensteinCubic.O

theorem log_source_support (W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W) :
    Function.support (CubicReflectionKernel.logSchwartz W a b ha hs hW)⊆
      Set.Icc (-(|Real.log a|+|Real.log b|)) (|Real.log a|+|Real.log b|) := by
  intro x hx
  have hh := hs hx
  change a≤Real.exp x ∧ Real.exp x≤b at hh
  have hl := Real.log_le_log ha hh.1
  have hu := Real.log_le_log (Real.exp_pos x) hh.2
  rw [Real.log_exp] at hl hu
  constructor
  · linarith [neg_abs_le (Real.log a),abs_nonneg (Real.log b)]
  · linarith [le_abs_self (Real.log b),abs_nonneg (Real.log a)]

theorem exists_actual_initial_windows
    (W₁ W₂:ℝ→ℂ)(a b bcap:ℝ)(ha:0<a)(hcap:1≤bcap)
    (hs₁:Function.support W₁⊆Set.Icc a b)(hs₂:Function.support W₂⊆Set.Icc a b)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)
    (lo hi:Fin 4→ℝ)(hlo:∀i,0<lo i)(hhi:∀i,lo i≤hi i) :
    ∃(wFresh:𝓢(ℝ,ℂ))(V:Fin 6→𝓢(ℝ,ℂ))(M:Fin 6→ℝ)(af bf:ℝ),
      0<af ∧ af≤bf ∧ HasCompactSupport (wFresh:ℝ→ℂ) ∧
      tsupport (wFresh:ℝ→ℂ)⊆Set.Icc af bf ∧
      (∀i,0≤M i) ∧ (∀i,HasCompactSupport (V i:ℝ→ℂ)) ∧
      (∀i,Function.support (V i)⊆Set.Icc (-M i) (M i)) ∧
      ∀{ι:Type*}[DecidableEq ι](p:ι→Eis)(_hp:∀i,p i≠0)
      [∀i,(Ideal.span {p i}).IsMaximal]
      (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
      (_hdiv:∀x∈S,x.divisor⊆x.common)(_hf:∀x∈S,x.frequency≠0)
      (ψ:Fin 4→ℝ→ℂ)(_hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
      (Z D B v θ H c₁ c₂ θ₁ θ₂:ℝ),0<Z→1≤c₁→c₁≤bcap→1≤c₂→c₂≤bcap→
      BlockSupport p (pointSource pool (windowSource p S ψ Z D B v θ H))
        W₁ W₂ wFresh wFresh (fun i=>V i) Z D B v θ H c₁ c₂ θ₁ θ₂ := by
  let m:=|Real.log a|+|Real.log b|
  obtain ⟨wFresh,V,M,af,bf,haf,hab,hwc,hws,hM,hVc,hVs,hw,hcut⟩ :=
    fixed_windows m bcap lo hi (fun _=>0) (by dsimp [m];positivity) hcap hlo hhi (by simp)
  refine ⟨wFresh,V,M,af,bf,haf,hab,hwc,hws,hM,hVc,hVs,?_⟩
  intro ι _ p hp _ pool S hdiv hf ψ hψ Z D B v θ H c₁ c₂ θ₁ θ₂ hZ hc₁ hb₁ hc₂ hb₂
  let g₁ := CubicReflectionKernel.logSchwartz W₁ a b ha hs₁ hW₁
  let g₂ := CubicReflectionKernel.logSchwartz W₂ a b ha hs₂ hW₂
  have hg₁ : Function.support g₁⊆Set.Icc (-m) m := log_source_support W₁ a b ha hs₁ hW₁
  have hg₂ : Function.support g₂⊆Set.Icc (-m) m := log_source_support W₂ a b ha hs₂ hW₂
  have hvalid : ∀x∈pointSource pool (windowSource p S ψ Z D B v θ H),Valid x :=
    pointSource_valid pool _ (fun x hx=>hdiv x (Finset.mem_filter.mp hx).1)
      (fun x hx=>hf x (Finset.mem_filter.mp hx).1)
  have hpos (x:Point ι)(hx:x∈pointSource pool (windowSource p S ψ Z D B v θ H)) :
      ∀i,0<relativeNorm (coordinates p x) Z D B v θ H i :=
    relativeNorm_pos _ (coordinates_pos p hp x (hvalid x hx)) hZ D B v θ H
  have hblock (x:Point ι)(hx:x∈pointSource pool (windowSource p S ψ Z D B v θ H)) :
      ∀i:Fin 4,relativeNorm (coordinates p x) Z D B v θ H (outerIndex i)∈Set.Icc (lo i) (hi i) :=
    fun i=>hψ i (windowSource_four_nonzero p pool S ψ Z D B v θ H hx i)
  refine ⟨?_,?_,?_⟩
  · intro x hx hn
    have he := hw g₁ hg₁ c₁ θ₁ _ _ _ hc₁ hb₁ (hblock x hx 0) (hblock x hx 2) (hpos x hx 4) ?_
    · rw [relative_column_left] at he
      rw [he,star_one]
    · change positiveSource g₁ c₁ θ₁
        (relativeNorm (coordinates p x) Z D B v θ H 0 *
          relativeNorm (coordinates p x) Z D B v θ H 2 *
          relativeNorm (coordinates p x) Z D B v θ H 4)≠0
      dsimp only [g₁]
      rw [positiveSource_logSchwartz W₁ a b ha hs₁ hW₁ (zero_lt_one.trans_le hc₁)
        (mul_pos (mul_pos (hpos x hx 0) (hpos x hx 2)) (hpos x hx 4))]
      exact hn
  · intro x hx hn
    have he := hw g₂ hg₂ c₂ θ₂ _ _ _ hc₂ hb₂ (hblock x hx 0) (hblock x hx 2) (hpos x hx 5) ?_
    · rwa [relative_column_right] at he
    · change positiveSource g₂ c₂ θ₂
        (relativeNorm (coordinates p x) Z D B v θ H 0 *
          relativeNorm (coordinates p x) Z D B v θ H 2 *
          relativeNorm (coordinates p x) Z D B v θ H 5)≠0
      dsimp only [g₂]
      rw [positiveSource_logSchwartz W₂ a b ha hs₂ hW₂ (zero_lt_one.trans_le hc₂)
        (mul_pos (mul_pos (hpos x hx 0) (hpos x hx 2)) (hpos x hx 5))]
      exact hn
  · intro x hx hl hr i
    have hl' : wFresh (relativeNorm (coordinates p x) Z D B v θ H 4)≠0 := by
      rw [relative_column_left]
      exact star_ne_zero.mp hl
    have hr' : wFresh (relativeNorm (coordinates p x) Z D B v θ H 5)≠0 := by
      rwa [relative_column_right]
    have he := hcut (relativeNorm (coordinates p x) Z D B v θ H) (fun _=>0)
      (by simp) (hblock x hx) hl' hr' i
    simpa only [add_zero,relativeLog] using he

end SevenEighths.InverseInitialEnergyCallerFixedWindows

end

end OAI
