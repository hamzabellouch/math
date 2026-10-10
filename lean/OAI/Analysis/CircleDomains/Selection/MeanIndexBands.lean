import OAI.Analysis.CircleDomains.Modulus.MeanIndexOscillation
import Mathlib.Topology.Order.LiminfLimsup

namespace OAI

/-! Boundary band widths of the actual mean are bounded by point hit
probabilities. This applies after any continuous local lift, including
limits along the physical domain at a collapsed complementary component. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem limsup_sub_liminf_le_of_pair_oscillation
    {X : Type*} (l : Filter X) [NeBot l] (u : X → ℝ) (C : ℝ)
    (hlo : IsBoundedUnder (· ≥ ·) l u) (hhi : IsBoundedUnder (· ≤ ·) l u)
    (hpair : ∀ ε : ℝ, 0 < ε → ∀ᶠ p : X × X in l ×ˢ l, |u p.1 - u p.2| < C + ε) :
    limsup u l - liminf u l ≤ C := by
  by_contra hn
  let ε := (limsup u l - liminf u l - C) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := eventually_prod_iff.mp (hpair ε hε)
  have he : ∀ᶠ y in l, limsup u l - C - ε ≤ u y := by
    filter_upwards [hQ] with y hy
    have hb : limsup u l ≤ u y + C + ε := by
      apply limsup_le_of_le hlo.isCoboundedUnder_le
      filter_upwards [hP] with x hx
      have hh := hPQ hx hy
      have ha := le_abs_self (u x - u y)
      linarith
    linarith
  have hl := le_liminf_of_le hhi.isCoboundedUnder_ge he
  dsimp [ε] at hl
  linarith

 theorem meanGeometricIndex_band_width
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K)
    {X : Type*} [TopologicalSpace X] (S : Set X) (s : X) (hs : s ∈ closure S)
    (L : X → ClosedUpperHalfPlane) (hL : ContinuousWithinAt L S s)
    (hz : 0 < (L s).val.im) :
    limsup (fun x => meanGeometricIndex hsch K hKS η (L x)) (𝓝[S] s) -
      liminf (fun x => meanGeometricIndex hsch K hKS η (L x)) (𝓝[S] s) ≤
        (η : Measure K).real {γ | diskRayProjection (L s).val ∈ range γ.val} := by
  let : NeBot (𝓝[S] s) := mem_closure_iff_nhdsWithin_neBot.mp hs
  let u : X → ℝ := fun x => meanGeometricIndex hsch K hKS η (L x)
  let C := (η : Measure K).real {γ | diskRayProjection (L s).val ∈ range γ.val}
  have hbase := meanGeometricIndex_oscillation_le_hit hsch hsep K hK hKS η (L s) hz zero_lt_one
  have hnear : ∀ᶠ x in 𝓝[S] s, |u x - u s| < C + 1 :=
    (hL.prodMk_nhds tendsto_const_nhds).eventually hbase
  have hlo : IsBoundedUnder (· ≥ ·) (𝓝[S] s) u :=
    isBoundedUnder_of_eventually_ge (hnear.mono fun x hx => by
      have hh := (abs_lt.mp hx).1
      exact (show u s - C - 1 ≤ u x by linarith))
  have hhi : IsBoundedUnder (· ≤ ·) (𝓝[S] s) u :=
    isBoundedUnder_of_eventually_le (hnear.mono fun x hx => by
      have hh := (abs_lt.mp hx).2
      exact (show u x ≤ u s + C + 1 by linarith))
  apply limsup_sub_liminf_le_of_pair_oscillation (𝓝[S] s) u C hlo hhi
  intro ε hε
  have hmap := Filter.Tendsto.prodMap
    (show Tendsto L (𝓝[S] s) (𝓝 (L s)) from hL)
    (show Tendsto L (𝓝[S] s) (𝓝 (L s)) from hL)
  rw [← nhds_prod_eq] at hmap
  exact hmap.eventually (meanGeometricIndex_oscillation_le_hit hsch hsep K hK hKS η (L s) hz hε)

end CircleDomainRigidity

end

end OAI
