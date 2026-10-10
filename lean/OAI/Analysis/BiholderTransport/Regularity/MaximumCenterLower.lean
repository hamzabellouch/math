import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.BilinearClose
import OAI.Analysis.BiholderTransport.Regularity.CenterSequenceCompact
import OAI.Analysis.BiholderTransport.Regularity.MaximumCenterSequence

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section MaximumCenterLower
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_maximum_center_gain :
    ∃ c0>0,∀ᶠ l:ℝ in 𝓝 1,0<l → l<1 →
    ∀ (hmtw : WeakMTW (n := n) (M := M)) (u v : M → ℝ),
    Continuous u → ∀ (Lv : ℝ≥0) (hv : LipschitzWith Lv v),
    IsCostDualPair u v →
    ∀ (α D bminus bplus : ℝ) (Bc Bo : ℝ → ℝ) (ho : Continuous Bo),
    ContDiff ℝ ∞ Bc →
    (∀ b∈Icc bminus bplus,Monotone (fun s=>modifiedScalar α D Bc (b,s))) →
    ∀ L:ℝ≥0,(∀ b∈Icc bminus bplus,LipschitzWith L (modifiedDatum v α D b Bc)) →
    ∀ (F : MaximumFamily (n := n) v α D bminus bplus Bc Bo) (a c:M) (N:Set (Model n)),
    ∀ J : MaximumJensenFamily hmtw hv.continuous ho F a c N,
    ∀ (q:Model n) (β:ℝ),
    (show TangentSpace 𝓘(ℝ,Model n) a from q)∈minimizingVectors a →
    riemannianExp a q=c →
    Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)) →
    Tendsto F.b atTop (𝓝 β) →
    deriv (fun s=>modifiedScalar α D Bc (β,s)) (v c)=l →
    ∀ ε:ℝ,0<ε → ∀ᶠ k in atTop,∀ d:Model n,
      c0*(1-l)*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2+
        (iteratedDeriv 2 (fun s=>modifiedScalar α D Bc (β,s)) (v c)/l^2)*
          (inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) d)^2 - ε*‖d‖^2 ≤
          (J.first k).H d d := by
  obtain ⟨c0,hc0,H⟩ := exists_actual_center_gain (n := n) (M := M)
  refine ⟨c0,hc0,?_⟩
  filter_upwards [H] with l hgain
  intro hl hl1 hmtw u v hu Lv hv hdual α D bminus bplus Bc Bo ho hBc hmono L hLip
    F a c N J q β hq he hQ hβ hder ε hε
  let θ := fun k:ℕ=>1/((k:ℝ)+1)
  have hθpos (k:ℕ) : 0<θ k := by dsimp [θ]; positivity
  have hθ : Tendsto θ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨S⟩ := J.exists_diagonal hθpos (P := fun _ _=>True) (fun _=>Eventually.of_forall (fun _=>True.intro))
  obtain ⟨hb,hp,hx,hg⟩ := S.limits J hθ hQ he
  have hlj := S.slope_tendsto hBc hβ hx
  rw [hder] at hlj
  obtain ⟨K,hK⟩ := eventually_atTop.mp (hlj.eventually (Ioo_mem_nhds hl hl1))
  let σ := fun i:ℕ=>i+K
  have hσ : Tendsto σ atTop atTop := tendsto_add_atTop_nat K
  let S1 := S.comp σ hσ
  have hls (i:ℕ) : 0<(J.comp σ hσ).sampleSlope i (S1.ν i) ∧
      (J.comp σ hσ).sampleSlope i (S1.ν i)<1 := hK (i+K) (Nat.le_add_left _ _)
  let CD := S1.center_sequence hu hv hdual hBc hmono hls (hg.comp hσ)
  have hτ : Tendsto (fun k=>1-F.t k) atTop (𝓝 (0:ℝ)) := by
    simpa only [sub_self] using (tendsto_const_nhds.sub F.time :
      Tendsto (fun k=>(1:ℝ)-F.t k) atTop (𝓝 (1-1)))
  have HG := hgain hl hl1 a c u v (modifiedScalar α D Bc) β hv.continuous
    (modifiedScalar_contDiff hBc α D).contDiffAt hder
    (F.b ∘ σ) (fun i=>J.sampleSlope (σ i) (S.ν (σ i))) (fun i=>1-F.t (σ i))
    (F.t ∘ σ) (fun i=>J.sampleCenter (σ i) (S.ν (σ i)))
    (fun i=>graphBaseCoordinate a (J.samplePoint (σ i) (S.ν (σ i))).1)
    (fun i=>graphVelocityCoordinate a (J.samplePoint (σ i) (S.ν (σ i))).1)
    (fun i=>graphProjection (cTransform (modifiedDatum v α D (F.b (σ i)) Bo)) (F.t (σ i))
      (J.samplePoint (σ i) (S.ν (σ i))))
    (fun i=>chartOuterEnvelope (modifiedDatum v α D (F.b (σ i)) Bo) (F.t (σ i)) c)
    CD q hq he (hβ.comp hσ) (hlj.comp hσ) (hτ.comp hσ) (F.time.comp hσ)
    (hx.comp hσ) (hb.comp hσ) (hp.comp hσ)
    (Eventually.of_forall (fun i=>by linarith [(F.prefixTime (σ i)).2])) L
    (Eventually.of_forall (fun i=>hLip _ (Ioo_subset_Icc_self (F.parameter (σ i)))))
    (ε/2) (half_pos hε)
  rw [←map_add_atTop_eq_nat K]
  change ∀ᶠ i in atTop,∀ d:Model n,_≤(J.first (i+K)).H d d
  filter_upwards [HG,(hθ.comp hσ).eventually (gt_mem_nhds (half_pos hε))] with i hi hθi
  intro d
  have Hclose := bilinear_quadratic_close ((S.HClose (σ i)).le.trans hθi.le) d
  have HH := hi d
  change _≤J.sampleH (σ i) (S.ν (σ i)) d d at HH
  nlinarith only [Hclose,HH]

end MaximumCenterLower
end WeakMTWTransport

end
end

end OAI
