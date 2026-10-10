import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.CenterRegularCompact
import OAI.Analysis.BiholderTransport.Regularity.MaximumCenterSequence

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section MaximumCenterRegular
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
lemma MaximumJensenFamily.center_regular
    {u v : M → ℝ} (hu : Continuous u) {Lv : ℝ≥0} (hv : LipschitzWith Lv v)
    (hdual : IsCostDualPair u v)
    {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ} {ho : Continuous Bo}
    (hBc : ContDiff ℝ ∞ Bc)
    (hmono : ∀ b∈Icc bminus bplus,Monotone (fun s=>modifiedScalar α D Bc (b,s)))
    (L : ℝ≥0) (hLip : ∀ b∈Icc bminus bplus,LipschitzWith L (modifiedDatum v α D b Bc))
    {hmtw : WeakMTW (n := n) (M := M)}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c:M} {N:Set (Model n)}
    (J : MaximumJensenFamily hmtw hv.continuous ho F a c N)
    {q:Model n} {β l:ℝ}
    (hq : (show TangentSpace 𝓘(ℝ,Model n) a from q)∈minimizingVectors a)
    (he : riemannianExp a q=c)
    (hQ : Tendsto (fun k=>(F.row k).q.1) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
    (hβ : Tendsto F.b atTop (𝓝 β))
    (hder : deriv (fun s=>modifiedScalar α D Bc (β,s)) (v c)=l)
    (hl:0<l) (hl1:l<1) :
    (show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a := by
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
  exact CD.regular_compact hv.continuous (modifiedScalar_contDiff hBc α D).contDiffAt
    hder hl hl1 hq he (hβ.comp hσ) (hlj.comp hσ) (hτ.comp hσ)
    (F.time.comp hσ) (hx.comp hσ) (hb.comp hσ)
    (Eventually.of_forall (fun i=>by change 0 < 1-F.t (σ i); linarith [(F.prefixTime (σ i)).2])) L
    (Eventually.of_forall (fun i=>hLip _ (Ioo_subset_Icc_self (F.parameter (σ i)))))

end MaximumCenterRegular
end WeakMTWTransport

end
end

end OAI
