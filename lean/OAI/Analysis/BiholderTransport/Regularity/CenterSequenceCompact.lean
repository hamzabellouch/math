import Mathlib
import OAI.Analysis.BiholderTransport.Convexity.ActualCenterSemibound

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section CenterSequenceCompact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def CenterSequenceData.comp {a c : M} {u v : M → ℝ} {Φ : ℝ×ℝ → ℝ}
    {γj lj τj tj : ℕ → ℝ} {xj bj qj : ℕ → Model n} {zj : ℕ → M}
    {F : ℕ → Model n → ℝ}
    (D : CenterSequenceData a c u v Φ γj lj τj tj xj bj qj zj F)
    (σ : ℕ → ℕ) (hσ : Tendsto σ atTop atTop) :
    CenterSequenceData a c u v Φ (γj ∘ σ) (lj ∘ σ) (τj ∘ σ) (tj ∘ σ)
      (xj ∘ σ) (bj ∘ σ) (qj ∘ σ) (zj ∘ σ) (F ∘ σ) where
  row i := D.row (σ i)
  endpoint i := D.endpoint (σ i)
  derivative := hσ.eventually D.derivative
  gradient := D.gradient.comp hσ
  backward := hσ.eventually D.backward

lemma exists_actual_center_gain :
    ∃ c0>0,∀ᶠ l : ℝ in 𝓝 1, 0<l → l<1 →
      ∀ (a c : M) (u v : M → ℝ) (Φ : ℝ×ℝ → ℝ) (γ : ℝ),
      Continuous v → ContDiffAt ℝ ∞ Φ (γ,v c) →
      deriv (fun s=>Φ (γ,s)) (v c)=l →
      ∀ (γj lj τj tj : ℕ → ℝ) (xj bj qj : ℕ → Model n) (zj : ℕ → M)
        (F : ℕ → Model n → ℝ),
      CenterSequenceData a c u v Φ γj lj τj tj xj bj qj zj F →
      ∀ q : Model n,
      (show TangentSpace 𝓘(ℝ,Model n) a from q)∈minimizingVectors a →
      riemannianExp a q=c →
      Tendsto γj atTop (𝓝 γ) → Tendsto lj atTop (𝓝 l) →
      Tendsto τj atTop (𝓝 0) → Tendsto tj atTop (𝓝 1) →
      Tendsto xj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)) →
      Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)) →
      Tendsto qj atTop (𝓝 q) →
      (∀ᶠ i in atTop,0<τj i) → ∀ L : ℝ≥0,
      (∀ᶠ i in atTop,LipschitzWith L (fun y=>Φ (γj i,v y))) →
      ∀ ε : ℝ,0<ε →
      ∀ᶠ i in atTop,∀ d : Model n,
        c0*(1-l)*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2+
          (iteratedDeriv 2 (fun s=>Φ (γ,s)) (v c)/l^2)*
            (inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) d)^2-ε*‖d‖^2 ≤
        coordinateCenterMatrix a (tj i) (hopfLax (τj i) (fun y=>Φ (γj i,v y)))
          (bj i) (qj i) d d := by
  obtain ⟨c0,hc0,H⟩ := exists_actual_center_sequential_gain (n := n) (M := M)
  refine ⟨c0,hc0,?_⟩
  filter_upwards [H] with l hgain
  intro hl hl1 a c u v Φ γ hv hΦ hder γj lj τj tj xj bj qj zj F D q hq he
    hγ hlm hτ ht hx hb hqq hτpos L hLip ε hε
  by_contra h
  have hf := not_eventually.mp h
  choose σ hσge hbad using frequently_atTop.mp hf
  have hσ : Tendsto σ atTop atTop := tendsto_atTop_mono hσge tendsto_id
  let D1 := D.comp σ hσ
  obtain ⟨κ,hκ,r,hr,hrr⟩ := center_support_family_subseq D1.row (hx.comp hσ)
  let D2 := D1.comp κ hκ.tendsto_atTop
  have Hlow := hgain hl hl1 a c u v Φ γ hv hΦ hder
    ((γj ∘ σ) ∘ κ) ((lj ∘ σ) ∘ κ) ((τj ∘ σ) ∘ κ) ((tj ∘ σ) ∘ κ)
    ((xj ∘ σ) ∘ κ) ((bj ∘ σ) ∘ κ) ((qj ∘ σ) ∘ κ) ((zj ∘ σ) ∘ κ)
    ((F ∘ σ) ∘ κ) D2 r q hr hq he
    ((hγ.comp hσ).comp hκ.tendsto_atTop) ((hlm.comp hσ).comp hκ.tendsto_atTop)
    ((hτ.comp hσ).comp hκ.tendsto_atTop) ((ht.comp hσ).comp hκ.tendsto_atTop)
    ((hx.comp hσ).comp hκ.tendsto_atTop) ((hb.comp hσ).comp hκ.tendsto_atTop)
    ((hqq.comp hσ).comp hκ.tendsto_atTop) hrr
    (hκ.tendsto_atTop.eventually (hσ.eventually hτpos)) L
    (hκ.tendsto_atTop.eventually (hσ.eventually hLip)) ε hε
  obtain ⟨i,hi⟩ := Hlow.exists
  exact hbad (κ i) hi

end CenterSequenceCompact
end WeakMTWTransport

end
end

end OAI
