import Mathlib
import OAI.Analysis.BiholderTransport.Convexity.MovingCenterSemibound
import OAI.Analysis.BiholderTransport.LinearAlgebra.HessianSequentialUpper

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section MovingCenterUpper
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma coordinateCenterMatrix_chain {a c:M} {t:ℝ} {b p:Model n} {G:M → ℝ}
    (hb:b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hc:movingPrefix a t b p∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (hn:∀ᶠ z in 𝓝 (movingPrefixChart a c t b p),
      DifferentiableAt ℝ (fun w=>G ((extChartAt 𝓘(ℝ,Model n) c).symm w)) z)
    (hd:DifferentiableAt ℝ (fderiv ℝ (fun w=>G ((extChartAt 𝓘(ℝ,Model n) c).symm w)))
      (movingPrefixChart a c t b p)) (d:Model n) :
    coordinateCenterMatrix a t G b p d d=
      fderiv ℝ (fderiv ℝ (movingPrefixEnergy a t b)) p d d+
      fderiv ℝ (fderiv ℝ (fun w=>G ((extChartAt 𝓘(ℝ,Model n) c).symm w)))
        (movingPrefixChart a c t b p) (fderiv ℝ (movingPrefixChart a c t b) p d)
          (fderiv ℝ (movingPrefixChart a c t b) p d)+
      fderiv ℝ (fun w=>G ((extChartAt 𝓘(ℝ,Model n) c).symm w))
        (movingPrefixChart a c t b p) (fderiv ℝ (fderiv ℝ (movingPrefixChart a c t b)) p d d) := by
  rw [coordinateCenterMatrix_chart hb hc]
  simp only [add_apply]
  have hg:ContDiffAt ℝ 2 (movingPrefixChart a c t b) p :=
    ((joint_movingPrefixChart_contDiffAt hb hc).comp p
      (contDiffAt_const.prodMk contDiffAt_id)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [second_fderiv_comp_at hn hd hg]
  exact (add_assoc _ _ _).symm

lemma movingPrefixChart_injective_at_center {a c:M} {q:Model n}
    (hq:(show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a)
    (hc:riemannianExp a q=c) :
    Function.Injective (fderiv ℝ (movingPrefixChart a c 1 (extChartAt 𝓘(ℝ,Model n) a a)) q) := by
  have heq:movingPrefixChart a c 1 (extChartAt 𝓘(ℝ,Model n) a a)=
      (fun r:Model n=>extChartAt 𝓘(ℝ,Model n) (riemannianExp a q) (riemannianExp a r)) := by
    funext r
    simp only [movingPrefixChart,movingPrefix_at_center,one_smul,hc]
  rw [heq]
  exact riemannianExp_interior_nonconjugate hq

lemma moving_center_derivative_limits {a c:M} {q:Model n}
    (hc:riemannianExp a q=c) {bj qj:ℕ → Model n} {tj:ℕ → ℝ}
    (hb:Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hqq:Tendsto qj atTop (𝓝 q)) (ht:Tendsto tj atTop (𝓝 1)) :
    Tendsto (fun i=>fderiv ℝ (movingPrefixChart a c (tj i) (bj i)) (qj i)) atTop
      (𝓝 (fderiv ℝ (movingPrefixChart a c 1 (extChartAt 𝓘(ℝ,Model n) a a)) q)) ∧
    Tendsto (fun i=>fderiv ℝ (fderiv ℝ (movingPrefixChart a c (tj i) (bj i))) (qj i)) atTop
      (𝓝 (fderiv ℝ (fderiv ℝ (movingPrefixChart a c 1 (extChartAt 𝓘(ℝ,Model n) a a))) q)) := by
  let b:=extChartAt 𝓘(ℝ,Model n) a a
  let g:(ℝ×Model n) → Model n → Model n:=fun z r=>movingPrefixChart a c z.1 z.2 r
  have hb0:b∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
  have hgc:movingPrefix a 1 b q∈(extChartAt 𝓘(ℝ,Model n) c).source := by
    simp only [b,movingPrefix_at_center,one_smul,hc]
    exact mem_extChartAt_source c
  have hg:ContDiffAt ℝ ∞ (Function.uncurry g) ((1,b),q):=
    joint_movingPrefixChart_contDiffAt (a := a) (c := c) (t := 1) (b := b) (p := q) hb0 hgc
  have harg:Tendsto (fun i=>((tj i,bj i),qj i)) atTop (𝓝 ((1,b),q)):=
    (ht.prodMk_nhds hb).prodMk_nhds hqq
  have hA : ContinuousAt (fun z:(ℝ×Model n)×Model n=>fderiv ℝ (g z.1) z.2) ((1,b),q) :=
    (ContDiffAt.partial_snd_fderiv (f := g) (q := (1,b)) (h := q) hg).continuousAt
  have hQ : ContinuousAt (fun z:(ℝ×Model n)×Model n=>fderiv ℝ (fderiv ℝ (g z.1)) z.2) ((1,b),q) :=
    (ContDiffAt.partial_snd_fderiv_two (f := g) (q := (1,b)) (h := q) hg).continuousAt
  have H1:=hA.tendsto.comp harg
  have H2:=hQ.tendsto.comp harg
  dsimp only [Function.comp_def,g,b] at H1 H2
  exact ⟨H1,H2⟩

lemma moving_center_limit_data {a c:M} {q:Model n}
    (hq:(show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a)
    (hc:riemannianExp a q=c) {bj qj:ℕ → Model n} {tj:ℕ → ℝ}
    (hb:Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hqq:Tendsto qj atTop (𝓝 q)) (ht:Tendsto tj atTop (𝓝 1)) :
    let g:(ℝ×Model n) → Model n → Model n:=fun z r=>movingPrefixChart a c z.1 z.2 r
    let b:=extChartAt 𝓘(ℝ,Model n) a a
    Function.Injective (fderiv ℝ (g (1,b)) q) ∧
    Tendsto (fun i=>fderiv ℝ (g (tj i,bj i)) (qj i)) atTop (𝓝 (fderiv ℝ (g (1,b)) q)) ∧
    Tendsto (fun i=>fderiv ℝ (fderiv ℝ (g (tj i,bj i))) (qj i)) atTop
      (𝓝 (fderiv ℝ (fderiv ℝ (g (1,b))) q)) ∧
    Tendsto (fun i=>fderiv ℝ (fderiv ℝ (movingPrefixEnergy a (tj i) (bj i))) (qj i)) atTop
      (𝓝 (fderiv ℝ (fderiv ℝ (movingPrefixEnergy a 1 b)) q)) ∧
    (∀ᶠ i in atTop,bj i∈(extChartAt 𝓘(ℝ,Model n) a).target) ∧
    (∀ᶠ i in atTop,movingPrefix a (tj i) (bj i) (qj i)∈(extChartAt 𝓘(ℝ,Model n) c).source) := by
  dsimp only
  let b:=extChartAt 𝓘(ℝ,Model n) a a
  let g:(ℝ×Model n) → Model n → Model n:=fun z r=>movingPrefixChart a c z.1 z.2 r
  have hb0:b∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
  have hgc:movingPrefix a 1 b q∈(extChartAt 𝓘(ℝ,Model n) c).source := by
    simp only [b,movingPrefix_at_center,one_smul,hc]
    exact mem_extChartAt_source c
  have harg:Tendsto (fun i=>((tj i,bj i),qj i)) atTop (𝓝 ((1,b),q)):=
    (ht.prodMk_nhds hb).prodMk_nhds hqq
  have hA:Function.Injective (fderiv ℝ (g (1,b)) q) :=
    movingPrefixChart_injective_at_center hq hc
  obtain ⟨hAlim,hQlim⟩ := moving_center_derivative_limits hc hb hqq ht
  have hElim:=moving_energy_hessian_tendsto (a := a) hq hb hqq ht
  have hbt:∀ᶠ i in atTop,bj i∈(extChartAt 𝓘(ℝ,Model n) a).target:=
    hb.eventually ((isOpen_extChartAt_target a).mem_nhds hb0)
  have hct:∀ᶠ i in atTop,movingPrefix a (tj i) (bj i) (qj i)∈(extChartAt 𝓘(ℝ,Model n) c).source:=
    ((joint_movingPrefix_contMDiffAt (a := a) (t := 1) (b := b) (p := q) hb0).continuousAt.tendsto.comp harg).eventually
      ((isOpen_extChartAt_source c).mem_nhds hgc)
  exact ⟨hA,hAlim,hQlim,hElim,hbt,hct⟩

lemma moving_center_sequential_upper {a c:M} {q:Model n}
    (hq:(show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a)
    (hc:riemannianExp a q=c) {bj qj:ℕ → Model n} {tj:ℕ → ℝ}
    (hb:Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hqq:Tendsto qj atTop (𝓝 q)) (ht:Tendsto tj atTop (𝓝 1))
    {Gj:ℕ → M → ℝ}
    (hnear:∀ᶠ i in atTop,∀ᶠ z in 𝓝 (movingPrefixChart a c (tj i) (bj i) (qj i)),
      DifferentiableAt ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w)) z)
    (hder:∀ᶠ i in atTop,DifferentiableAt ℝ
      (fderiv ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w)))
        (movingPrefixChart a c (tj i) (bj i) (qj i)))
    {P C:ℝ} (hP:0 ≤ P) (hC:0 ≤ C)
    (hp:∀ᶠ i in atTop,‖fderiv ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w))
      (movingPrefixChart a c (tj i) (bj i) (qj i))‖ ≤ P)
    (hB:∀ᶠ i in atTop,∀d,coordinateCenterMatrix a (tj i) (Gj i) (bj i) (qj i) d d ≤ C*‖d‖^2) :
    ∃K≥0,∀ᶠ i in atTop,∀d,
      fderiv ℝ (fderiv ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w)))
        (movingPrefixChart a c (tj i) (bj i) (qj i)) d d ≤ K*‖d‖^2 := by
  let g:(ℝ×Model n) → Model n → Model n:=fun z r=>movingPrefixChart a c z.1 z.2 r
  obtain ⟨hA,hAlim,hQlim,hElim,hbt,hct⟩:=moving_center_limit_data hq hc hb hqq ht
  have he:∀ᶠ i in atTop,∀d,
      coordinateCenterMatrix a (tj i) (Gj i) (bj i) (qj i) d d=
      fderiv ℝ (fderiv ℝ (movingPrefixEnergy a (tj i) (bj i))) (qj i) d d+
      fderiv ℝ (fderiv ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w)))
        (g (tj i,bj i) (qj i)) (fderiv ℝ (g (tj i,bj i)) (qj i) d)
          (fderiv ℝ (g (tj i,bj i)) (qj i) d)+
      fderiv ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w))
        (g (tj i,bj i) (qj i)) (fderiv ℝ (fderiv ℝ (g (tj i,bj i))) (qj i) d d) := by
    filter_upwards [hbt,hct,hnear,hder] with i hbi hci hni hdi
    exact coordinateCenterMatrix_chain hbi hci hni hdi
  exact sequential_quadratic_upper_transfer hA hAlim hElim hQlim he hP hC hp hB

end MovingCenterUpper
end WeakMTWTransport

end
end

end OAI
