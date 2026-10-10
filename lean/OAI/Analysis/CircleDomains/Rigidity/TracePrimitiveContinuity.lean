import OAI.Analysis.CircleDomains.Rigidity.TraceMaskTail

namespace OAI

/-! Joint continuity of finite primitives follows from the explicit
finite variation bound. Uniformly small scalar tails then prove the
continuity of the actual infinite masked scalar at a common point. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem finiteTracePrimitive_continuous {X : Type*} [TopologicalSpace X]
    {cutoff : ℕ → X → ℝ} (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1)
    (hcc : ∀ j, Continuous (cutoff j)) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    (a : ℝ) (n : ℕ) :
    Continuous (fun p : X × ℝ => finiteTracePrimitive cutoff I a p.1 p.2 n) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let B := fun q : X × ℝ => |q.2-p.2|+
    ∑ j ∈ Finset.range n, volume.real (I j)*|cutoff j q.1-cutoff j p.1|
  have hB : Continuous B := by dsimp only [B]; fun_prop
  have hB0 : B p = 0 := by simp [B]
  have hb : Tendsto B (𝓝 p) (𝓝 0) := hB0 ▸ hB.continuousAt.tendsto
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) _ hb
  intro q
  calc
    _ ≤ dist (finiteTracePrimitive cutoff I a q.1 q.2 n)
          (finiteTracePrimitive cutoff I a q.1 p.2 n)+
        dist (finiteTracePrimitive cutoff I a q.1 p.2 n)
          (finiteTracePrimitive cutoff I a p.1 p.2 n) := dist_triangle _ _ _
    _ ≤ B q := by
      apply add_le_add
      · simpa only [NNReal.coe_one,one_mul,Real.dist_eq] using
          (finiteTracePrimitive_lipschitz hc hI q.1 n a).dist_le_mul q.2 p.2
      · simpa only [Real.dist_eq] using finiteTracePrimitive_variation hc hI hIf q.1 p.1 a p.2 n

 theorem infinite_masked_scalar_continuousAt {X : Type*} [TopologicalSpace X]
    {cutoff : ℕ → X → ℝ} (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1)
    (hcc : ∀ j, Continuous (cutoff j)) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    {b : X → ℝ} {x : X} (hb : ContinuousAt b x) (a : ℝ)
    (htail : ∀ δ > 0, ∃ N : ℕ, ∀ᶠ y in 𝓝 x,
      ∀ j, N ≤ j → ∀ t ∈ I j, t ∉ Ioo (b x-δ) (b x+δ) → cutoff j y = 1) :
    ContinuousAt (fun y => infiniteTracePrimitive cutoff I a y (b y)) x := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε/8
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨N,hN⟩ := htail δ hδ
  have hNx := hN.self_of_nhds
  have hcont := (finiteTracePrimitive_continuous hc hcc hI hIf a N).continuousAt.comp
    (continuousAt_id.prodMk hb)
  have hnear := hcont.eventually (Metric.ball_mem_nhds _ hδ)
  filter_upwards [hN,hnear] with y hy hnear
  have hJ : MeasurableSet (Ioo (b x-δ) (b x+δ)) := measurableSet_Ioo
  have hJf : volume (Ioo (b x-δ) (b x+δ)) ≠ ∞ := by simp
  have hlen : volume.real (Ioo (b x-δ) (b x+δ)) = 2*δ := by
    rw [Real.volume_real_Ioo_of_le (by linarith : b x-δ ≤ b x+δ)]
    ring
  have h1 := tracePrimitive_tail_bound hc hI hJ hJf hy a (b y)
  have h2 := tracePrimitive_tail_bound hc hI hJ hJf hNx a (b x)
  rw [hlen] at h1 h2
  have h3 : dist (finiteTracePrimitive cutoff I a y (b y) N)
      (finiteTracePrimitive cutoff I a x (b x) N) < δ := hnear
  have hd := dist_triangle (infiniteTracePrimitive cutoff I a y (b y))
    (finiteTracePrimitive cutoff I a y (b y) N) (infiniteTracePrimitive cutoff I a x (b x))
  have hd' := dist_triangle (finiteTracePrimitive cutoff I a y (b y) N)
    (finiteTracePrimitive cutoff I a x (b x) N) (infiniteTracePrimitive cutoff I a x (b x))
  simp only [Real.dist_eq] at hd hd' h3 ⊢
  have h2' : |finiteTracePrimitive cutoff I a x (b x) N-
      infiniteTracePrimitive cutoff I a x (b x)| ≤ 2*δ := by simpa only [abs_sub_comm] using h2
  dsimp only [δ] at *
  linarith

end CircleDomainRigidity

end

end OAI
