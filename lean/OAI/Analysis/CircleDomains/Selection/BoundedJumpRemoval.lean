import OAI.Analysis.CircleDomains.Selection.FixedPatternJumpRemoval
import OAI.Analysis.CircleDomains.Selection.JumpBlockCodes

namespace OAI

/-! Remove all new shrinking jumps from a fixed finite old-jump pattern.
All blocks use one common subsequence, so the total budget is retained. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable {I : Type*} [Fintype I] [MeasurableSpace C(PathTime, Sphere)]

theorem exists_mesh_preserving_bounded_chain_lower_bound
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
    (hUB : Disjoint d.quotientDomain B) (hdense : Dense d.quotientDomain)
    (hinfty : π OnePoint.infty ∉ B)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (F H : Set Sphere) (O : I → Set Sphere)
    (hF : frontier F ⊆ d.quotientDomain) (hH : frontier H ⊆ d.quotientDomain)
    (hO : ∀i, frontier (O i) ⊆ d.quotientDomain)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (r : ℝ≥0∞) {τ : ℝ} (hτ : 0 < τ) (T : I → ℝ≥0∞)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {β Δ : ℝ} (hΔ : 0 < Δ) (hΔβ : Δ < β)
    (hlower : ∀x ∈ F ∩ d.quotientDomain, ∀y ∈ H ∩ d.quotientDomain, ∀c,
      PaidChain (physicalJumpEdge d ν N g m O T) x y c → ENNReal.ofReal β ≤ c)
    (n : ℕ) :
    ∃ε : ℝ, 0 < ε ∧ ∀P : BoundedBlockPattern I n, ∀Z : JumpBlockCode d P,
      IsJumpBlockCode d ν N B F H O P Z →
      (∀b i, Metric.diam (Z.disks b i) ≤ ε) →
      ENNReal.ofReal (β-Δ) ≤ jumpBlockCost d B g m r τ T P Z := by
  classical
  by_contra h
  push Not at h
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hε (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  choose P hP using (fun k => h (ε k) (hε k))
  obtain ⟨P₀, s, hs, heq⟩ := exists_constant_finite_pattern_subsequence P
  have hviolations (k : ℕ) : ∃Z : JumpBlockCode d P₀,
      IsJumpBlockCode d ν N B F H O P₀ Z ∧
      (∀b i, Metric.diam (Z.disks b i) ≤ ε (s k)) ∧
      jumpBlockCost d B g m r τ T P₀ Z < ENNReal.ofReal (β-Δ) := by
    have hk := hP (s k)
    rw [heq k] at hk
    exact hk
  choose Z hZ hmesh hcost using hviolations
  have heps : Tendsto (ε ∘ s) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hs.tendsto_atTop
  have hdiam (b : Fin (P₀.1.val+1)) (i : Fin (P₀.2.2 b).val) :
      Tendsto (fun k => Metric.diam ((Z k).disks b i)) atTop (𝓝 0) :=
    squeeze_zero (fun _ => Metric.diam_nonneg) (fun k => hmesh k b i) heps
  let E := blockAnchors F H O P₀
  let T' : Fin P₀.1.val → ℝ≥0∞ := fun i => T (P₀.2.1 i)
  have hbudget (k : ℕ) :
      (∑b, ((∑j, physicalTollCost d g m ((Z k).paths b j).1) +
        ∑i, fixedWidthJumpToll B m r τ ((Z k).disks b i))) + (∑i, T' i) ≤
      ENNReal.ofReal (β-Δ) := (hcost k).le
  have hhalf : 0 < Δ/2 := by positivity
  obtain ⟨x, hx, y, hy, c, hc, hcb⟩ := exists_old_chain_of_shrinking_blocks
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad hUB hdense hinfty
    ν N P₀.1.val E (blockAnchors_frontier F H d.quotientDomain O P₀ hF hH hO) T'
    (fun b => (P₀.2.2 b).val) (fun b j k => (Z k).paths b j)
    (fun b j k => (hZ k).allowed b j) (fun b k => (hZ k).start b)
    (fun b k => (hZ k).finish b) (fun b i k => (Z k).disks b i)
    (fun b i k => (hZ k).left b i) (fun b i k => (hZ k).right b i)
    (fun b i k => (hZ k).meets b i) hdiam
    g hg henergy m hm r hτ (ENNReal.ofReal (β-Δ)) ENNReal.ofReal_lt_top hbudget
    w hw hpos hpoint hhalf
  have hcOld : PaidChain (physicalJumpEdge d ν N g m O T) x y c := by
    clear hx hy hcb
    induction hc with
    | refl x => exact PaidChain.refl x
    | @cons x y z a b hxy _ ih =>
      apply PaidChain.cons ?_ ih
      rcases hxy with hpath | ⟨i, hxi, hyi, ha⟩
      · exact Or.inl hpath
      · change x ∈ blockAnchors F H O P₀ i.succ.castSucc ∩ d.quotientDomain at hxi
        change y ∈ blockAnchors F H O P₀ i.succ.castSucc ∩ d.quotientDomain at hyi
        rw [blockAnchors_internal] at hxi hyi
        exact Or.inr ⟨P₀.2.1 i, hxi, hyi, ha⟩
  have hxF : x ∈ F ∩ d.quotientDomain := by simpa [E] using hx
  have hyH : y ∈ H ∩ d.quotientDomain := by simpa [E] using hy
  have hstrict : ENNReal.ofReal (β-Δ) + ENNReal.ofReal (Δ/2) < ENNReal.ofReal β := by
    rw [← ENNReal.ofReal_add (by linarith : 0 ≤ β-Δ) hhalf.le]
    exact ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < β) |>.mpr (by linarith)
  exact (hlower x hxF y hyH c hcOld).not_gt (hcb.trans_lt hstrict)

end CircleDomainRigidity

end

end OAI
