import OAI.Analysis.CircleDomains.Selection.JumpChainEdges
import OAI.Analysis.CircleDomains.Topology.FiniteJumpCompactness

namespace OAI

/-! Remove all new shrinking jumps from a fixed finite old-jump pattern.
All blocks use one common subsequence, so the total budget is retained. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]

theorem exists_old_chain_of_shrinking_blocks
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
    (q : ℕ) (E : Fin (q+2) → Set Sphere)
    (hE : ∀i, frontier (E i) ⊆ d.quotientDomain) (T : Fin q → ℝ≥0∞)
    (shape : Fin (q+1) → ℕ)
    (Γ : ∀b, Fin (shape b + 1) → ℕ → TaggedPhysicalPath d)
    (hΓ : ∀b j k, AllowedTaggedPath d ν N ((Γ b j k).1.val, (Γ b j k).2))
    (hΓF : ∀b k, (Γ b 0 k).1.val ⊥ ∈ E b.castSucc ∩ d.quotientDomain)
    (hΓH : ∀b k, (Γ b (Fin.last (shape b)) k).1.val ⊤ ∈ E b.succ ∩ d.quotientDomain)
    (V : ∀b, Fin (shape b) → ℕ → Set Sphere)
    (hleft : ∀b i k, (Γ b i.castSucc k).1.val ⊤ ∈ V b i k)
    (hright : ∀b i k, (Γ b i.succ k).1.val ⊥ ∈ V b i k)
    (hmeet : ∀b i k, (V b i k ∩ B).Nonempty)
    (hdiam : ∀b i, Tendsto (fun k => Metric.diam (V b i k)) atTop (𝓝 0))
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (r : ℝ≥0∞) {τ : ℝ} (hτ : 0 < τ) (M : ℝ≥0∞) (hM : M < ∞)
    (hbudget : ∀k, (∑b, ((∑j, physicalTollCost d g m (Γ b j k).1) +
      ∑i, fixedWidthJumpToll B m r τ (V b i k))) + (∑i, T i) ≤ M)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃x ∈ E 0 ∩ d.quotientDomain, ∃y ∈ E (Fin.last (q+1)) ∩ d.quotientDomain,
      ∃c : ℝ≥0∞,
        PaidChain (physicalJumpEdge d ν N g m (fun i : Fin q => E i.succ.castSucc) T) x y c ∧
        c ≤ M + ENNReal.ofReal η := by
  let I := Σb : Fin (q+1), Fin (shape b)
  let P := Σb : Fin (q+1), Fin (shape b + 1)
  let V' : I → ℕ → Set Sphere := fun i k => V i.1 i.2 k
  let x' : I → ℕ → Sphere := fun i k => (Γ i.1 i.2.castSucc k).1.val ⊤
  let y' : I → ℕ → Sphere := fun i k => (Γ i.1 i.2.succ k).1.val ⊥
  let c' : P → ℕ → ℝ≥0∞ := fun i k => physicalTollCost d g m (Γ i.1 i.2 k).1
  have hb (k : ℕ) : (∑i, c' i k) + (∑i, fixedWidthJumpToll B m r τ (V' i k)) +
      (∑i, T i) ≤ M := by
    simpa only [I, P, V', c', Fintype.sum_sigma, Finset.sum_add_distrib] using hbudget k
  obtain ⟨s, p, A, J, hs, hpB, hend, hstart, hcost, hJcost, hpaid, htotal⟩ :=
    exists_joint_finite_jump_limits B hB m r hτ V' x' y' c'
      (fun i k => hleft i.1 i.2 k) (fun i k => hright i.1 i.2 k)
      (fun i k => hmeet i.1 i.2 k) (fun i => hdiam i.1 i.2) (∑i, T i) M hb
  have hp (i : I) : p i ≠ π OnePoint.infty := fun heq => hinfty (heq ▸ hpB i)
  have hA (i : P) : A i < ∞ := by
    have hi : A i ≤ ∑j, A j := Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ _)
    exact lt_of_le_of_lt (hi.trans ((le_add_right (le_add_right le_rfl)).trans htotal)) hM
  let C : Fin (q+1) → ℝ≥0∞ := fun b => (∑j, A ⟨b, j⟩) + (∑i, J ⟨b, i⟩)
  let R := physicalJumpEdge d ν N g m (fun i : Fin q => E i.succ.castSucc) T
  let E' : Fin (q+2) → Set Sphere := fun i => E i ∩ d.quotientDomain
  have hblocks (b : Fin (q+1)) (ε : ℝ) (hε : 0 < ε) :
      ∃x ∈ E' b.castSucc, ∃y ∈ E' b.succ, ∃c : ℝ≥0∞,
        PaidChain R x y c ∧ c ≤ C b + ENNReal.ofReal ε := by
    obtain ⟨ρ, θ, hρ, hρ0, hρ1, hc⟩ := exists_path_replacing_finite_limit_block
      hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad hUB hdense
      ν N (E b.castSucc) (E b.succ) (hE _) (hE _) (shape b)
      (fun i => p ⟨b, i⟩) (fun i => hpB ⟨b, i⟩) (fun i => hp ⟨b, i⟩)
      (fun j k => Γ b j (s k)) (fun j k => hΓ b j (s k))
      (fun k => hΓF b (s k)) (fun k => hΓH b (s k))
      (fun i => hstart ⟨b, i⟩) (fun i => hend ⟨b, i⟩)
      g hg henergy m hm (fun j => A ⟨b, j⟩) (fun j => hA ⟨b, j⟩)
      (fun j => hcost ⟨b, j⟩) (fun i => J ⟨b, i⟩) (fun i => hpaid ⟨b, i⟩)
      w hw hpos hpoint hε
    exact ⟨ρ.val ⊥, hρ0, ρ.val ⊤, hρ1, physicalTollCost d g m ρ,
      PaidChain.single (physicalJumpEdge_of_path d ν N g m _ T (ρ, θ) hρ hρ0.2 hρ1.2), hc⟩
  have hjumps (i : Fin q) (x : Sphere) (hx : x ∈ E' i.succ.castSucc)
      (y : Sphere) (hy : y ∈ E' i.succ.castSucc) : R x y (T i) :=
    physicalJumpEdge_of_jump d ν N g m _ T i hx hy
  obtain ⟨x, hx, y, hy, c, hc, hbound⟩ :=
    exists_paid_chain_from_approximate_blocks R q E' C T hjumps hblocks hη
  refine ⟨x, hx, y, hy, c, hc, hbound.trans ?_⟩
  apply add_le_add _ le_rfl
  simpa only [C, P, I, Fintype.sum_sigma, Finset.sum_add_distrib] using htotal

end CircleDomainRigidity

end

end OAI
