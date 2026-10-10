import OAI.Analysis.CircleDomains.Selection.NewJumpLevel
import OAI.Analysis.CircleDomains.Selection.TrueChainConcatenation
import OAI.Analysis.CircleDomains.Modulus.BarrierJumpLosses

namespace OAI

/-! Install all finite jump levels while retaining a common separation bound.
Each stage is obtained from the proved jump-removal theorem, and every finite
chain in the union is reduced to one finite stage. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]

theorem exists_progressive_barrier_jump_system
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
    (F H : Set Sphere)
    (hF : frontier F ⊆ d.quotientDomain) (hH : frontier H ⊆ d.quotientDomain)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    (htrue : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ F → Γ.1.val ⊤ ∈ H → ENNReal.ofReal ((1 : ℝ)/2) ≤ physicalTollCost d g m Γ.1)
    (hBU : Bᶜ ⊆ d.quotientDomain) (S : Set Sphere) (hS : IsOpen S) (hBS : B ⊆ S)
    (ρ : ℕ → ℝ≥0∞) (hρ : ∀n, 0 < ρ n)
    (τ mesh : ℕ → ℝ) (hτ : ∀n, 0 < τ n) (hmesh : ∀n, 0 < mesh n) :
    ∃J : ℕ → FiniteJumpSystem Sphere,
      (∀n i, frontier ((J n).region i) ⊆ d.quotientDomain) ∧
      (∀n i, 0 < (J n).toll i) ∧
      (∀n x y c, (J n).edge d ν N g m x y c → (J (n+1)).edge d ν N g m x y c) ∧
      (∀n, ∃k : ℕ, ∃V : Fin k → Set Sphere,
        (∀i, IsOpen (V i)) ∧ B ⊆ ⋃i, V i ∧
        Pairwise (Disjoint on fun i => closure (V i)) ∧
        (∀i, closure (V i) ⊆ S) ∧ (∀i, Metric.diam (V i) < mesh n) ∧
        (∀i, (V i ∩ B).Nonempty) ∧
        ∀i x, x ∈ V i ∩ d.quotientDomain → ∀y, y ∈ V i ∩ d.quotientDomain →
          (J (n+1)).edge d ν N g m x y (fixedWidthJumpToll B m (ρ n) (τ n) (V i))) ∧
      ∀x ∈ F ∩ d.quotientDomain, ∀y ∈ H ∩ d.quotientDomain, ∀c,
        PaidChain (fun x y c => ∃n, (J n).edge d ν N g m x y c) x y c →
          ENNReal.ofReal ((1 : ℝ)/4) ≤ c := by
  classical
  let Good (n : ℕ) (A : FiniteJumpSystem Sphere) : Prop :=
    (∀i, frontier (A.region i) ⊆ d.quotientDomain) ∧ (∀i, 0 < A.toll i) ∧
    ∀x ∈ F ∩ d.quotientDomain, ∀y ∈ H ∩ d.quotientDomain, ∀c,
      PaidChain (A.edge d ν N g m) x y c → ENNReal.ofReal (barrierStageLower n) ≤ c
  let Stage (n : ℕ) := {A : FiniteJumpSystem Sphere // Good n A}
  let Step (n : ℕ) (A C : FiniteJumpSystem Sphere) : Prop :=
    (∀x y c, A.edge d ν N g m x y c → C.edge d ν N g m x y c) ∧
    ∃k : ℕ, ∃V : Fin k → Set Sphere,
      (∀i, IsOpen (V i)) ∧ B ⊆ ⋃i, V i ∧
      Pairwise (Disjoint on fun i => closure (V i)) ∧
      (∀i, closure (V i) ⊆ S) ∧ (∀i, Metric.diam (V i) < mesh n) ∧
      (∀i, (V i ∩ B).Nonempty) ∧
      ∀i x, x ∈ V i ∩ d.quotientDomain → ∀y, y ∈ V i ∩ d.quotientDomain →
        C.edge d ν N g m x y (fixedWidthJumpToll B m (ρ n) (τ n) (V i))
  have hnext (n : ℕ) (A : Stage n) : ∃C : Stage (n+1), Step n A.val C.val := by
    let := A.val.finite
    obtain ⟨k, V, hVo, hcover, hpair, hsafe, hdiam, hmeet, hfront, hpositive, hlower⟩ :=
      exists_safe_new_jump_level hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj
        hr he hB hTD hbad hUB hdense hinfty ν N F H A.val.region hF hH A.property.1
        g hg henergy m hm (ρ n) (hτ n) A.val.toll w hw hpos hpoint
        (barrierStageLoss_pos n) (barrierStageLoss_lt n) A.property.2.2
        (hρ n) A.property.2.1 hBU S hS hBS (hmesh n)
    let C := A.val.append k V (fun i => fixedWidthJumpToll B m (ρ n) (τ n) (V i))
    have hC : Good (n+1) C := by
      refine ⟨?_, ?_, ?_⟩
      · intro i
        change A.val.Label ⊕ Fin k at i
        cases i with
        | inl i => exact A.property.1 i
        | inr i => exact hfront i
      · intro i
        change A.val.Label ⊕ Fin k at i
        cases i with
        | inl i => exact A.property.2.1 i
        | inr i => exact hpositive i
      · intro x hx y hy c hc
        have h := hlower x hx y hy c hc
        rw [barrierStageLower_sub_loss] at h
        exact h
    refine ⟨⟨C, hC⟩, ?_, k, V, hVo, hcover, hpair, hsafe, hdiam, hmeet, ?_⟩
    · intro x y c hc
      exact A.val.edge_append_old k V _ d ν N g m hc
    · intro i x hx y hy
      exact A.val.edge_append_new k V _ d ν N g m i hx hy
  have hzero : Good 0 FiniteJumpSystem.empty := by
    refine ⟨fun i => PEmpty.elim i, fun i => PEmpty.elim i, ?_⟩
    intro x hx y hy c hc
    obtain ⟨Γ, hΓ, hΓ0, hΓ1, hcost⟩ := exists_path_of_true_paid_chain
      d hU hdisj ν N g hg m hm hpoint hc hx.2 hy.2
    rw [barrierStageLower_zero, ← hcost]
    exact htrue Γ hΓ (hΓ0.symm ▸ hx.1) (hΓ1.symm ▸ hy.1)
  let A₀ : Stage 0 := ⟨FiniteJumpSystem.empty, hzero⟩
  let A : ∀n, Stage n := fun n => Nat.rec A₀ (fun n C => Classical.choose (hnext n C)) n
  have hstep (n : ℕ) : Step n (A n).val (A (n+1)).val :=
    Classical.choose_spec (hnext n (A n))
  let J : ℕ → FiniteJumpSystem Sphere := fun n => (A n).val
  have hmono (n k : ℕ) (hnk : n ≤ k) :
      ∀x y c, (J n).edge d ν N g m x y c → (J k).edge d ν N g m x y c := by
    induction k, hnk using Nat.le_induction with
    | base => exact fun _ _ _ h => h
    | succ k hk ih => exact fun x y c hc => (hstep k).1 x y c (ih x y c hc)
  refine ⟨J, fun n => (A n).property.1, fun n => (A n).property.2.1,
    fun n => (hstep n).1, fun n => (hstep n).2, ?_⟩
  intro x hx y hy c hc
  obtain ⟨n, hn⟩ := hc.exists_stage hmono
  exact (ENNReal.ofReal_le_ofReal (quarter_lt_barrierStageLower n).le).trans
    ((A n).property.2.2 x hx y hy c hn)

end CircleDomainRigidity

end

end OAI
