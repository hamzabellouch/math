import Mathlib
import OAI.Geometry.NearbyLagrangian.CriticalSections
import OAI.Geometry.NearbyLagrangian.VerticalChanges
import OAI.Geometry.NearbyLagrangian.HomogeneousTails
import OAI.Geometry.NearbyLagrangian.SupportedEvolution
import OAI.Geometry.NearbyLagrangian.FlatCotangent

namespace OAI

/-! Restored central endpoints after compact Hamiltonian transport. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Transport
open Set Filter ContinuousLinearMap InnerProductSpace TopologicalSpace SmoothFlow Tubes
open scoped ContDiff Topology Manifold
variable {V Z B : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace Z] {I : ModelWithCorners ℝ V Z}
  [TopologicalSpace B] [ChartedSpace Z B] [IsManifold I ∞ B]
  [T2Space B] [CompactSpace B]

theorem exists_core_restored_endpoint {m d : ℕ}
    (U₀ : Opens (Euclidean d)) {C : Set (Euclidean d)}
    (hC : IsOpen C) (hCU : C ⊆ (U₀:Set (Euclidean d)))
    {F g : Euclidean d × Euclidean (m+m) → ℝ}
    (hF : ∀ x ∈ U₀, ∀ w, ContDiffAt ℝ ∞ F (x,w))
    (hg : ∀ x ∈ U₀, ∀ w, ContDiffAt ℝ 1 g (x,w))
    (hhom : ∀ x ∈ U₀, ∀ r : ℝ, 0 < r → ∀ w, g (x,r • w) = r^2*g (x,w))
    (hreg : ∀ x ∈ U₀, ∀ w, w ≠ 0 → verticalDifferential g x w ≠ 0)
    (R₀ : ℝ) (htail : ∀ x ∈ U₀, ∀ w, R₀ ≤ ‖w‖ → F (x,w) = g (x,w))
    (hM : MorseOn U₀ F)
    (hinj : Function.Injective (fun q : PhaseCritical U₀ F => phaseGenerate F q.val))
    {K : ℝ × (Euclidean d × Euclidean d) → ℝ}
    (T : SupportedHamiltonianEvolution (CotangentGeometry.openPhase U₀) K)
    (hcenter : Set.range (fun q : PhaseCritical U₀ F =>
        evolution T.flow ((0,phaseGenerate F q.val),1)) ∩ (C ×ˢ univ) =
      Set.range (fun x : C => ((x:Euclidean d),(0:Euclidean d))))
    {j : B → Euclidean d} (hj : ContMDiff I 𝓘(ℝ,Euclidean d) ∞ j)
    (hjC : ∀ b, j b ∈ C) (a : C(B,Tube m m))
    (href : ∀ b w, g (j b,w) = (a b).val w) :
    ∃ (n : ℕ) (A : ℝ)
      (δ : C(B,Tube (transportIndex m d n) (transportIndex m d n)))
      (H : B × Euclidean (transportIndex m d n+transportIndex m d n) → ℝ)
      (σ : B → Euclidean (transportIndex m d n+transportIndex m d n)),
      1 ≤ A ∧ ((addBalancedFor m d n).comp a).Homotopic δ ∧
      (∀ q : B × Euclidean (transportIndex m d n+transportIndex m d n), q.2 ≠ 0 →
        ContMDiffAt (I.prod 𝓘(ℝ,Euclidean (transportIndex m d n+transportIndex m d n)))
          𝓘(ℝ,ℝ) ∞ (fun q => (δ q.1).val q.2) q) ∧
      ContMDiff (I.prod 𝓘(ℝ,Euclidean (transportIndex m d n+transportIndex m d n)))
        𝓘(ℝ,ℝ) ∞ H ∧
      (∀ q, 2*A ≤ ‖q.2‖ → H q = (δ q.1).val q.2) ∧
      ContMDiff I 𝓘(ℝ,Euclidean (transportIndex m d n+transportIndex m d n)) ∞ σ ∧
      (∀ b w, fderiv ℝ (fun w => H (b,w)) w = 0 ↔ w = σ b) ∧
      (∀ b, Function.Bijective (fderiv ℝ (fderiv ℝ (fun w => H (b,w))) (σ b))) := by
  let S : Set (Euclidean d) := Prod.fst '' T.supportSet ∪ Set.range j
  have hS : IsCompact S := (T.compact.image continuous_fst).union
    (isCompact_range hj.continuous)
  have hSU : S ⊆ U₀ := by
    rintro x (⟨z,hz,rfl⟩ | ⟨b,rfl⟩)
    · exact (T.inside hz).1
    · exact hCU (hjC b)
  obtain ⟨U,hU,hSU',hclU,hcomp⟩ :=
    exists_open_between_and_isCompact_closure hS U₀.isOpen hSU
  have hUU : U ⊆ U₀ := subset_closure.trans hclU
  have hjU (b : B) : j b ∈ U := hSU' (Or.inr (mem_range_self b))
  have hsupport : ∀ z ∈ T.supportSet, z.1 ∈ U := by
    intro z hz
    exact hSU' (Or.inl ⟨z,hz,rfl⟩)
  let C' := U ∩ C
  have hC' : IsOpen C' := hU.inter hC
  have hC'U : C' ⊆ U := inter_subset_left
  have hT : TameOn U F g := tameOn_of_compact_homogeneous_tail U₀.isOpen
    hcomp subset_closure hclU hF hg hhom
    (fun x hx => hreg x (hclU hx)) R₀ htail
  let ψ : ℝ → Euclidean d × Euclidean d → Euclidean d × Euclidean d :=
    fun t z => evolution T.flow ((0,z),t)
  have hfix (z : Euclidean d × Euclidean d) (hz : z.1 ∉ U) : ψ 1 z = z := by
    by_contra hn
    have hs : z ∈ T.supportSet := T.flowSupport 0 1 (sub_ne_zero.mpr hn)
    exact hz (hsupport z hs)
  have himage : Set.range (fun q : PhaseCritical U F => ψ 1 (phaseGenerate F q.val)) ∩
      (C' ×ˢ univ) = Set.range (fun x : C' => ((x:Euclidean d),(0:Euclidean d))) := by
    ext z
    constructor
    · rintro ⟨⟨q,hq⟩,hz⟩
      have hz₀ : z ∈ Set.range (fun q : PhaseCritical U₀ F => ψ 1 (phaseGenerate F q.val)) ∩
          (C ×ˢ univ) :=
        ⟨⟨⟨q.val,hUU q.property.1,q.property.2⟩,hq⟩,hz.1.2,mem_univ _⟩
      change z ∈ Set.range (fun q : PhaseCritical U₀ F =>
        evolution T.flow ((0,phaseGenerate F q.val),1)) ∩ (C ×ˢ univ) at hz₀
      rw [hcenter] at hz₀
      obtain ⟨x,hx⟩ := hz₀
      refine ⟨⟨z.1,hz.1⟩,?_⟩
      change (z.1,(0:Euclidean d)) = z
      apply Prod.ext
      · rfl
      · change (0:Euclidean d) = z.2
        have hh := congrArg (fun q : Euclidean d × Euclidean d => q.2) hx
        exact hh
    · rintro ⟨x,rfl⟩
      have hz₀ : ((x:Euclidean d),0) ∈ Set.range (fun q : PhaseCritical U₀ F =>
          evolution T.flow ((0,phaseGenerate F q.val),1)) ∩ (C ×ˢ univ) := by
        rw [hcenter]
        exact ⟨⟨x.val,x.property.2⟩,rfl⟩
      obtain ⟨⟨q,hq⟩,_⟩ := hz₀
      have hqU : q.val.1 ∈ U := by
        by_contra hn
        have he := hfix (phaseGenerate F q.val) hn
        have he' : ψ 1 (phaseGenerate F q.val) = ((x:Euclidean d),0) := hq
        have hx : q.val.1 = (x:Euclidean d) := congrArg Prod.fst (he.symm.trans he')
        exact hn (hx ▸ x.property.1)
      exact ⟨⟨⟨q.val,hqU,q.property.2⟩,hq⟩,x.property,mem_univ _⟩
  have hψ₀ : ∀ z, ψ 0 z = z := fun z => evolution_initial T.flow 0 z
  have hψ₁ : Function.Injective (ψ 1) :=
    (evolutionDiffeomorph T.flow (contDiff_hamiltonianField T.smooth) T.lipschitz 0 1).injective
  obtain ⟨n,F',s,hT',hM',hs,hc,hh⟩ := transported_central_zeroSection_endpoint hU hC' hC'U
    T.compact hsupport T.smooth.contDiffOn (fun t _ => T.hamiltonianSupport t)
    (fun z t _ => (evolution_derivative T.flow 0 z t).hasDerivWithinAt) hψ₀ hψ₁ hT
    (fun x hx => hM x (hUU hx)) (phase_injective_restrict hUU hinj) himage
  obtain ⟨A,δ,H,σ,hA,_,hδ,hδs,hHs,_,hHo,hσ,hHc,hHh⟩ :=
    exists_restored_tube_endpoint hT' hs hc hh hj (fun b => ⟨hjU b,hjC b⟩) a href 0
  exact ⟨n,A,δ,H,σ,hA,hδ,hδs,hHs,hHo,hσ,hHc,hHh⟩

end NearbyLagrangian.Transport

end

end OAI
