import OAI.MeasureTheory.Falconer.Estimates.PositiveDistancePushforward
import OAI.MeasureTheory.Falconer.Angular.StationaryPairSupport
import OAI.MeasureTheory.Falconer.Recursion.InheritedPolicyState

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem endpointDescriptorGood_of_occupied (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ)
    (d : PolicyDescriptor) (x : Plane) (dir : UnitCircle) (P : CellPath)
    (hP : P ∈ occupiedAnchorPaths Q ρ (descriptorAnchor d))
    (hx : x ∈ (Q.descendant P).carrier)
    (hg : dir ∈ descriptorGoodSet Q ρ m N lam sig J i P d) :
    (x,dir) ∈ endpointDescriptorGood Q ρ m N lam sig J i d := by
  intro P' hP' hx'
  have hlen := (mem_dyadicPaths _ P).mp (Finset.mem_filter.mp hP).1
  have hlen' := (mem_dyadicPaths _ P').mp hP'
  have he : P' = P := by
    by_contra hne
    exact Set.disjoint_left.mp (Q.descendants_disjoint hQ (hlen'.trans hlen.symm) hne) hx' hx
  simpa only [he] using hg

theorem ae_all_occupied_pair (Q : DyadicSquare) (ρ : Measure Plane) [SFinite ρ]
    (hcarry : ρ Q.carrierᶜ = 0) :
    ∀ᵐ z ∂ρ.prod ρ, ∀ n : ℕ,
      (∃ P ∈ occupiedAnchorPaths Q ρ n, z.1 ∈ (Q.descendant P).carrier) ∧
      (∃ P ∈ occupiedAnchorPaths Q ρ n, z.2 ∈ (Q.descendant P).carrier) := by
  have ha : ∀ᵐ x ∂ρ, ∀ n : ℕ,
      ∃ P ∈ occupiedAnchorPaths Q ρ n, x ∈ (Q.descendant P).carrier :=
    ae_all_iff.mpr (fun n => ae_occupied_anchor Q ρ hcarry n)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae ha,
    Measure.quasiMeasurePreserving_snd.ae ha] with z hz₁ hz₂
  exact fun n => ⟨hz₁ n,hz₂ n⟩

theorem uniform_actual_pair_minimal_good {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicSquare), Q.side = 1 →
    ∀ (ρ : Measure Plane) [SFinite ρ], ρ Q.carrierᶜ = 0 →
    ∀ (m : ℝ → ℝ) (q a₀ t₀ a b v : ℕ), 0 < q → a₀ ≤ b → v ≤ t₀ →
    a ≤ b → v ≤ N →
    ∀ (S : Finset PolicyDescriptor) (k : PolicyDescriptor → ℕ),
    remainingPolicyDescriptors (fun n => m n-(n:ℝ)/(N:ℝ)) N q a₀ t₀ a ⊆ S →
    ∀ (lam : ℝ) (i : ℕ) (h : Plane → ℂ),
    ∀ᵐ z ∂ρ.prod ρ, ∀ (plus : Bool) (j : ℕ) (θ Λ : ℝ),
    sourceRadialUnit z.2 z.1 = sourceUnitDirection θ →
    signedStationaryJet plus j
      (fun t => inheritedCircleSymbol S id k Q ρ m N lam sig J i h z.1 (sourceUnitDirection t) *
        conj (inheritedCircleSymbol S id k Q ρ m N lam sig J i h z.2 (sourceUnitDirection t))) θ Λ ≠ 0 →
    z ∈ positiveDistanceGoodSet Q ρ m N q b v lam sig J (i+1) := by
  obtain ⟨N₀,h₀⟩ := uniform_actual_pair_jet_good hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ _ hcarry m q a₀ t₀ a b v hq hl hr hab hv S k hS lam i h
  have hmin := (minimal_policy_list_survives (fun n => m n-(n:ℝ)/(N:ℝ))
    hq hl hr hab).trans hS
  filter_upwards [ae_all_occupied_pair Q ρ hcarry] with z hz
  intro plus j θ Λ hdir hn d hd
  obtain ⟨⟨Px,hPx,hx⟩,⟨Py,hPy,hy⟩⟩ := hz (descriptorAnchor d)
  have hg := h₀ N hN S id k Q hQ ρ m lam i h z.1 z.2 plus j θ Λ hn d (hmin hd)
    (policyDescriptor_valid _ hq hv hd) Px Py hPx hPy hx hy
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  rw [← hdir] at hg
  exact ⟨endpointDescriptorGood_of_occupied Q hQpos ρ m N lam sig J (i+1) d z.1 _ Px hPx hx hg.1,
    endpointDescriptorGood_of_occupied Q hQpos ρ m N lam sig J (i+1) d z.2 _ Py hPy hy hg.2⟩

end PlanarFalconer

end OAI
