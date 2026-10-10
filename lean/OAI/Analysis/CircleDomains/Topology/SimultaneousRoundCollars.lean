import OAI.Analysis.CircleDomains.Topology.RoundCollarLifts

namespace OAI

/-! Finitely many actual source branches give all the nonsingular target
collar lifts at one common positive width. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem exists_common_positive_bound {I : Type*} [Fintype I]
    (d : I → ℝ) (hd : ∀ i, 0 < d i) :
    ∃ δ > 0, ∀ i, δ ≤ d i := by
  classical
  let S : Finset ℝ := insert 1 (Finset.univ.image d)
  have hS : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨S.min' hS, ?_, ?_⟩
  · have hm := Finset.min'_mem S hS
    rcases Finset.mem_insert.mp hm with hm | hm
    · rw [hm]; exact zero_lt_one
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
      rw [← hi]
      exact hd i
  · intro i
    exact Finset.min'_le S (d i)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))

 theorem TerminalComponentAssignment.simultaneous_round_collar_lifts
    {I : Type*} [Fintype I] {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (c : I → ℂ) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hext : ((↑) : ℂ → Sphere) ⁻¹' V = (⋃ i, closedBall (c i) (r i))ᶜ)
    (htarget : ∀ i, ((↑) : ℂ → Sphere) '' closedBall (c i) (r i) ⊆
      connectedComponentIn Vᶜ (a.point i))
    (b : I) (U : I → Set Sphere) (v : I → Sphere → ℝ) (w : Sphere → UnitAddCircle)
    (hU : ∀ i ≠ b, IsOpen (U i))
    (hboundary : ∀ i ≠ b, ((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i)) ⊆ U i)
    (hv : ∀ i ≠ b, ContinuousOn (v i) (U i))
    (hproj : ∀ i ≠ b, ∀ x ∈ U i, (v i x : UnitAddCircle) = w x)
    (A : I → ℝ) (hA : ∀ i ≠ b, ∀ x ∈ frontier (jordanInterior (T i)),
      ∀ y ∈ frontier (jordanInterior (T i)), |v i (x : Sphere) - v i (y : Sphere)| ≤ A i)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ρ ∈ Ioo (0 : ℝ) δ, ∃ q : I → ℝ → ℝ, ∀ i ≠ b,
      Continuous (q i) ∧
      (∀ t, (q i t : UnitAddCircle) = w (fi (unitCircleParam (c i) (r i + ρ) t : Sphere))) ∧
      q i 1 = q i 0 ∧ ∀ t ∈ Icc (0 : ℝ) 1, |q i t - q i 0| ≤ A i + ε := by
  classical
  have hex (i : I) : ∃ δ > 0, ∀ ρ ∈ Ioo (0 : ℝ) δ, i ≠ b →
      Continuous (roundCollarRealLift fi (v i) (c i) (r i + ρ)) ∧
      (∀ t, (roundCollarRealLift fi (v i) (c i) (r i + ρ) t : UnitAddCircle) =
        w (fi (unitCircleParam (c i) (r i + ρ) t : Sphere))) ∧
      roundCollarRealLift fi (v i) (c i) (r i + ρ) 1 = roundCollarRealLift fi (v i) (c i) (r i + ρ) 0 ∧
      ∀ t ∈ Icc (0 : ℝ) 1, |roundCollarRealLift fi (v i) (c i) (r i + ρ) t -
        roundCollarRealLift fi (v i) (c i) (r i + ρ) 0| ≤ A i + ε := by
    by_cases hi : i = b
    · exact ⟨1, zero_lt_one, fun _ _ hne => (hne hi).elim⟩
    · obtain ⟨δ, hδ, hvδ⟩ := a.exists_round_collar_lifts hf c r hr hd hext i (htarget i)
        (hU i hi) (hboundary i hi) (v i) (hv i hi) w (hproj i hi) (A i) (hA i hi) hε
      exact ⟨δ, hδ, fun ρ hρ _ => hvδ ρ ⟨hρ.1, hρ.2.le⟩⟩
  choose d hdpos hvalid using hex
  obtain ⟨δ, hδ, hδle⟩ := exists_common_positive_bound d hdpos
  refine ⟨δ, hδ, ?_⟩
  intro ρ hρ
  exact ⟨fun i => roundCollarRealLift fi (v i) (c i) (r i + ρ),
    fun i hi => hvalid i ρ ⟨hρ.1, hρ.2.trans_le (hδle i)⟩ hi⟩

end CircleDomainRigidity

end

end OAI
