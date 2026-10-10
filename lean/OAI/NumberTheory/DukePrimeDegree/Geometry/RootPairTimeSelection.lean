import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingTimeCovariance

namespace OAI

/-!
# Actual diagonal recurrence with simultaneous leaf covariance

The correct two-coordinate shearing flow has a large measurable set on
which both recurrence estimates hold on every long interval. Removing
one null set also gives leaf covariance at almost every time. The common
time can therefore satisfy all six recurrence conditions and all six
covariance identities used in the two-scale argument.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def RootPairLeafCovariance {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (x : X n) (t : ℝ) : Prop :=
  intrinsicRootKernel hij μ hfree (rightAction x (rootPairFlow i j (-t))) =
    rootPairCovarianceKernel hij μ hfree (x, t)

theorem exists_rootPair_two_target_covariance_set
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (G H : Set (X (d + 1))) (hG : MeasurableSet G) (hH : MeasurableSet H)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Z : Set (X (d + 1)), MeasurableSet Z ∧
      μ Zᶜ ≤ ENNReal.ofReal (2 * μ.real Gᶜ / ε) + ENNReal.ofReal (2 * μ.real Hᶜ / ε) ∧
      ∀ z ∈ Z,
        (∀ᵐ t : ℝ ∂volume, RootPairLeafCovariance hij μ hfree z t) ∧
        ∀ T : ℝ, 1 ≤ T →
          volume.real (Ioc 0 T ∩ {t | rightAction z (rootPairFlow i j (-t)) ∉ G}) ≤ ε * T ∧
          volume.real (Ioc 0 T ∩ {t | rightAction z (rootPairFlow i j (-t)) ∉ H}) ≤ ε * T := by
  obtain ⟨ZG, hZG, hmG, htG⟩ :=
    exists_rootPairFlow_return_good_set d i j μ hA Gᶜ hG.compl ε hε
  obtain ⟨ZH, hZH, hmH, htH⟩ :=
    exists_rootPairFlow_return_good_set d i j μ hA Hᶜ hH.compl ε hε
  have hcov : ∀ᵐ x ∂μ, ∀ᵐ t : ℝ ∂volume, RootPairLeafCovariance hij μ hfree x t :=
    ae_rootPairKernel_covariance_time d hij μ hA hfree
  obtain ⟨N, hbad, hN, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hcov)
  refine ⟨(ZG ∩ ZH) \ N, (hZG.inter hZH).diff hN, ?_, ?_⟩
  · rw [compl_sdiff, compl_inter, union_comm N]
    calc
      μ (ZGᶜ ∪ ZHᶜ ∪ N) ≤ μ (ZGᶜ ∪ ZHᶜ) + μ N := measure_union_le _ _
      _ = μ (ZGᶜ ∪ ZHᶜ) := by rw [hNzero, add_zero]
      _ ≤ μ ZGᶜ + μ ZHᶜ := measure_union_le _ _
      _ ≤ _ := add_le_add hmG hmH
  · intro z hz
    refine ⟨?_, fun T hT => ⟨htG z hz.1.1 T hT, htH z hz.1.2 T hT⟩⟩
    by_contra h
    exact hz.2 (hbad h)

theorem common_rootPair_time_with_covariance
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (G H : Set (X (d + 1))) (z : Fin 2 → X (d + 1))
    (T ε : ℝ) (hT : 1 ≤ T) (hε : 36 * ε < 1)
    (θ η : Fin 2 → ℝ)
    (hθlo : ∀ q, 4 * T ≤ θ q) (hθhi : ∀ q, θ q ≤ 6 * T)
    (hη : ∀ q, η q = 0 ∨ η q = 1)
    (hcov : ∀ k, ∀ᵐ t : ℝ ∂volume, RootPairLeafCovariance hij μ hfree (z k) t)
    (hcontrol : ∀ k, ∀ S : ℝ, 1 ≤ S →
      volume.real (Ioc 0 S ∩ {t | rightAction (z k) (rootPairFlow i j (-t)) ∉ G}) ≤ ε * S ∧
      volume.real (Ioc 0 S ∩ {t | rightAction (z k) (rootPairFlow i j (-t)) ∉ H}) ≤ ε * S) :
    ∃ τ ∈ Ioc 0 T,
      (∀ k, rightAction (z k) (rootPairFlow i j (-τ)) ∈ G ∧
        RootPairLeafCovariance hij μ hfree (z k) τ) ∧
      ∀ k q, rightAction (z k)
          (rootPairFlow i j (-((θ q + (2 - η q) * τ) / 2))) ∈ H ∧
        RootPairLeafCovariance hij μ hfree (z k) ((θ q + (2 - η q) * τ) / 2) := by
  exact exists_common_two_scale_time_with_covariance
    (fun t x => rightAction x (rootPairFlow i j (-t))) G H z T ε
    (by linarith) hε θ η hθlo hθhi hη
    (fun k => (hcontrol k T hT).1)
    (fun k => (hcontrol k (4 * T) (by linarith)).2)
    (RootPairLeafCovariance hij μ hfree) hcov

end DukePrimeDegree

end

end OAI
