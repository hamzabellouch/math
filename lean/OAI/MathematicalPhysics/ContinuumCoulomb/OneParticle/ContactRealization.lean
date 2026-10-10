import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactGlobalSeparation
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactExtent

namespace OAI

/-! A geometric realization of the exact final mediator graph, with
independently prescribed near-unit edge lengths and uniform nonedge gaps. -/

noncomputable section
namespace ContinuumCoulomb.ContactMediator
open MediatorIteration

/-- No graph isomorphism or extra geometric premise is assumed: the output
is indexed by the actual finalGraph vertices and edges. -/
theorem exists_finalGraph_realization (d : SquareLatticeHeisenberg) (W G : ℕ)
    (ℓ : GlobalEdge d → ℝ)
    (hℓ : ∀ a, ℓ a ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance)) :
    ∃ Q : GlobalSite d → ContactPoint,
      (∀ i, Q (siteEquiv d.vertices d.edges (Sum.inl i)) = contactGridPoint (d.coordinate i)) ∧
      (∀ a, dist (Q ((finalGraph d.bonds W G).left a))
        (Q ((finalGraph d.bonds W G).right a)) = ℓ a) ∧
      (∀ x y, x ≠ y → Nonedge d W G x y → 6 / 5 < dist (Q x) (Q y)) ∧
      (∀ x y, x ≠ y → 1 - contactLengthTolerance ≤ dist (Q x) (Q y)) ∧
      (∀ M : ℝ, (∀ j i, |(contactGridAxis (d.coordinate j) i : ℝ)| ≤ M) →
        ∀ x i, |Q x i| ≤ 17 * M + 17) := by
  choose P hP using fun e => exists_finalGraph_gadget_geometry d.bonds W G e ℓ hℓ
  have h₀ : ∀ e, P e (localOld 0) = contactPoint 0 0 := fun e => (hP e).1
  have h₁ : ∀ e, P e (localOld 1) = contactPoint 17 0 := fun e => (hP e).2.1
  have hlen : ∀ e a, dist (P e (localLeft (member (d.coefficient e)) a))
      (P e (localRight a)) = ℓ (encodeEdge d.edges e a) := fun e => (hP e).2.2.1
  have hsep : ∀ e x y, x ≠ y → Nonedge d W G
      (localVertex (d.left e) (d.right e) e x)
      (localVertex (d.left e) (d.right e) e y) → 6 / 5 < dist (P e x) (P e y) :=
    fun e => (hP e).2.2.2.1
  have hnear : ∀ e x, dist (P e x)
      (contactBaseGadgetPosition (edgeNegative d.bonds e) (localToContact x)) < 1 / 20 :=
    fun e => (hP e).2.2.2.2
  have hn := globalPosition_nonedge d W G P h₀ h₁ hsep hnear
  exact ⟨globalPosition d P, globalPosition_old d P,
    globalPosition_link_lengths d W G P h₀ h₁ ℓ hlen, hn,
    globalPosition_separation d W G P h₀ h₁ ℓ hlen (fun a => (hℓ a).1) hn,
    fun _ hc x i => globalPosition_coordinate_bound d P hc hnear x i⟩

private theorem dist_real_smul (D : ℝ) (hD : 0 < D) (x y : ContactPoint) :
    dist (D • x) (D • y) = D * dist x y := by
  simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hD]

/-- Multiplication by the chosen physical spacing preserves every exact
edge length and gives the required strict nonedge separation. -/
theorem exists_scaled_finalGraph_realization (d : SquareLatticeHeisenberg) (W G : ℕ)
    (D : ℝ) (hD : 0 < D) (ℓ : GlobalEdge d → ℝ)
    (hℓ : ∀ a, ℓ a ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance)) :
    ∃ Q : GlobalSite d → ContactPoint,
      (∀ a, dist (Q ((finalGraph d.bonds W G).left a))
        (Q ((finalGraph d.bonds W G).right a)) = D * ℓ a) ∧
      (∀ x y, x ≠ y → Nonedge d W G x y → (6 / 5) * D < dist (Q x) (Q y)) ∧
      (∀ x y, x ≠ y → (1 - contactLengthTolerance) * D ≤ dist (Q x) (Q y)) ∧
      Function.Injective Q ∧
      (∀ M : ℝ, (∀ j i, |(contactGridAxis (d.coordinate j) i : ℝ)| ≤ M) →
        ∀ x i, |Q x i| ≤ D * (17 * M + 17)) := by
  obtain ⟨Q, _, hlen, hnon, hsep, hext⟩ := exists_finalGraph_realization d W G ℓ hℓ
  refine ⟨fun x => D • Q x, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [dist_real_smul D hD, hlen]
  · intro x y hxy hn
    rw [dist_real_smul D hD]
    nlinarith [hnon x y hxy hn]
  · intro x y hxy
    rw [dist_real_smul D hD]
    nlinarith [hsep x y hxy]
  · intro x y hxy
    by_contra hne
    have hpos : 0 < (1 - contactLengthTolerance) * D :=
      mul_pos (by norm_num [contactLengthTolerance]) hD
    have hs := hsep x y hne
    have hz : dist (D • Q x) (D • Q y) = 0 := dist_eq_zero.mpr hxy
    rw [dist_real_smul D hD] at hz
    nlinarith
  · intro M hc x i
    change |D * Q x i| ≤ _
    rw [abs_mul, abs_of_pos hD]
    exact mul_le_mul_of_nonneg_left (hext M hc x i) hD.le

end ContinuumCoulomb.ContactMediator

end

end OAI
