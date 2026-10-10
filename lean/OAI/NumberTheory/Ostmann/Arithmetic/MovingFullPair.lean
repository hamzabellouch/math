import OAI.NumberTheory.Ostmann.Arithmetic.MovingFullSpectator
import OAI.NumberTheory.Ostmann.Arithmetic.SampledSpectatorComparison

namespace OAI

/-! # The good-matching diagram for the full moving-giant coefficients -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def movingSampleBaseWeight {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ) (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List σ) n) (samples : MovingSampleSlots σ n) (XL XR : ℕ) : ℂ :=
  recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
    (movingSlotCutoff value childBound pivotBound extra) n
    ⟨n, buildMovingSlotData n t small bulk samples, XL, XR⟩ t

noncomputable def movingSampleFullWeight {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ) (g : ZMod q → ℂ) (D : (ZMod q)ˣ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n) (XL XR : ℕ) : ℂ :=
  movingSampleBaseWeight value childBound pivotBound
    (fun x s => F x s * spectatorHistoryLeaf (movingSlotModulus value) g D x s)
    extra n t small bulk samples XL XR

theorem moving_sample_full_weight_factor {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (hextra : ∀ x s v w, extra x s v w ≠ 0 →
      (historyPivot (movingSlotSystem value childBound pivotBound) x s v w : ZMod q) ≠ 0)
    (g : ZMod q → ℂ) (D : (ZMod q)ˣ) (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List σ) n) (samples : MovingSampleSlots σ n) (XL XR : ℕ) :
    movingSampleFullWeight value childBound pivotBound F extra g D n t small bulk samples XL XR =
      movingSampleBaseWeight value childBound pivotBound F extra n t small bulk samples XL XR *
      movingGiantAmplitude g D
        (buildMovingGiantTree n t (movingSlotValues value n small) (samples.values value))
        XL XR (movingSlotValues value n bulk) := by
  unfold movingSampleFullWeight movingSampleBaseWeight
  rw [movingSlotWeight_spectator value childBound pivotBound F extra hextra g D _ t
    (buildMovingSlotData_follows n t small bulk samples) XL XR, buildMovingSlotData_spectator]

/-- The quartet bound is now attached to the actual full coefficient, with
its original arithmetic and smooth support retained in the scalar factor. -/
theorem moving_full_pair_good_comparison {σ : Type*} {q : ℕ} [Fact q.Prime] (hq : 3 ≤ q)
    (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : Bool → MovingSlotState σ → ℤ → ℂ)
    (extra : Bool → MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (hextra : ∀ b x s v w, extra b x s v w ≠ 0 →
      (historyPivot (movingSlotSystem value childBound pivotBound) x s v w : ZMod q) ≠ 0)
    (n m : ℕ) (hm : 0 < m) (e : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
    (hgood : 4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤
      3 * Fintype.card (TreeLeafIndex (n + 2)))
    (t : Bool → FrequencyTree ℤ (n + 2)) (small : Bool → TreeLeafTuple (List σ) (n + 2))
    (samples : Bool → MovingSampleSlots σ (n + 2))
    (hfreq : ∀ b, movingGiantFrequencyUnits q (n + 2) (t b))
    (hsmall : ∀ b, ((treeLeafProduct (n + 2) (movingSlotValues value (n + 2) (small b)) : ℕ) : ZMod q) ≠ 0)
    (hsamples : ∀ b, ((samples b).values value).UnitsAt q)
    (D : Bool → (ZMod q)ˣ) (XL XR : Bool → ℕ) (A B : Bool → (ZMod q)ˣ)
    (hA : ∀ b, (XL b : ZMod q) = A b) (hB : ∀ b, (XR b : ZMod q) = B b)
    (S : Finset (ZMod q)) (hlo : (1 / 3 : ℝ) ≤ residueDensity S)
    (hhi : residueDensity S ≤ 2 / 3) (hS : S.Nonempty) (hSq : S.card < q)
    (β ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hprincipal : 3 / Real.sqrt (q : ℝ) ≤ ε) (hβ : 2 * β ≤ ε)
    (hbias : ∀ (χ : MulChar (ZMod q) ℂ), χ ≠ 1 → ∀ a : ZMod q,
      ‖(S.card : ℂ)⁻¹ * ∑ x ∈ S, χ⁻¹ (-a - x)‖ ≤ β) :
    ∃ d₁ d₂ : SpectatorDiagram q (n + 2),
      (∀ (bulk₁ bulk₂ : TreeLeafTuple (List σ) (n + 2))
        (y₁ y₂ : TreeLeafTuple (ZMod q)ˣ (n + 2)),
        TreeNaturalLift (n + 2) (movingSlotValues value (n + 2) bulk₁) y₁ →
        TreeNaturalLift (n + 2) (movingSlotValues value (n + 2) bulk₂) y₂ →
        movingSampleFullWeight value childBound pivotBound (F false) (extra false)
            (normalizedResidueTransform S) (D false) (n + 2) (t false) (small false) bulk₁
            (samples false) (XL false) (XR false) *
          conj (movingSampleFullWeight value childBound pivotBound (F true) (extra true)
            (normalizedResidueTransform S) (D true) (n + 2) (t true) (small true) bulk₂
            (samples true) (XL true) (XR true)) =
          (movingSampleBaseWeight value childBound pivotBound (F false) (extra false)
              (n + 2) (t false) (small false) bulk₁ (samples false) (XL false) (XR false) *
            conj (movingSampleBaseWeight value childBound pivotBound (F true) (extra true)
              (n + 2) (t true) (small true) bulk₂ (samples true) (XL true) (XR true))) *
          (d₁.value (normalizedResidueTransform S) y₁ * conj (d₂.value (normalizedResidueTransform S) y₂))) ∧
      ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod q)ˣ) : ℂ)⁻¹ *
        (∑ x : TreeLeafIndex (n + 2) × Fin m → (ZMod q)ˣ,
          d₁.bulkValue (normalizedResidueTransform S) x *
            conj (d₂.bulkValue (normalizedResidueTransform S) (x ∘ e.symm)))‖ ^ 2 ≤
        quartetTreeConstant n * (ε ^ 2 + Real.sqrt (3 / (q : ℝ))) := by
  obtain ⟨d₁, d₂, hd, hbound⟩ := sampled_good_spectator_comparison hq n m hm e hgood
    (t false) (t true) (movingSlotValues value (n + 2) (small false))
    (movingSlotValues value (n + 2) (small true)) ((samples false).values value)
    ((samples true).values value) (hfreq false) (hfreq true) (hsmall false) (hsmall true)
    (hsamples false) (hsamples true) (D false) (D true) (XL false) (XR false) (XL true) (XR true)
    (A false) (B false) (A true) (B true) (hA false) (hB false) (hA true) (hB true)
    S hlo hhi hS hSq β ε hε hε1 hprincipal hβ hbias
  refine ⟨d₁, d₂, ?_, hbound⟩
  intro bulk₁ bulk₂ y₁ y₂ hy₁ hy₂
  let W₁ := movingSampleBaseWeight value childBound pivotBound (F false) (extra false)
    (n + 2) (t false) (small false) bulk₁ (samples false) (XL false) (XR false)
  let W₂ := movingSampleBaseWeight value childBound pivotBound (F true) (extra true)
    (n + 2) (t true) (small true) bulk₂ (samples true) (XL true) (XR true)
  have hI (b : Bool) (bulk : TreeLeafTuple (List σ) (n + 2))
      (hW : movingSampleBaseWeight value childBound pivotBound (F b) (extra b)
        (n + 2) (t b) (small b) bulk (samples b) (XL b) (XR b) ≠ 0) :
      (buildMovingGiantTree (n + 2) (t b) (movingSlotValues value (n + 2) (small b))
        ((samples b).values value)).Integral (XL b) (XR b) (movingSlotValues value (n + 2) bulk) := by
    apply (buildMovingSlotData_integral value (n + 2) (t b) (small b) bulk (samples b) (XL b) (XR b)).mp
    exact movingSlotWeight_nonzero_integral value childBound pivotBound (F b) (extra b) _ _
      (buildMovingSlotData_follows (n + 2) (t b) (small b) bulk (samples b)) _ _ hW
  have he := hd (movingSlotValues value (n + 2) bulk₁) (movingSlotValues value (n + 2) bulk₂)
    y₁ y₂ (W₁ * conj W₂) hy₁ hy₂ (fun h => by
      have h₁ : W₁ ≠ 0 := fun hz => h (by rw [hz, zero_mul])
      have h₂ : W₂ ≠ 0 := fun hz => h (by rw [hz, map_zero, mul_zero])
      exact ⟨hI false bulk₁ h₁, hI true bulk₂ h₂⟩)
  rw [moving_sample_full_weight_factor value childBound pivotBound (F false) (extra false)
    (hextra false), moving_sample_full_weight_factor value childBound pivotBound (F true) (extra true)
    (hextra true)]
  simp only [map_mul]
  change (W₁ * _) * (conj W₂ * _) = _
  convert he using 1
  ring

end Ostmann

end OAI
