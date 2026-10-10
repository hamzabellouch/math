import OAI.Geometry.NodalSets.Elliptic.UniformRecursiveJet
import OAI.Geometry.NodalSets.Waves.FiniteWaveJet

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section
variable {T : Type*} [TopologicalSpace T]

lemma transportKnown_family (W : T → ℕ → Fin 4 → CPoly) (c f a : T → Jet)
    (hW : ∀ r i, ContinuousPolyFamily (fun t ↦ W t r i))
    (hc : ∀ r, ContinuousPolyFamily (fun t ↦ c t r))
    (hf : ∀ r, ContinuousPolyFamily (fun t ↦ f t r))
    (ha : ∀ r, ContinuousPolyFamily (fun t ↦ a t r)) (n : ℕ) :
    ContinuousPolyFamily (fun t ↦ transportKnown (W t) (c t) (f t) n (a t)) := by
  unfold transportKnown
  apply ContinuousPolyFamily.sub _ (hf n)
  apply ContinuousPolyFamily.add
  · apply ContinuousPolyFamily.sum
    intro r _
    apply ContinuousPolyFamily.sum
    intro i _
    exact (hW _ i).mul ((ha _).pderiv i)
  · exact ContinuousPolyFamily.sum _ (fun r _ ↦ (hc r).mul (ha _))

lemma secondOrderCoefficient_family (g : T → ℕ → Fin 4 → Fin 4 → CPoly)
    (b : T → ℕ → Fin 4 → CPoly) (a : T → Jet)
    (hg : ∀ r i j, ContinuousPolyFamily (fun t ↦ g t r i j))
    (hb : ∀ r i, ContinuousPolyFamily (fun t ↦ b t r i))
    (ha : ∀ r, ContinuousPolyFamily (fun t ↦ a t r)) (n : ℕ) :
    ContinuousPolyFamily (fun t ↦ secondOrderCoefficient (g t) (b t) (a t) n) := by
  unfold secondOrderCoefficient
  apply ContinuousPolyFamily.homogeneousComponent
  apply ContinuousPolyFamily.add
  · apply ContinuousPolyFamily.sum
    intro r _
    apply ContinuousPolyFamily.sum
    intro i _
    apply ContinuousPolyFamily.sum
    intro j _
    exact (hg _ i j).mul (((ha _).pderiv j).pderiv i)
  · apply ContinuousPolyFamily.sum
    intro r _
    apply ContinuousPolyFamily.sum
    intro i _
    exact (hb _ i).mul ((ha _).pderiv i)

theorem finite_transport_jets_continuous
    (w : T → Fin 4 → ℂ) (hw : ∀ j, Continuous (fun t ↦ w t j))
    (i : Fin 4) (hi : ∀ t, w t i ≠ 0)
    (W : T → ℕ → Fin 4 → CPoly) (c f : T → Jet)
    (hW : ∀ r i, ContinuousPolyFamily (fun t ↦ W t r i))
    (hc : ∀ r, ContinuousPolyFamily (fun t ↦ c t r))
    (hf : ∀ r, ContinuousPolyFamily (fun t ↦ f t r))
    (value : T → ℂ) (hvalue : Continuous value) (degree : ℕ) :
    ∃ a : T → Jet,
      (∀ t k, (a t k).IsHomogeneous k) ∧
      (∀ k, ContinuousPolyFamily (fun t ↦ a t k)) ∧
      (∀ t, a t 0 = C (value t)) ∧
      ∀ t n, n < degree → transportCoefficient (w t) (W t) (c t) (f t) n (a t) = 0 := by
  let initial : T → Jet := fun t k ↦ if k = 0 then C (value t) else 0
  have hinitial : ∀ t k, (initial t k).IsHomogeneous k := by
    intro t k
    dsimp [initial]
    split_ifs with hk
    · subst k; exact isHomogeneous_C _ _
    · exact isHomogeneous_zero _ _ _
  have hic : ∀ k, ContinuousPolyFamily (fun t ↦ initial t k) := by
    intro k
    dsimp [initial]
    split_ifs
    · exact ContinuousPolyFamily.C hvalue
    · exact ContinuousPolyFamily.const _
  let low : T → ℕ → Jet → CPoly := fun t n a ↦
    homogeneousComponent n (transportKnown (W t) (c t) (f t) n a)
  obtain ⟨a, ha, hac, hkeep, hsolve⟩ := finite_triangular_jets_continuous w hw i hi low
    (fun t n a ↦ homogeneousComponent_isHomogeneous _ _)
    (fun t n a b h ↦ congrArg (homogeneousComponent n)
      (transportKnown_congr (W t) (c t) (f t) n a b h))
    (fun n a hac ↦ (transportKnown_family W c f a hW hc hf hac n).homogeneousComponent n)
    initial hinitial hic 0 degree
  refine ⟨a, ha, hac, fun t ↦ by simpa [initial] using hkeep t 0 (by omega), ?_⟩
  intro t n hn
  rw [transportCoefficient_split, map_add,
    homogeneousComponent_eq_self (direction_homogeneous _ (ha t (n + 1)))]
  exact hsolve t n (Nat.zero_le _) (by simpa using hn)

theorem transport_tower_continuous
    (w : T → Fin 4 → ℂ) (hw : ∀ j, Continuous (fun t ↦ w t j))
    (i : Fin 4) (hi : ∀ t, w t i ≠ 0)
    (W : T → ℕ → Fin 4 → CPoly) (c : T → Jet)
    (g : T → ℕ → Fin 4 → Fin 4 → CPoly) (b : T → ℕ → Fin 4 → CPoly)
    (hW : ∀ r i, ContinuousPolyFamily (fun t ↦ W t r i))
    (hc : ∀ r, ContinuousPolyFamily (fun t ↦ c t r))
    (hg : ∀ r i j, ContinuousPolyFamily (fun t ↦ g t r i j))
    (hb : ∀ r i, ContinuousPolyFamily (fun t ↦ b t r i)) (m J : ℕ) :
    ∃ A : ℕ → T → Jet,
      (∀ j t k, (A j t k).IsHomogeneous k) ∧
      (∀ j k, ContinuousPolyFamily (fun t ↦ A j t k)) ∧
      (∀ j t, A j t 0 = if j = 0 then 1 else 0) ∧
      (∀ t n, n < m + 1 + 2 * J →
        transportCoefficient (w t) (W t) (c t) 0 n (A 0 t) = 0) ∧
      ∀ j t n, n < m + 1 + 2 * (J - (j + 1)) →
        transportCoefficient (w t) (W t) (c t)
          (fun k ↦ -secondOrderCoefficient (g t) (b t) (A j t) k) n (A (j + 1) t) = 0 := by
  let Family := {a : T → Jet // (∀ t k, (a t k).IsHomogeneous k) ∧
    ∀ k, ContinuousPolyFamily (fun t ↦ a t k)}
  have hex (f : T → Jet) (hf : ∀ k, ContinuousPolyFamily (fun t ↦ f t k))
      (value : ℂ) (d : ℕ) :=
    finite_transport_jets_continuous w hw i hi W c f hW hc hf
      (fun _ ↦ value) continuous_const d
  let solve (f : T → Jet) (hf : ∀ k, ContinuousPolyFamily (fun t ↦ f t k))
      (value : ℂ) (d : ℕ) : Family :=
    ⟨Classical.choose (hex f hf value d), (Classical.choose_spec (hex f hf value d)).1,
      (Classical.choose_spec (hex f hf value d)).2.1⟩
  have hs (f : T → Jet) (hf : ∀ k, ContinuousPolyFamily (fun t ↦ f t k))
      (value : ℂ) (d : ℕ) := (Classical.choose_spec (hex f hf value d)).2.2
  let A : ℕ → Family := fun j ↦ Nat.rec
    (solve (fun _ ↦ 0) (fun _ ↦ ContinuousPolyFamily.const _) 1 (m + 1 + 2 * J))
    (fun j prev ↦ solve (fun t k ↦ -secondOrderCoefficient (g t) (b t) (prev.val t) k)
      (fun k ↦ (secondOrderCoefficient_family g b prev.val hg hb prev.property.2 k).neg)
      0 (m + 1 + 2 * (J - (j + 1)))) j
  refine ⟨fun j ↦ (A j).val, fun j ↦ (A j).property.1, fun j ↦ (A j).property.2, ?_, ?_, ?_⟩
  · intro j t
    cases j with
    | zero => simpa [A, solve] using (hs (fun _ ↦ 0) (fun _ ↦ ContinuousPolyFamily.const _) 1 _).1 t
    | succ j =>
      exact ((hs (fun t k ↦ -secondOrderCoefficient (g t) (b t) ((A j).val t) k)
        (fun k ↦ (secondOrderCoefficient_family g b (A j).val hg hb (A j).property.2 k).neg)
        0 _).1 t).trans (map_zero C)
  · exact (hs (fun _ ↦ 0) (fun _ ↦ ContinuousPolyFamily.const _) 1 _).2
  · intro j
    exact (hs (fun t k ↦ -secondOrderCoefficient (g t) (b t) ((A j).val t) k)
      (fun k ↦ (secondOrderCoefficient_family g b (A j).val hg hb (A j).property.2 k).neg)
      0 _).2

end
end Yau.Jets

end OAI
