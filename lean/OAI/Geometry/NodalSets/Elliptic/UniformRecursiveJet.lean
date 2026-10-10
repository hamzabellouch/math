import OAI.Geometry.NodalSets.Elliptic.UniformDirectional

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section
variable {T : Type*} [TopologicalSpace T]

lemma ContinuousPolyFamily.neg {P : T → CPoly} (hp : ContinuousPolyFamily P) :
    ContinuousPolyFamily (fun t ↦ -P t) := by
  simpa using hp.smul (continuous_const : Continuous (fun _ : T ↦ (-1 : ℂ)))

lemma ContinuousPolyFamily.sub {P Q : T → CPoly}
    (hp : ContinuousPolyFamily P) (hq : ContinuousPolyFamily Q) :
    ContinuousPolyFamily (fun t ↦ P t - Q t) := by
  simpa only [sub_eq_add_neg] using hp.add hq.neg

lemma ContinuousPolyFamily.pderiv {P : T → CPoly} (hp : ContinuousPolyFamily P)
    (i : Fin 4) : ContinuousPolyFamily (fun t ↦ pderiv i (P t)) :=
  hp.linearMap (MvPolynomial.pderiv i).toLinearMap

lemma ContinuousPolyFamily.homogeneousComponent {P : T → CPoly}
    (hp : ContinuousPolyFamily P) (n : ℕ) :
    ContinuousPolyFamily (fun t ↦ homogeneousComponent n (P t)) :=
  hp.linearMap (MvPolynomial.homogeneousComponent n)

theorem finite_triangular_jets_continuous
    (v : T → Fin 4 → ℂ) (hv : ∀ j, Continuous (fun t ↦ v t j))
    (i : Fin 4) (hi : ∀ t, v t i ≠ 0)
    (lower : T → ℕ → Jet → CPoly)
    (hlower : ∀ t n a, (lower t n a).IsHomogeneous n)
    (hcausal : ∀ t n a b, (∀ k, k ≤ n → a k = b k) → lower t n a = lower t n b)
    (hc : ∀ n (a : T → Jet), (∀ k, ContinuousPolyFamily (fun t ↦ a t k)) →
      ContinuousPolyFamily (fun t ↦ lower t n (a t)))
    (initial : T → Jet) (hinitial : ∀ t k, (initial t k).IsHomogeneous k)
    (hic : ∀ k, ContinuousPolyFamily (fun t ↦ initial t k)) (base steps : ℕ) :
    ∃ a : T → Jet,
      (∀ t k, (a t k).IsHomogeneous k) ∧
      (∀ k, ContinuousPolyFamily (fun t ↦ a t k)) ∧
      (∀ t k, k ≤ base → a t k = initial t k) ∧
      ∀ t n, base ≤ n → n < base + steps →
        direction (v t) (a t (n + 1)) + lower t n (a t) = 0 := by
  induction steps with
  | zero => exact ⟨initial, hinitial, hic, fun _ _ _ ↦ rfl, by omega⟩
  | succ steps ih =>
    obtain ⟨a, ha, hac, hkeep, hsolve⟩ := ih
    let n := base + steps
    let q : T → CPoly := fun t ↦ directionalPrimitive (v t) i (-lower t n (a t))
    have hq (t : T) : (q t).IsHomogeneous (n + 1) :=
      directionalPrimitive_homogeneous _ _ (hlower t n (a t)).neg
    have hqc : ContinuousPolyFamily q := (hc n a hac).neg.directionalPrimitive v hv i hi
    let b : T → Jet := fun t ↦ Function.update (a t) (n + 1) (q t)
    have heq (t : T) (k : ℕ) (hk : k ≤ n) : b t k = a t k :=
      Function.update_of_ne (by omega) _ _
    refine ⟨b, ?_, ?_, ?_, ?_⟩
    · intro t k
      by_cases hk : k = n + 1
      · subst k; simpa [b] using hq t
      · simpa [b, Function.update_of_ne hk] using ha t k
    · intro k
      by_cases hk : k = n + 1
      · subst k; simpa [b] using hqc
      · simpa [b, Function.update_of_ne hk] using hac k
    · intro t k hk
      exact (heq t k (by dsimp [n]; omega)).trans (hkeep t k hk)
    · intro t r hr hrbound
      by_cases hrn : r = n
      · subst r
        rw [hcausal t n (b t) (a t) (heq t)]
        rw [show b t (n + 1) = q t by simp [b]]
        rw [show direction (v t) (q t) = -lower t n (a t) from
          directionalPrimitive_right_inverse (v t) i (hi t) _]
        exact neg_add_cancel _
      · have hrlt : r < n := by dsimp [n] at *; omega
        rw [heq t (r + 1) (by omega), hcausal t r (b t) (a t)
          (fun k hk ↦ heq t k (by omega))]
        exact hsolve t r hr hrlt

end
end Yau.Jets

end OAI
