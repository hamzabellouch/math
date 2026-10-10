import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.CrossingEnergy
import OAI.MathematicalPhysics.PEPSFilters.SiteBlocks
import OAI.MathematicalPhysics.PEPSFilters.ContourReduction

namespace OAI

/-! Propagated site and edge energy estimates across nested contours. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
open Set Filter
open scoped Topology
open scoped BigOperators
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
open scoped BigOperators InnerProductSpace

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Energy
open Matrix
variable {L q : ℕ}

lemma regularized_edge_crossing [NeZero q]
    (A : Finset (Vertex L)) (φ : State L q) (hφ : φ ≠ 0)
    (p : SpectralCoordinate (RegionConfiguration q A))
    (r : RegionConfiguration q A → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hρ : reducedDensity φ A = Unitary.conjStarAlgAut ℂ _ p.1
      (Matrix.diagonal fun i => (r i : ℂ)))
    {b c a : ℝ} (hb : 0 < b) (hc : 0 < c) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hclip : ∀ i, p.2.val i+b = max b (r i/c))
    (v w : Vertex L) (hv : v ∈ A) (hw : w ∉ A)
    (H : Operator L q) (hH : H.IsHermitian) (hs : SupportedOn H {v,w}) :
    let ψ := ((‖φ‖⁻¹ : ℝ) : ℂ) • φ
    let F := regularizedCoordinateMatrix b a p
    |(inner ℂ ψ (asMap (liftLocal A F) (asMap H (asMap (liftLocal A F⁻¹) ψ)))).re -
      (inner ℂ ψ (asMap H ψ)).re| ≤ (q:ℝ)^2 * a^2 * ‖H‖ := by
  classical
  obtain ⟨B,C,he,hB,hC⟩ := exists_two_site_crossing_factors A v w hv hw H hs
  have hsum : (∑ z, ‖B z‖ * ‖C z‖) ≤ (q:ℝ)^2 * ‖H‖ := by
    calc
      _ ≤ ∑ _z : Fin q × Fin q, ‖H‖ := Finset.sum_le_sum (fun z _ => by
        calc
          _ ≤ 1 * ‖H‖ := mul_le_mul (hB z) (hC z) (norm_nonneg _) (by norm_num)
          _ = _ := one_mul _)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, pow_two]
  have hh := regularized_one_crossing A φ hφ p r hr hρ hb hc ha ha1 hclip B C H hH he
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hsum (sq_nonneg a)])

end PolynomialPEPS.PinnedEntropy.NestedFilter.Energy

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Energy
open Matrix
variable {L q m : ℕ}

def Crosses (A : Finset (Vertex L)) (e : Edge L) : Prop :=
  (e.val.1 ∈ A ∧ e.val.2 ∉ A) ∨ (e.val.2 ∈ A ∧ e.val.1 ∉ A)

instance (A : Finset (Vertex L)) (e : Edge L) : Decidable (Crosses A e) :=
  inferInstanceAs (Decidable ((e.val.1 ∈ A ∧ e.val.2 ∉ A) ∨ (e.val.2 ∈ A ∧ e.val.1 ∉ A)))

lemma crossing_before_disjoint {X : Fin m → Finset (Vertex L)} (hX : Monotone X)
    {e : Edge L} (hu : ∀ j k, Crosses (X j) e → Crosses (X k) e → j = k)
    {j k : Fin m} (hj : Crosses (X j) e) (hk : k < j) : Disjoint (X k) (EdgeSites e) := by
  apply Finset.disjoint_left.mpr
  intro x hx hxe
  have he : e.val.1 ∈ X k ∨ e.val.2 ∈ X k := by
    rcases Finset.mem_insert.mp hxe with h | h
    · exact Or.inl (h ▸ hx)
    · exact Or.inr ((Finset.mem_singleton.mp h) ▸ hx)
  have hc : Crosses (X k) e := by
    rcases hj with ⟨ha,hb⟩ | ⟨hb,ha⟩
    · have hb' : e.val.2 ∉ X k := fun h => hb (hX hk.le h)
      exact Or.inl ⟨he.resolve_right hb', hb'⟩
    · have ha' : e.val.1 ∉ X k := fun h => ha (hX hk.le h)
      exact Or.inr ⟨he.resolve_left ha', ha'⟩
  exact hk.ne (hu k j hc hj)

lemma crossing_after_contains {X : Fin m → Finset (Vertex L)} (hX : Monotone X)
    {e : Edge L} (hu : ∀ j k, Crosses (X j) e → Crosses (X k) e → j = k)
    {j k : Fin m} (hj : Crosses (X j) e) (hk : j < k) : EdgeSites e ⊆ X k := by
  have hab : e.val.1 ∈ X k ∧ e.val.2 ∈ X k := by
    rcases hj with ⟨ha,hb⟩ | ⟨hb,ha⟩
    · have ha' := hX hk.le ha
      refine ⟨ha', ?_⟩
      by_contra hb'
      exact hk.ne (hu j k (Or.inl ⟨ha,hb⟩) (Or.inl ⟨ha',hb'⟩))
    · have hb' := hX hk.le hb
      refine ⟨?_,hb'⟩
      by_contra ha'
      exact hk.ne (hu j k (Or.inr ⟨hb,ha⟩) (Or.inr ⟨hb',ha'⟩))
  exact Finset.insert_subset hab.1 (Finset.singleton_subset_iff.mpr hab.2)

lemma not_crossing_classify (A : Finset (Vertex L)) (e : Edge L) (h : ¬ Crosses A e) :
    Disjoint A (EdgeSites e) ∨ EdgeSites e ⊆ A := by
  classical
  by_cases ha : e.val.1 ∈ A
  · have hb : e.val.2 ∈ A := by
      by_contra hb
      exact h (Or.inl ⟨ha,hb⟩)
    exact Or.inr (Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb))
  · have hb : e.val.2 ∉ A := fun hb => h (Or.inr ⟨hb,ha⟩)
    exact Or.inl (Finset.disjoint_left.mpr (by
      intro x hx hxe
      rcases Finset.mem_insert.mp hxe with hxe | hxe
      · exact ha (hxe ▸ hx)
      · exact hb ((Finset.mem_singleton.mp hxe) ▸ hx)))

lemma propagate_site_expectation (ψ : State L q)
    (X : Fin m → Finset (Vertex L)) (hX : Monotone X)
    (F : FilterFamily q m X) (hdet : ∀ j, IsUnit (F j).matrix.det)
    (hc : ∀ j, Commute (F j).matrix (reducedDensity ψ (X j)))
    (v : Vertex L) (H : Operator L q) (hH : SupportedOn H {v}) :
    inner ℂ ψ (asMap (propagateConjugation
      (fun k => liftLocal (X k) (F k).matrix)
      (fun k => liftLocal (X k) (F k).matrix⁻¹) H) ψ) = inner ℂ ψ (asMap H ψ) := by
  apply propagate_no_crossing ψ X hX F hdet hc H
  intro k
  by_cases hv : v ∈ X k
  · exact Or.inr (hH.mono (Finset.singleton_subset_iff.mpr hv))
  · exact Or.inl (SupportedOn.commute_disjoint ⟨_,rfl⟩ hH (by simpa))

lemma propagate_edge_no_crossing (ψ : State L q)
    (X : Fin m → Finset (Vertex L)) (hX : Monotone X)
    (F : FilterFamily q m X) (hdet : ∀ j, IsUnit (F j).matrix.det)
    (hc : ∀ j, Commute (F j).matrix (reducedDensity ψ (X j)))
    (e : Edge L) (H : Operator L q) (hH : SupportedOn H (EdgeSites e))
    (hcross : ∀ j, ¬ Crosses (X j) e) :
    inner ℂ ψ (asMap (propagateConjugation
      (fun k => liftLocal (X k) (F k).matrix)
      (fun k => liftLocal (X k) (F k).matrix⁻¹) H) ψ) = inner ℂ ψ (asMap H ψ) := by
  apply propagate_no_crossing ψ X hX F hdet hc H
  intro k
  rcases not_crossing_classify (X k) e (hcross k) with h | h
  · exact Or.inl (SupportedOn.commute_disjoint ⟨_,rfl⟩ hH h)
  · exact Or.inr (hH.mono h)

lemma regularized_propagated_edge [NeZero q]
    (X : Fin m → Finset (Vertex L)) (hX : Monotone X)
    {b : ℝ} (hb : 0 < b) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) (ha1 : ∀ j, a j ≤ 1)
    (p : CoordinateFamily q X) (φ : State L q) (hφ : φ ≠ 0)
    (hc : ∀ j, Commute (regularizedFilters hb.le a p j).matrix (reducedDensity φ (X j)))
    (hclip : ∀ j, let ρ := reducedDensity φ (X j)
      ρ = Unitary.conjStarAlgAut ℂ _ (p j).1
        (Matrix.diagonal fun i => (marginalDiagonal (p j).1 ρ i : ℂ)) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ i, (p j).2.val i+b = max b (marginalDiagonal (p j).1 ρ i/c))
    (e : Edge L) (hu : ∀ j k, Crosses (X j) e → Crosses (X k) e → j = k)
    (H : Operator L q) (hH : H.IsHermitian) (hs : SupportedOn H (EdgeSites e)) :
    let ψ := ((‖φ‖⁻¹ : ℝ):ℂ) • φ
    |(inner ℂ ψ (asMap (propagateConjugation
      (fun k => liftLocal (X k) (regularizedCoordinateMatrix b (a k) (p k)))
      (fun k => liftLocal (X k) (regularizedCoordinateMatrix b (a k) (p k))⁻¹) H) ψ)).re -
      (inner ℂ ψ (asMap H ψ)).re| ≤
      (q:ℝ)^2 * ‖H‖ * ∑ j, if Crosses (X j) e then (a j)^2 else 0 := by
  classical
  let ψ := ((‖φ‖⁻¹ : ℝ):ℂ) • φ
  let F := regularizedFilters hb.le a p
  have hdet (j) : IsUnit (F j).matrix.det := regularizedCoordinateMatrix_invertible hb _ _
  have hc' (j) : Commute (F j).matrix (reducedDensity ψ (X j)) := by
    rw [reducedDensity_real_smul]
    exact (hc j).smul_right _
  by_cases he : ∃ j, Crosses (X j) e
  · obtain ⟨j,hj⟩ := he
    have heq := propagate_single_crossing ψ X hX F hdet hc' H j
      (fun k hk => SupportedOn.commute_disjoint ⟨_,rfl⟩ hs (crossing_before_disjoint hX hu hj hk))
      (fun k hk => hs.mono (crossing_after_contains hX hu hj hk))
    change |(inner ℂ ψ (asMap (propagateConjugation
      (fun k => liftLocal (X k) (F k).matrix) (fun k => liftLocal (X k) (F k).matrix⁻¹) H) ψ)).re - _| ≤ _
    rw [heq]
    have hsum : (∑ k, if Crosses (X k) e then (a k)^2 else 0) = (a j)^2 := by
      rw [Finset.sum_eq_single j]
      · exact ite_eq_left hj
      · intro k _ hkj
        exact ite_eq_right (fun hk => hkj (hu k j hk hj))
      · simp
    rw [hsum]
    obtain ⟨hd,c,hcpos,hcval⟩ := hclip j
    have hr (i) : 0 ≤ marginalDiagonal (p j).1 (reducedDensity φ (X j)) i :=
      marginalDiagonal_nonneg _ (reducedDensity_posSemidef _ _) i
    have hbound : |(inner ℂ ψ (asMap (liftLocal (X j) (F j).matrix)
        (asMap H (asMap (liftLocal (X j) (F j).matrix⁻¹) ψ)))).re -
        (inner ℂ ψ (asMap H ψ)).re| ≤ (q:ℝ)^2 * (a j)^2 * ‖H‖ := by
      rcases hj with ⟨hv,hw⟩ | ⟨hw,hv⟩
      · exact regularized_edge_crossing (X j) φ hφ (p j) _ hr hd hb hcpos
          (ha j) (ha1 j) hcval e.val.1 e.val.2 hv hw H hH hs
      · exact regularized_edge_crossing (X j) φ hφ (p j) _ hr hd hb hcpos
          (ha j) (ha1 j) hcval e.val.2 e.val.1 hw hv H hH
          (by simpa only [EdgeSites, Finset.pair_comm] using hs)
    simpa only [asMap_mul, mul_assoc, mul_comm ‖H‖ ((a j)^2)] using hbound
  · have hn : ∀ j, ¬ Crosses (X j) e := fun j hj => he ⟨j,hj⟩
    have heq := propagate_edge_no_crossing ψ X hX F hdet hc' e H hs hn
    change |(inner ℂ ψ (asMap (propagateConjugation
      (fun k => liftLocal (X k) (F k).matrix) (fun k => liftLocal (X k) (F k).matrix⁻¹) H) ψ)).re - _| ≤ _
    rw [heq]
    simp only [ψ, hn, ite_false, Finset.sum_const_zero, mul_zero, sub_self, abs_zero, le_refl]

end PolynomialPEPS.PinnedEntropy.NestedFilter.Energy

end
end
end

end OAI
