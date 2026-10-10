import OAI.Probability.BenjaminiSchramm.ThinSphereProbability

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem domain_cluster_subset (G : BondGraph V E) (S ω : Set E) (x : V) :
    cluster G (ω ∩ S) x ⊆ cluster G ω x :=
  fun _ h => conn_mono G Set.inter_subset_left h

theorem radius_thin_sphere_recurrence [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (r k : ℕ) (hr : 0 < r) (b : ℝ≥0∞)
    (hb : ∀ (I : Set E) z, law p (domainRadiusEvent G I z r) ≤ b)
    (S : Set E) (x : V) :
    law p (domainRadiusEvent G S x (3*r)) ≤
      law p (volumeEvent G x ((r+1)*(k+1))) + k * b^2 := by
  let A : (ℕ × Finset V × Finset V) → Set (Set E) := fun a =>
    activeThinSphereCell G S x r k a.1 a.2.1 a.2.2
  let R := domainRadiusEvent G S x (3*r)
  have hmA (a) : MeasurableSet (A a) :=
    measurableSet_activeThinSphereCell G hloc S x r k a.1 hr a.2.1 a.2.2
  have hdisj : Pairwise (fun a c => Disjoint (A a) (A c)) := activeThinSphereCell_pairwise G S x r k
  have hsub : R ≤ᵐ[law p] volumeEvent G x ((r+1)*(k+1)) ∪ ⋃ a, A a ∩ R := by
    filter_upwards [hfin x] with ω hω
    intro hR
    by_cases hv : ω ∈ volumeEvent G x ((r+1)*(k+1))
    · exact Or.inl hv
    · have hsmallG : (cluster G ω x).ncard < (r+1)*(k+1) := by
        change ¬ (((r+1)*(k+1) : ℕ) : ℕ∞) ≤ (cluster G ω x).encard at hv
        rw [←hω.cast_ncard_eq] at hv
        exact_mod_cast lt_of_not_ge hv
      have hdomain := domain_cluster_subset G S ω x
      have hf := hω.subset hdomain
      have hsmall : (cluster G (ω ∩ S) x).ncard < (r+1)*(k+1) :=
        (Set.ncard_le_ncard hdomain hω).trans_lt hsmallG
      have hRr : ω ∈ domainRadiusEvent G S x r := by
        obtain ⟨y,hc,hd⟩ := hR
        exact ⟨y,hc,(by omega : r ≤ 3*r).trans hd⟩
      obtain ⟨a,ha⟩ := exists_activeThinSphereCell_of_small_cluster G hloc S ω x r k hf hsmall hRr
      exact Or.inr (Set.mem_iUnion.mpr ⟨a,ha,hR⟩)
  have hsumA : (∑' a, law p (A a)) ≤ b := by
    rw [←measure_iUnion hdisj hmA]
    apply (measure_mono (show (⋃ a, A a) ⊆ domainRadiusEvent G S x r from ?_)).trans (hb S x)
    intro ω hω
    obtain ⟨a,ha⟩ := Set.mem_iUnion.mp hω
    exact ha.2
  have hsum : (∑' a, law p (A a ∩ R)) ≤ k * b^2 := by
    calc
      _ ≤ ∑' a, law p (A a) * k * b := ENNReal.tsum_le_tsum (fun a =>
        activeThinSphereCell_survival_bound G hloc p S x r k a.1 hr a.2.1 a.2.2 b hb)
      _ = (∑' a, law p (A a)) * k * b := by rw [ENNReal.tsum_mul_right,ENNReal.tsum_mul_right]
      _ ≤ b * k * b := mul_le_mul' (mul_le_mul' hsumA le_rfl) le_rfl
      _ = _ := by ring
  exact (measure_mono_ae hsub).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl ((measure_iUnion_le (fun a => A a ∩ R)).trans hsum)))

end Percolation.BenjaminiSchramm

end OAI
