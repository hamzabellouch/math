import OAI.Probability.BenjaminiSchramm.CayleyInputs

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u
variable {Λ : Type u} [Group Λ]

theorem cayleyRootTransport (S : Finset Λ) :
    RootTransport (fun _ : Unit => (1 : Λ)) (fun _ => (1 : ℝ))
      (vertexAut (cayleyBond S)) := by
  intro m hm _hrow _hcol
  simp only [Complex.ofReal_one, one_mul, Finset.univ_unique, Finset.sum_singleton]
  calc
    ∑' y, m 1 y = ∑' y, m y⁻¹ 1 := by
      apply tsum_congr
      intro y
      have h := hm (Equiv.mulLeft y⁻¹)
        ⟨(cayleyLeftIso S y⁻¹).mapEdgeSet, cayleyLeft_isAut S y⁻¹⟩ 1 y
      simpa using h.symm
    _ = ∑' x, m x 1 := (Equiv.inv Λ).tsum_eq (fun x => m x 1)

theorem cayleyRootCover (S : Finset Λ) :
    ∀ x : Λ, ∃ _i : Unit, ∃ a ∈ vertexAut (cayleyBond S), a 1 = x := by
  intro x
  exact ⟨(), Equiv.mulLeft x,
    ⟨(cayleyLeftIso S x).mapEdgeSet, cayleyLeft_isAut S x⟩, mul_one x⟩

theorem cayley_critical_bounded
    (S : Finset Λ) (hsym : ∀ s ∈ S, s⁻¹ ∈ S) (_hone : 1 ∉ S)
    (hgen : Subgroup.closure (S : Set Λ) = ⊤) (hna : ¬ FolnerAmenable Λ) :
    OperatorBounded (cayleyBond S) (pc (cayleyBond S)) := by
  classical
  let : Infinite Λ := infinite_of_not_folnerAmenable hna
  have hconn := cayleyBond_connected S hgen
  have hloc := cayleyBond_locallyFinite S hsym
  have hqt := cayleyBond_quasiTransitive S
  have hh := cayleyFolnerInput_proved hna S hsym hgen
  let : Countable Λ := countable_vertices hloc hconn
  let : Countable (CayleyEdge S) := countable_edges hloc
  have htr := cayleyRootTransport S
  have hcov := cayleyRootCover S
  have hw : ∀ _ : Unit, (0 : ℝ) < 1 := fun _ => zero_lt_one
  have hw1 : ∑ _ : Unit, (1 : ℝ) = 1 := by simp
  have hf := critical_finite_of_transport (cayleyBond S) hconn hloc hqt hh
    (fun _ : Unit => (1 : Λ)) (fun _ => (1 : ℝ))
    (vertexAut (cayleyBond S)) (Set.Subset.refl _) htr hcov hw hw1
  have hb := critical_bounded_of_transport_finiteness (cayleyBond S)
    Subtype.val_injective hconn hloc hqt hh
    (fun _ : Unit => (1 : Λ)) (fun _ => (1 : ℝ)) htr hcov hw hw1 (fun _ => hf 1)
  exact hb

end Percolation.BenjaminiSchramm

end OAI
