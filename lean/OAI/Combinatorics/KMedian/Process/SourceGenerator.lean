import Mathlib
import OAI.Combinatorics.KMedian.Geometry.GraphLaw
import OAI.Combinatorics.KMedian.Geometry.ChunkCharges
import OAI.Combinatorics.KMedian.Process.GeneratorAverage

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic GeneratorAverage GraphMoments
variable {I : Type*} [DecidableEq I] [Fintype I]

noncomputable def graphActions (G : I → Finset I) : Actions I I where
  source := id
  erase := fun h => univ.filter (fun i => h ∈ G i)
  ordinary := univ

 theorem mem_graph_erase (G : I → Finset I) (h i : I) :
    i ∈ (graphActions G).erase h ↔ h ∈ G i := by simp [graphActions]

 theorem indicator_sum (G : I → Finset I) (S : Finset I) (h : I) (f : I → ℝ) :
    (∑ i : S, f i*GraphLaw.edge G h i)=∑ i ∈ S ∩ (graphActions G).erase h, f i := by
  rw [sum_coe_sort S (fun i => f i*GraphLaw.edge G h i)]
  simp only [GraphLaw.edge, mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_inter, mem_graph_erase]

 theorem nonindicator_sum (G : I → Finset I) (S : Finset I) (h : I) (f : I → ℝ) :
    (∑ i : S, f i*(1-GraphLaw.edge G h i))=∑ i ∈ S \ (graphActions G).erase h, f i := by
  rw [sum_coe_sort S (fun i => f i*(1-GraphLaw.edge G h i))]
  have he : ∀ i, f i*(1-GraphLaw.edge G h i)=if h ∉ G i then f i else 0 := by
    intro i
    by_cases hi : h ∈ G i <;> simp [GraphLaw.edge, hi]
  simp only [he]
  rw [← sum_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_sdiff, mem_graph_erase]

 theorem graph_removed_mass (G : I → Finset I) (S : Finset I) (h : I) (g : ℝ) :
    (∑ i : S, g*GraphLaw.edge G h i)=mass g (S ∩ (graphActions G).erase h) := by
  rw [indicator_sum G S h (fun _ => g)]
  simp only [mass, sum_const, nsmul_eq_mul, mul_comm]

 theorem graph_removed_cost (G : I → Finset I) (S : Finset I) (h : I) (g : ℝ) (d : I → ℝ) :
    (∑ i : S, g*d i*GraphLaw.edge G h i)=PhysicalPotential.cost g d (S ∩ (graphActions G).erase h) :=
  indicator_sum G S h (fun i => g*d i)

theorem source_generator_identity (G : I → Finset I) (S : Finset I)
    (x g b : ℝ) (d : I → ℝ) :
    g*(∑ h ∈ relevant (graphActions G) S, charge (graphActions G) x g b d S h)=
      inside g (coefficient x (mass g S)) (potential x g d S b) (fun i : S => d i)
        (fun (_ : Unit) h i => GraphLaw.edge G h i) ()+
      external g (coefficient x (mass g S)) (B x) (PhysicalPotential.cost g d S)
        (fun h : (Sᶜ : Finset I) => min b (d h)) (fun i : S => d i)
        (fun (_ : Unit) h i => GraphLaw.edge G h i) () := by
  rw [sum_charge_relevant, mul_sum, ← sum_add_sum_compl S]
  congr 1
  · unfold inside
    simp only
    rw [sum_coe_sort S (fun h => g*(d h -
      (∑ i : S, g*(1-GraphLaw.edge G h i)*max (d h-coefficient x (mass g S)*d i) 0) -
      potential x g d S b))]
    apply sum_congr rfl
    intro h hh
    have hin : h ∈ (graphActions G).ordinary ∧ (graphActions G).source h ∈ S :=
      ⟨mem_univ h, hh⟩
    rw [charge, ite_eq_left hin]
    have hs : (∑ i : S, g*(1-GraphLaw.edge G h i)*max (d h-coefficient x (mass g S)*d i) 0)=
        ∑ i ∈ S \ (graphActions G).erase h, g*max (d h-coefficient x (mass g S)*d i) 0 := by
      calc
        _ = ∑ i : S, (g*max (d h-coefficient x (mass g S)*d i) 0)*(1-GraphLaw.edge G h i) := by
          apply sum_congr rfl
          intro i _
          ring
        _ = _ := nonindicator_sum G S h (fun i => g*max (d h-coefficient x (mass g S)*d i) 0)
    rw [hs]
    rfl
  · unfold external
    simp only [removedMass, removedCost, graph_removed_mass, graph_removed_cost]
    rw [sum_coe_sort (Sᶜ : Finset I) (fun h => g*(
      mass g (S ∩ (graphActions G).erase h)*min b (d h) -
      coefficient x (mass g S)*PhysicalPotential.cost g d (S ∩ (graphActions G).erase h) -
      B x*mass g (S ∩ (graphActions G).erase h)*
        (PhysicalPotential.cost g d S-PhysicalPotential.cost g d (S ∩ (graphActions G).erase h))))]
    apply sum_congr rfl
    intro h hh
    have hout : ¬(h ∈ (graphActions G).ordinary ∧ (graphActions G).source h ∈ S) := by
      rintro ⟨_, hs⟩
      exact mem_compl.mp hh hs
    rw [charge, ite_eq_right hout]
    rfl

end MetricKMedian.FixedBatch
end
end

end OAI
