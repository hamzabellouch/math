import OAI.NumberTheory.Jacobsthal.Estimates.PairCollisionCount

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosHyperbolaIdentities

attribute [local instance] Classical.decEq

private theorem fibre_subset (N T : ℕ) [NeZero N] [NeZero T] (hT : T ∣ N)
    (a : (ZMod T)ˣ) (c u : (ZMod N)ˣ) (I J : Finset ℤ)
    (hu : u ∈ unitClass N T hT a) : pairFibre N c u I J ⊆ hyperbolaPairs N T a c I J := by
  rintro ⟨x,y⟩ hxy
  obtain ⟨hxf, hyf⟩ := Finset.mem_product.mp hxy
  obtain ⟨hxI, hxu⟩ := (mem_integerFibre _ _ _ _).mp hxf
  obtain ⟨hyJ, hyu⟩ := (mem_integerFibre _ _ _ _).mp hyf
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨hxI, hyJ⟩, ?_, ?_⟩
  · rw [hxu, hyu]
    calc
      _ = (c : ZMod N)*((u : ZMod N)*(↑u⁻¹ : ZMod N)) := by ring
      _ = _ := by simp
  · exact (unit_class_of_int N T hT a u x hxu.symm).mp ((mem_unitClass _ _ _ _ _).mp hu)

theorem hyperbolaPairs_eq_fibres (N T : ℕ) [NeZero N] [NeZero T] (hT : T ∣ N)
    (a : (ZMod T)ˣ) (c : (ZMod N)ˣ) (I J : Finset ℤ) :
    hyperbolaPairs N T a c I J = (unitClass N T hT a).biUnion (fun u => pairFibre N c u I J) := by
  apply Finset.Subset.antisymm
  · rintro ⟨x,y⟩ hpair
    obtain ⟨hIJ, hxy, hclass⟩ := Finset.mem_filter.mp hpair
    obtain ⟨hxI, hyJ⟩ := Finset.mem_product.mp hIJ
    have hprod : IsUnit ((x : ZMod N)*(y : ZMod N)) := by rw [hxy]; exact c.isUnit
    obtain ⟨u, hux⟩ := isUnit_of_mul_isUnit_left hprod
    have hu : u ∈ unitClass N T hT a :=
      (mem_unitClass _ _ _ _ _).mpr ((unit_class_of_int N T hT a u x hux).mpr hclass)
    have hyu : (y : ZMod N) = (c : ZMod N)*(↑u⁻¹ : ZMod N) := by
      have he : (u : ZMod N)*(y : ZMod N) = (c : ZMod N) := by rw [hux]; exact hxy
      have hm := congrArg (fun z : ZMod N => (↑u⁻¹ : ZMod N)*z) he
      rw [Units.inv_mul_cancel_left] at hm
      simpa only [mul_comm] using hm
    apply Finset.mem_biUnion.mpr
    refine ⟨u, hu, ?_⟩
    exact Finset.mem_product.mpr
      ⟨(mem_integerFibre _ _ _ _).mpr ⟨hxI, hux.symm⟩,
        (mem_integerFibre _ _ _ _).mpr ⟨hyJ, hyu⟩⟩
  · intro xy hxy
    obtain ⟨u, hu, hf⟩ := Finset.mem_biUnion.mp hxy
    exact fibre_subset N T hT a c u I J hu hf

theorem pairFibres_disjoint (N : ℕ) [NeZero N] (c u v : (ZMod N)ˣ) (I J : Finset ℤ)
    (huv : u ≠ v) : Disjoint (pairFibre N c u I J) (pairFibre N c v I J) := by
  apply Finset.disjoint_left.mpr
  rintro ⟨x,y⟩ hxu hxv
  have hu := ((mem_integerFibre N I (u : ZMod N) x).mp (Finset.mem_product.mp hxu).1).2
  have hv := ((mem_integerFibre N I (v : ZMod N) x).mp (Finset.mem_product.mp hxv).1).2
  exact huv (Units.ext (hu.symm.trans hv))

theorem hyperbolaPairs_card_eq_fibre_sum (N T : ℕ) [NeZero N] [NeZero T] (hT : T ∣ N)
    (a : (ZMod T)ˣ) (c : (ZMod N)ˣ) (I J : Finset ℤ) :
    (hyperbolaPairs N T a c I J).card =
      ∑ u ∈ unitClass N T hT a,
        (integerFibre N I (u : ZMod N)).card *
          (integerFibre N J ((c : ZMod N)*(↑u⁻¹ : ZMod N))).card := by
  have hd : (↑(unitClass N T hT a) : Set (ZMod N)ˣ).PairwiseDisjoint
      (fun u => pairFibre N c u I J) := by
    intro u _ v _ huv
    exact pairFibres_disjoint N c u v I J huv
  rw [hyperbolaPairs_eq_fibres N T hT a c I J, Finset.card_biUnion hd]
  simp only [pairFibre, Finset.product_eq_sprod, Finset.card_product]

end ErdosHyperbolaIdentities

end

end Erdos970

end OAI
