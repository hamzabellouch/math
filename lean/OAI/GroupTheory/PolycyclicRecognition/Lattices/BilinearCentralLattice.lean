import OAI.GroupTheory.PolycyclicRecognition.Geometry.BilinearCentralLieModel

namespace OAI

/-! # Uniform lattices for integral bilinear central extensions

The central coordinate of a fundamental-domain representative is reduced
after subtracting the bilinear correction from the first coordinate.
-/

noncomputable section
namespace PolycyclicRecognition
open Set Module

variable {V W : Type} [NormedAddCommGroup V] [NormedAddCommGroup W]
  [NormedSpace ℝ V] [NormedSpace ℝ W] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
  {d e : ℕ} (b : Basis (Fin d) ℝ V) (c : Basis (Fin e) ℝ W)
  (B : V →L[ℝ] V →L[ℝ] W)
  (hB : ∀ x ∈ Submodule.span ℤ (range b), ∀ y ∈ Submodule.span ℤ (range b),
    B x y ∈ Submodule.span ℤ (range c))

def bilinearCentralLattice : Subgroup (bilinearCentralLieModel B).carrier where
  carrier := {x | x.1 ∈ Submodule.span ℤ (range b) ∧
    x.2 ∈ Submodule.span ℤ (range c)}
  one_mem' := ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
  mul_mem' := by
    intro x y hx hy
    exact ⟨Submodule.add_mem _ hx.1 hy.1,
      Submodule.add_mem _ (Submodule.add_mem _ hx.2 hy.2) (hB _ hx.1 _ hy.1)⟩
  inv_mem' := by
    intro x hx
    exact ⟨Submodule.neg_mem _ hx.1,
      Submodule.add_mem _ (Submodule.neg_mem _ hx.2) (hB _ hx.1 _ hx.1)⟩

theorem bilinearCentralLattice_discrete :
    DiscreteTopology (bilinearCentralLattice b c B hB) := by
  let L := Submodule.span ℤ (range b)
  let M := Submodule.span ℤ (range c)
  let f : bilinearCentralLattice b c B hB → L × M :=
    fun x => (⟨x.val.1, x.property.1⟩, ⟨x.val.2, x.property.2⟩)
  have hval : Continuous (fun x : bilinearCentralLattice b c B hB => (x.val : V × W)) :=
    continuous_subtype_val
  have hf : Continuous f := by
    exact (hval.fst.subtype_mk _).prodMk (hval.snd.subtype_mk _)
  apply DiscreteTopology.of_continuous_injective hf
  intro x y h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun z : L × M => z.1.val) h)
    (congrArg (fun z : L × M => z.2.val) h)

theorem bilinearCentralLattice_uniform :
    IsUniformLattice (bilinearCentralLattice b c B hB) := by
  refine ⟨bilinearCentralLattice_discrete b c B hB, ?_⟩
  let K : Set (V × W) := parallelepiped b ×ˢ parallelepiped c
  have hK : IsCompact K := b.parallelepiped.isCompact.prod c.parallelepiped.isCompact
  refine ⟨K, hK, ?_⟩
  intro g
  let a := ZSpan.floor b g.1
  let u := ZSpan.fract b g.1
  let z := g.2 - B a u
  let q := ZSpan.floor c z
  let v := ZSpan.fract c z
  refine ⟨⟨((a : V), (q : W)), a.property, q.property⟩, (u, v), ?_, ?_⟩
  · exact ⟨ZSpan.fundamentalDomain_subset_parallelepiped b
        (ZSpan.fract_mem_fundamentalDomain b g.1),
      ZSpan.fundamentalDomain_subset_parallelepiped c
        (ZSpan.fract_mem_fundamentalDomain c z)⟩
  · apply Prod.ext
    · change (a : V) + u = g.1
      dsimp only [a, u, ZSpan.fract]
      abel
    · change (q : W) + v + B a u = g.2
      dsimp only [q, v, ZSpan.fract, z]
      abel

end PolycyclicRecognition

end

end OAI
