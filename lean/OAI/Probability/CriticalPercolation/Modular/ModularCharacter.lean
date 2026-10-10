import Mathlib
import OAI.Probability.CriticalPercolation.Modular.GraphModular

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma modularRatio_aut_translate (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x : V) (φ : G.Aut) :
    G.modularRatio o (φ.vertex x) =
      G.modularRatio o (φ.vertex o) * G.modularRatio o x := by
  rw [←G.modularRatio_cocycle hc hl o (φ.vertex o) (φ.vertex x),Aut.modularRatio]

lemma modularRatio_aut_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x : V) (φ : G.Aut) :
    G.modularRatio x (φ.vertex x) = G.modularRatio o (φ.vertex o) := by
  have h1 := G.modularRatio_cocycle hc hl o x (φ.vertex x)
  rw [G.modularRatio_aut_translate hc hl o x φ] at h1
  exact (mul_left_cancel₀ (ne_of_gt (G.modularRatio_pos hc hl o x)))
    (h1.trans (mul_comm _ _))

def modularCharacter (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (o : V) :
    G.Aut →* ℝ where
  toFun φ := G.modularRatio o (φ.vertex o)
  map_one' := G.modularRatio_self o
  map_mul' φ ψ := by
    change G.modularRatio o (φ.vertex (ψ.vertex o)) = _
    exact G.modularRatio_aut_translate hc hl o (ψ.vertex o) φ

@[simp] lemma modularCharacter_apply (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o : V) (φ : G.Aut) :
    G.modularCharacter hc hl o φ = G.modularRatio o (φ.vertex o) := rfl

lemma modularCharacter_pos (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o : V) (φ : G.Aut) : 0 < G.modularCharacter hc hl o φ :=
  G.modularRatio_pos hc hl o (φ.vertex o)

lemma modularCharacter_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x : V) : G.modularCharacter hc hl o = G.modularCharacter hc hl x := by
  ext φ
  exact (G.modularRatio_aut_base hc hl o x φ).symm

def modularKernel (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (o : V) :
    Subgroup G.Aut := (G.modularCharacter hc hl o).ker

lemma mem_modularKernel (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o : V) (φ : G.Aut) : φ ∈ G.modularKernel hc hl o ↔
      ∀ x, G.modularRatio o (φ.vertex x) = G.modularRatio o x := by
  change G.modularCharacter hc hl o φ = 1 ↔ _
  constructor
  · intro h x
    rw [G.modularRatio_aut_translate hc hl o x φ,←G.modularCharacter_apply hc hl,h,one_mul]
  · intro h
    simpa only [modularCharacter_apply,G.modularRatio_self] using h o

lemma stabilizer_le_modularKernel (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x : V) : MulAction.stabilizer G.Aut x ≤ G.modularKernel hc hl o := by
  intro φ hφ
  change G.modularCharacter hc hl o φ = 1
  rw [G.modularCharacter_base hc hl o x,modularCharacter_apply]
  change φ.vertex x = x at hφ
  rw [hφ,G.modularRatio_self]

lemma modularKernel_transitive_on_level (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x y : V) (hxy : ∃ φ : G.Aut, φ.vertex x = y)
    (hlevel : G.modularRatio o x = G.modularRatio o y) :
    ∃ φ : G.modularKernel hc hl o, φ.val.vertex x = y := by
  obtain ⟨φ,hφ⟩ := hxy
  refine ⟨⟨φ,?_⟩,hφ⟩
  change G.modularRatio o (φ.vertex o) = 1
  have hh := G.modularRatio_aut_translate hc hl o x φ
  rw [hφ,←hlevel] at hh
  exact (mul_right_cancel₀ (ne_of_gt (G.modularRatio_pos hc hl o x)))
    (hh.symm.trans (one_mul _).symm)

def modularCoordinate (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x : V) : ℝˣ := Units.mk0 (G.modularRatio o x)
      (ne_of_gt (G.modularRatio_pos hc hl o x))

@[simp] lemma modularCoordinate_val (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x : V) : (G.modularCoordinate hc hl o x : ℝ) = G.modularRatio o x := rfl

def modularUnitCharacter (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (o : V) :
    G.Aut →* ℝˣ where
  toFun φ := G.modularCoordinate hc hl o (φ.vertex o)
  map_one' := Units.ext (G.modularRatio_self o)
  map_mul' φ ψ := Units.ext (G.modularRatio_aut_translate hc hl o (ψ.vertex o) φ)

lemma modularCoordinate_equivariant (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o : V) (φ : G.Aut) (x : V) :
    G.modularCoordinate hc hl o (φ • x) =
      G.modularUnitCharacter hc hl o φ * G.modularCoordinate hc hl o x :=
  Units.ext (G.modularRatio_aut_translate hc hl o x φ)

lemma unit_stabilizer_le_kernel (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x : V) : MulAction.stabilizer G.Aut x ≤ (G.modularUnitCharacter hc hl o).ker := by
  intro φ hφ
  apply Units.ext
  exact G.stabilizer_le_modularKernel hc hl o x hφ

end CriticalPercolation.BondGraph
end
end

end OAI
