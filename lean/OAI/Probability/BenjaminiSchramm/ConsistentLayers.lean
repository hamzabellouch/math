import OAI.Probability.BenjaminiSchramm.NormalizedLayerTransport

namespace OAI

noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def adjustedLayerIndex (a : V → ℝ) (R u : ℝ) (x y : V) : ℤ :=
  ⌊G.orbitAdjustedHeight a x y/R+u⌋-⌊u⌋

@[simp] lemma adjustedLayerIndex_self (a : V → ℝ) (R u : ℝ) (x : V) :
    G.adjustedLayerIndex a R u x x=0 := by simp [adjustedLayerIndex]

lemma adjustedLayerIndex_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (R u : ℝ)
    (φ : G.Aut) (x y : V) :
    G.adjustedLayerIndex a R u (φ.vertex x) (φ.vertex y)=G.adjustedLayerIndex a R u x y := by
  simp only [adjustedLayerIndex,G.orbitAdjustedHeight_aut a ha]

lemma adjustedLayerIndex_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R u : ℝ) (x y z : V) :
    G.adjustedLayerIndex a R u x z = G.adjustedLayerIndex a R u x y+
      G.adjustedLayerIndex a R (G.orbitAdjustedHeight a x y/R+u) y z := by
  unfold adjustedLayerIndex
  rw [G.orbitAdjustedHeight_change_base hc hl a x y z]
  have he : (G.orbitAdjustedHeight a x y+G.orbitAdjustedHeight a y z)/R+u =
      G.orbitAdjustedHeight a y z/R+(G.orbitAdjustedHeight a x y/R+u) := by ring
  rw [he]
  ring

lemma adjustedLayerIndex_periodic (a : V → ℝ) (R u : ℝ) (n : ℤ) (x y : V) :
    G.adjustedLayerIndex a R (u+n) x y=G.adjustedLayerIndex a R u x y := by
  unfold adjustedLayerIndex
  rw [←add_assoc,Int.floor_add_intCast,Int.floor_add_intCast]
  ring

lemma adjustedLayerIndex_height_bounds (a : V → ℝ) (R u : ℝ) (hR : 0 < R) (x y : V) :
    R*((G.adjustedLayerIndex a R u x y : ℝ)-1) < G.orbitAdjustedHeight a x y ∧
      G.orbitAdjustedHeight a x y < R*((G.adjustedLayerIndex a R u x y : ℝ)+1) := by
  have h₁ := Int.floor_le (G.orbitAdjustedHeight a x y/R+u)
  have h₂ := Int.lt_floor_add_one (G.orbitAdjustedHeight a x y/R+u)
  have h₃ := Int.floor_le u
  have h₄ := Int.lt_floor_add_one u
  have he : (G.adjustedLayerIndex a R u x y : ℝ) =
      (⌊G.orbitAdjustedHeight a x y/R+u⌋ : ℝ)-(⌊u⌋ : ℝ) := by
    simp only [adjustedLayerIndex,Int.cast_sub]
  rw [he]
  constructor
  · have hh : (⌊G.orbitAdjustedHeight a x y/R+u⌋ : ℝ)-(⌊u⌋ : ℝ)-1 <
        G.orbitAdjustedHeight a x y/R := by linarith
    have hm := (lt_div_iff₀ hR).mp hh
    nlinarith
  · have hh : G.orbitAdjustedHeight a x y/R <
        (⌊G.orbitAdjustedHeight a x y/R+u⌋ : ℝ)-(⌊u⌋ : ℝ)+1 := by linarith
    have hm := (div_lt_iff₀ hR).mp hh
    nlinarith

lemma adjustedLayerIndex_edge_jump (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R u : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight a v w| ≤ R)
    (x v w : V) (e : E) (hv : v ∈ G.ends e) (hw : w ∈ G.ends e) :
    G.adjustedLayerIndex a R u x v-1 ≤ G.adjustedLayerIndex a R u x w ∧
      G.adjustedLayerIndex a R u x w ≤ G.adjustedLayerIndex a R u x v+1 := by
  have hh := abs_le.mp (hjump e v w hv hw)
  have hcoc := G.orbitAdjustedHeight_change_base hc hl a x v w
  have hdiv : G.orbitAdjustedHeight a x v/R-1 ≤ G.orbitAdjustedHeight a x w/R ∧
      G.orbitAdjustedHeight a x w/R ≤ G.orbitAdjustedHeight a x v/R+1 := by
    constructor
    · apply (le_div_iff₀ hR).mpr
      have he : (G.orbitAdjustedHeight a x v/R-1)*R = G.orbitAdjustedHeight a x v-R := by
        field_simp
      rw [he]
      linarith
    · apply (div_le_iff₀ hR).mpr
      have he : (G.orbitAdjustedHeight a x v/R+1)*R = G.orbitAdjustedHeight a x v+R := by
        field_simp
      rw [he]
      linarith
  have hlo := Int.floor_mono (add_le_add hdiv.1 (le_refl u))
  have hhi := Int.floor_mono (add_le_add hdiv.2 (le_refl u))
  have helo : G.orbitAdjustedHeight a x v/R-1+u = G.orbitAdjustedHeight a x v/R+u-1 := by ring
  have hehi : G.orbitAdjustedHeight a x v/R+1+u = G.orbitAdjustedHeight a x v/R+u+1 := by ring
  rw [helo,Int.floor_sub_one] at hlo
  rw [hehi,Int.floor_add_one] at hhi
  unfold adjustedLayerIndex
  omega

end CriticalPercolation.BondGraph

end

end OAI
