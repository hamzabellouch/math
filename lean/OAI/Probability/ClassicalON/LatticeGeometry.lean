import OAI.Probability.ClassicalON.ProfileEstimates

namespace OAI

noncomputable section
open scoped BigOperators
namespace ClassicalON

def latticeAxis (m : Bool) : Site := if m then (0,1) else (1,0)

def latticeTorus (L : ℕ) (x : Site) : DiscreteTorus L := ((x.1:ZMod L),(x.2:ZMod L))

@[simp] theorem latticeTorus_add (L : ℕ) (x y : Site) :
    latticeTorus L (x+y) = latticeTorus L x+latticeTorus L y := by
  ext <;> simp [latticeTorus]

def scaledSite (k : ℕ) (x : Site) : ℝ × ℝ :=
  ((x.1:ℝ)/(2:ℝ)^k, (x.2:ℝ)/(2:ℝ)^k)

@[simp] theorem scaledSite_add_axis (k : ℕ) (x : Site) (m : Bool) :
    scaledSite k (x+latticeAxis m) = squareStep m (1/(2:ℝ)^k) (scaledSite k x) := by
  cases m <;> ext <;> simp [scaledSite, latticeAxis, squareStep, add_div]

namespace LatticeGraph

def edgeDirection (G : LatticeGraph) (e : G.edges) : Bool :=
  decide (e.val.2.val.1 = e.val.1.val.1)

theorem edge_step (G : LatticeGraph) (e : G.edges) :
    e.val.2.val = e.val.1.val+latticeAxis (G.edgeDirection e) := by
  rcases G.nearest e.val e.property with h | h
  · have hn : e.val.2.val.1 ≠ e.val.1.val.1 := by omega
    simp only [edgeDirection, decide_eq_false hn, latticeAxis, Bool.false_eq_true, ↓reduceIte]
    exact Prod.ext h.1 (by simpa using h.2)
  · simp only [edgeDirection, h.1, decide_true, latticeAxis, ↓reduceIte]
    exact Prod.ext (by simpa using h.1) h.2

abbrev DirectionalEdges (G : LatticeGraph) (m : Bool) := {e : G.edges // G.edgeDirection e=m}

theorem directional_origin_injective (G : LatticeGraph) (m : Bool) :
    Function.Injective (fun e : G.DirectionalEdges m => e.val.val.1) := by
  intro e f h
  change e.val.val.1 = f.val.val.1 at h
  have he := G.edge_step e.val
  have hf := G.edge_step f.val
  rw [e.property] at he
  rw [f.property] at hf
  have hy : e.val.val.2 = f.val.val.2 := by
    apply Subtype.ext
    rw [he, hf, h]
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext h hy

def WithinDyadicBox (G : LatticeGraph) (k : ℕ) : Prop :=
  ∀ x : G.vertices, |x.val.1| ≤ 2*(2^k:ℕ) ∧ |x.val.2| ≤ 2*(2^k:ℕ)

theorem torus_site_injective (G : LatticeGraph) (k : ℕ) (hG : G.WithinDyadicBox k) :
    Function.Injective (fun x : G.vertices => latticeTorus (16*2^k) x.val) := by
  intro x y h
  apply Subtype.ext
  apply Prod.ext
  · apply zmod_cast_inj_interval (16*2^k) (-(2*(2^k:ℕ)):ℤ) _ _
    · have hx := abs_le.mp (hG x).1; have hN : 0<2^k := by positivity
      constructor <;> omega
    · have hy := abs_le.mp (hG y).1; have hN : 0<2^k := by positivity
      constructor <;> omega
    · exact congrArg Prod.fst h
  · apply zmod_cast_inj_interval (16*2^k) (-(2*(2^k:ℕ)):ℤ) _ _
    · have hx := abs_le.mp (hG x).2; have hN : 0<2^k := by positivity
      constructor <;> omega
    · have hy := abs_le.mp (hG y).2; have hN : 0<2^k := by positivity
      constructor <;> omega
    · exact congrArg Prod.snd h

theorem directional_torus_injective (G : LatticeGraph) (k : ℕ) (hG : G.WithinDyadicBox k) (m : Bool) :
    Function.Injective (fun e : G.DirectionalEdges m => latticeTorus (16*2^k) e.val.val.1.val) :=
  (G.torus_site_injective k hG).comp (G.directional_origin_injective m)

theorem edge_card_bound (G : LatticeGraph) (k : ℕ) (hG : G.WithinDyadicBox k) :
    (Fintype.card G.edges:ℝ) ≤ 512*((2:ℝ)^k)^2 := by
  let i := fun e : G.edges => (G.edgeDirection e, latticeTorus (16*2^k) e.val.1.val)
  have hi : Function.Injective i := by
    intro e f h
    have hm : G.edgeDirection e = G.edgeDirection f := congrArg Prod.fst h
    have hx := (G.torus_site_injective k hG) (congrArg Prod.snd h)
    have he := G.edge_step e
    have hf := G.edge_step f
    have hy : e.val.2 = f.val.2 := by
      apply Subtype.ext
      rw [he,hf,hm,hx]
    apply Subtype.ext
    exact Prod.ext hx hy
  have hc := Fintype.card_le_of_injective i hi
  simp only [Fintype.card_prod, Fintype.card_bool, ZMod.card] at hc
  have hh : (Fintype.card G.edges:ℝ) ≤ 2*((16*(2:ℝ)^k)*(16*(2:ℝ)^k)) := by exact_mod_cast hc
  nlinarith

theorem scaled_edge_distance (G : LatticeGraph) (k : ℕ) (e : G.edges) :
    ‖scaledSite k e.val.2.val-scaledSite k e.val.1.val‖ = 1/(2:ℝ)^k := by
  rw [G.edge_step e, scaledSite_add_axis, squareStep_distance, abs_of_pos (by positivity)]

end LatticeGraph
end ClassicalON

end

end OAI
