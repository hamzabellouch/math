import Mathlib
import OAI.Geometry.HyperbolicGroups.FinitePolyhedronPathAlgebra
import OAI.Geometry.HyperbolicGroups.LoopSpaceReversal
import OAI.Geometry.HyperbolicGroups.VoltageEdgeAgreement

namespace OAI

/-! Choose representatives of a directed pi2-cochain with LITERAL spatial
reversal, so corrected edge prisms agree as maps, not merely as classes. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
open HSpacePathObstruction
variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G) (z : v.TotalSpace)
local notation "e" => Path.refl z
abbrev LoopClass := FundamentalGroup (Path z z) e

def loopRepresentative (c : v.LoopClass z) : Path e e :=
  (Path.Homotopic.Quotient.mk_surjective c).choose
omit [LinearOrder V] in
lemma loopRepresentative_class (c : v.LoopClass z) : loopClass (v.loopRepresentative z c) = c :=
  (Path.Homotopic.Quotient.mk_surjective c).choose_spec

variable (L : G → V → V → v.LoopClass z)
  (hs : ∀ g a, L g a a = 1)
  (hr : ∀ {a b}, {a,b} ∈ K.faces → ∀ g, L (g*v.value a b) b a = (L g a b)⁻¹)

def correctionLoop {a b : V} (_ : {a,b} ∈ K.faces) (g : G) : Path e e :=
  if a = b then Path.refl e else if a < b then v.loopRepresentative z (L g a b)
  else LoopSpaceReversal.reverse z (v.loopRepresentative z (L (g*v.value a b) b a))

include hs hr in
lemma correctionLoop_class {a b : V} (h : {a,b} ∈ K.faces) (g : G) :
    loopClass (v.correctionLoop z L h g) = L g a b := by
  unfold correctionLoop
  split_ifs with hab hlt
  · subst b; exact (hs g a).symm
  · exact v.loopRepresentative_class z _
  · rw [LoopSpaceReversal.reverse_class,v.loopRepresentative_class,hr h g,inv_inv]

lemma correctionLoop_reverse {a b : V} (h : {a,b} ∈ K.faces) (g : G) (t s : I) :
    v.correctionLoop z L (show {b,a} ∈ K.faces by simpa [Finset.pair_comm] using h)
      (g*v.value a b) t s = v.correctionLoop z L h g t (unitInterval.symm s) := by
  by_cases hab : a = b
  · subst b; simp only [correctionLoop,ite_true,eq_self]; rfl
  by_cases hlt : a < b
  · have hnl : ¬ b < a := not_lt_of_gt hlt
    simp only [correctionLoop,hab,Ne.symm hab,ite_false,hlt,hnl,ite_true]
    rw [v.value_reverse_mul h]
    rfl
  · have hgt : b < a := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hab)
    simp only [correctionLoop,hab,Ne.symm hab,ite_false,hlt,hgt,ite_true]
    rw [LoopSpaceReversal.reverse_apply,unitInterval.symm_symm]

def correctionSquare {a b : V} (h : {a,b} ∈ K.faces) (g : G) : C(I × I,v.TotalSpace) :=
  ⟨fun ts => ((Path.refl e).trans (v.correctionLoop z L h g)) ts.1 ts.2,
    Path.continuous_uncurry_iff.mpr (Path.refl e |>.trans (v.correctionLoop z L h g)).continuous⟩

lemma correctionSquare_reverse {a b : V} (h : {a,b} ∈ K.faces) (g : G) (t s : I) :
    v.correctionSquare z L (show {b,a} ∈ K.faces by simpa [Finset.pair_comm] using h)
      (g*v.value a b) (t,s) = v.correctionSquare z L h g (t,unitInterval.symm s) := by
  simp only [correctionSquare,ContinuousMap.coe_mk,Path.trans_apply]
  split_ifs
  · rfl
  · exact v.correctionLoop_reverse z L h g _ s

lemma correctionSquare_initial {a b : V} (h : {a,b} ∈ K.faces) (g : G) (s : I) :
    v.correctionSquare z L h g (0,s) = z := by simp [correctionSquare]
lemma correctionSquare_final {a b : V} (h : {a,b} ∈ K.faces) (g : G) (s : I) :
    v.correctionSquare z L h g (1,s) = z := by simp [correctionSquare]

def correctionEdgeData : v.EdgeData (X := v.TotalSpace) where
  vertex _ _ _ := z
  edge h g t s := v.correctionSquare z L h g (t,s)
  left h g t := by change ((Path.refl e).trans (v.correctionLoop z L h g)) t 0 = z; exact Path.source _
  right h g t := by change ((Path.refl e).trans (v.correctionLoop z L h g)) t 1 = z; exact Path.target _
  collapsed a g t s := by
    change ((Path.refl e).trans (v.correctionLoop z L (edge_self K a) g)) t s = z
    simp only [correctionLoop,ite_true,eq_self,Path.refl_trans_refl]; rfl
  reversed := v.correctionSquare_reverse z L

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
