import Mathlib
import OAI.Geometry.HyperbolicGroups.PolygonLiftedCochain
import OAI.Geometry.HyperbolicGroups.PolygonCornerPrimitive

namespace OAI

/-! Cochain extension with literal initial-sheet coordinates for every collar
triangle. Its only algebraic input is the precise polygon boundary equation. -/
noncomputable section

namespace HyperbolicObstruction.FinitePolygonModel.Data
variable {V E C G B : Type*}
  [DecidableEq V] [DecidableEq E] [DecidableEq C] [Group G] [AddCommGroup B]
  (P : Data V E C) (v : E → G) (w : G × E → B)

def signedCochain (g : G) (e : E × Bool) : B :=
  if e.2 then w (g,e.1) else -w (g*(v e.1)⁻¹,e.1)
def segmentCochain (g : G) (q : P.Position) : B :=
  if q.2.2.val = 1 then signedCochain v w g (P.side q.1 q.2.1) else 0

lemma cochain_base_next (diag outer apex : G → P.Position → B) (g : G) (q : P.Position) :
    P.liftedCochain v w diag outer apex g (P.base q) (P.base (P.next q)) = P.segmentCochain v w g q := by
  rw [P.base_next]
  rcases q with ⟨c,i,j⟩
  fin_cases j <;> cases hb : (P.side c i).2 <;>
    simp [base,dartStart,liftedCochain,graphCochain,segmentCochain,signedCochain,hb]

variable (T : G → P.Position → Fin 3 → B)
def triangleWeight (g : G) (q : P.Position) : B := T g q 0 - T g q 1 + T g q 2

def correctionDiagonal (g : G) (q : P.Position) : B := P.segmentCochain v w g q - T g q 0
def correctionOuter (g : G) (q : P.Position) : B := P.correctionDiagonal v w T g q + T g q 1
def correctionIncrement (d : G) (q : P.Position) : B :=
  P.triangleWeight T (d*P.cornerOffset v q) q - P.segmentCochain v w (d*P.cornerOffset v q) q

def correctionApex (d : G) (q : P.Position) : B := P.cornerPrimitive (P.correctionIncrement v w T d) q

def triangleCochain (g : G) (a b : P.Vertex) : B := P.liftedCochain v w
  (P.correctionDiagonal v w T) (P.correctionOuter v w T) (P.correctionApex v w T) g a b

variable (hc : ∀ c, (List.ofFn (fun i => signed v (P.side c i))).prod = 1)
variable (hw : ∀ d c, (∑ i : Fin (P.size c),
    signedCochain v w (d*((List.ofFn (fun i => signed v (P.side c i))).take i.val).prod) (P.side c i)) =
    ∑ i : Fin (P.size c), ∑ j : Fin 3,
      P.triangleWeight T (d*P.cornerOffset v ⟨c,(i,j)⟩) ⟨c,(i,j)⟩)

omit [DecidableEq V] [DecidableEq E] [DecidableEq C] in
include hw in
lemma correctionIncrement_sum (d : G) (c : C) :
    ∑ i : Fin (P.size c), ∑ j : Fin 3, P.correctionIncrement v w T d ⟨c,(i,j)⟩ = 0 := by
  simp only [correctionIncrement,Finset.sum_sub_distrib]
  rw [←hw d c]
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro i hi
  simp [Fin.sum_univ_three,segmentCochain,cornerOffset]

omit [DecidableEq V] [DecidableEq E] [DecidableEq C] in
include hc hw in
lemma correctionApex_difference (g : G) (q : P.Position) :
    P.correctionApex v w T (g*(P.cornerOffset v q)⁻¹) q -
      P.correctionApex v w T ((g*P.segment v q)*(P.cornerOffset v (P.next q))⁻¹) (P.next q) =
      P.triangleWeight T g q - P.segmentCochain v w g q := by
  have he : (g*P.segment v q)*(P.cornerOffset v (P.next q))⁻¹ = g*(P.cornerOffset v q)⁻¹ := by
    rw [P.cornerOffset_next v hc]
    group
  rw [he,correctionApex,correctionApex,P.cornerPrimitive_difference _
    (P.correctionIncrement_sum v w T hw (g*(P.cornerOffset v q)⁻¹))]
  simp [correctionIncrement,mul_assoc]

include hc hw in
/-- Values on the three LITERAL oriented triangle boundaries. The second
collar orientation uses a plus rather than silently sharing the polygon sign. -/
theorem triangleCochain_coboundary (g : G) (q : P.Position) :
    (P.triangleCochain v w T g (P.outer q) (P.base q) +
      P.triangleCochain v w T (g*P.value v (P.outer q) (P.base q)) (P.base q) (P.base (P.next q)) -
      P.triangleCochain v w T g (P.outer q) (P.base (P.next q)) = T g q 0) ∧
    (P.triangleCochain v w T g (P.outer q) (P.outer (P.next q)) +
      P.triangleCochain v w T (g*P.value v (P.outer q) (P.outer (P.next q))) (P.outer (P.next q)) (P.base (P.next q)) -
      P.triangleCochain v w T g (P.outer q) (P.base (P.next q)) = T g q 1) ∧
    (P.triangleCochain v w T g (P.outer q) (P.outer (P.next q)) +
      P.triangleCochain v w T (g*P.value v (P.outer q) (P.outer (P.next q))) (P.outer (P.next q)) (P.apex q.1) -
      P.triangleCochain v w T g (P.outer q) (P.apex q.1) = T g q 2) := by
  simp only [triangleCochain,P.cochain_outer_base,P.cochain_base_next,P.cochain_outer_nextbase,
    P.cochain_outer_next,P.value_outer_base,P.value_outer_next,mul_one,zero_add,add_zero]
  constructor
  · unfold correctionDiagonal; abel
  constructor
  · unfold correctionOuter; abel
  · have hn : (P.next q).1 = q.1 := rfl
    rw [←hn,P.cochain_outer_apex,hn,P.cochain_outer_apex]
    have hh := P.correctionApex_difference v w T hc hw g q
    rw [←sub_eq_add_neg,sub_neg_eq_add]
    calc _ = P.correctionOuter v w T g q +
        (P.correctionApex v w T (g*(P.cornerOffset v q)⁻¹) q -
          P.correctionApex v w T ((g*P.segment v q)*(P.cornerOffset v (P.next q))⁻¹) (P.next q)) := by abel
      _ = T g q 2 := by rw [hh]; unfold correctionOuter correctionDiagonal triangleWeight; abel

end HyperbolicObstruction.FinitePolygonModel.Data
end

end OAI
