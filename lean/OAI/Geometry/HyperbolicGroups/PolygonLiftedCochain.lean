import Mathlib
import OAI.Geometry.HyperbolicGroups.FinitePolygonVoltage

namespace OAI

/-! Oriented cochains on the literal lifted triangulation, retaining all
independent sheet labels. Negative edges use the reverse initial sheet. -/
noncomputable section

namespace HyperbolicObstruction.FinitePolygonModel.Data
variable {V E C G B : Type*} [Fintype V] [Fintype E] [Fintype C]
  [DecidableEq V] [DecidableEq E] [DecidableEq C] [Group G] [AddCommGroup B]
  (P : Data V E C) (v : E → G)
  (w : G × E → B) (diag outer apex : G → P.Position → B)

def graphCochain (g : G) : GraphVertex (V := V) (E := E) → GraphVertex (V := V) (E := E) → B
  | .inr (e,a), .inr (f,b) => if e = f ∧ a ≠ b then
      if a then w (g,e) else -w (g*(v e)⁻¹,e) else 0
  | _,_ => 0

def liftedCochain (g : G) : P.Vertex → P.Vertex → B
  | .inl a, .inl b => graphCochain v w g a b
  | .inr (.inr q), .inl b => if P.graph b = P.base (P.next q) then diag g q else 0
  | .inl a, .inr (.inr q) =>
      if P.graph a = P.base (P.next q) then -diag (g*(P.segment v q)⁻¹) q else 0
  | .inr (.inr q), .inr (.inr r) =>
      if r = P.next q then outer g q else if q = P.next r then -outer (g*(P.segment v r)⁻¹) r else 0
  | .inr (.inl c), .inr (.inr q) => if c = q.1 then apex g q else 0
  | .inr (.inr q), .inr (.inl c) => if c = q.1 then -apex (g*(P.cornerOffset v q)⁻¹) q else 0
  | _,_ => 0

omit [Fintype V] [Fintype E] [DecidableEq V] in
lemma graphCochain_reverse (g : G) (a b : GraphVertex (V := V) (E := E)) :
    graphCochain v w (g*graphValue v a b) b a = -graphCochain v w g a b := by
  rcases a with a|⟨e,a⟩ <;> rcases b with b|⟨f,b⟩ <;> try simp [graphCochain,graphValue]
  by_cases he : e = f
  · subst f
    cases a <;> cases b <;> simp [signed,mul_assoc]
  · simp [he,Ne.symm he]

omit [Fintype V] [Fintype E] [Fintype C] in
lemma liftedCochain_self (g : G) (a : P.Vertex) : P.liftedCochain v w diag outer apex g a a = 0 := by
  rcases a with a|(c|q)
  · rcases a with a|⟨e,b⟩ <;> simp [liftedCochain,graphCochain]
  · rfl
  · simp [liftedCochain,Ne.symm (P.next_ne q)]

omit [Fintype V] [Fintype E] [Fintype C] in
lemma liftedCochain_reverse (g : G) (a b : P.Vertex) :
    P.liftedCochain v w diag outer apex (g*P.value v a b) b a =
      -P.liftedCochain v w diag outer apex g a b := by
  rcases a with a|(c|q) <;> rcases b with b|(d|r)
  · exact graphCochain_reverse v w g a b
  · simp [liftedCochain]
  · simp only [liftedCochain,value]
    split_ifs <;> simp
  · simp [liftedCochain]
  · simp [liftedCochain]
  · simp only [liftedCochain,value]
    split_ifs <;> simp [mul_assoc]
  · simp only [liftedCochain,value]
    split_ifs <;> simp
  · simp only [liftedCochain,value]
    split_ifs <;> simp
  · by_cases hr : r = P.next q
    · subst r
      simp [liftedCochain,value,Ne.symm (P.next_next_ne q),mul_assoc]
    · by_cases hq : q = P.next r
      · subst q
        simp [liftedCochain,value,hr]
      · simp [liftedCochain,hr,hq]

omit [Fintype V] [Fintype E] [Fintype C] in
lemma cochain_outer_base (g : G) (q : P.Position) :
    P.liftedCochain v w diag outer apex g (P.outer q) (P.base q) = 0 := by
  obtain ⟨b,hb⟩ := P.base_graph q
  have hn := P.base_ne_next q
  rw [hb] at hn ⊢
  simp [liftedCochain,hn]
omit [Fintype V] [Fintype E] [Fintype C] in
lemma cochain_outer_nextbase (g : G) (q : P.Position) :
    P.liftedCochain v w diag outer apex g (P.outer q) (P.base (P.next q)) = diag g q := by
  obtain ⟨b,hb⟩ := P.base_graph (P.next q)
  rw [hb]
  simp [liftedCochain,hb]
omit [Fintype V] [Fintype E] [Fintype C] in
lemma cochain_outer_next (g : G) (q : P.Position) :
    P.liftedCochain v w diag outer apex g (P.outer q) (P.outer (P.next q)) = outer g q := by
  simp [liftedCochain]
omit [Fintype V] [Fintype E] [Fintype C] in
lemma cochain_apex_outer (g : G) (q : P.Position) :
    P.liftedCochain v w diag outer apex g (P.apex q.1) (P.outer q) = apex g q := by
  simp [liftedCochain]
omit [Fintype V] [Fintype E] [Fintype C] in
lemma cochain_outer_apex (g : G) (q : P.Position) :
    P.liftedCochain v w diag outer apex g (P.outer q) (P.apex q.1) = -apex (g*(P.cornerOffset v q)⁻¹) q := by
  simp [liftedCochain]

end HyperbolicObstruction.FinitePolygonModel.Data
end

end OAI
