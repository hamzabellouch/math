import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCellCorridor

namespace OAI

/-! A finite catalog of the four local route types used by the physical graph.
Every valid catalog entry is a simple grid path of at most twenty steps. -/

namespace ContinuumCoulomb

inductive QMACellRouteBody where
  | ray (cell : ℕ × ℕ) (port : Fin 4)
  | pair (cell : ℕ × ℕ) (edge : Fin 6)
  | patch (cell : ℕ × ℕ) (edge : Fin 9)
  | corridor (cell : ℕ × ℕ) (port : Fin 4) (cross nextCross : Bool)

namespace QMACellRouteBody

def path : QMACellRouteBody → List (ℕ × ℕ)
  | .ray p a => (qmaCellRayPath a).map (qmaCellTranslate p)
  | .pair p e => (qmaCellPairPath e).map (qmaCellTranslate p)
  | .patch p e => qmaCrossingPathAt p e
  | .corridor p a b c => qmaCellCorridor p a b c

def source : QMACellRouteBody → ℕ × ℕ
  | .ray p _ => qmaExpandedPoint p
  | .pair p e => qmaGridPort p (qmaCellPairLeft e)
  | .patch p e => qmaPatchTranslate p (qmaCrossingPatchVertex (qmaCrossingPatchLeft e))
  | .corridor p a b _ => qmaCellTranslate p (qmaLocalPort b a)

def target : QMACellRouteBody → ℕ × ℕ
  | .ray p a => qmaGridPort p a
  | .pair p e => qmaGridPort p (qmaCellPairRight e)
  | .patch p e => qmaPatchTranslate p (qmaCrossingPatchVertex (qmaCrossingPatchRight e))
  | .corridor p a _ c => qmaCellTranslate (qmaGridNeighbor p a) (qmaLocalPort c (qmaPortOpposite a))

def Valid : QMACellRouteBody → Prop
  | .corridor p _ _ _ => 0 < p.1 ∧ 0 < p.2
  | _ => True

theorem endpoints (R : QMACellRouteBody) :
    R.path.head? = some R.source ∧ R.path.getLast? = some R.target := by
  cases R with
  | ray p a =>
    simpa only [path,source,target,List.head?_map,List.getLast?_map,
      (qmaCellRay_endpoints a).1,(qmaCellRay_endpoints a).2,Option.map_some,
      qmaCellTranslate_port] using
      (show some (qmaCellTranslate p (16,16)) = some (qmaExpandedPoint p) ∧
        some (qmaGridPort p a) = some (qmaGridPort p a) from ⟨rfl,rfl⟩)
  | pair p e =>
    simp only [path,source,target,List.head?_map,List.getLast?_map,
      (qmaCellPair_endpoints e).1,(qmaCellPair_endpoints e).2,Option.map_some,qmaCellTranslate_port]
    constructor <;> trivial
  | patch p e =>
    simp only [path,source,target,qmaCrossingPathAt,List.head?_map,List.getLast?_map,
      (qmaCrossingPatch_endpoints e).1,(qmaCrossingPatch_endpoints e).2,Option.map_some]
    constructor <;> trivial
  | corridor p a b c => exact qmaCellCorridor_endpoints p a b c

theorem length_bounds (R : QMACellRouteBody) : 3 ≤ R.path.length ∧ R.path.length ≤ 21 := by
  cases R with
  | ray p a => simp only [path,List.length_map,qmaCellRay_length]; omega
  | pair p e => simp only [path,List.length_map,qmaCellPair_length]; omega
  | patch p e =>
    have hlo : 3 ≤ (qmaCrossingPatchPath e).length := by fin_cases e <;> decide
    have hhi := qmaCrossingPatch_length e
    simp only [path,qmaCrossingPathAt,List.length_map]
    omega
  | corridor p a b c =>
    have h := qmaCellCorridor_length p a b c
    exact ⟨(by decide : 3 ≤ 18).trans h.1,h.2⟩

theorem simple (R : QMACellRouteBody) (hR : R.Valid) : R.path.Nodup := by
  cases R with
  | ray p a => exact (qmaCellRay_simple a).map (qmaCellTranslate_injective p)
  | pair p e => exact (qmaCellPair_simple e).map (qmaCellTranslate_injective p)
  | patch p e => exact qmaCrossingPathAt_simple p e
  | corridor p a b c => exact qmaCellCorridor_simple p hR a b c

theorem chain (R : QMACellRouteBody) (hR : R.Valid) :
    R.path.IsChain (fun x y => qmaSquareGrid.Adj x y) := by
  cases R with
  | ray p a =>
    apply List.isChain_map_of_isChain (qmaCellTranslate p) _ (qmaCellRay_chain a)
    intro x y h
    change Nat.dist _ _ + Nat.dist _ _ = 1
    simpa only [qmaCellTranslate_step] using h
  | pair p e =>
    apply List.isChain_map_of_isChain (qmaCellTranslate p) _ (qmaCellPair_chain e)
    intro x y h
    change Nat.dist _ _ + Nat.dist _ _ = 1
    simpa only [qmaCellTranslate_step] using h
  | patch p e => exact qmaCrossingPathAt_chain p e
  | corridor p a b c => exact qmaCellCorridor_chain p hR a b c

end QMACellRouteBody

structure QMACellRoute where
  body : QMACellRouteBody
  reversed : Bool

namespace QMACellRoute

def path (R : QMACellRoute) := if R.reversed then R.body.path.reverse else R.body.path
def source (R : QMACellRoute) := if R.reversed then R.body.target else R.body.source
def target (R : QMACellRoute) := if R.reversed then R.body.source else R.body.target
def Valid (R : QMACellRoute) := R.body.Valid

theorem endpoints (R : QMACellRoute) :
    R.path.head? = some R.source ∧ R.path.getLast? = some R.target := by
  rcases R with ⟨body,b⟩
  cases b
  · exact body.endpoints
  · simpa only [path,source,target,ite_true,List.head?_reverse,List.getLast?_reverse] using
      body.endpoints.symm

theorem length_bounds (R : QMACellRoute) : 3 ≤ R.path.length ∧ R.path.length ≤ 21 := by
  rcases R with ⟨body,b⟩
  cases b <;> simpa only [path,Bool.false_eq_true,ite_false,ite_true,List.length_reverse] using body.length_bounds

theorem simple (R : QMACellRoute) (hR : R.Valid) : R.path.Nodup := by
  rcases R with ⟨body,b⟩
  cases b
  · exact body.simple hR
  · exact List.nodup_reverse.mpr (body.simple hR)

theorem chain (R : QMACellRoute) (hR : R.Valid) :
    R.path.IsChain (fun x y => qmaSquareGrid.Adj x y) := by
  rcases R with ⟨body,b⟩
  cases b
  · exact body.chain hR
  · exact List.isChain_reverse.mpr ((body.chain hR).imp (fun _ _ h => h.symm))

end QMACellRoute
end ContinuumCoulomb

end OAI
