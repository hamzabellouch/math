import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingTable
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCellCatalogProgram

namespace OAI

/-! Evaluate each candidate together with its finite permission bit. Keeping
that bit attached to the path preserves the exact catalog order during the
bounded search, including reversed paths. -/

noncomputable section
namespace ContinuumCoulomb.QuantumTaggedRouteProgram
open scoped Classical
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode
open QuantumRoutingTable

abbrev Tagged := Bool × List Pair
def taggedCode : Tagged → List Bool := prodCode Procedure.boolCode (listCode pairCode)
def bodyPermitted (t : Table) (B : QMACellRouteBody) : Bool := allowed t B && decide B.Valid

theorem bodyPermitted_eq_true (t : Table) (B : QMACellRouteBody) :
    bodyPermitted t B = true ↔ allowed t B = true ∧ B.Valid := by
  simp only [bodyPermitted,Bool.and_eq_true]
  exact and_congr_right (fun _ => ⟨of_decide_eq_true,decide_eq_true⟩)

def tagged (t : Table) (R : QMACellRoute) : Tagged := (bodyPermitted t R.body,R.path)

def oriented (b : Bool) (xs : List Pair) : List Tagged := [(b,xs),(b,xs.reverse)]

private noncomputable def append {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (d : β) {f g : α → List β} (p : Procedure ea (listCode eb) f)
    (q : Procedure ea (listCode eb) g) : Procedure ea (listCode eb) (fun x => f x++g x) :=
  (Procedure.listAppend eb d).comp (p.pair q)

private noncomputable def fixedFlat {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (d : β) (m : ℕ) (f : Fin m → α → List β)
    (p : ∀ i, Procedure ea (listCode eb) (f i)) :
    Procedure ea (listCode eb) (fun x => (List.ofFn (fun i => f i x)).flatten) := by
  induction m with
  | zero => exact (Procedure.constant _ _ []).congrFun (by intro x; simp)
  | succ m ih =>
    exact (append ea eb d (p 0) (ih (fun i => f i.succ) (fun i => p i.succ))).congrFun (by
      intro x
      simp only [List.ofFn_succ,List.flatten_cons])

noncomputable opaque orientedProgram : Procedure taggedCode (listCode taggedCode)
    (fun x => oriented x.1 x.2) := by
  let same := Procedure.identity taggedCode
  let rev := (Procedure.first Procedure.boolCode (listCode pairCode)).pair
    ((Procedure.listReverse pairCode (0,0)).comp
      (Procedure.second Procedure.boolCode (listCode pairCode)))
  exact (Procedure.listCons taggedCode).comp (same.pair
    ((Procedure.listCons taggedCode).comp
      (rev.pair (Procedure.constant taggedCode (listCode taggedCode) []))))

private noncomputable def bodyProgram (B : Pair → QMACellRouteBody)
    (p : Procedure inputCode (listCode pairCode) (fun x => (B x.2).path))
    (q : Procedure inputCode Procedure.boolCode (fun x => bodyPermitted x.1 (B x.2))) :
    Procedure inputCode (listCode taggedCode)
      (fun x => oriented (bodyPermitted x.1 (B x.2)) ((B x.2).path)) :=
  orientedProgram.comp (q.pair p)

noncomputable opaque rayProgram (a : Fin 4) : Procedure inputCode (listCode taggedCode)
    (fun x => oriented (bodyPermitted x.1 (.ray x.2 a)) ((QMACellRouteBody.ray x.2 a).path)) :=
  bodyProgram (fun p => .ray p a) ((QuantumCellPathProgram.rayProgram a).comp cellProgram)
    ((rayAllowedProgram a).congrFun (by
      intro x
      apply Bool.eq_iff_iff.mpr
      rw [bodyPermitted_eq_true]
      exact ⟨fun h => ⟨h,trivial⟩,And.left⟩))

noncomputable opaque pairProgram (e : Fin 6) : Procedure inputCode (listCode taggedCode)
    (fun x => oriented (bodyPermitted x.1 (.pair x.2 e)) ((QMACellRouteBody.pair x.2 e).path)) :=
  bodyProgram (fun p => .pair p e) ((QuantumCellPathProgram.pairProgram e).comp cellProgram)
    ((pairAllowedProgram e).congrFun (by
      intro x
      apply Bool.eq_iff_iff.mpr
      rw [bodyPermitted_eq_true]
      exact ⟨fun h => ⟨h,trivial⟩,And.left⟩))

noncomputable opaque patchProgram (e : Fin 9) : Procedure inputCode (listCode taggedCode)
    (fun x => oriented (bodyPermitted x.1 (.patch x.2 e)) ((QMACellRouteBody.patch x.2 e).path)) :=
  bodyProgram (fun p => .patch p e) ((QuantumCellPathProgram.patchProgram e).comp cellProgram)
    ((patchAllowedProgram e).congrFun (by
      intro x
      apply Bool.eq_iff_iff.mpr
      rw [bodyPermitted_eq_true]
      exact ⟨fun h => ⟨h,trivial⟩,And.left⟩))

noncomputable opaque cellPositiveProgram : Procedure inputCode Procedure.boolCode
    (fun x => decide (0 < x.2.1 ∧ 0 < x.2.2)) := by
  let one := Procedure.constant inputCode Nat.bits 1
  let px := (Procedure.first Nat.bits Nat.bits).comp cellProgram
  let py := (Procedure.second Nat.bits Nat.bits).comp cellProgram
  exact (Procedure.boolAnd.comp
    ((Procedure.binaryLe.comp (one.pair px)).pair (Procedure.binaryLe.comp (one.pair py)))).congrFun (by
      intro x
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_apply,Bool.and_eq_true,decide_eq_true_eq]
      omega)

noncomputable opaque corridorProgram (a : Fin 4) (b c : Bool) :
    Procedure inputCode (listCode taggedCode)
      (fun x => oriented (bodyPermitted x.1 (.corridor x.2 a b c))
        ((QMACellRouteBody.corridor x.2 a b c).path)) :=
  bodyProgram (fun p => .corridor p a b c)
    ((QuantumCellPathProgram.corridorProgram a b c).comp cellProgram)
    ((Procedure.boolAnd.comp ((corridorAllowedProgram a b c).pair cellPositiveProgram)).congrFun (by
      intro x
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_apply,Bool.and_eq_true,decide_eq_true_eq,bodyPermitted_eq_true]
      rfl))

noncomputable opaque corridorBlock (a : Fin 4) : Procedure inputCode (listCode taggedCode)
    (fun x => oriented (bodyPermitted x.1 (.corridor x.2 a false false))
        ((QMACellRouteBody.corridor x.2 a false false).path) ++
      oriented (bodyPermitted x.1 (.corridor x.2 a false true))
        ((QMACellRouteBody.corridor x.2 a false true).path) ++
      oriented (bodyPermitted x.1 (.corridor x.2 a true false))
        ((QMACellRouteBody.corridor x.2 a true false).path) ++
      oriented (bodyPermitted x.1 (.corridor x.2 a true true))
        ((QMACellRouteBody.corridor x.2 a true true).path)) :=
  append inputCode taggedCode (false,[]) (append inputCode taggedCode (false,[])
    (append inputCode taggedCode (false,[]) (corridorProgram a false false)
      (corridorProgram a false true)) (corridorProgram a true false)) (corridorProgram a true true)

noncomputable opaque cellProgram : Procedure inputCode (listCode taggedCode)
    (fun x => (qmaCellRoutes x.2).map (tagged x.1)) := by
  let rays := fixedFlat inputCode taggedCode (false,[]) 4 _ rayProgram
  let pairs := fixedFlat inputCode taggedCode (false,[]) 6 _ pairProgram
  let patches := fixedFlat inputCode taggedCode (false,[]) 9 _ patchProgram
  let corridors := fixedFlat inputCode taggedCode (false,[]) 4 _ corridorBlock
  exact (append inputCode taggedCode (false,[])
    (append inputCode taggedCode (false,[]) (append inputCode taggedCode (false,[]) rays pairs)
      patches) corridors).congrFun (by
    intro x
    simp only [qmaCellRoutes,qmaCellBodies,List.flatMap_def,List.map_flatten,List.map_append,
      List.map_map,List.ofFn_eq_map,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,
      List.flatten_append,List.flatten_flatten,
      Function.comp_def,tagged,oriented,QMACellRoute.path,Bool.false_eq_true,ite_false,ite_true,
      List.append_assoc,List.append_nil])

end ContinuumCoulomb.QuantumTaggedRouteProgram

end

end OAI
