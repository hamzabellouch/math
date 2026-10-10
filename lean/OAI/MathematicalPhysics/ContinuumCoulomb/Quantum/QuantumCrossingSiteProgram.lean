import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortSelectionProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFirstUseProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortChainProgram

namespace OAI

/-! Locate crossing terminals by scanning the actual physical position tape.
The finite search returns exactly the existing terminal spin indices. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingSiteProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumCrossingListBlock
open scoped Classical

abbrev Input := List Pair × Pair
def inputCode : Input → List Bool := prodCode (listCode pairCode) pairCode
def flags (x : Input) : List Bool := x.1.map (fun p => decide (p=x.2))
def index (x : Input) : ℕ := QuantumFirstUseProgram.first (flags x)

noncomputable opaque flagsProgram : Procedure inputCode (listCode Procedure.boolCode) flags := by
  let targets := Procedure.second (listCode pairCode) pairCode
  let ps := Procedure.first (listCode pairCode) pairCode
  let eq := QuantumFiniteMembership.pairEqProgram.comp
    ((Procedure.second pairCode pairCode).pair (Procedure.first pairCode pairCode))
  exact (Procedure.listMapWith (f := fun q p => decide (p=q)) (0,0) false eq).comp
    (targets.pair ps)
noncomputable opaque indexProgram : Procedure inputCode unaryCode index :=
  QuantumFirstUseProgram.firstProgram.comp flagsProgram

theorem index_eq (x : Input) : index x=x.1.findIdx (fun p => decide (p=x.2)) := by
  rw [index,QuantumFirstUseProgram.first_eq_findIdx,flags,List.findIdx_map]
  rfl

theorem index_ofFn {n : ℕ} (pos : Fin n → Pair) (hinj : Function.Injective pos) (v : Fin n) :
    index (List.ofFn pos,pos v)=v.val := by
  rw [index_eq]
  apply (List.findIdx_eq (by simpa only [List.length_ofFn] using v.isLt)).mpr
  constructor
  · simp only [List.getElem_ofFn,decide_eq_true_eq]
  · intro j hj
    simp only [List.getElem_ofFn,decide_eq_false_iff_not]
    intro h
    have hv := congrArg Fin.val (hinj h)
    exact (Nat.ne_of_lt hj) hv

def target (a : Fin 4) (x : Input) : Input :=
  (x.1,qmaGridPort x.2 (qmaPatchDirection a))
def terminal (a : Fin 4) (x : Input) : ℕ := index (target a x)
def sites (x : Input) : Sites := ((terminal 0 x,terminal 1 x),(terminal 2 x,terminal 3 x))

noncomputable opaque targetProgram (a : Fin 4) : Procedure inputCode inputCode (target a) := by
  let p := Procedure.second (listCode pairCode) pairCode
  let endpoint := (QuantumPortChainProgram.portProgram.comp
    (p.pair (Procedure.constant inputCode Nat.bits (qmaPatchDirection a).val))).congrFun
      (by intro x; exact QuantumPortChainProgram.port_fin x.2 (qmaPatchDirection a))
  exact (Procedure.first (listCode pairCode) pairCode).pair endpoint
noncomputable opaque terminalProgram (a : Fin 4) : Procedure inputCode Nat.bits (terminal a) :=
  Procedure.unaryToBits.comp (indexProgram.comp (targetProgram a))
noncomputable opaque sitesProgram : Procedure inputCode sitesCode sites :=
  ((terminalProgram 0).pair (terminalProgram 1)).pair
    ((terminalProgram 2).pair (terminalProgram 3))

def allSites (x : List Pair × List Pair) : List Sites := x.2.map (fun c => sites (x.1,c))
noncomputable opaque allSitesProgram :
    Procedure (prodCode (listCode pairCode) (listCode pairCode)) (listCode sitesCode) allSites :=
  Procedure.listMapWith (f := fun ps c => sites (ps,c)) (0,0) ((0,0),(0,0)) sitesProgram

theorem terminal_actual {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) (i : Fin P.crossingCells.card) (a : Fin 4) :
    terminal a (List.ofFn (P.finishedPosition N D),(P.crossingCell i).val)=
      (P.crossingSiteFin N hD i a).val := by
  unfold terminal target
  rw [← P.crossingSite_spec N hD (P.crossingCell i) (qmaPatchDirection a)]
  exact index_ofFn (P.finishedPosition N D) (P.toEmbedding.iterate N D).position_injective
    (P.crossingSiteFin N hD i a)

theorem sites_actual {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) (i : Fin P.crossingCells.card) :
    sites (List.ofFn (P.finishedPosition N D),(P.crossingCell i).val)=
      QuantumCrossingSelectProgram.encodedSites (P.crossingSiteFin N hD) i := by
  simp only [sites,terminal_actual P N hD,QuantumCrossingSelectProgram.encodedSites]

theorem allSites_actual {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) :
    allSites (List.ofFn (P.finishedPosition N D),List.ofFn (fun i => (P.crossingCell i).val))=
      List.ofFn (QuantumCrossingSelectProgram.encodedSites (P.crossingSiteFin N hD)) := by
  simp only [allSites,List.map_ofFn,Function.comp_def,sites_actual P N hD]

end ContinuumCoulomb.QuantumCrossingSiteProgram

end

end OAI
