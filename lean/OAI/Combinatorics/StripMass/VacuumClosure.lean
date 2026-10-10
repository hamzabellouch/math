import Mathlib
import OAI.Combinatorics.StripMass.VacuumDegree

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators
namespace Graph
lemma closure_drains_local {V : Type*} {n : ℕ} {r : V → V → Prop}
    {a : Fin n → V} {q : Pairing n} {root : Fin n}
    (h : DrainsAt (boundaryClosure r a q) (a root)) : DrainsBoundary r a := by
  intro v w hvw
  have hr := h v w (Or.inl hvw)
  clear hvw w h
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨root, .refl⟩
  | @head x y hxy hpath ih =>
    rcases hxy with hxy | ⟨i,j,_,rfl,_⟩
    · obtain ⟨i,hi⟩ := ih
      exact ⟨i,hi.head hxy⟩
    · exact ⟨i,.refl⟩

end Graph

namespace Pairing

def join {n : ℕ} (p q : Pairing n) (i j : Fin n) : Prop := p.Adj i j ∨ q.Adj i j

instance join_symm {n : ℕ} (p q : Pairing n) : Std.Symm (join p q) :=
  ⟨fun _ _ h => h.elim (fun h => Or.inl (adj_symm h)) (fun h => Or.inr (adj_symm h))⟩

 

def GluesAt {n : ℕ} (root : Fin n) (p q : Pairing n) : Prop :=
  p.Occupied root ∧ (∀ i, p.Occupied i ↔ q.Occupied i) ∧ Graph.DrainsAt (join p q) root

lemma GluesAt.symm {n : ℕ} {root : Fin n} {p q : Pairing n}
    (h : GluesAt root p q) : GluesAt root q p := by
  refine ⟨(h.2.1 root).mp h.1,fun i => (h.2.1 i).symm,?_⟩
  intro i j hij
  exact Relation.ReflTransGen.mono (r := p.join q) (p := q.join p) (fun _ _ hh => hh.symm) _ _ (h.2.2 i j hij.symm)

end Pairing

namespace GraphRealizes
variable {V : Type*} {n : ℕ} {r : V → V → Prop} {a : Fin n → V}
  {p q : Pairing n}

lemma closure_reach (hp : GraphRealizes r a p) (i j : Fin n) :
    Relation.ReflTransGen (Graph.boundaryClosure r a q) (a i) (a j) ↔
      Relation.ReflTransGen (p.join q) i j := by
  constructor
  · intro h
    have hs : ∀ {x}, Relation.ReflTransGen (Graph.boundaryClosure r a q) (a i) x →
        ∃ k, Relation.ReflTransGen (p.join q) i k ∧ Relation.ReflTransGen r (a k) x := by
      intro x hx
      induction hx with
      | refl => exact ⟨i,.refl,.refl⟩
      | @tail x y hx hxy ih =>
        obtain ⟨k,hk,hr⟩ := ih
        rcases hxy with hxy | ⟨l,m,hlm,hl,hm⟩
        · exact ⟨k,hk,hr.tail hxy⟩
        · subst x; subst y
          have hkl : Relation.ReflTransGen (p.join q) k l := by
            rcases (hp.reach k l).mp hr with rfl | hkl
            · exact .refl
            · exact .single (Or.inl hkl)
          exact ⟨m,(hk.trans hkl).tail (Or.inr hlm),.refl⟩
    obtain ⟨k,hk,hr⟩ := hs h
    rcases (hp.reach k j).mp hr with rfl | hkj
    · exact hk
    · exact hk.tail (Or.inl hkj)
  · intro h
    apply Graph.map_reach a _ h
    intro k l hkl
    rcases hkl with hkl | hkl
    · exact Graph.closure_lift ((hp.reach k l).mpr (Or.inr hkl))
    · exact .single (Or.inr ⟨k,l,hkl,rfl,rfl⟩)

lemma closure_drains_iff (hp : GraphRealizes r a p) (ha : Function.Injective a)
    (root : Fin n) :
    Graph.DrainsAt (Graph.boundaryClosure r a q) (a root) ↔
      Graph.DrainsAt (p.join q) root := by
  constructor
  · intro h i j hij
    apply (hp.closure_reach i root).mp
    rcases hij with hpij | hqij
    · obtain ⟨w,hw⟩ := (hp.boundary_used_iff ha i).mpr ⟨j,hpij⟩
      exact h _ _ (Or.inl hw)
    · exact h _ _ (Or.inr ⟨i,j,hqij,rfl,rfl⟩)
  · intro h v w hvw
    rcases hvw with hvw | ⟨i,j,hij,rfl,rfl⟩
    · obtain ⟨i,⟨j,hij⟩,hi⟩ := hp.no_loop v w hvw
      exact (Graph.closure_lift hi).trans ((hp.closure_reach i root).mpr
        (h i j (Or.inl hij)))
    · exact (hp.closure_reach i root).mpr (h i j (Or.inr hij))

end GraphRealizes

namespace Tile

def transpose : Tile → Tile
  | .diagonal₀ => .diagonal₁
  | .diagonal₁ => .diagonal₀
  | .cap => .cup
  | .cup => .cap
  | x => x

def transposePort : Fin 4 → Fin 4 := ![2,3,0,1]

@[simp] lemma transpose_transpose (t : Tile) : t.transpose.transpose = t := by cases t <;> rfl
@[simp] lemma transposePort_involutive (i : Fin 4) : transposePort (transposePort i)=i := by
  fin_cases i <;> rfl
@[simp] lemma transpose_adj (t : Tile) (i j : Fin 4) :
    t.transpose.Adj (transposePort i) (transposePort j) ↔ t.Adj i j := by
  cases t <;> fin_cases i <;> fin_cases j <;> decide
@[simp] lemma transpose_occupied (t : Tile) (i : Fin 4) :
    t.transpose.Occupied (transposePort i) ↔ t.Occupied i := by
  cases t <;> fin_cases i <;> decide
@[simp] lemma weight_transpose {K : Type*} [One K] (w : Weights K) (t : Tile) :
    w.tile t.transpose = w.tile t := by cases t <;> rfl

def transposeEquiv : Tile ≃ Tile :=
  ⟨transpose,transpose,transpose_transpose,transpose_transpose⟩

end Tile

namespace Pairing

 
def GateCompatible {n : ℕ} (p q : Pairing n) (a b : Fin n) (t : Tile) : Prop :=
  CutPatch.Compatible (p.cutShape a b) t ∧
    ∀ i, p.stepSupport a b t i ↔ q.Occupied i

def flipStep {n : ℕ} : StepVertex n → StepVertex n
  | .old i => .out i
  | .out i => .old i
  | .box i => .box (Tile.transposePort i)

@[simp] lemma flipStep_involutive {n : ℕ} (v : StepVertex n) : flipStep (flipStep v)=v := by
  cases v <;> simp [flipStep]

lemma GateCompatible.transpose {n : ℕ} {p q : Pairing n} {a b : Fin n}
    (hab : a≠b) {t : Tile} (h : GateCompatible p q a b t) :
    GateCompatible q p a b t.transpose := by
  have hp := (p.cutShape_compatible a b t).mp h.1
  have hqa : t.Occupied 2 ↔ q.Occupied a := by simpa [stepSupport] using h.2 a
  have hqb : t.Occupied 3 ↔ q.Occupied b := by simpa [stepSupport,Ne.symm hab] using h.2 b
  refine ⟨(q.cutShape_compatible a b t.transpose).mpr ?_,?_⟩
  · constructor
    · exact hqa.symm.trans (t.transpose_occupied (2 : Fin 4)).symm
    · exact hqb.symm.trans (t.transpose_occupied (3 : Fin 4)).symm
  · intro i
    by_cases hia : i=a
    · subst i
      simp only [stepSupport,ite_true]
      exact (t.transpose_occupied (0 : Fin 4)).trans hp.1.symm
    · by_cases hib : i=b
      · subst i
        simp only [stepSupport,ite_eq_right (Ne.symm hab),ite_true]
        exact (t.transpose_occupied (1 : Fin 4)).trans hp.2.symm
      · simpa [stepSupport,hia,hib] using (h.2 i).symm

 
def closedStep {n : ℕ} (p q : Pairing n) (a b : Fin n) (t : Tile) :=
  Graph.boundaryClosure (p.stepWiring a b t) StepVertex.out q

lemma closedStep_flip {n : ℕ} {p q : Pairing n} {a b : Fin n} (hab : a≠b)
    {t : Tile} (h : GateCompatible p q a b t) (v w : StepVertex n) :
    closedStep q p a b t.transpose (flipStep v) (flipStep w) ↔
      closedStep p q a b t v w := by
  have hp := (p.cutShape_compatible a b t).mp h.1
  have hqa : t.Occupied 2 ↔ q.Occupied a := by simpa [stepSupport] using h.2 a
  have hqb : t.Occupied 3 ↔ q.Occupied b := by simpa [stepSupport,Ne.symm hab] using h.2 b
  have ho (i : Fin n) (hia : i≠a) (hib : i≠b) : q.Occupied i ↔ p.Occupied i := by
    simpa [stepSupport,hia,hib] using (h.2 i).symm
  have ht0 : t.transpose.Occupied 0 ↔ t.Occupied 2 := t.transpose_occupied 2
  have ht1 : t.transpose.Occupied 1 ↔ t.Occupied 3 := t.transpose_occupied 3
  have ht2 : t.transpose.Occupied 2 ↔ t.Occupied 0 := t.transpose_occupied 0
  have ht3 : t.transpose.Occupied 3 ↔ t.Occupied 1 := t.transpose_occupied 1
  cases v with
  | old i =>
    cases w with
    | old j => simp [closedStep,Graph.boundaryClosure,stepWiring,flipStep]
    | box k =>
      fin_cases k <;>
        simp [closedStep,Graph.boundaryClosure,stepWiring,flipStep,Tile.transposePort,
          ht2,ht3,←hp.1,←hp.2]
    | out j =>
      simp only [closedStep,Graph.boundaryClosure,stepWiring,flipStep]
      constructor <;> rintro (⟨hij,hia,hib,hi⟩ | ⟨k,l,_,hk,hl⟩)
      · subst j; exact Or.inl ⟨rfl,hia,hib,(ho i hia hib).mp hi⟩
      · cases hl
      · subst j; exact Or.inl ⟨rfl,hia,hib,(ho i hia hib).mpr hi⟩
      · cases hk
  | box k =>
    cases w with
    | old i =>
      fin_cases k <;>
        simp [closedStep,Graph.boundaryClosure,stepWiring,flipStep,Tile.transposePort,
          ht2,ht3,←hp.1,←hp.2]
    | box l => simp [closedStep,Graph.boundaryClosure,stepWiring,flipStep]
    | out i =>
      fin_cases k <;>
        simp [closedStep,Graph.boundaryClosure,stepWiring,flipStep,Tile.transposePort,
          hqa,hqb]
  | out i =>
    cases w with
    | old j =>
      simp only [closedStep,Graph.boundaryClosure,stepWiring,flipStep]
      constructor <;> rintro (⟨hij,hia,hib,hi⟩ | ⟨k,l,_,hk,hl⟩)
      · subst j; exact Or.inl ⟨rfl,hia,hib,(ho i hia hib).mp hi⟩
      · cases hk
      · subst j; exact Or.inl ⟨rfl,hia,hib,(ho i hia hib).mpr hi⟩
      · cases hl
    | box k =>
      fin_cases k <;>
        simp [closedStep,Graph.boundaryClosure,stepWiring,flipStep,Tile.transposePort,
          hqa,hqb]
    | out j => simp [closedStep,Graph.boundaryClosure,stepWiring,flipStep]

 
lemma glues_tile_iff_closedStep {n : ℕ} {p q : Pairing n} {a b root : Fin n}
    (hab : a.val+1=b.val) (hra : root ≠ a) (hrb : root ≠ b) (t : Tile) :
    (∃ r, p.tileStep a b hab t = some r ∧ GluesAt root r q) ↔
      p.Occupied root ∧ GateCompatible p q a b t ∧
        Graph.DrainsAt (closedStep p q a b t) (.out root) := by
  constructor
  · rintro ⟨r,hr,hg⟩
    refine ⟨?_,⟨p.tileStep_compatible a b hab t r hr,?_⟩,?_⟩
    · have hh := (p.tileStep_support a b hab t r hr root).mp hg.1
      simpa only [stepSupport,ite_eq_right hra,ite_eq_right hrb] using hh
    · intro i
      exact (p.tileStep_support a b hab t r hr i).symm.trans (hg.2.1 i)
    · exact ((p.stepWiring_realizes a b hab t r hr).closure_drains_iff
        (fun _ _ h => StepVertex.out.inj h) root).mpr hg.2.2
  · rintro ⟨hp,hc,hd⟩
    have hn := p.tileStep_ne_none_of_drains a b hab t hc.1
      (Graph.closure_drains_local hd)
    obtain ⟨r,hr⟩ := Option.ne_none_iff_exists'.mp hn
    refine ⟨r,hr,?_,?_,?_⟩
    · apply (p.tileStep_support a b hab t r hr root).mpr
      simpa only [stepSupport,ite_eq_right hra,ite_eq_right hrb] using hp
    · intro i
      exact (p.tileStep_support a b hab t r hr i).trans (hc.2 i)
    · exact ((p.stepWiring_realizes a b hab t r hr).closure_drains_iff
        (fun _ _ h => StepVertex.out.inj h) root).mp hd

lemma glues_tile_flip {n : ℕ} {p q : Pairing n} {a b root : Fin n}
    (hab : a.val+1=b.val) (hra : root ≠ a) (hrb : root ≠ b) (t : Tile)
    (h : ∃ r, p.tileStep a b hab t = some r ∧ GluesAt root r q) :
    ∃ r, q.tileStep a b hab t.transpose = some r ∧ GluesAt root r p := by
  obtain ⟨hp,hc,hd⟩ := (glues_tile_iff_closedStep hab hra hrb t).mp h
  have hne : a≠b := by intro hh; have := congrArg Fin.val hh; omega
  have hq : q.Occupied root := (hc.2 root).mp
    (by simpa only [stepSupport,ite_eq_right hra,ite_eq_right hrb] using hp)
  apply (glues_tile_iff_closedStep hab hra hrb t.transpose).mpr
  refine ⟨hq,hc.transpose hne,?_⟩
  have hf := hd.map (Function.Involutive.toPerm (@flipStep n) flipStep_involutive)
    (closedStep_flip hne hc)
  apply hf.mono_root
  exact .single (Or.inl ⟨rfl,hra,hrb,hq⟩)

 

theorem glues_tile_adjoint {n : ℕ} {p q : Pairing n} {a b root : Fin n}
    (hab : a.val+1=b.val) (hra : root ≠ a) (hrb : root ≠ b) (t : Tile) :
    (∃ r, p.tileStep a b hab t = some r ∧ GluesAt root r q) ↔
      (∃ r, q.tileStep a b hab t.transpose = some r ∧ GluesAt root p r) := by
  constructor
  · intro h
    obtain ⟨r,hr,hg⟩ := glues_tile_flip hab hra hrb t h
    exact ⟨r,hr,hg.symm⟩
  · rintro ⟨r,hr,hg⟩
    simpa only [Tile.transpose_transpose] using glues_tile_flip hab hra hrb
      t.transpose ⟨r,hr,hg.symm⟩

lemma gluesAt_comm {n : ℕ} (root : Fin n) (p q : Pairing n) :
    GluesAt root p q ↔ GluesAt root q p := ⟨GluesAt.symm,GluesAt.symm⟩

end Pairing

 

def glueMatrix {K : Type*} [Zero K] [One K] {n : ℕ} (root : Fin n) :
    Matrix (Pairing n) (Pairing n) K :=
  fun p q => if Pairing.GluesAt root p q then 1 else 0

lemma glueMatrix_transpose {K : Type*} [Zero K] [One K] {n : ℕ} (root : Fin n) :
    (glueMatrix root : Matrix _ _ K).transpose = glueMatrix root := by
  ext p q
  simp only [Matrix.transpose_apply,glueMatrix,Pairing.gluesAt_comm root q p]

lemma mul_optionMatrix_apply {K P Q R : Type*} [Semiring K] [Fintype Q]
    (A : Matrix R Q K) (f : P → Option Q) (r : R) (p : P) :
    (A * (optionMatrix f : Matrix Q P K)) r p = (f p).elim 0 (A r) := by
  rcases Option.eq_none_or_eq_some (f p) with h | ⟨q,h⟩
  · simp [Matrix.mul_apply,optionMatrix,h]
  · simp [Matrix.mul_apply,optionMatrix,h,mul_ite]

lemma transpose_optionMatrix_mul_apply {K P Q R : Type*} [Semiring K] [Fintype Q]
    (A : Matrix Q R K) (f : P → Option Q) (p : P) (r : R) :
    ((optionMatrix f : Matrix Q P K).transpose * A) p r = (f p).elim 0 (fun q => A q r) := by
  rcases Option.eq_none_or_eq_some (f p) with h | ⟨q,h⟩
  · simp [Matrix.mul_apply,optionMatrix,h]
  · simp [Matrix.mul_apply,optionMatrix,h,ite_mul]

lemma tileMatrix_glue_adjoint {K : Type*} [Semiring K] {n : ℕ} (a : Position n)
    (root : Fin n) (hra : root≠a.left) (hrb : root≠a.right) (t : Tile) :
    (glueMatrix root : Matrix _ _ K) *
        optionMatrix (fun p => p.tileStep a.left a.right a.adjacent t) =
      (optionMatrix (fun p => p.tileStep a.left a.right a.adjacent t.transpose)).transpose *
        glueMatrix root := by
  ext q p
  rw [mul_optionMatrix_apply,transpose_optionMatrix_mul_apply]
  have hh := Pairing.glues_tile_adjoint (p:=p) (q:=q) a.adjacent hra hrb t
  rcases Option.eq_none_or_eq_some (p.tileStep a.left a.right a.adjacent t) with hp | ⟨r,hp⟩
  <;> rcases Option.eq_none_or_eq_some (q.tileStep a.left a.right a.adjacent t.transpose)
    with hq | ⟨s,hq⟩
  · simp [hp,hq]
  · have hs : ¬ Pairing.GluesAt root p s := by simpa [hp,hq] using hh.symm
    simpa [hp,hq,glueMatrix,Pairing.gluesAt_comm root s p] using
      (ite_eq_right hs : (if Pairing.GluesAt root p s then (1:K) else 0) = 0).symm
  · have hr : ¬ Pairing.GluesAt root r q := by simpa [hp,hq] using hh
    simp [hp,hq,glueMatrix,Pairing.gluesAt_comm root q r,hr]
  · have he : Pairing.GluesAt root r q ↔ Pairing.GluesAt root p s := by
      simpa [hp,hq] using hh
    simp only [hp,hq,Option.elim_some,glueMatrix,Pairing.gluesAt_comm root q r,
      Pairing.gluesAt_comm root s p,he]

 

theorem localR_glue_adjoint {K : Type*} [CommRing K] {n : ℕ} (a : Position n)
    (root : Fin n) (hra : root≠a.left) (hrb : root≠a.right) (w : Weights K) :
    (glueMatrix root : Matrix _ _ K) * localR a w = (localR a w).transpose * glueMatrix root := by
  simp only [localR,Finset.mul_sum,Matrix.mul_smul,Finset.sum_mul,
    Matrix.transpose_sum,Matrix.transpose_smul,Matrix.smul_mul]
  rw [← Equiv.sum_comp Tile.transposeEquiv]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Tile.transposeEquiv,Equiv.coe_fn_mk,Tile.weight_transpose]
  rw [tileMatrix_glue_adjoint a root hra hrb]
  simp only [Tile.transpose_transpose]



 


 
def sourceBlock {K : Type*} {n m : ℕ}
    (M : Matrix (Pairing (m+1)) (Pairing (n+1)) K) :
    Matrix (SourcePairing m) (SourcePairing n) K := fun p q => M p.val q.val

lemma LastMatrix.source_mulVec {K : Type*} [CommRing K] {n m : ℕ}
    {M : Matrix (Pairing (m+1)) (Pairing (n+1)) K} (hM : LastMatrix M)
    (V : Pairing (n+1) → K) (p : SourcePairing m) :
    M.mulVec V p.val = (sourceBlock M).mulVec (fun q => V q.val) p := by
  simp only [Matrix.mulVec, dotProduct, sourceBlock]
  symm
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro q hq
    have hn : ¬q.Occupied (Fin.last n) := by
      intro h
      exact hq ⟨⟨q,h⟩,rfl⟩
    rw [hM p.val q (by simp [p.property, hn]), zero_mul]
  · intro q; rfl

lemma LastMatrix.source_coeff {K : Type*} [CommRing K] {n m : ℕ}
    {M : Matrix (Pairing (m+1)) (Pairing (n+1)) K} (hM : LastMatrix M)
    (V : Pairing (n+1) → Polynomial K) (p : SourcePairing m) (k : ℕ) :
    (matrixPolynomial M V p.val).coeff k =
      (sourceBlock M).mulVec (fun q => (V q.val).coeff k) p := by
  rw [matrixPolynomial_coeff, hM.source_mulVec]

 
lemma northNumerator_covariance {n : ℕ} (r : ℕ) (hr : r+2≤n) :
    northNumerator n =
      (sourceBlock (localR (PartialColumn.rowPosition r hr).padTop
        (torusWeights (variableF ⟨r+1,by omega⟩ / variableF ⟨r,by omega⟩)))).mulVec
        (fun p => permSpectral (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩)
          (northNumerator n p)) := by
  funext p
  have hh := congrArg (fun U : Pairing (n+1) → Polynomial (SpectralField n) =>
      (U p.val).coeff (n-1)) (rationalNodalPolynomial_covariance r hr)
  rw [nodalExchangePolynomial_coeff] at hh
  change northNumerator n p = _ at hh
  exact hh.trans ((LastMatrix.local _ _).source_mulVec _ p)

lemma northNumerator_parity {n : ℕ} (k : Fin n) (p : SourcePairing n) :
    signSpectral k (northNumerator n p) =
      occupancySign p.val k.castSucc * northNumerator n p := by
  have h := congrArg (fun P : Polynomial (SpectralField n) => P.coeff (n-1))
    (rationalNodalPolynomial_parity k p.val)
  simpa [northNumerator] using h

 

lemma LastDegree.occupied_mul_top {K : Type*} [CommRing K] {n m d : ℕ}
    (P : Pairing (n+1) → Polynomial K) (hP : LastDegree m P)
    (F : Polynomial K) (hF : F.natDegree ≤ d) (q : Pairing (n+1))
    (hq : q.Occupied (Fin.last n)) (hm : 1 ≤ m) :
    (F*P q).coeff (m+d-1) = F.coeff d * (P q).coeff (m-1) := by
  rw [show m+d-1=d+(m-1) by omega]
  apply Polynomial.coeff_mul_add_eq_of_natDegree_le hF
  exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    (fun k hk => hP q k (by simp only [hq,ite_true]; omega))

 
lemma isEmpty_source_zero : IsEmpty (SourcePairing 0) :=
  ⟨fun p => p.ne_empty (p.val.eq_empty_of_le_one (by omega))⟩

 

end
end CriticalStrip.Diagram

end OAI
