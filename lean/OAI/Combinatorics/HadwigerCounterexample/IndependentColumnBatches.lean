import OAI.Combinatorics.HadwigerCounterexample.AmbientBatchSlots

namespace OAI

/-! # Independent Column Batches -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix LinearMap Module Finset Function
variable {I G J A B : Type} [Fintype I] [Fintype G] [Fintype J] [Fintype A] [Fintype B]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]
variable {p : Shape} {n N : ℕ}

theorem joint_map {A B : I→ Type} [∀ i,Fintype (A i)] [∀ i,Fintype (B i)]
    (w : ∀ i,Wgt (A i)) (f : ∀ i,A i→ B i) :
    mapW (prodW w) (fun x i => f i (x i))=prodW (fun i => mapW (w i) (f i)) := by
  classical
  funext x
  unfold mapW
  simp_rw [funext_iff]
  exact prodW_pr _ (fun i y => f i y=x i)

def rawC (m : Mixer p n) (N : ℕ) : Wgt (Oframe p n N) := unifOn (FramesAt (gramCond m))
def peer (p : Shape) {n} (A B : Mat (Row p n) I) {N} (x : Oframe p n N) :
    Rack I N := (primary x.1*A,primary x.2*B)

theorem peer_cap (m : Mixer p n) (N : ℕ) (hN : 2*num (Full p n)<N)
    {A B : Mat (Row p n) I} (hA : Injective A.mulVec) (hB : Injective B.mulVec) :
    mapW (rawC m N) (peer p A B)=unifOn (gramGood (pullM A B (selfM p n m.mixM))) := by
  classical
  have hh : ∃ x : Oframe p n N,FramesAt (gramCond m) x :=
    framesAt_exists (gramCond_exists m)
      (by rw [← two_mul]; simpa only [num,Fintype.card_fin] using hN)
  let U : Mat (Full p n) (Row p n) := embedMat (.inl ·)
  have he : Injective U.mulVec := embedMat_inj Sum.inl_injective
  have hP (x : Mat (Fin N) (Full p n)) : x*U=primary x := by
    unfold U; rw [mul_embedMat]; rfl
  have hS (M : Mat (Full p n) (Full p n)) (hM : gramCond m M) :
      (U*A)ᵀ*M*(U*B) = pullM A B (selfM p n m.mixM) := by
    rw [pullM_def]
    have ht : Uᵀ*M*U=selfM p n m.mixM := by
      unfold U; rw [embedMat_mul,mul_embedMat]; exact hM.1
    rw [←ht,Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  have ht : peer p A B (N:=N)=observe (U*A) (U*B) := by
    funext x
    unfold peer observe
    rw [←Matrix.mul_assoc,← Matrix.mul_assoc,hP,hP]
  rw [ht]
  exact framesAt_observe hh _ _ (inj_comp_mat _ _ he hA) (inj_comp_mat _ _ he hB) hS

abbrev Forum (p : Shape) (n N : ℕ) (G : Type) := G → Oframe p n N
def forumLaw (m : Mixer p n) (N : ℕ) : Wgt (Forum p n N G) :=
  prodW (fun (_ : G) => rawC m N)

abbrev NomQuery (p : Shape) (n : ℕ) {I G : Type} (g : Route I G) :=
  ∀ i, Mat (Row p n) (Port g i)
variable {g : Route I G}
def peekR (p : Shape) {n} (g : Route I G) (A B : NomQuery p n g)
    {N} (x : Forum p n N G) :=
  (rackEquiv g N).symm (fun i => peer p (A i) (B i) (x i))
def database (m : Mixer p n) (A B : NomQuery p n g) : GeoM g :=
  fun i => pullM (A i) (B i) (selfM p n m.mixM)

theorem law_peekR (m : Mixer p n) {N : ℕ} (hN : 2*num (Full p n)<N)
    {A B : NomQuery p n g}
    (ha : ∀ i,Injective (A i).mulVec) (hb : ∀ i, Injective (B i).mulVec) :
    mapW (forumLaw m N) (peekR p g A B)=rackStation (database m A B) N := by
  classical
  let v := forumLaw m N (G:=G)
  let E := rackEquiv g N
  let w := rackStation (database m A B) N
  let f (x : Forum p n N G) := fun i => peer p (A i) (B i) (x i)
  have h : mapW v f=mapW w E := by
    unfold v f w E forumLaw
    rw [joint_map (B:=fun i => Rack (Port g i) N) (w:=fun (_:G) => rawC m N)
      (f:=fun i => peer p (A i) (B i)),station_split]
    apply congrArg (prodW (ι:=G))
    funext i
    exact peer_cap m N hN (ha i) (hb i)
  change mapW v (E.symm ∘ f)=w
  rw [←mapW_nested,h]
  funext x
  rw [mapW_equiv_val,mapW_equiv_val,Equiv.symm_symm,Equiv.symm_apply_apply]

/-- Merge two endpoints of raw frame. Assign ports according
to their endpoint. -/
abbrev Ports (p : Shape) := Bool × Comp p.g
def mergeR (p : Shape) {n N} :
    UnitType p n N ≃ Forum p n N (Ports p) where
  toFun x i := onSide x i.1 i.2
  invFun x := (fun i => x (true,i),fun i => x (false,i))
  left_inv _ := rfl
  right_inv x := funext fun i => by rcases i with ⟨c|c,z⟩ <;> rfl

theorem law_mergeR (m : Mixer p n) (N : ℕ) :
    mapW (pairW (raw m N) (raw m N)) (mergeR p)=forumLaw m N := by
  classical
  funext x
  rw [mapW_equiv_val,forumLaw,prodW,Fintype.prod_prod_type,Fintype.prod_bool]
  rfl

end HadwigerCounterexample

end

end OAI
