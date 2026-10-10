import OAI.MathematicalPhysics.Heisenberg.MatrixUnitLift

namespace OAI

noncomputable section
open scoped Classical BigOperators Matrix
namespace Heisenberg.TensorUnits
variable {R E K : Type*} [CommSemiring R] [Semiring E] [Algebra R E]
  [Fintype K] [DecidableEq K]

lemma list_prod_smul {I : Type*} (L : List I) (c : I → R) (f : I → E) :
    (L.map (fun i=>c i • f i)).prod=(L.map c).prod • (L.map f).prod := by
  induction L with
  | nil=>simp
  | cons a L ih=>simp only [List.map_cons,List.prod_cons,ih,smul_mul_smul_comm]

lemma ofFn_prod_smul {n : ℕ} (c : Fin n → R) (f : Fin n → E) :
    (List.ofFn (fun i=>c i • f i)).prod=(∏ i,c i) • (List.ofFn f).prod := by
  have hh:=list_prod_smul (List.ofFn (id:Fin n → Fin n)) c f
  simpa only [List.map_ofFn,Function.comp_id,List.prod_ofFn] using hh

def pairConfigEquiv (n : ℕ) (K : Type*) : (Fin n → K×K) ≃ (Fin n → K)×(Fin n → K) where
  toFun f:=(fun i=>(f i).1,fun i=>(f i).2)
  invFun f i:=(f.1 i,f.2 i)
  left_inv _:=rfl
  right_inv _:=rfl

omit [DecidableEq K] in
lemma lift_tensorFin {n : ℕ} (u : Fin n → K → K → E) (M : Fin n → Matrix K K R) :
    liftLinear (system u) (fun a b=>∏ i,M i (a i) (b i))=
      (List.ofFn (fun i=>liftLinear (u i) (M i))).prod := by
  have hh:=(MultilinearMap.mkPiAlgebraFin R n E).map_sum
    (fun i (v : K×K)=>M i v.1 v.2 • u i v.1 v.2)
  simp only [Fintype.sum_prod_type,MultilinearMap.mkPiAlgebraFin_apply] at hh
  rw [←(pairConfigEquiv n K).symm.sum_comp,Fintype.sum_prod_type] at hh
  simp only [ofFn_prod_smul] at hh
  exact hh.symm

end Heisenberg.TensorUnits
end

end OAI
