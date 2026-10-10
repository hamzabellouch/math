import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalCore

namespace OAI

/-! Tensoring with fresh mediators adds precisely their explicit supports. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem QMALocalOn.joinLeft {S : Finset ι} {A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ}
    (hA : QMALocalOn S A) :
    QMALocalOn (S.map (Function.Embedding.inl : ι ↪ ι ⊕ κ)) (qmaJoinMatrix A (κ := κ) 1) := by
  obtain ⟨B,rfl⟩ := hA
  let T := S.map (Function.Embedding.inl : ι ↪ ι ⊕ κ)
  let k : {i // i ∈ S} → {i // i ∈ T} := fun i =>
    ⟨Sum.inl i.val,Finset.mem_map.mpr ⟨i.val,i.property,rfl⟩⟩
  refine ⟨(fun u v => B (u ∘ k) (v ∘ k)),?_⟩
  ext s t
  change (B (fun i => s (Sum.inl i.val)) (fun i => t (Sum.inl i.val))*
      if (fun i : {i // i ∉ S} => s (Sum.inl i.val)) =
        (fun i : {i // i ∉ S} => t (Sum.inl i.val)) then 1 else 0)*
      (if (s ∘ Sum.inr) = (t ∘ Sum.inr) then (1:ℂ) else 0) =
    B (fun i => s (Sum.inl i.val)) (fun i => t (Sum.inl i.val))*
      if (fun i : {i // i ∉ T} => s i.val) = (fun i : {i // i ∉ T} => t i.val) then 1 else 0
  have he : ((fun i : {i // i ∉ T} => s i.val) = (fun i : {i // i ∉ T} => t i.val)) ↔
      (fun i : {i // i ∉ S} => s (Sum.inl i.val)) =
        (fun i : {i // i ∉ S} => t (Sum.inl i.val)) ∧ (s ∘ Sum.inr) = (t ∘ Sum.inr) := by
    constructor
    · intro h
      constructor
      · funext i
        exact congrFun h ⟨Sum.inl i.val,by simpa [T] using i.property⟩
      · funext i
        exact congrFun h ⟨Sum.inr i,by simp [T]⟩
    · rintro ⟨hl,hr⟩
      funext i
      rcases i with ⟨i,hi⟩
      cases i with
      | inl j => exact congrFun hl ⟨j,by simpa [T] using hi⟩
      | inr j => exact congrFun hr j
  by_cases hl : (fun i : {i // i ∉ S} => s (Sum.inl i.val)) =
      (fun i : {i // i ∉ S} => t (Sum.inl i.val))
  <;> by_cases hr : (s ∘ Sum.inr) = (t ∘ Sum.inr)
  <;> simp only [he,hl,hr,and_self,and_false,false_and,ite_true,ite_false,mul_one,mul_zero]

theorem qmaJoinMatrix_mul (A B : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (C D : Matrix (κ → Fin 2) (κ → Fin 2) ℂ) :
    qmaJoinMatrix (A*B) (C*D) = qmaJoinMatrix A C*qmaJoinMatrix B D := by
  unfold qmaJoinMatrix
  rw [Matrix.submatrix_mul_equiv,← Matrix.mul_kronecker_mul]

theorem QMALocalOn.join {S : Finset ι} {T : Finset κ}
    {A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ} {B : Matrix (κ → Fin 2) (κ → Fin 2) ℂ}
    (hA : QMALocalOn S A) (hB : QMALocalOn T B) :
    QMALocalOn (S.map Function.Embedding.inl ∪ T.map Function.Embedding.inr) (qmaJoinMatrix A B) := by
  have he : qmaJoinMatrix A B = qmaJoinMatrix A (κ := κ) 1*qmaJoinMatrix (ι := ι) 1 B := by
    rw [← qmaJoinMatrix_mul,mul_one,one_mul]
  rw [he]
  exact (hA.joinLeft.mono Finset.subset_union_left).mul
    (hB.joinRight.mono Finset.subset_union_right)

theorem qmaJoin_two_local {S : Finset ι} {T : Finset κ}
    {A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ} {B : Matrix (κ → Fin 2) (κ → Fin 2) ℂ}
    (hA : QMALocalOn S A) (hB : QMALocalOn T B) (hS : S.card ≤ 1) (hT : T.card ≤ 1) :
    ∃ U : Finset (ι ⊕ κ), U.card ≤ 2 ∧ QMALocalOn U (qmaJoinMatrix A B) := by
  refine ⟨_,?_,hA.join hB⟩
  have hc := Finset.card_union_le (S.map (Function.Embedding.inl : ι ↪ ι ⊕ κ))
    (T.map (Function.Embedding.inr : κ ↪ ι ⊕ κ))
  simp only [Finset.card_map] at hc
  omega

end ContinuumCoulomb

end

end OAI
