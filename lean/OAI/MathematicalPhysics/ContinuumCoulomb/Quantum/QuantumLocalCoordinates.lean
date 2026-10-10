import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalEnlarge

namespace OAI

/-! Diagonal controls and changes between explicit qubit coordinate sets. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical Kronecker

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaLocalOn_diagonal (S : Finset ι) (d : (ι → Fin 2) → ℂ)
    (hd : ∀ s t, (∀ i ∈ S, s i = t i) → d s = d t) :
    QMALocalOn S (Matrix.diagonal d) := by
  refine ⟨Matrix.diagonal (fun u => d (qmaSupportExtend S u)),?_⟩
  ext s t
  rw [qmaLocalLift_apply]
  by_cases hs : (fun i : {i // i ∈ S} => s i.val) = (fun i : {i // i ∈ S} => t i.val)
  · by_cases hr : (fun i : {i // i ∉ S} => s i.val) = (fun i : {i // i ∉ S} => t i.val)
    · have hst : s = t := by
        funext i
        by_cases hi : i ∈ S
        · exact congrFun hs ⟨i,hi⟩
        · exact congrFun hr ⟨i,hi⟩
      subst t
      simp only [Matrix.diagonal_apply_eq,ite_true,mul_one]
      apply hd
      intro i hi
      simp [qmaSupportExtend,hi]
    · have hst : s ≠ t := by intro h; apply hr; rw [h]
      simp only [Matrix.diagonal_apply_ne _ hst,ite_eq_right hr,mul_zero]
  · have hst : s ≠ t := by intro h; apply hs; rw [h]
    simp only [Matrix.diagonal_apply_ne _ hst,Matrix.diagonal_apply_ne _ hs,zero_mul]

def qmaJoinMatrix {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (B : Matrix (κ → Fin 2) (κ → Fin 2) ℂ) :
    Matrix (ι ⊕ κ → Fin 2) (ι ⊕ κ → Fin 2) ℂ :=
  (A ⊗ₖ B).submatrix (Equiv.sumArrowEquivProdArrow ι κ (Fin 2))
    (Equiv.sumArrowEquivProdArrow ι κ (Fin 2))

theorem QMALocalOn.joinRight {κ : Type*} [Fintype κ] [DecidableEq κ]
    {S : Finset κ} {A : Matrix (κ → Fin 2) (κ → Fin 2) ℂ}
    (hA : QMALocalOn S A) :
    QMALocalOn (S.map (Function.Embedding.inr : κ ↪ ι ⊕ κ)) (qmaJoinMatrix (ι := ι) 1 A) := by
  obtain ⟨B,rfl⟩ := hA
  let T := S.map (Function.Embedding.inr : κ ↪ ι ⊕ κ)
  let k : {i // i ∈ S} → {i // i ∈ T} := fun i =>
    ⟨Sum.inr i.val,Finset.mem_map.mpr ⟨i.val,i.property,rfl⟩⟩
  refine ⟨(fun u v => B (u ∘ k) (v ∘ k)),?_⟩
  ext s t
  change (if (s ∘ Sum.inl) = (t ∘ Sum.inl) then (1:ℂ) else 0)*
    (B (fun i => s (Sum.inr i.val)) (fun i => t (Sum.inr i.val))*
      if (fun i : {i // i ∉ S} => s (Sum.inr i.val)) =
          (fun i : {i // i ∉ S} => t (Sum.inr i.val)) then 1 else 0) =
    B (fun i => s (Sum.inr i.val)) (fun i => t (Sum.inr i.val))*
      if (fun i : {i // i ∉ T} => s i.val) = (fun i : {i // i ∉ T} => t i.val) then 1 else 0
  have he : ((fun i : {i // i ∉ T} => s i.val) = (fun i : {i // i ∉ T} => t i.val)) ↔
      (s ∘ Sum.inl) = (t ∘ Sum.inl) ∧
      (fun i : {i // i ∉ S} => s (Sum.inr i.val)) =
        (fun i : {i // i ∉ S} => t (Sum.inr i.val)) := by
    constructor
    · intro h
      constructor
      · funext i
        exact congrFun h ⟨Sum.inl i,by simp [T]⟩
      · funext i
        exact congrFun h ⟨Sum.inr i.val,by simpa [T] using i.property⟩
    · rintro ⟨hl,hr⟩
      funext i
      rcases i with ⟨i,hi⟩
      cases i with
      | inl j => exact congrFun hl j
      | inr j => exact congrFun hr ⟨j,by simpa [T] using hi⟩
  by_cases hl : (s ∘ Sum.inl) = (t ∘ Sum.inl)
  <;> by_cases hr : (fun i : {i // i ∉ S} => s (Sum.inr i.val)) =
      (fun i : {i // i ∉ S} => t (Sum.inr i.val))
  <;> simp only [he,hl,hr,and_self,and_false,false_and,ite_true,ite_false,mul_one,
    one_mul,zero_mul,mul_zero]

end ContinuumCoulomb

end

end OAI
