import Mathlib
import OAI.Analysis.FreeWords.PatchingExpansion

namespace OAI

noncomputable section

namespace KKLocalPatching

open KKTraceTransfer KKFreeLiftFrontier KKUltraTrace KKProjectionSupport KKMatrixQuantization

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)

theorem trace_colored_single (v w : PartialUnitary (ConcreteAlgebra M))
    (p s : List (ConcreteAlgebra M × ℤ)) (z : ConcreteAlgebra M × ℤ) (right : ConcreteAlgebra M) :
    τ.map (Colored.value v.power w.power (Colored.old p++(z,true)::Colored.old s)*right)=
      τ.map (w.power z.2*(PatchingWord.tailValue v.power s*right*PatchingWord.tailValue v.power p*z.1)) := by
  simp only [Colored.value_append,Colored.value_cons,ite_true,Colored.value_old]
  change τ.map ((PatchingWord.tailValue v.power p*(z.1*w.power z.2*PatchingWord.tailValue v.power s))*right)=_
  rw [show (PatchingWord.tailValue v.power p*(z.1*w.power z.2*PatchingWord.tailValue v.power s))*right=
    (PatchingWord.tailValue v.power p*z.1)*(w.power z.2*(PatchingWord.tailValue v.power s*right)) by noncomm_ring]
  rw [τ.tracial]
  congr 1

theorem trace_colored_multiple (v w : PartialUnitary (ConcreteAlgebra M))
    (p g : List (ConcreteAlgebra M × ℤ)) (z y : ConcreteAlgebra M × ℤ)
    (r : List (Colored.Cell (ConcreteAlgebra M))) (right : ConcreteAlgebra M) :
    τ.map (Colored.value v.power w.power (Colored.old p++(z,true)::(Colored.old g++(y,true)::r))*right)=
      τ.map (w.power z.2*(PatchingWord.tailValue v.power g*y.1)*w.power y.2*
        (Colored.value v.power w.power r*right*PatchingWord.tailValue v.power p*z.1)) := by
  simp only [Colored.value_append,Colored.value_cons,ite_true,Colored.value_old]
  change τ.map ((PatchingWord.tailValue v.power p*
    (z.1*w.power z.2*(PatchingWord.tailValue v.power g*(y.1*w.power y.2*Colored.value v.power w.power r))))*right)=_
  rw [show (PatchingWord.tailValue v.power p*
    (z.1*w.power z.2*(PatchingWord.tailValue v.power g*(y.1*w.power y.2*Colored.value v.power w.power r))))*right=
      (PatchingWord.tailValue v.power p*z.1)*
        (w.power z.2*(PatchingWord.tailValue v.power g*y.1)*w.power y.2*Colored.value v.power w.power r*right) by noncomm_ring]
  rw [τ.tracial]
  congr 1

theorem norm_mul_le_one {a b : ConcreteAlgebra M} (ha : ‖a‖≤1) (hb : ‖b‖≤1) : ‖a*b‖≤1 := by
  simpa only [one_mul] using (norm_mul_le a b).trans (mul_le_mul ha hb (norm_nonneg _) zero_le_one)

theorem norm_raw_coefficients {X : Set (ConcreteAlgebra M)} {K : Set ℤ} {N : ℕ}
    (hX : ∀ x∈X, ‖x‖≤1) {w : PatchingWord (ConcreteAlgebra M)}
    (hw : PatchingWord.Admissible X K N w) :
    (∀ z∈w.raw, ‖z.1‖≤1) ∧ ‖w.right‖≤1 := by
  have hE : ∀ x∈insert (1:ConcreteAlgebra M) X, ‖x‖≤1 := by
    intro x hx
    rcases hx with rfl | hx
    · exact PatchingWord.concrete_norm_one_le
    · exact hX x hx
  refine ⟨?_,hE _ hw.2.2.1⟩
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · exact hE _ hw.1
  · exact hX _ (hw.2.2.2.1 z hz).1

theorem norm_colored_multiple_rest (v w : PartialUnitary (ConcreteAlgebra M))
    (p g : List (ConcreteAlgebra M × ℤ)) (z y : ConcreteAlgebra M × ℤ)
    (r : List (Colored.Cell (ConcreteAlgebra M))) (right : ConcreteAlgebra M)
    (h : ∀ a∈Colored.old p++(z,true)::(Colored.old g++(y,true)::r), ‖a.1.1‖≤1)
    (hright : ‖right‖≤1) :
    ‖Colored.value v.power w.power r*right*PatchingWord.tailValue v.power p*z.1‖≤1 := by
  have hz : ‖z.1‖≤1 := h (z,true) (List.mem_append_right _ List.mem_cons_self)
  have hp : ‖PatchingWord.tailValue v.power p‖≤1 := by
    have hh := norm_colored_value_le_one v w (Colored.old p)
      (fun a ha => h a (List.mem_append_left _ ha))
    simpa only [Colored.value_old,PatchingWord.tailValue] using hh
  have hr : ‖Colored.value v.power w.power r‖≤1 := by
    apply norm_colored_value_le_one v w r
    intro a ha
    exact h a (List.mem_append_right _ (List.mem_cons_of_mem _
      (List.mem_append_right _ (List.mem_cons_of_mem _ ha))))
  exact norm_mul_le_one (norm_mul_le_one (norm_mul_le_one hr hright) hp) hz

end

end KKLocalPatching
end

end OAI
