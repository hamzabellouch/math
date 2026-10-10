import Mathlib
import OAI.Analysis.FreeWords.ColoredExpansion
import OAI.Analysis.FreeWords.PartialUnitaryNorm
import OAI.Analysis.FreeWords.PatchingGapWords

namespace OAI

noncomputable section

namespace KKLocalPatching

open KKTraceTransfer KKFreeLiftFrontier KKUltraTrace KKProjectionSupport KKMatrixQuantization

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)

theorem norm_list_sum_le_length_mul {ι : Type*} (s : List ι) (f : ι → ℂ) {b : ℝ}
    (hf : ∀ i∈s, ‖f i‖≤b) : ‖(s.map f).sum‖≤ s.length*b := by
  induction s with
  | nil => simp
  | cons a s ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    calc
      _ ≤ ‖f a‖+‖(s.map f).sum‖ := norm_add_le _ _
      _ ≤ b+s.length*b := add_le_add (hf a List.mem_cons_self)
        (ih fun i hi => hf i (List.mem_cons_of_mem _ hi))
      _ = _ := by ring

theorem expanded_value (w : PatchingWord (ConcreteAlgebra M))
    (u v : ℤ → ConcreteAlgebra M) :
    w.value (fun k => u k+v k)=w.value u+
      ((Colored.changes w.raw).map (fun c => Colored.value u v c*w.right)).sum := by
  rw [PatchingWord.value_raw,PatchingWord.tailValue,Colored.expansion,add_mul]
  rw [List.sum_map_mul_right]
  rfl

theorem expanded_trace_bound (w : PatchingWord (ConcreteAlgebra M))
    (u v : ℤ → ConcreteAlgebra M) {b : ℝ} (hb : 0≤b)
    (hterms : ∀ c∈Colored.changes w.raw, ‖τ.map (Colored.value u v c*w.right)‖≤b) :
    ‖τ.map (w.value (fun k => u k+v k))‖≤‖τ.map (w.value u)‖+2^w.length*b := by
  rw [expanded_value,map_add,map_list_sum,List.map_map]
  have he := Colored.changes_length w.raw
  have hlen : (Colored.changes w.raw).length≤2^w.length := by
    rw [PatchingWord.raw_length] at he
    omega
  calc
    _ ≤ ‖τ.map (w.value u)‖+
        ‖((Colored.changes w.raw).map (fun c => τ.map (Colored.value u v c*w.right))).sum‖ := norm_add_le _ _
    _ ≤ ‖τ.map (w.value u)‖+(Colored.changes w.raw).length*b :=
      add_le_add le_rfl (norm_list_sum_le_length_mul _ _ hterms)
    _ ≤ ‖τ.map (w.value u)‖+2^w.length*b := add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hb)

theorem norm_colored_value_le_one (v w : PartialUnitary (ConcreteAlgebra M))
    (c : List (Colored.Cell (ConcreteAlgebra M)))
    (hc : ∀ z∈c, ‖z.1.1‖≤1) : ‖Colored.value v.power w.power c‖≤1 := by
  induction c with
  | nil => exact PatchingWord.concrete_norm_one_le
  | cons z c ih =>
    rw [Colored.value_cons]
    have hk : ‖(if z.2 then w.power z.1.2 else v.power z.1.2)‖≤1 := by
      split <;> exact PartialUnitary.norm_power_le_one _ _
    have hz : ‖z.1.1*(if z.2 then w.power z.1.2 else v.power z.1.2)‖≤1 := by
      simpa only [one_mul] using (norm_mul_le _ _).trans
        (mul_le_mul (hc z List.mem_cons_self) hk (norm_nonneg _) zero_le_one)
    simpa only [one_mul] using (norm_mul_le _ _).trans
      (mul_le_mul hz (ih fun a ha => hc a (List.mem_cons_of_mem _ ha)) (norm_nonneg _) zero_le_one)

end

end KKLocalPatching
end

end OAI
