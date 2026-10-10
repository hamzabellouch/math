import OAI.Combinatorics.EditDistance.Metric
import OAI.Combinatorics.EditDistance.PrimeDisplacement

namespace OAI

/-!
# Finite word families with averaged displacement control
-/

namespace EditFamily
open scoped BigOperators
open EditDistortion EditAverage EditFourier

structure Family (p n A : ℕ) (α Q : ℝ) where
  State : Type
  [group : AddCommGroup State]
  [finite : Fintype State]
  v : State
  annihilate : p • v = 0
  word : State → Fin n → Fin A
  steps : List (State × ℝ)
  positive : ∀ e r, (e,r) ∈ steps → 0 < r
  cheap : ∀ e r, (e,r) ∈ steps → ∀ z,
    (indel (List.ofFn (word z)) (List.ofFn (word (z + e))) : ℝ) ≤ n * r
  far : ∀ z u, 0 < u → u < p →
    (n : ℝ) * α ≤ (indel (List.ofFn (word z)) (List.ofFn (word (z + u • v))) : ℝ)
  control : ∀ H : State → L1,
    (∀ e r, (e,r) ∈ steps → variation H e ≤ r) →
    ∀ u, 0 < u → u < p → variation H (u • v) ≤ Q

attribute [instance] Family.group Family.finite

lemma indel_singletons_le {A : Type*} (a b : A) : indel [a] [b] ≤ 2 := by
  exact cost_le ((Script.to_nil [a]).trans (Script.to_nil [b]).symm)

noncomputable def base {p A : ℕ} (hp : p.Prime) (hA : p ≤ A) : Family p 1 A 1 2 := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  let W : ZMod p → Fin 1 → Fin A := fun z _ => ⟨z.val, lt_of_lt_of_le (ZMod.val_lt z) hA⟩
  let S : List (ZMod p × ℝ) :=
    ((Finset.univ.filter (fun e : ZMod p => e ≠ 0)).toList).map (fun e => (e,2))
  have memS (e : ZMod p) (r : ℝ) : (e,r) ∈ S ↔ e ≠ 0 ∧ r = 2 := by
    simp [S, eq_comm]
  have phase (u : ℕ) (hu : 0 < u) (hup : u < p) : u • (1 : ZMod p) ≠ 0 := by
    simp only [nsmul_eq_mul, mul_one, Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hu hup
  refine { State := ZMod p
           group := inferInstance
           finite := inferInstance
           v := 1
           annihilate := ?_
           word := W
           steps := S
           positive := ?_
           cheap := ?_
           far := ?_
           control := ?_ }
  · simp [nsmul_eq_mul]
  · intro e r hr
    rw [(memS e r).mp hr |>.2]
    norm_num
  · intro e r hr z
    rw [(memS e r).mp hr |>.2]
    simpa [List.ofFn_succ, W] using
      (show (indel [W z 0] [W (z+e) 0] : ℝ) ≤ 2 from by exact_mod_cast indel_singletons_le _ _)
  · intro z u hu hup
    have hne : List.ofFn (W z) ≠ List.ofFn (W (z + u • (1 : ZMod p))) := by
      intro he
      have hx : W z 0 = W (z + u • (1 : ZMod p)) 0 := by
        simpa [List.ofFn_succ] using he
      have hz : z = z + u • (1 : ZMod p) := by
        apply ZMod.val_injective
        exact congrArg Fin.val hx
      exact phase u hu hup (add_eq_left.mp hz.symm)
    have hpos : 0 < indel (List.ofFn (W z)) (List.ofFn (W (z + u • (1 : ZMod p)))) :=
      Nat.pos_of_ne_zero (fun hh => hne ((cost_eq_zero_iff (s := false)).mp hh))
    have hlow : (1 : ℝ) ≤ indel (List.ofFn (W z)) (List.ofFn (W (z + u • (1 : ZMod p)))) := by
      exact_mod_cast hpos
    simpa using hlow
  · intro H hH u hu hup
    exact hH _ 2 ((memS _ _).mpr ⟨phase u hu hup, rfl⟩)

end EditFamily

end OAI
