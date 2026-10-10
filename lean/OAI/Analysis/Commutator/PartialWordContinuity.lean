import Mathlib
import OAI.Analysis.Commutator.PartialWordPerturbation
import OAI.Analysis.Commutator.TracialL2Continuity

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Topology

open Filter

namespace Kadison.FinitePatching

variable {A J K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

include hτ in
lemma PartialUnitary.support_norm_sub (v w : PartialUnitary A) :
    TracialL2.norm τ (v.support-w.support) ≤ 2*TracialL2.norm τ (v.val-w.val) := by
  rw [←v.star_mul,←w.star_mul]
  have hh := TracialL2.norm_mul_sub_mul τ hτ (star v.val) v.val (star w.val) w.val
  rw [←star_sub,TracialL2.norm_star τ hτ,_root_.norm_star] at hh
  exact hh.trans (by
    have h1 := mul_le_of_le_one_right (TracialL2.norm_nonneg τ (v.val-w.val)) v.norm_le_one
    have h2 := mul_le_of_le_one_left (TracialL2.norm_nonneg τ (v.val-w.val)) w.norm_le_one
    linarith)

include hτ in
lemma PartialUnitary.power_norm_sub (v w : PartialUnitary A) (k : ℤ) :
    TracialL2.norm τ (v.power k-w.power k) ≤ ((k.natAbs:ℝ)+2)*TracialL2.norm τ (v.val-w.val) := by
  cases k with
  | ofNat n =>
    cases n with
    | zero => simpa only [PartialUnitary.power,Int.natAbs_ofNat',Nat.cast_zero,zero_add] using
        support_norm_sub τ hτ v w
    | succ n =>
      have hh := TracialL2.norm_pow_sub_pow τ hτ v.val w.val v.norm_le_one w.norm_le_one (n+1)
      change TracialL2.norm τ (v.val^(n+1)-w.val^(n+1)) ≤ _
      simp only [Int.natAbs_ofNat']
      exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (TracialL2.norm_nonneg τ _))
  | negSucc n =>
    have hh := TracialL2.norm_pow_sub_pow τ hτ (star v.val) (star w.val)
      (by simpa using v.norm_le_one) (by simpa using w.norm_le_one) (n+1)
    rw [←star_sub,TracialL2.norm_star τ hτ] at hh
    change TracialL2.norm τ ((star v.val)^(n+1)-(star w.val)^(n+1)) ≤ _
    simp only [Int.natAbs_negSucc]
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (TracialL2.norm_nonneg τ _))

namespace Words

variable (x : J → A) (k : K → ℤ)

def slotCost : Slot K → ℕ
  | none => 0
  | some none => 2
  | some (some i) => (k i).natAbs+2

def wordCost (l : List (Letter J K)) : ℕ := (l.map (fun i => slotCost k i.2)).sum

include hτ in
lemma slotPower_norm_sub (v w : PartialUnitary A) (s : Slot K) :
    TracialL2.norm τ (slotPower k v s-slotPower k w s) ≤
      (slotCost k s:ℝ)*TracialL2.norm τ (v.val-w.val) := by
  cases s with
  | none => simp [slotPower,slotCost,TracialL2.norm]
  | some s =>
    cases s with
    | none => exact v.support_norm_sub τ hτ w
    | some i => simpa only [slotPower,slotCost,Nat.cast_add,Nat.cast_ofNat] using
        v.power_norm_sub τ hτ w (k i)

include hτ in
lemma letter_norm_sub (hx : ∀ j,‖x j‖ ≤ 1) (v w : PartialUnitary A) (i : Letter J K) :
    TracialL2.norm τ (letter x k v i-letter x k w i) ≤
      (slotCost k i.2:ℝ)*TracialL2.norm τ (v.val-w.val) := by
  simp only [letter,←mul_sub]
  exact (TracialL2.norm_mul_left τ _ _).trans
    ((mul_le_of_le_one_left (TracialL2.norm_nonneg τ _) (hx i.1)).trans
      (slotPower_norm_sub τ hτ k v w i.2))

include hτ in
lemma word_norm_sub (hx : ∀ j,‖x j‖ ≤ 1) (v w : PartialUnitary A) (l : List (Letter J K)) :
    TracialL2.norm τ (word x k v l-word x k w l) ≤
      (wordCost k l:ℝ)*TracialL2.norm τ (v.val-w.val) := by
  induction l with
  | nil => simp [wordCost,TracialL2.norm]
  | cons i l ih =>
    rw [word_cons,word_cons]
    have hh := TracialL2.norm_mul_sub_mul τ hτ (letter x k v i) (word x k v l)
      (letter x k w i) (word x k w l)
    have h1 := (mul_le_of_le_one_right (TracialL2.norm_nonneg τ _)
      (word_norm x k hx v l)).trans (letter_norm_sub τ hτ x k hx v w i)
    have h2 := (mul_le_of_le_one_left (TracialL2.norm_nonneg τ _)
      (letter_norm x k hx w i)).trans ih
    exact hh.trans ((add_le_add h1 h2).trans_eq (by
      simp only [wordCost,List.map_cons,List.sum_cons,Nat.cast_add]; ring))

include hτ in
lemma trace_word_norm_sub (hone : τ 1=1) (hx : ∀ j,‖x j‖ ≤ 1)
    (v w : PartialUnitary A) (l : List (Letter J K)) :
    ‖τ (word x k v l)-τ (word x k w l)‖ ≤
      (wordCost k l:ℝ)*TracialL2.norm τ (v.val-w.val) := by
  rw [←map_sub]
  exact (TracialL2.norm_trace_le τ hτ hone _).trans (word_norm_sub τ hτ x k hx v w l)

include hτ in
lemma momentBound_limit {I : Type*} {f : Filter I} [NeBot f]
    (hone : τ 1=1) (hx : ∀ j,‖x j‖ ≤ 1)
    (v : I → PartialUnitary A) (w : PartialUnitary A) (B : I → ℝ) (b : ℝ) (N : ℕ)
    (hv : Tendsto (fun i => TracialL2.norm τ ((v i).val-w.val)) f (𝓝 0))
    (hB : Tendsto B f (𝓝 b)) (hb : ∀ i,MomentBound τ x k (v i) N (B i)) :
    MomentBound τ x k w N b := by
  have hpow (i : K) : Tendsto (fun j => τ ((v j).power (k i))) f (𝓝 (τ (w.power (k i)))) := by
    apply TracialL2.tendsto_trace τ hτ hone
    have hh := hv.const_mul ((k i).natAbs+2:ℝ)
    rw [mul_zero] at hh
    exact squeeze_zero (fun _ => TracialL2.norm_nonneg τ _) (fun j =>
      (v j).power_norm_sub τ hτ w (k i)) hh
  refine ⟨fun i => le_of_tendsto_of_tendsto (hpow i |>.norm) hB
    (Eventually.of_forall fun j => (hb j).1 i),?_⟩
  intro l hl hlen hvalid
  have hw : Tendsto (fun j => τ (word x k (v j) l)) f (𝓝 (τ (word x k w l))) := by
    apply TracialL2.tendsto_trace τ hτ hone
    have hh := hv.const_mul (wordCost k l:ℝ)
    rw [mul_zero] at hh
    exact squeeze_zero (fun _ => TracialL2.norm_nonneg τ _) (fun j => word_norm_sub τ hτ x k hx
      (v j) w l) hh
  exact le_of_tendsto_of_tendsto hw.norm hB (Eventually.of_forall fun j => (hb j).2 l hl hlen hvalid)

end Words

end Kadison.FinitePatching

end

end
end

end OAI
