import OAI.Combinatorics.EditDistance.UpperRecursion
import OAI.Combinatorics.EditDistance.UpperParameters
import OAI.Combinatorics.EditDistance.CutRealization
import OAI.Combinatorics.EditDistance.DistortionMonotonicity

namespace OAI

/-!
# Alphabet-uniform upper bounds for least distortion
-/

namespace EditUpper
open EditDistortion EditCutModel
universe u

lemma model_E_bound (A : Type u) [Fintype A] [Nonempty A] {d : ℕ} (hd : 1 ≤ d)
    (M : Model (List A)) {D : ℝ} (hD : 0 ≤ D)
    (hlo : ∀ x y : List A, x.length ≤ d → y.length ≤ d → (indel x y : ℝ) ≤ M.dist x y)
    (hup : ∀ x y : List A, M.dist x y ≤ D*(indel x y : ℝ)) : E A d ≤ 2*D := by
  classical
  let : Finite (Words A d) := finite_words A d
  let x : Words A d := ⟨[],by simp⟩
  let y : Words A d := ⟨[Classical.arbitrary A],by simpa using hd⟩
  let : Nontrivial (Words A d) := ⟨⟨x,y,by simp [x,y]⟩⟩
  let f : Words A d ↪ L1 :=
    { toFun := fun z => M.vector z.val
      inj' := by
        intro v w he
        change M.vector v.val = M.vector w.val at he
        have hh := hlo v.val w.val v.property w.property
        rw [← M.vector_distance,he,sub_self,norm_zero] at hh
        have hz : indel v.val w.val = 0 := by exact_mod_cast le_antisymm hh (Nat.cast_nonneg _)
        exact Subtype.ext ((cost_eq_zero_iff (s := false)).mp hz) }
  apply (leastDistortion_le _ (fun z => edit_real_diag z.val)
    (fun v w h => edit_real_pos v.val w.val (fun hh => h (Subtype.ext hh))) f).trans
  have hbound : distortion (fun v w : Words A d => (edit v.val w.val : ℝ)) f ≤ (2*D)*1 := by
    apply distortion_le_of_bounds _
      (fun v w h => edit_real_pos v.val w.val (fun hh => h (Subtype.ext hh))) f (by positivity)
    · intro v w
      change ‖M.vector v.val-M.vector w.val‖ ≤ _
      rw [M.vector_distance]
      have hi : (indel v.val w.val : ℝ) ≤ 2*(edit v.val w.val : ℝ) := by
        exact_mod_cast indel_le_two_edit v.val w.val
      calc
        _ ≤ D*(indel v.val w.val : ℝ) := hup _ _
        _ ≤ D*(2*(edit v.val w.val : ℝ)) := mul_le_mul_of_nonneg_left hi hD
        _ = _ := by ring
    · intro v w
      change (edit v.val w.val : ℝ) ≤ 1*‖M.vector v.val-M.vector w.val‖
      rw [one_mul,M.vector_distance]
      exact (show (edit v.val w.val : ℝ) ≤ indel v.val w.val by
        exact_mod_cast edit_le_indel v.val w.val).trans (hlo _ _ v.property w.property)
  simpa using hbound

lemma level_E_bound (b N : ℕ) (hb : 1 ≤ b) (A : Type u) [Fintype A] [Nonempty A]
    {d : ℕ} (hd : 1 ≤ d) (hcap : d ≤ b^N) :
    E A d ≤ 2*(((b : ℝ)+2)*(growth b N)^N) := by
  obtain ⟨M,hlo,hup⟩ := exists_level b N hb N le_rfl A
  have hD : 0 ≤ ((b : ℝ)+2)*(growth b N)^N := by
    have hh := growth_ge (N := N) hb
    positivity
  exact model_E_bound A hd M hD
    (fun x y hx hy => hlo x y (hx.trans hcap) (hy.trans hcap)) hup

theorem eventual_upper : ∀ᶠ d : ℕ in Filter.atTop,
    (∀ (A : Type u) [Fintype A], 2 ≤ Fintype.card A → E A d ≤ exponentScale 32 d) ∧
    alphabetSup d ≤ exponentScale 32 d := by
  filter_upwards [EditUpperParameters.eventual_choice,Filter.eventually_ge_atTop (1 : ℕ)] with d hc hd
  rcases hc with ⟨hN,hb,hcap,hbound⟩
  let N := EditUpperParameters.level (Real.log (d : ℝ))
  let b := EditUpperParameters.branching (Real.log (d : ℝ))
  have hnum : 2*(((b : ℝ)+2)*(growth b N)^N) ≤ exponentScale 32 d := by
    simpa [growth,exponentScale,b,N,mul_assoc] using hbound
  constructor
  · intro A inst hA
    let : Nonempty A := Fintype.card_pos_iff.mp (by omega)
    exact (level_E_bound b N (by omega) A hd hcap).trans hnum
  · apply csSup_le (s := {r : ℝ | ∃ n : ℕ, 2 ≤ n ∧ r = E (Fin n) d})
      ⟨E (Fin 2) d,2,by omega,rfl⟩
    rintro r ⟨n,hn,rfl⟩
    let : NeZero n := ⟨by omega⟩
    exact (level_E_bound b N (by omega) (Fin n) hd hcap).trans hnum

end EditUpper

end OAI
