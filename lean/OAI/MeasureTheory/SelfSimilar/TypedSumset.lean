import OAI.MeasureTheory.SelfSimilar.RetainedLoss

namespace OAI

universe uα uβ

namespace EntropyRateDimension.Typed
open FairPairs FiniteCondition
open scoped BigOperators
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

omit [DecidableEq β] in

theorem translation_coefficients (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    {n : ℕ} (w : Fin n → α) :
    ∃ R : Fin n → ℝ, ∀ v, tagWord tag v=tagWord tag w →
      (S.completeMap v).2=∑ j, R j*S.offset (v j) := by
  induction n with
  | zero =>
    refine ⟨Fin.elim0,fun v _ => ?_⟩
    simp [System.completeMap,System.wordAffine]
  | succ n ih =>
    obtain ⟨R,hR⟩ := ih (fun j => w j.succ)
    refine ⟨Fin.cons 1 (fun j => S.ratio (w 0)*R j),fun v hv => ?_⟩
    have ht : tagWord tag (fun j => v j.succ)=tagWord tag (fun j => w j.succ) :=
      funext (fun j => congrFun hv j.succ)
    have hr0 := hr (v 0) (w 0) (congrFun hv 0)
    conv_lhs => rw [← Fin.cons_self_tail v,S.completeMap_cons]
    simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,one_mul]
    rw [hR (Fin.tail v) ht,hr0]
    simp only [Finset.mul_sum,mul_assoc,Fin.tail]
    ring

theorem support_digit_representation (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    {n : ℕ} (w : Fin n → α) :
    ∃ R : Fin n → ℝ, ∀ x ∈ (law S tag w).support,
      ∃ v : Fin n → α, x=∑ j, R j*S.offset (v j) := by
  obtain ⟨R,hR⟩ := translation_coefficients S tag hr w
  refine ⟨R,fun x hx => ?_⟩
  change x ∈ (fiber (tagWord tag) w).image (fun v => (S.completeMap v).2) at hx
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
  exact ⟨v,hR v (Finset.mem_filter.mp hv).2⟩

theorem sumset_card_bound (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    {n : ℕ} (w : Fin n → α) (k : ℕ) :
    ((law S tag w).sumset k).card ≤ (k+1)^(n*Fintype.card α) := by
  obtain ⟨R,hR⟩ := support_digit_representation S tag hr w
  simpa only [Fintype.card_fin, DigitSumset.sumset, Law.sumset] using
    DigitSumset.card_sumset_le (law S tag w).support (fun j a => R j*S.offset a) hR k

theorem sumset_log_bound (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    {n : ℕ} (w : Fin n → α) (k : ℕ) :
    Real.log ((law S tag w).sumset k).card ≤ (n : ℝ)*Fintype.card α*Real.log (k+1) := by
  classical
  obtain ⟨x,hx⟩ := (law S tag w).support_nonempty
  have hs : ((law S tag w).sumset k).Nonempty :=
    Finset.image_nonempty.mpr (Finset.univ_nonempty_iff.mpr ⟨fun _ : Fin k => ⟨x,hx⟩⟩)
  have hb : (((law S tag w).sumset k).card : ℝ) ≤ ((k : ℝ)+1)^(n*Fintype.card α) := by
    exact_mod_cast sumset_card_bound S tag hr w k
  have hh := Real.log_le_log (show (0 : ℝ)<((law S tag w).sumset k).card by
    exact_mod_cast Finset.card_pos.mpr hs) hb
  rw [Real.log_pow,Nat.cast_mul] at hh
  exact hh

end EntropyRateDimension.Typed

end OAI
