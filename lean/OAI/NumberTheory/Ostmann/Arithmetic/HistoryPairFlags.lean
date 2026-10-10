import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairFlagBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairPolynomialKernel

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairFlags
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives HistoryPairFlagScope
open HistoryPairPolynomialKernel MvPolynomial
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

abbrev Index (h k : History l) (r : Representative h k) :=
  (Fiber h k r × Bool) ⊕ (Fiber h k r × Fiber h k r)

def polynomial (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) : Index h k r → MvPolynomial (PairKey h k) ℤ
  | .inl (i,false) => leftFlag h k hs ks i.val
  | .inl (i,true) => rightFlag h k hs ks i.val
  | .inr (i,j) => minorFlag h k hs ks i.val j.val

theorem index_card (h k : History l) (r : Representative h k) :
    Fintype.card (Index h k r)=2*Fintype.card (Fiber h k r)+(Fintype.card (Fiber h k r))^2 := by
  simp only [Index,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,pow_two]
  omega

theorem fiber_level (h k : History l) (r : Representative h k) (i : Fiber h k r) :
    level h k i.val=r.val.1 :=
  congrArg (fun a : Representative h k => a.val.1) i.property

theorem polynomial_scope (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (j : Index h k r) :
    EarlierSmall h k r.val.1 (polynomial h k hs ks r j) := by
  rcases j with ⟨i,b⟩ | ⟨i,j⟩
  · cases b
    · simpa only [polynomial,fiber_level h k r i] using (flags_earlierSmall h k hs ks i.val).1
    · simpa only [polynomial,fiber_level h k r i] using (flags_earlierSmall h k hs ks i.val).2
  · have he : level h k i.val=level h k j.val := (fiber_level h k r i).trans (fiber_level h k r j).symm
    simpa only [polynomial,fiber_level h k r i] using minor_earlierSmall h k hs ks i.val j.val he

theorem polynomial_degree (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (j : Index h k r) :
    (polynomial h k hs ks r j).totalDegree ≤ 4*degreeBudget h k := by
  rcases j with ⟨i,b⟩ | ⟨i,j⟩
  · have hh := flag_degrees h k hs ks i.val
    cases b
    · exact hh.1.trans (by omega)
    · exact hh.2.trans (by omega)
  · exact minorFlag_degree h k hs ks i.val j.val

def envelope (h k : History l) (V : ℕ → ℕ) (B : ℝ) : ℝ :=
  (HistoryPairFlagBounds.height h k V B)^2+2*(HistoryPairFlagBounds.height h k V B)^4

theorem polynomial_eval_bound (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (j : Index h k r) (x : PairKey h k → ℝ) {B : ℝ} (hB : 1≤B)
    (hx : ∀ a : Fin h.root.small.length ⊕ InternalKey h, |x (leftMap h k (.inr a))|≤B)
    (hy : ∀ a : Fin k.root.small.length ⊕ InternalKey k, |x (rightMap h k (.inr a))|≤B) :
    |eval₂ (Int.castRingHom ℝ) x (polynomial h k hs ks r j)| ≤ envelope h k V B := by
  rcases j with ⟨i,b⟩ | ⟨i,j⟩
  · have hh := HistoryPairFlagBounds.flags_eval_bound h k hs ks i.val x hB hx hy
    have hnonneg : 0≤2*(HistoryPairFlagBounds.height h k V B)^4 := by positivity
    cases b
    · exact hh.1.trans (le_add_of_nonneg_right hnonneg)
    · exact hh.2.trans (le_add_of_nonneg_right hnonneg)
  · exact (HistoryPairFlagBounds.minor_eval_bound h k hs ks i.val j.val x hB hx hy).trans
      (le_add_of_nonneg_left (sq_nonneg _))

theorem polynomial_integer_log_bound (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (j : Index h k r) (x : PairKey h k → ℤ) {B : ℝ} (hB : 1≤B)
    (hx : ∀ a : Fin h.root.small.length ⊕ InternalKey h, |(x (leftMap h k (.inr a)):ℝ)|≤B)
    (hy : ∀ a : Fin k.root.small.length ⊕ InternalKey k, |(x (rightMap h k (.inr a)):ℝ)|≤B)
    (hn : eval x (polynomial h k hs ks r j)≠0) :
    Real.log |(eval x (polynomial h k hs ks r j):ℝ)| ≤ Real.log (envelope h k V B) := by
  have hh := polynomial_eval_bound h k hs ks r j (fun a => (x a:ℝ)) hB hx hy
  rw [Expr.eval₂_cast_int] at hh
  have hn' : (eval x (polynomial h k hs ks r j):ℝ)≠0 := by exact_mod_cast hn
  exact Real.log_le_log (abs_pos.mpr hn') hh

theorem noAccidentalFlags_iff (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (x : PairKey h k → ZMod (prime h k r)) :
    NoAccidentalFlags h k hs ks r x ↔ ∀ j : Index h k r,
      eval₂ (Int.castRingHom _) x (polynomial h k hs ks r j)=0 ↔ polynomial h k hs ks r j=0 := by
  constructor
  · rintro ⟨hleft,hright,hminor⟩ j
    rcases j with ⟨i,b⟩ | ⟨i,j⟩
    · cases b
      · exact hleft i
      · exact hright i
    · exact hminor i j
  · intro hf
    exact ⟨fun i => hf (.inl (i,false)),fun i => hf (.inl (i,true)),fun i j => hf (.inr (i,j))⟩

end Ostmann.Arithmetic.HistoryPairFlags

end

end OAI
