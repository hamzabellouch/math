import OAI.Computability.StarHeight.StreamRecovery

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uAlphabet uAlphabet2 uAlphabet3 uJ uC uAlphabet4 uT uP
universe uC2 uAlphabet5 uJ2 uC3

namespace SourceSchedule

structure Late (Alphabet : Type uAlphabet) (B : ℕ) (h w E earlyLast : ℤ) where
  endRule : CanonicalEpisodes.Parameters Alphabet
  lag : ℤ
  modulus : endRule.B=B
  spacing : 4*(h+w+1) < endRule.S
  separation : 10*(B:ℤ)*endRule.S+10*(h+w+1) < endRule.d
  lag_pos : 0 < lag
  lag_margin : earlyLast < lag-E
  offset_margin : E < endRule.offset-(2*w+endRule.width+endRule.rule.r+endRule.K+1)
  tail_margin : (endRule.d:ℤ)+(endRule.B-1)*endRule.S+
    (2*w+endRule.width+endRule.rule.r+endRule.K+1) < endRule.tail

lemma exists_late {Alphabet : Type uAlphabet2} [Fintype Alphabet] (B : ℕ) (hB : 0 < B)
    (h w E earlyLast : ℤ) (hh : 0 ≤ h) (hw : 0 ≤ w) (hE : 0 ≤ E) :
    Nonempty (Late Alphabet B h w E earlyLast) := by
  let S : ℤ := 4*(h+w+1)+1
  have hS : 0 ≤ S := by dsimp [S];omega
  let D : ℤ := 10*(B:ℤ)*S+10*(h+w+1)
  have hD : 0 ≤ D := by dsimp [D];positivity
  let d : ℕ := D.toNat+2
  have hd : (d:ℤ)=D+2 := by simp only [d,Nat.cast_add,Int.toNat_of_nonneg hD,Nat.cast_ofNat]
  have hd₂ : 2 ≤ d := by dsimp [d];omega
  let K : ℕ := 3*d^2+1
  obtain ⟨rule⟩ := LocalMarkers.nonempty_rule (Alphabet := Alphabet) (d := d) (K := K) hd₂
    (show 3*d^2<K by dsimp [K];omega)
  let width : ℤ := 3*d+((B:ℤ)-1)*S
  have hwidth : 0 ≤ width := by
    have hBb : (0:ℤ) ≤ (B:ℤ)-1 := by
      have : (1:ℤ) ≤ B := by exact_mod_cast hB
      omega
    dsimp [width];positivity
  let endE : ℤ := 2*w+width+rule.r+K+1
  have hr := rule.radius_ge
  have hendE : 0 ≤ endE := by dsimp [endE];omega
  let tail : ℤ := d+((B:ℤ)-1)*S+endE+2
  have htail : 0 < tail := by
    have hBb : (0:ℤ) ≤ (B:ℤ)-1 := by
      have : (1:ℤ) ≤ B := by exact_mod_cast hB
      omega
    dsimp [tail];positivity
  let er : CanonicalEpisodes.Parameters Alphabet :=
    ⟨B,S,d,K,E+endE+1,tail,rule,by exact_mod_cast hB,hS,hd₂,
      by dsimp [K];omega,htail⟩
  refine ⟨⟨er,|earlyLast|+E+1,rfl,?_,?_,?_,?_,?_,?_⟩⟩
  · dsimp [er,S];omega
  · change D < (d:ℤ);omega
  · positivity
  · have := le_abs_self earlyLast;omega
  · change E < E+endE+1-endE;omega
  · change (d:ℤ)+((B:ℤ)-1)*S+endE < tail
    dsimp [tail];omega

namespace Late

variable {Alphabet : Type uAlphabet3} {B : ℕ} {h w E earlyLast : ℤ}
    (L : Late Alphabet B h w E earlyLast)

lemma radius_nonneg : 0 ≤ L.endRule.rule.r :=
  (show (0:ℤ) ≤ L.endRule.K by positivity).trans L.endRule.rule.radius_ge

lemma overlap (hh : 0 ≤ h) (hw : 0 ≤ w) :
    (L.endRule.d:ℤ)^2+w ≤ L.endRule.K := by
  have hd := L.separation
  have hS := L.endRule.S_nonneg
  have hprod : 0 ≤ 10*(B:ℤ)*L.endRule.S := by positivity
  have hseed : 3*(L.endRule.d:ℤ)^2 < L.endRule.K := by exact_mod_cast L.endRule.seed_long
  have hd₂ : (2:ℤ) ≤ L.endRule.d := by exact_mod_cast L.endRule.d_ge
  nlinarith

lemma complete_lower {f : ℤ → Alphabet} {s b : ℤ}
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (s+L.lag+L.endRule.offset) (L.endRule.small f (s+L.lag+L.endRule.offset)) b) :
    s+L.lag+L.endRule.offset+(2*w+L.endRule.width+L.endRule.rule.r+L.endRule.K+1) < b := by
  have hb := L.endRule.end_lower he
  have ht := L.tail_margin
  omega

lemma visible {J : Type uJ} {C : Type uC} (A : ExceptionalOrigins.Parameters Alphabet J C)
    (heq : A.endRule=L.endRule) (hw : A.w=w) (hwpos : 0 ≤ w) (hE : 0 ≤ E)
    (hinleft : ∀ j, -E ≤ A.offset j-w-A.w₀-A.innerRule.r)
    (hinright : ∀ j u, A.offset j+w+A.H u+max A.ext A.w₀+A.innerRule.r ≤ E)
    {f : ℤ → Alphabet} {s b δ Q : ℤ} (hδ : |δ| ≤ w)
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (s+L.lag+L.endRule.offset) (L.endRule.small f (s+L.lag+L.endRule.offset)) b) :
    A.Visible (s+earlyLast) b (s+L.lag+δ) Q := by
  have hlo := L.lag_margin
  have hoff := L.offset_margin
  have hb := L.complete_lower he
  have hδ' := abs_le.mp hδ
  have hr := L.radius_nonneg
  have hwidth := L.endRule.width_nonneg
  have hK : (0:ℤ) ≤ L.endRule.K := by positivity
  have hlower : s+earlyLast < s+L.lag-E := by omega
  refine ⟨?_,?_,?_⟩
  · rw [heq]
    refine ⟨?_,?_,?_,?_⟩ <;> omega
  · intro v _ hav
    rw [hw] at hav
    have hv := abs_le.mp hav
    rw [heq]
    constructor <;> omega
  · intro j
    have hj := hinleft j
    have hj' := hinright j (A.residue (Q-(s+L.lag+δ)))
    have hEend : 0 ≤ 2*w+L.endRule.width+L.endRule.rule.r+L.endRule.K+1 := by omega
    constructor <;> omega

end Late

end SourceSchedule

namespace SourceSchedule

noncomputable def finiteBound (F : Finset ℤ) : ℕ := F.sup Int.natAbs

lemma abs_le_finiteBound {F : Finset ℤ} {x : ℤ} (hx : x ∈ F) :
    |x| ≤ (finiteBound F:ℤ) := by
  have hh : x.natAbs ≤ finiteBound F := Finset.le_sup (f := Int.natAbs) hx
  simpa only [Int.natCast_natAbs] using (show (x.natAbs:ℤ) ≤ finiteBound F by exact_mod_cast hh)

namespace Early

open scoped BigOperators

variable {Alphabet : Type uAlphabet4} {T : Type uT} {P : Type uP} {C : Type uC2} [Fintype T] [Fintype P] [Fintype C]
    {g' B size : ℕ} {clock : RobustClock.Specification T P C}
    {label : P → Fin g'} {reserved : P → ℤ}
    (S : Early (Alphabet := Alphabet) clock B size label reserved)

noncomputable def period : ℕ := ∏ c, S.denominator c

lemma period_pos : 0 < S.period := Finset.prod_pos (fun c _ => (S.prime c).pos)

noncomputable def cuts (g : ℕ) : OuterStream.Cuts g B where
  main j := S.inner.mainBase j.val
  periodic j u := S.inner.periodicOffset j.val u 0
  R := S.R
  N := S.period * innerD S.p (B*S.R) * size.factorial
  R_pos := S.R_pos
  N_pos := Nat.mul_pos (Nat.mul_pos S.period_pos (by have := innerD_ge S.p (B*S.R);omega))
    (Nat.factorial_pos _)

noncomputable def diameter : ℤ := 2*(absoluteBound S.p:ℤ)+1

lemma diameter_pos : 0 < S.diameter := by dsimp [diameter];positivity

noncomputable def sweepWidth (g : ℕ) : ℤ :=
  2*S.diameter+2*(finiteBound (S.cuts g).offsets:ℤ)+1

lemma sweepWidth_large (g : ℕ) : 2*S.diameter < S.sweepWidth g := by
  dsimp [sweepWidth];omega

lemma sweepWidth_pos (g : ℕ) : 0 < S.sweepWidth g := by
  have := S.diameter_pos;have := S.sweepWidth_large g;omega

lemma offsets_difference (g : ℕ) {a b : ℤ} (ha : a ∈ (S.cuts g).offsets)
    (hb : b ∈ (S.cuts g).offsets) : |a-b| < S.sweepWidth g := by
  have ha' := abs_le_finiteBound ha
  have hb' := abs_le_finiteBound hb
  have hh := abs_sub a b
  have hd := S.diameter_pos
  dsimp [sweepWidth]
  omega

lemma stencil_difference (g : ℕ) (i j : P) : |S.p i-S.p j| < S.sweepWidth g := by
  have hh := difference_bound S.p i j
  have hw := S.sweepWidth_large g
  have hd := S.diameter_pos
  change |S.p i-S.p j| ≤ S.diameter at hh
  omega

noncomputable def envelope (g : ℕ) : ℤ :=
  S.sweepWidth g+2*|((B*S.R:ℕ):ℤ)|+|S.rule.r|+
    (absoluteBound (fun j : Fin (g+1) => S.inner.boundary j.val):ℤ)+
    (absoluteBound S.inner.H:ℤ)+|S.inner.extension|+
    (3*(innerD S.p (B*S.R))^2+1:ℕ)+
    (size*innerD S.p (B*S.R):ℕ)+(finiteBound (S.cuts g).offsets:ℤ)+1

lemma envelope_pos (g : ℕ) : 0 < S.envelope g := by
  have := S.sweepWidth_pos g
  dsimp [envelope];positivity

lemma inner_left (g : ℕ) (j : Fin (g+1)) :
    -S.envelope g ≤ S.inner.boundary j.val-S.sweepWidth g-(B*S.R:ℕ)-S.rule.r := by
  have hj := abs_le_absoluteBound (fun j : Fin (g+1) => S.inner.boundary j.val) j
  have hab := neg_abs_le (S.inner.boundary j.val)
  have hr := le_abs_self S.rule.r
  have hw := le_abs_self ((B*S.R:ℕ):ℤ)
  have hH : (0:ℤ) ≤ absoluteBound S.inner.H := by positivity
  have := abs_nonneg S.inner.extension
  have := abs_nonneg ((B*S.R:ℕ):ℤ)
  have := sq_nonneg (innerD S.p (B*S.R):ℤ)
  have : (0:ℤ) ≤ (size:ℤ)*(innerD S.p (B*S.R):ℤ) :=
    mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  simp only [envelope,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,Nat.cast_ofNat]
  simp only [Nat.cast_mul] at *
  omega

lemma inner_right (g : ℕ) (j : Fin (g+1)) (u : Fin B) :
    S.inner.boundary j.val+S.sweepWidth g+S.inner.H u+
      max S.inner.extension (B*S.R:ℕ)+S.rule.r ≤ S.envelope g := by
  have hj := (le_abs_self (S.inner.boundary j.val)).trans
    (abs_le_absoluteBound (fun j : Fin (g+1) => S.inner.boundary j.val) j)
  have hH := (le_abs_self (S.inner.H u)).trans (abs_le_absoluteBound S.inner.H u)
  have hr := le_abs_self S.rule.r
  have he := le_abs_self S.inner.extension
  have hw := le_abs_self ((B*S.R:ℕ):ℤ)
  have hwpos := abs_nonneg ((B*S.R:ℕ):ℤ)
  have hepos := abs_nonneg S.inner.extension
  have hm : max S.inner.extension (B*S.R:ℕ) ≤ |S.inner.extension|+|((B*S.R:ℕ):ℤ)| := by
    apply max_le <;> omega
  have := sq_nonneg (innerD S.p (B*S.R):ℤ)
  have : (0:ℤ) ≤ (size:ℤ)*(innerD S.p (B*S.R):ℤ) :=
    mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  simp only [envelope,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,Nat.cast_ofNat]
  simp only [Nat.cast_mul] at *
  omega

lemma exists_full_late [Fintype Alphabet] (hB : 0 < B) (g : ℕ) :
    Nonempty (Late Alphabet B S.diameter (S.sweepWidth g) (S.envelope g) (S.β (Fin.last g'))) :=
  exists_late B hB _ _ _ _ S.diameter_pos.le (S.sweepWidth_pos g).le (S.envelope_pos g).le

variable (g : ℕ) (L : Late Alphabet B S.diameter (S.sweepWidth g) (S.envelope g) (S.β (Fin.last g')))

noncomputable def parameters (hB : 0 < B) : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C where
  endRule := L.endRule
  d := innerD S.p (B*S.R)
  K := 3*(innerD S.p (B*S.R))^2+1
  B := B
  B_pos := hB
  end_modulus := L.modulus
  innerRule := S.rule
  offset j := S.inner.boundary j.val
  H := S.inner.H
  w := S.sweepWidth g
  w₀ := (B*S.R:ℕ)
  ext := S.inner.extension
  φ := PeriodicClock.speedMap (fun c => (S.numerator c:ℝ)/S.denominator c)
  W := clock.W

lemma geometry (hB : 0 < B) : OuterStream.Geometry (S.parameters g L hB) (S.cuts g) := by
  have hw := (S.sweepWidth_pos g).le
  have hr := L.radius_nonneg
  have hwidth := L.endRule.width_nonneg
  have hK : (0:ℤ) ≤ L.endRule.K := by positivity
  have he := (S.envelope_pos g).le
  have hbound : ∀ a ∈ (S.cuts g).offsets, |a| ≤ S.envelope g := by
    intro a ha
    have hh := abs_le_finiteBound ha
    have hw' := S.sweepWidth_pos g
    dsimp [envelope]
    have hrest : 0 ≤ 2*|((B*S.R:ℕ):ℤ)|+|S.rule.r|+
        (absoluteBound (fun j : Fin (g+1) => S.inner.boundary j.val):ℤ)+
        (absoluteBound S.inner.H:ℤ)+|S.inner.extension|+
        (3*(innerD S.p (B*S.R))^2+1:ℕ)+(size*innerD S.p (B*S.R):ℕ) := by positivity
    push_cast at *
    omega
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro role
    cases role with
    | inl j => simpa only [parameters,cuts,OuterStream.Cuts.base,IntegerSchedules.Inner.mainOffset,Nat.cast_zero,zero_mul,add_zero]
        using S.inner.main_multiple j.val 0
    | inr ju => exact S.inner.periodic_multiple ju.1.val ju.2 0
  · intro u i j hij
    have hh := (S.inner.halfGap_large hB (by have := S.rule.radius_ge;omega)).1
    have hH := S.inner.H_bounded u
    have hgap := S.inner.gap_pos
    have hrule : 0 ≤ S.rule.r := (show (0:ℤ) ≤ 3*(innerD S.p (B*S.R))^2+1 by positivity).trans S.rule.radius_ge
    have hij' : (i.val:ℤ)+1 ≤ j.val := by exact_mod_cast (show i.val+1 ≤ j.val from hij)
    have hm := mul_le_mul_of_nonneg_right hij' (show 0 ≤ 2*S.inner.halfGap by positivity)
    change S.inner.boundary i.val+S.inner.H u ≤ S.inner.boundary j.val
    dsimp [IntegerSchedules.Inner.boundary]
    nlinarith
  · intro a ha
    have hh := (le_abs_self a).trans (hbound a ha)
    have hoff := L.offset_margin
    change a+L.endRule.width+L.endRule.rule.r ≤ L.endRule.offset
    omega
  · intro a ha b hb
    have hh := (le_abs_self (a-b)).trans (S.offsets_difference g ha hb).le
    have ht := L.tail_margin
    change a-b+L.endRule.width+L.endRule.rule.r+
      ((L.endRule.d:ℤ)+(L.endRule.B-1)*L.endRule.S) ≤ L.endRule.tail
    omega
  · intro a ha b hb
    have hh := (le_abs_self (a-b)).trans (S.offsets_difference g ha hb).le
    have ht := L.tail_margin
    change a-b+L.endRule.K+((L.endRule.d:ℤ)+(L.endRule.B-1)*L.endRule.S) ≤ L.endRule.tail
    omega
  · intro a ha b hb
    exact (add_le_add_right (S.offsets_difference g ha hb).le _).trans
      (L.overlap S.diameter_pos.le hw)

lemma actual_visible (hB : 0 < B) {f : ℤ → Alphabet} {s b δ Q : ℤ}
    (hδ : |δ| ≤ S.sweepWidth g)
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (s+L.lag+L.endRule.offset) (L.endRule.small f (s+L.lag+L.endRule.offset)) b) :
    (S.parameters g L hB).Visible (s+S.β (Fin.last g')) b (s+L.lag+δ) Q :=
  L.visible (S.parameters g L hB) rfl rfl (S.sweepWidth_pos g).le (S.envelope_pos g).le
    (S.inner_left g) (S.inner_right g) hδ he

end Early

end SourceSchedule

namespace ExceptionalOrigins.Parameters

variable {Alphabet : Type uAlphabet5} {J : Type uJ2} {C : Type uC3} (A : ExceptionalOrigins.Parameters Alphabet J C)

lemma not_failed_clock {f : ℤ → Alphabet} {t Q : ℤ} (hn : ¬A.Failed f t Q) :
    A.φ (Q-t) ∉ A.W := fun h => hn (Or.inr (Or.inl h))

lemma not_failed_inner {f : ℤ → Alphabet} {t Q δ : ℤ} (hn : ¬A.Failed f t Q)
    (hδ : |δ| ≤ A.w₀) (j : J) :
    A.inner f j (A.residue (Q-t)) (t+δ) = A.inner f j (A.residue (Q-t)) t := by
  by_contra he
  apply hn
  right;right
  refine ⟨j,Or.inl ⟨δ,hδ,?_⟩⟩
  simpa only [inner,add_right_comm t δ,add_right_comm (t+A.offset j) δ] using Ne.symm he

lemma not_failed_absent {f : ℤ → Alphabet} {t Q : ℤ} (hn : ¬A.Failed f t Q)
    (j : J) (hj : A.inner f j (A.residue (Q-t)) t = none) :
    ∀ x, t+A.offset j ≤ x → x ≤ t+A.offset j+A.H (A.residue (Q-t))+A.ext →
      x ∉ A.innerRule.markers f := by
  intro x hx hx' hm
  exact hn (Or.inr (Or.inr ⟨j,Or.inr ⟨hj,x,hm,hx,hx'⟩⟩))

lemma not_failed_end {f : ℤ → Alphabet} {t Q δ : ℤ} (hn : ¬A.Failed f t Q)
    (hδ : |δ| ≤ A.w) (hm : (A.B:ℤ) ∣ δ) :
    A.endRule.small f (t+δ+A.endRule.offset) = A.endRule.small f (t+A.endRule.offset) ∧
    A.endRule.large f (t+δ+A.endRule.offset) = A.endRule.large f (t+A.endRule.offset) := by
  constructor
  · by_contra he
    apply hn
    left;left
    refine ⟨δ,hm,hδ,?_⟩
    simpa only [CanonicalEpisodes.Parameters.small,←A.end_modulus,add_right_comm t δ]
      using Ne.symm he
  · by_contra he
    apply hn
    left;right
    refine ⟨δ,hm,hδ,?_⟩
    simpa only [CanonicalEpisodes.Parameters.large,←A.end_modulus,add_right_comm t δ]
      using Ne.symm he

end ExceptionalOrigins.Parameters

end GeneralizedStarHeight

end OAI
