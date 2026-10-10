import OAI.Analysis.FourierLLogL.Procedure.Play

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure
open Law Node Real Period Compress.Params Thermal Fund Scene

variable {M J j : ℕ} {s : Scene M}
open scoped Classical

lemma top_avg {E : Type*} [AddCommMonoid E] [MulAction ℝ E] (f : Grid M → E) :
    root.avg f = expU f := by
  rw [avg_sum, group_top,len_top,inv_one,one_smul]
  rfl

lemma lose_eq (u : Update j M s.here) (x : Grid M) :
    (lose s u).wage x = if u.take s.fund.mood x then 0 else s.wage x := by
  by_cases H : u.take s.fund.mood x <;> simp [lose,Set.indicator,H]
lemma win_eq (u : Update j M s.here) (x : Grid M) :
    (win s u).wage x = if u.take s.fund.mood x then s.wage x else 0 := by
  by_cases H : u.take s.fund.mood x <;> simp [win,Set.indicator,H]

lemma split_pos (u : Update j M s.here) (h : 0 ≤ s.wage) :
    (0 ≤ (lose s u).wage ∧ (lose s u).wage ≤ s.wage) ∧
      (0 ≤ (win s u).wage ∧ (win s u).wage ≤ s.wage) := by
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  all_goals
    intro i
    dsimp only [Pi.zero_apply]
    first | rw [lose_eq] | rw [win_eq]
    split_ifs <;> first | exact h i | exact le_rfl

private def bonus (s : Scene M) : ℕ :=
    (if s.live then 2 else 0)+(if s.enter then 1 else 0)
private def playing (s : Scene M) :=
    Finset.univ.filter fun x => 0 < s.wage x

private def totalUse (j : ℕ) := Nat.ceil (capA*H j)
private def stage (j : ℕ) (s : Scene M) : ℕ :=
    ((totalUse j-s.fund.uses) * (Fintype.card (Grid M)+1)+(playing s).card)*4+bonus s

private lemma begin_ok :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, ∀ (f : Grid M → ℝ) (b : Bool), 0 ≤ f → expU f ≤ 2 →
      (beginPlay f b).Safe j J f := by
  filter_upwards [Fund.fund_est] with j hj
  intro M J f b hp h
  refine ⟨root_ok _,Nat.zero_le _,(hj M).1,le_rfl,hp,le_rfl,?_⟩
  change root.avg f ≤ _
  rw [top_avg]
  unfold cutoff; have hi := Nat.cast_nonneg (α:=ℝ) j
  have h1 : 1 ≤ ((j:ℝ)+1)^3 := one_le_pow₀ (by linarith)
  linarith

theorem plant :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, J ≤ M → ∀ f : Grid M → ℝ,
    0 ≤ f → expU f ≤ 2 → (∀ x, f x ≤ exp (height j)) →
    ∀ b : Bool, ∃ t : Play j M (beginPlay f b), t.Follows J f := by
  classical
  filter_upwards [begin_ok, Fund.fund_est, make_update capA cap_ok] with j hb hK hM
  intro M J hJ f h0 ht he b
  let OK (s : Scene M) := ∃ t : Play j M s, t.Follows J f
  suffices HH : ∀ k : ℕ, ∀ s : Scene M, s.here.lev+k=J →
      s.Safe j J f → OK s by
    exact HH J _ (by simp [beginPlay,root]) (hb M J f b h0 ht)
  intro k; induction k using Nat.strong_induction_on with
  | h k ih =>
  intro s hi hy
  suffices IH : ∀ n : ℕ, ∀ s : Scene M, s.here.lev+k=J →
      s.Safe j J f → stage j s=n → OK s from IH _ s hi hy rfl
  intro n; induction n using Nat.strong_induction_on with
  | h n Now =>
  intro s hi hy hn
  subst n
  by_cases ho : openHere s j J f
  case neg => exact ⟨Play.rest s, hy, ho⟩
  have hh1 := hy.positive
  have hm : 0 < s.mass := ho.2.2
  have hL : s.here.lev < J := ho.1
  have hR : s.here.lev < M := hL.trans_le hJ
  have hp : s.here.valid := hy.within.1
  by_cases h : retire s j
  · have hq : s.out.Safe j J f := by
      obtain ⟨a,b,c,d,e,f,g⟩ := hy
      exact ⟨a,b,c,le_rfl,e,f,g⟩
    obtain ⟨t,h1⟩ := Now _ (show stage j s.out < _ by
      have heq : playing s.out = playing s := rfl
      have hmass : 0 < s.here.avg s.wage := hm
      have hbonusOut : bonus s.out = 1 := by simp [bonus,out,enter,mass,hmass]
      have hbonusS : 2 ≤ bonus s := by simp [bonus,h.1]
      have hfund : s.out.fund.uses = s.fund.uses := rfl
      rw [stage,stage,heq,hfund]
      rw [hbonusOut]
      omega)
      s.out hi hq rfl
    exact ⟨Play.freeze s t, hy,ho,h,h1⟩
  by_cases ha : enter s
  · have ha' : ¬ enter s.reset := by unfold enter reset; change ¬ 2*s.mass<s.mass; linarith
    have hq : s.reset.Safe j J f := by
      obtain ⟨a,b,c,d,e,f,g⟩ := hy
      exact ⟨a,b,c,hm.le,e,f,g⟩
    obtain ⟨t,h1⟩ := Now _ (show stage j s.reset < _ by
      have heq : playing s.reset = playing s := rfl
      have hbonus : bonus s.reset + 1 = bonus s := by
        unfold bonus
        rw [ite_eq_right ha', ite_eq_left ha]
        rfl
      have hfund : s.reset.fund.uses = s.fund.uses := rfl
      rw [stage,stage,heq,hfund]
      omega) s.reset hi hq rfl
    exact ⟨Play.ticket s t, hy,ho,h,ha,h1⟩
  by_cases HH : settled s j
  · have hE (b : Bool) : OK (s.smaller b) := by
      have H : (s.smaller b).here.lev = s.here.lev+1 := by cases b <;> rfl
      apply ih (k-1) (by omega)
      · omega
      refine ⟨s.here.child_ok hp hR b,by rw [H]; exact hL,
        hy.capital.restrict (s.here.child_below _), hy.norm_ok, hh1,hy.sub,?_⟩
      have H1 := avg_nonneg s.here.L (f:=f) fun x _ => h0 x
      have H2 := avg_nonneg s.here.R (f:=f) fun x _ => h0 x
      have H3 := ho.2.1
      rw [avg_split_real s.here] at H3
      cases b
      · change s.here.L.avg f ≤ _; linarith
      · change s.here.R.avg f ≤ _; linarith
    obtain ⟨l,hl⟩ := hE false
    obtain ⟨r,hr⟩ := hE true
    exact ⟨Play.jump s l r,hy,⟨ho,h,ha⟩,HH,hl,hr⟩
  unfold settled at HH; push Not at HH
  obtain ⟨hl,i,HH',HE⟩ := HH
  have hb : ¬ breached j s.fund := fun he => h ⟨hl,Or.inl he⟩
  have hx : exp (-height j) ≤ s.mass := by
    apply le_of_not_gt; exact fun hi => h ⟨hl,Or.inr hi⟩
  have hW := ((hK M).2 s.fund s.here hy.capital).2 hb hy.within
  have hV := actor_def hy.within hy.positive hm
  unfold enter at ha
  obtain ⟨u,rfl,hu⟩ := hM _ _ _ hR hW.1 s.wage hh1
    (fun x => le_trans (hy.sub x) (he x)) hx _ _ hV
    (by linarith) (le_of_not_gt ha) i HH' HE
  have h₁ := split_pos u hh1
  have h₂ : ∀ s : Scene M, bonus s ≤ 3 := fun s => by unfold bonus; split_ifs <;> omega
  have hY₁ : Safe (s.lose u) j J f :=
    ⟨hy.within,hy.depth_ok,hy.capital,hy.norm_ok,h₁.1.1,h₁.1.2.trans hy.sub,hy.cut⟩
  have hY₂ : Safe (s.win u) j J f :=
    ⟨hy.within,hy.depth_ok,hW.2.2 u _ hu,le_rfl,h₁.2.1,h₁.2.2.trans hy.sub,hy.cut⟩
  have hww : stage j (s.win u) < stage j s := by
      let N := totalUse j
      have h4 : s.fund.uses+1 ≤ N := by
        have HH := (Nat.le_ceil (capA*H j))
        have He : ((s.fund.uses+1:ℕ):ℝ) ≤ ↑N := by push_cast; exact hW.2.1.trans HH
        exact_mod_cast He
      have h3 := h₂ (s.win u)
      let L := Fintype.card (Grid M)+1
      have h5 : (s.win u).fund.uses = s.fund.uses+1 := rfl
      have h6 : (playing (s.win u)).card < L := Nat.lt_succ_of_le (Finset.card_le_univ _)
      unfold stage; rw [h5,show totalUse j - s.fund.uses= N-(s.fund.uses+1)+1 by omega]; simp only [add_mul, one_mul]
      dsimp only [N,L] at *; omega
  have hll : stage j (s.lose u) < stage j s := by
    have h4 : (playing (s.lose u)).card < (playing s).card := by
      apply Finset.card_lt_card
      refine Finset.ssubset_iff_of_subset (s₁:=playing (s.lose u)) ?_ |>.mpr ?_
      · intro x hx
        simp only [playing,Finset.mem_filter,Finset.mem_univ,true_and] at *
        exact lt_of_lt_of_le hx (h₁.1.2 _)
      have HE := lt_of_lt_of_le (show 0 < beta u.ix /2 from by have := beta_pos u.ix; positivity) hu.bias
      obtain ⟨x,hx,hx'⟩ := (prob_pos_iff _ _).mp HE
      have hf : 0 < s.wage x := by
        by_contra! H
        have hh := H.antisymm (hh1 x)
        rw [hV _,wt,hh,mul_zero,zero_div] at hx'
        exact lt_irrefl _ hx'
      refine ⟨x,?_,?_⟩ <;> simp [playing,hf,lose_eq, hx]
    unfold stage
    rw [show (s.lose u).fund=s.fund from rfl]
    have hh := h₂ (s.lose u); omega
  obtain ⟨l,hl'⟩ := Now _ hll (s.lose u) hi hY₁ rfl
  obtain ⟨r,hr'⟩ := Now _ hww (s.win u) hi hY₂ rfl
  exact ⟨Play.attempt s u l r, hy, ⟨ho,h,ha⟩,hl,hu,hl',hr'⟩

end FourierLLogL.Dyadic.Procedure

end OAI
