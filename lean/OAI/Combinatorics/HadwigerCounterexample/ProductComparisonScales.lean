import OAI.Combinatorics.HadwigerCounterexample.RecursiveComparisonErrors

namespace OAI

/-! # Product Comparison Scales -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Function Finset Filter
open scoped BigOperators
variable {p : Shape} {n N M : ℕ} {I : Type} [Fintype I] [DecidableEq I]
namespace Template
variable (v : Template p I)

def play (v : Template p I) (M : ℕ) (C b ε : ℝ) :=
  ∃ (r : ℕ) (c : ℝ),0<c ∧ ∀ᶠ n : ℕ in atTop, let N:=M*n; ∀ (q : I→F)
    (U : Wgt (Keys (p:=p) v.t N)), (∀ i, |U i|≤ b) →
    ∃ T,design v T b r∧ shadowed v q (U-T) ε ∧ engaged v q (U-T) n C (bp (-c*n)) ε

theorem play_empty (v : Template p I) (M : ℕ) (C b ε : ℝ) [IsEmpty I]
    (hε : 0≤ε) :
    play v M C b ε := by
  classical
  refine ⟨1,1,zero_lt_one,.of_forall (fun n => ?_)⟩
  intro N q U hU
  let i : Keys (p:=p) v.t N := 0
  refine ⟨U, ⟨fun _ => ⟨U i,fun _ _=> True⟩,?_,fun _=>hU _⟩,fun f h=>?_,
    fun m hN w hw s x h hh =>?_⟩
  · funext x
    simp only [mural,Paint.cost,prodW,ind_true,prod_const_one,mul_one,sum_const,
      card_univ,Fintype.card_fin,one_smul]
    exact congrArg U (Subsingleton.elim x i)
  · simp only [board,sub_self,curtain,Pi.zero_apply,mul_zero,zero_mul,avg_zero,abs_zero]
    exact hε
  · have ht o : ¬ exceeds v q (U-U) s m x ε o := by
      rintro ⟨f,_,hh⟩
      simp only [scene,protean,curtain,sub_self,Pi.zero_apply,mul_zero,zero_mul,avg_zero,
        abs_zero] at hh
      exact (not_lt_of_ge hε) hh
    rw [show exceeds _ _ _ _ _ _ _=(fun _=>False) from funext fun i=>propext ⟨ht i,False.elim⟩,
      pr_false]; exact (bp_pos _).le

set_option maxHeartbeats 1200000 in
theorem play_step (v : Template p I) (j : I) (M : ℕ) (hM : 1≤ M) (C b ε : ℝ)
    (hb : 0≤b) (hε : 0<ε)
    (h : play (v.beyond j) M C b (ε/2)) :
    play v M C b ε := by
  classical
  let u:= ε/2; let L:=1+2*b; have hu : 0<u := by positivity
  have hL : 0<L := by positivity
  obtain ⟨δ,hδ,hh⟩ := shade_calendar v j M hM C (u/L) (by positivity)
  let d := min δ (u/L)
  have hd : 0<d := lt_min hδ (by positivity)
  obtain ⟨s,hs⟩ := shattered v j b L d hL hb (by unfold L; linarith) hd
  obtain ⟨r,c,hc,h⟩ := h
  let t := min (1/16:ℝ) c
  have ht : 0<t := lt_min (by norm_num) hc
  refine ⟨s*r,t/2,by linarith,?_⟩
  filter_upwards [hh,h,pay_nat (a:=t) (b:=t/2) ((s:ℝ)+1) (by linarith)]
    with n hn h ha N q U hU
  obtain ⟨l,hl,a,B,hb',hs,hQ,hW⟩ := hs N q U hU
  let V:= patched v j a B
  let W := U-V
  let R i := curtain v q W i/L
  let T:=v.beyond j
  let Q:= v.boundTail j q
  choose g h1 h2 h3 using fun i=> h Q (B i) (hb' i)
  let D := patched v j a g
  have hT : shadowed v q W u := by
    have he := chair_board v j q W L d hL hQ
    have hm : d*L ≤ u := (le_div_iff₀ hL).mp (min_le_right ..)
    exact fun i hi => (he i hi).trans hm
  have hx : engaged v q W n C (bp (-(1/16:ℝ)*n)) u := by
    intro m hN w hw s x hx hz
    have he : chairCut v j R δ :=
      fun i hi k hk=> (hQ i hi k hk).trans (min_le_left ..)
    have hg (x) : |propel v s m x|≤1 := by
      unfold propel; rw [abs_of_nonneg (ind_nonneg _)]
      exact ind_le_one _
    obtain ⟨hw,hv,h',hm'⟩ := hw
    have h4 := hn q R (propel v s m) x hs he hW hg hx hz m hN w hw hv h' hm'
    refine (pr_mono hw.nz (fun i hh => ?_)).trans h4
    obtain ⟨f,hf,hg⟩ := hh
    refine ⟨f,hf,?_⟩
    unfold R
    rw [put_back v q W L,abs_div,abs_of_pos hL]
    exact div_lt_div_of_pos_right hg hL
  have hg := gild_play v j q n N l a B g U C u _ _ hT hx h2 h3
  have heq : u+u=ε := by unfold u; ring
  dsimp only at hg
  rw [heq] at hg
  refine ⟨D,design_mono v D b _ (s*r) hb (Nat.mul_le_mul_right r hl)
    (design_patch v j l r a g b h1),hg.1,?_⟩
  intro m hN w hw s' x hx hz
  apply (hg.2 m hN w hw s' x hx hz).trans
  apply le_trans ?_ ha
  let z := bp (-t*n)
  have h1 : bp (-c*n)≤ z := bp_le (by gcongr; exact min_le_right ..)
  have h2 : bp (-(1/16:ℝ)*n)≤ z := bp_le (by gcongr; exact min_le_left ..)
  exact (add_le_add h2 (mul_le_mul (by exact_mod_cast hl) h1 (bp_pos _).le
    (Nat.cast_nonneg s))).trans_eq (by ring)

theorem plays_calendar (p : Shape) (M : ℕ) (hM : 1≤M) (C b : ℝ) (hb : 0 ≤ b)
    (r : ℕ) :
    ∀ (I : Type) [Fintype I] [DecidableEq I],Fintype.card I≤r →
      ∀ v : Template p I,∀ ε : ℝ,0< ε→play v M C b ε := by
  classical
  induction r with
  | zero =>
    intro I inst h hi v ε he
    have : IsEmpty I := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hi)
    exact play_empty v M C b ε he.le
  | succ r ih =>
    intro I _ _ h v ε he
    cases isEmpty_or_nonempty I
    next => exact play_empty v M C b ε he.le
    next hi =>
      obtain ⟨i⟩:=hi
      apply play_step v i M hM C b ε hb he
      refine ih _ ?_ _ _ (half_pos he)
      have hh : Fintype.card (Aside i)+1=Fintype.card I := by
        have hg := Fintype.card_congr (Equiv.optionSubtypeNe i)
        simpa only [Aside,Fintype.card_option] using hg
      omega
end Template
end HadwigerCounterexample

end

end OAI
