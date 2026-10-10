import OAI.Combinatorics.HadwigerCounterexample.PhaseAlternativeSupport

namespace OAI

/-! # Finite Phase Alternative -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N r : ℕ}

def maxSpan (m b r : ℕ) := r*(2^m*(2*b))

structure PhaseReady (p : Shape) (n N m b r k d : ℕ) (mix : Mixer p n)
    (c l ψ ε L H : ℝ) : Prop where
  hb : 1≤b
  hm : 16*r<m
  hk : k≤d
  hc : 0<c
  hc' : c≤1
  hl : 0<l
  hl' : l≤1
  hψ : 0<ψ
  hε : 0<ε
  hL : 0≤ L
  hH : 0≤ H
  hN : 2*num (Full p n)-N≤ -1
  cap : initCap p N mix ε
  noBranch : ψ+noSweepBudget p N m b r c ψ H<0.005
  frames : scaleBill p n N (maxSpan m b r) L≤c/2
  atlas (T : Cov p N) (ht : ∀ i,cdSign p T i≤ maxSpan m b r) :
    num (Atlas p r T)≤bp (0.002*N)
  price : selPrice p r n N (rhUp L c) ε
  price' : selPrice p r n N (rhUp (rhUp L c) l) ε
  localQ : quest p r k n N (rhUp H c) ε
  testFailure : glimpsesBill p k (rhUp L c)+bp (-0.1*N)<l^(k+1)
  testFailure' : 2*glimpsesBill p d (rhUp L c)≤l/2
  beatSlack : 5*l+bp (-0.24*N)<0.005

def voidFrame (p : Shape) {N n} (x : UnitType p n N) (T : Cov p N) :=
  ∀ i z,Disjoint (T z) (imageP p x i z)

theorem framesCost {w : Wgt (UnitType p n N)} (hw : SubLaw w) (m : Mixer p n)
    {H : ℝ} (hl : 0≤ H) (hh : bySide p w m H) (hN : 2*num (Full p n)-N≤ -1)
    (T : Cov p N) (r : ℕ) (hT : ∀ i,cdSign p T i ≤r) :
    pr w (fun x => ¬voidFrame p x T) ≤ scaleBill p n N r H := by
  classical
  let P := fun i : Place p × Bool => fun x => ¬ Disjoint (imageP p (x : UnitType p n N) i.2 i.1)
      (T i.1)
  have h x : ¬voidFrame p (n:=n) x T → ∃ i,P i x := by
    intro h
    unfold voidFrame at h; push Not at h
    obtain ⟨i,z,h⟩ := h
    exact ⟨(z,i),fun he => h he.symm⟩
  let Y := H*2 * bp (num (Row p n)+r-N)
  have hr i : pr w (P i) ≤ Y := by
    rcases i with ⟨⟨z,b⟩,i⟩
    have hh' : dim (T (z,b)) ≤ r :=
      (Finset.single_le_sum (fun j _ => Nat.zero_le (dim (T (j,b)))) (Finset.mem_univ z)).trans
        (hT b)
    exact (any_frame_hit m hl hh i _ hN _).trans (mul_le_mul_of_nonneg_left (bp_le (by
      have hf : (dim (T (z,b)):ℝ) ≤ r := by exact_mod_cast hh'
      linarith only [hf])) (by positivity))
  refine ((pr_mono hw.nz h).trans (pr_exists_le hw.nz P)).trans ?_
  refine (Finset.sum_le_sum fun i _ => hr i).trans_eq ?_
  simp only [Y,scaleBill,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,num,Fintype.card_prod,
    Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat]

private theorem mark_bazaar (m : BMark p n N) {v : Wgt (UnitType p n N)}
    {T : Cov p N} (h : ∀ x,v x≠0 → covered p T (delta m x) ∧ voidFrame p x T ∧
       delta m x≠0 ∧ epoch p (mrAmbient m x true)≤r) :
    ∃ s : Bazaar p n r T,s.opened (delta m) v := by
  classical
  have he x : ∃ s : Atlas p r T,
      v x≠0 →
        standard s ∧ ∀ i,∃ A,compFor s A (imageP p x i) (delta m x) := by
    by_cases he : v x≠0
    · obtain ⟨hC,hV,hD,hR⟩ := h x he
      obtain ⟨X,hX,hY⟩ := delta_offset m x hC hD hV hR
      exact ⟨X,fun _ => ⟨hX,hY⟩⟩
    exact ⟨default,fun hs => (he hs).elim⟩
  choose f hf using he
  choose A hA using
    show ∀ (M : Atlas p r T) (i : Bool) (x), ∃ A,
        M=f x → v x≠0 → compFor M A (imageP p x i) (delta m x) from by
      intro M i x
      by_cases hs : v x=0
      · exact ⟨0,fun _ hh => (hh hs).elim⟩
      by_cases he : M=f x
      · subst M
        obtain ⟨A,hA⟩ := (hf x hs).2 i
        exact ⟨A,fun _ _ => hA⟩
      exact ⟨0,fun H => (he H).elim⟩
  exact ⟨⟨f,A⟩,fun x h => ⟨(hf x h).1,fun i => hA _ i x rfl h⟩⟩

set_option maxHeartbeats 800000 in
theorem phase_alternative {w : Wgt (UnitType p n N)}
    (mark : BMark p n N)
    {c l ψ ε L H : ℝ} {m b k d : ℕ}
    (mix : Mixer p n) (hr : PhaseReady p n N m b r k d mix c l ψ ε L H)
    (hw : IsLaw w)
    (hk : bySide p w mix L)
    (hv : ∀ x,w x≤H * pairW (raw mix N) (raw mix N) x)
    (hh : ∀ x,w x≠0 → delta mark x≠0 ∧ epoch p (mrAmbient mark x true) ≤ r)
    (hK : ∀ x,epoch p (delta mark x) ≤r) :
    ∃ P : UnitType p n N→Prop,(c/2)*(l/2)≤pr w P ∧
      (tonalMix p (delta mark) (onW w P) ∨ tonalTiny p (delta mark) (onW w P) d) := by
  classical
  have hc := hr.hc
  have hl := hr.hl
  by_cases he : ∀ T : Cov p N, (∀ i,cdSign p T i≤maxSpan m b r) →
      pr w (fun i => covered p T (delta mark i)) ≤ c
  · refine ⟨fun _ => True,?_,Or.inl ?_⟩
    · rw [pr_true,hw.total]
      nlinarith [hr.hc',hr.hl']
    rw [onW_true w hw]
    apply tonal_left _ _
    intro S R hS
    exact (pitch_no_cover p _ hw S R hS _ _ _ hK hr.hm hr.hb c ψ H hc.le he
      hr.hψ hr.hH mix hr.hN hv).trans_lt hr.noBranch
  push Not at he
  obtain ⟨T,hT,hW⟩ := he
  let P := fun x : UnitType p n N => covered p T (delta mark x) ∧ voidFrame p x T
  let v := onW w P
  have hp : c/2≤pr w P := by
    have he := framesCost hw.sub mix hr.hL hk hr.hN T (maxSpan m b r) hT
    have hs := pr_shield hw.nz (fun x => covered p T (delta mark x)) (fun x => voidFrame p x T)
    change _ ≤ pr w P at hs
    linarith only [hr.frames,hW,he,hs]
  have hpp : 0<pr w P := lt_of_lt_of_le (half_pos hc) hp
  have hf : IsLaw v := on_law hw.nz hpp
  obtain ⟨s,h⟩ := mark_bazaar (r:=r) mark
    (show ∀ x,v x≠0 → covered p T (delta mark x) ∧ voidFrame p x T ∧ delta mark x≠0 ∧
       epoch p (mrAmbient mark x true)≤r from fun x h => by
      obtain ⟨⟨ha,hb⟩,ht⟩ := onW_ne h; exact ⟨ha,hb,hh x ht⟩)
  have hH := hr.hH; have hL := hr.hL
  have hm : IsLaw (raw mix N) := raw_law mix (by linarith only [hr.hN])
  have he x : v x≤rhUp H c * pairW (raw mix N) (raw mix N) x := by
    apply (on_mon hw.nz (half_pos hc) hp x).trans
    unfold rhUp; rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hv x) (by positivity)
  obtain ⟨Q,hQ,hV⟩ := s.cover_options _ v mix hf h hm hr.cap
    (by unfold rhUp; positivity) hl hr.hl' (bySide_on mix hw.nz hk P hc hp)
    (by unfold rhUp; positivity) he hr.hN (hr.atlas T hT) hr.price hr.price'
    k d hr.hk hr.localQ hr.testFailure hr.testFailure' hr.beatSlack
  refine ⟨fun x => P x ∧ Q x,?_,?_⟩
  · rw [pr_of_on hw.nz]
    exact mul_le_mul hp hQ (by positivity) hpp.le
  rw [← on_both w P Q hw.nz hpp (lt_of_lt_of_le (half_pos hl) hQ)]
  exact hV

end HadwigerCounterexample

end

end OAI
