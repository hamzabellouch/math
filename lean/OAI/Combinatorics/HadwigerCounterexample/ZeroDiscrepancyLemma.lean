import OAI.Combinatorics.HadwigerCounterexample.OppositePredictions

namespace OAI

/-! # Zero Discrepancy Lemma -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Finset Function Filter Real
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {A B : Type} [Fintype A] [Fintype B]

theorem weighted_some [Nonempty B] {w : Wgt A} (h : IsLaw w) (f : B → A→Prop)
    (he : ∀ i,w i≠0 → ∃ j,f j i) :
    ∃ j,(num B)⁻¹ ≤ pr w (f j) := by
  classical
  have hi : pr w (fun _=> True) ≤ pr w (fun i=>∃ j,f j i) := pr_mono_support w h.nz
    (fun i hi _=> he i hi)
  have hx := hi.trans (pr_exists_le h.nz f)
  rw [pr_true,h.total] at hx
  by_contra! hh
  have ht : ∑ i:B,pr w (f i)<∑ i:B,(num B)⁻¹ := by
    obtain ⟨i⟩ := (inferInstance:Nonempty B)
    exact Finset.sum_lt_sum (fun i _=> (hh i).le) ⟨i,mem_univ _,hh i⟩
  have hb : (num B:ℝ)≠0 := by unfold num; positivity
  simp only [sum_const, card_univ,nsmul_eq_mul] at ht
  change ∑ i:B,pr w _<num B*(num B)⁻¹ at ht
  rw [mul_inv_cancel₀ hb] at ht; exact not_lt_of_ge hx ht

set_option maxHeartbeats 1200000 in
theorem unit_screen (p : Shape)
    (K D q B : ℕ)
    (hD : 4*D≤ p.g*q) (hg : 8*D<p.g*p.g)
    (hB : B < Fintype.card (Label p.b))
    (m : Mixer p n) (x : UnitType p n N)
    (hg' : Odd p.g) (hj : 1≤p.j)
    (v : Bool → Profile p n) (α : Bool → F) (ha : α true≠α false)
    (hy : ∀ i, v i ∈ Xspace p n ∧ totalRank (v i) ≤ K ∧ frameLaw m (onSide x i))
    (hz : joins x ≤2*D) (h : Uembed x.1 (v true)=Uembed x.2 (v false))
    (L : Bool→ Finset (Label p.b)) (hL : ∀ i,(L i).card≤B)
    (g : Bool→Augur p N) (ε : ℝ)
    (he : claimed p x g m v α L ε) :
    ∃ (s : Label p.b) (E : Finset (Tag p.g)), E.card≤ q ∧ ∃ b,
      screen p (onSide x b) s E (screenRank p K) (g b) ε := by
  classical
  have hxA : frameLaw m x.1 := (hy true).2.2
  have hxB : frameLaw m x.2 := (hy false).2.2
  obtain ⟨h1,h2⟩:=totalRank_shared hxA hxB h
  have ht (i:Bool) : totalRank (v i) ≤2*D := by
    cases i
    · rw [←h1]; exact h2.trans hz
    exact h2.trans hz
  choose w hw hW hs ht' using fun i:Bool=> sparse_rep (hy i).1
    (show 4*totalRank (v i)<p.g*p.g by have hM:=ht i; omega)
  have hP : parityW (w true)=parityW (w false) :=
    parityW_shared hj hxA hxB (hW _) (hW _) (by rw [hw,hw,h]) (ht' _) (ht' _)
  obtain ⟨b,hb⟩ : ∃ b, parityW (w b)+α b=1 := by
    by_contra! hv
    have hz (i:Bool) : parityW (w i)+α i=0 := (bit_cases _).resolve_right (hv i)
    have hx := hz true; rw [hP] at hx
    exact ha (add_left_cancel (hx.trans (hz false).symm))
  obtain ⟨s,hf⟩ : ∃ s,s∉L b := by
    by_contra! h
    have hz : univ ⊆ L b := fun i _=>h i
    have hh := (card_le_card hz).trans (hL b); rw [card_univ] at hh; omega
  have hx : 0<p.g := by obtain ⟨_,hh⟩:=hg'; omega
  refine ⟨s,zoomset p (w b), le_trans (zoom_le _) ?_,b,?_⟩
  · apply Nat.le_of_mul_le_mul_left _ hx
    have hm:=hs b; have hv:=ht b; omega
  exact zero_screen p x b s m (α b) hg' _ (hW b) hb K (by rw [hw]; exact (hy b).2.1)
    _ ε (L b) hf (by rw [hw]; exact he b)

set_option maxHeartbeats 1200000 in
theorem silicon_calendar (p : Shape)
    (M K D q B : ℕ) (hM : 1 ≤ M)
    (hD : 4*D≤ p.g*q) (hg : 8*D<p.g*p.g)
    (hB : B < Fintype.card (Label p.b))
    (hj : 1≤p.j) (hg' : Odd p.g) (hr : 1≤p.r)
    (hs : 2*screenRank p K+1 ≤ ((p.g-1)/2)*(p.g-q)*p.r)
    (L : ℝ) (hL : 0≤L) :
    ∃ ε:ℝ,0<ε∧∀ᶠ n : ℕ in atTop,
      let N:=M*n; let U:=UnitType p n N
      ∀ m : Mixer p n, 2*num (Full p n)<N →
      ∀ (w : Wgt U) (α : Bool→F) (g : Bool→Augur p N), IsLaw w → bySide p w m L →
      (∀ x,w x≠0 → joins x≤2*D ∧ ∃ (v : Bool → Profile p n) (H : Bool → Finset (Label p.b)),
        (∀ i:Bool,(H i).card≤B ∧ v i∈ Xspace p n ∧ totalRank (v i) ≤ K ∧ frameLaw m (onSide x i))
          ∧ Uembed x.1 (v true)=Uembed x.2 (v false) ∧ claimed p x g m v α H ε) →
        α true=α false := by
  classical
  let V := Label p.b× Finset (Tag p.g) × Bool
  have hp : 0<num V := by unfold num; positivity
  obtain ⟨ε,hε,hh⟩:= screen_calendar p (screenRank p K) M hM (num V*L) (by positivity)
    hr hj hg'
  refine ⟨ε,hε,?_⟩
  filter_upwards [hh] with n hn N U m hN w α g hw hk h
  by_contra he
  let S (i : V) (x : U) := i.2.1.card ≤ q ∧ screen p (onSide x i.2.2) i.1 i.2.1
    (screenRank p K) (g i.2.2) ε
  obtain ⟨i,hi⟩ : ∃ i,(num V)⁻¹≤ pr w (S i) := weighted_some hw S (fun x hx=>by
    obtain ⟨hd,v,H,hZ,hT,hV⟩:=h x hx
    obtain ⟨s,E,hE,t,hQ⟩:= unit_screen p K D q B hD hg hB m x hg' hj v α he
      (fun i=>(hZ i).2) hd hT H (fun i=>(hZ i).1) g ε hV
    exact ⟨(s,E,t),hE,hQ⟩)
  let E := i.2.1; let t := i.2.2
  let z := onW w (S i)
  have hi' := ((inv_pos_of_pos hp).trans_le hi)
  have hZ : IsLaw z := on_law hw.nz hi'
  let v := mapW z (fun x=>onSide x t)
  have hv (x) : v x ≤ num V*L*raw m N x := by
    have hx (i) : z i≤num V*w i := (on_mon hw.nz (inv_pos_of_pos hp) hi i).trans_eq
      (by rw [inv_inv])
    exact (mapW_cap hx (fun x=>onSide x t) _).trans
      (le_trans (mul_le_mul_of_nonneg_left (hk t x) hp.le) (le_of_eq (by ring)))
  have hB : E.card ≤ q := by
    obtain ⟨x,hx,_⟩:=exists_of_pr_pos hw.nz hi'
    exact hx.1
  apply hn m hN E (le_trans hs (by gcongr)) i.1 (g t) v (mapW_law hZ _) hv
  have hp : carried z (S i) := normW_carried (subW_carried w _)
  have hb : carried v (fun y => screen p y i.1 E (screenRank p K) (g t) ε) :=
    mapW_carried hp (fun x hx=> hx.2)
  exact fun i hi=>not_not.mp fun h=>hi (hb i h)
end HadwigerCounterexample

end

end OAI
