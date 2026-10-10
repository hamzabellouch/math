import OAI.Combinatorics.HadwigerCounterexample.AdaptiveRecordBounds
import OAI.Combinatorics.HadwigerCounterexample.PhaseMomentBounds

namespace OAI

/-! # Phase Alternative Support -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N r : ℕ}
variable {A : Type} [Fintype A]

theorem onW_ne {w : Wgt A} {P : A→Prop} {x : A} (h : onW w P x≠0) : P x ∧ w x≠0 := by
  have hh : subW w P x≠0 := fun hx => h (by unfold onW normW; rw [hx,zero_div])
  exact ⟨Classical.byContradiction (fun hx => hh (subW_carried _ _ _ hx)),
    left_ne_zero_of_mul hh⟩

theorem on_law {w : Wgt A} (hw : ∀ x,0 ≤ w x) {P : A→Prop} (hp : 0<pr w P) :
    IsLaw (onW w P) := normW_law (subW_nonneg hw _) hp
theorem onW_true (w : Wgt A) (h : IsLaw w) : onW w (fun _ => True)=w := by
  funext x
  simp only [onW_val,ind_true,mul_one,pr_true,h.total,div_one]
theorem on_both (w : Wgt A) (p q : A→Prop) (h : ∀ x,0≤ w x) (hp : 0<pr w p)
    (hq : 0< pr (onW w p) q) :
    onW (onW w p) q=onW w (fun x => p x∧q x) := by
  funext x
  rw [onW_val,onW_val,onW_val,pr_of_on h p q,ind_and]
  field_simp

theorem pr_shield {w : Wgt A} (h : ∀ x,0≤w x) (P Q : A→Prop) :
    pr w P-pr w (fun x => ¬Q x) ≤ pr w (fun x => P x ∧ Q x) := by
  have ht x : P x → (P x∧Q x) ∨ ¬Q x := fun h => by by_cases he:Q x <;> simp [h,he]
  exact sub_le_iff_le_add.mpr ((pr_mono h ht).trans (pr_or_le h))

def rhUp (H c : ℝ) := (c/2)⁻¹ * H
theorem bySide_on {w : Wgt (UnitType p n N)} (m : Mixer p n)
    {H : ℝ} (hw : ∀ x,0≤w x) (hh : bySide p w m H)
    (P : UnitType p n N → Prop) {c : ℝ} (hc : 0<c)
    (hp : c/2 ≤ pr w P) :
    bySide p (onW w P) m (rhUp H c) := by
  intro i x
  refine (mapW_cap (on_mon hw (show 0<c/2 by linarith) hp) _ x).trans ?_
  unfold rhUp
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hh i x) (by positivity)

def scaleBill (p : Shape) (n N k : ℕ) (H : ℝ) :=
  (num (Place p)*2)*(H*2 * bp (num (Row p n)+k-N))

def tonalMix (p : Shape) {n N} (Δ : UnitType p n N → Ambient p N) (w) :=
  ∀ S R,S ≠ 0 ∨ R ≠ 0 → |pitch p Δ w S R|< 0.005
def tonalTiny (p : Shape) {n N} (Δ : UnitType p n N → Ambient p N) (w : Wgt (UnitType p n N)) (d : ℕ) :=
  ∃ S : Cov p N, cdim p S≤d ∧ (∀ x,w x≠0 → covered p S (Δ x)) ∧
    ∀ i : Bool,∀ R : Party, |pitch p Δ w (unary i) R|≤bp (-0.24*N)

theorem pitch_turn (Δ : UnitType p n N → Ambient p N) (w S R) :
    pitch p Δ w S R=pitch p Δ w R S := by
  unfold pitch
  rw [pairW_avg,pairW_avg,avg_avg]
  refine avg_congr (fun x hx => avg_congr (fun y hy => ?_))
  exact congrArg wsign (add_comm _ _)

theorem tonal_left (Δ : UnitType p n N → Ambient p N) (w)
    (h : ∀ S R,S≠0 → |pitch p Δ w S R|<0.005) : tonalMix p Δ w := by
  rintro S R (he|he)
  · exact h _ _ he
  rw [pitch_turn]; exact h _ _ he

theorem glimpse_sub (x : UnitType p n N) (i : Bool) (C : Cov p N) {q : Place p→ℕ}
    (A : DTuple (p:=p) q N) (h : ∀ z,colSp (A z) ≤ C z) (hA : ∀ z,Injective (A z).mulVec)
    (hg : glimpse p x i (q:=fun z => dim (C z)) (fun z => pack (C z))) :
    glimpse p x i A := by
  classical
  intro z
  obtain ⟨X,hX⟩ := pull_cols (pack (C z)) (A z) (by rw [colSp_pack]; exact h z)
  have hI : Injective X.mulVec := by
    have ht := hA z
    rw [←hX] at ht
    intro a b h
    apply ht
    rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,h]
  rw [←hX,← Matrix.mul_assoc]; exact inj_comp_mat _ _ (hg z) hI

def preGlimpse (x : UnitType p n N) (C : Cov p N) :=
  ∀ i,glimpse p x i (q:=fun z => dim (C z)) (fun z => pack (C z))

theorem glimpse_cover_failure {w : Wgt (UnitType p n N)} (hv : SubLaw w) (m : Mixer p n)
    {L : ℝ} (h : bySide p w m L) (hL : 0 ≤ L)
    (C : Cov p N) (d : ℕ) (hd : cdim p C≤d)
    (hN : 2*num (Full p n)-N ≤ -1) :
    pr w (fun x => ¬preGlimpse x C) ≤ 2*glimpsesBill p d L := by
  classical
  let M : DTuple (p:=p) (fun z => dim (C z)) N := fun z => pack (C z)
  let P (i : Bool) := fun x : UnitType p n N => ¬glimpse p x i M
  have hp x : ¬preGlimpse x C → ∃ i,P i x := by
    intro h
    unfold preGlimpse at h; push Not at h; exact h
  have hh z : dim (C z) ≤ d :=
    (Finset.single_le_sum (fun z _ => Nat.zero_le (dim (C z))) (Finset.mem_univ z)).trans hd
  refine ((pr_mono hv.nz hp).trans (pr_exists_le hv.nz P)).trans ?_
  rw [Fintype.sum_bool,two_mul]
  exact add_le_add (glimpse_failure m hL h hv true hN M d (fun z => pack_inj _) hh)
    (glimpse_failure m hL h hv false hN M d (fun z => pack_inj _) hh)

namespace Bazaar

variable {T : Cov p N}
variable (s : Bazaar p n r T)

set_option maxHeartbeats 600000 in
theorem cover_options (Δ : UnitType p n N →Ambient p N) (w : Wgt (UnitType p n N))
    (m : Mixer p n) {ε L H l : ℝ} (hw : IsLaw w) (h : s.opened Δ w)
    (hem : IsLaw (raw m N)) (hi : initCap p N m ε)
    (hl : 0 ≤ L) (he₀ : 0< l) (he' : l≤1) (hL : bySide p w m L)
    (hH : 0 ≤ H) (hF : ∀ x,w x≤H*pairW (raw m N) (raw m N) x)
    (hN : 2*num (Full p n)-N≤ -1)
    (ht : num (Atlas p r T) ≤ bp (0.002*N))
    (hd : selPrice p r n N L ε) (hd' : selPrice p r n N (rhUp L l) ε)
    (k d : ℕ) (hK : k≤d) (hQ : quest p r k n N H ε)
    (hk : glimpsesBill p k L+bp (-0.1*N)<l^(k+1))
    (hg : 2*glimpsesBill p d L≤l/2)
    (hψ : 5*l+bp (-0.24*N)<0.005) :
    ∃ P : UnitType p n N→Prop,
      l/2≤pr w P ∧ (tonalMix p Δ (onW w P) ∨ tonalTiny p Δ (onW w P) d) := by
  classical
  let bite (C : Cov p N) := fun x => offsetCov (s.ix x) ≤ C
  by_cases hh : ∀ C,cdim p C≤d → pr w (bite C) ≤ l
  · refine ⟨fun _ => True,by rw [pr_true,hw.total]; linarith, Or.inl ?_⟩
    rw [onW_true w hw]; apply tonal_left Δ w
    intro S R hS
    obtain ⟨j,hj⟩ : ∃ i,S i=1 := by
      by_contra! he
      exact hS (funext fun i => (bit_cases (S i)).resolve_right (he i))
    have heq := s.calm_pitch h hw j R S m hem hi hl hL hd ht
    have hφ := s.frequent_sparse hw h S j hj k d hK l he₀ hh
      (fun A G Z => s.bids_bound S j A G Z hw.sub (bag_rate m hl hem hi hw.sub hL h hd G j))
      m hN hi hH hQ hF hl hL ht hk
    exact ((heq.trans (add_le_add_left hφ _))).trans_lt hψ
  push Not at hh
  obtain ⟨C,hC,hX⟩ := hh
  let P := fun x : UnitType p n N => bite C x ∧ preGlimpse x C
  have hp : l/2≤pr w P := by
    have ht := glimpse_cover_failure hw.sub m hL hl C d hC hN
    have hh := pr_shield hw.nz (bite C) (fun x => preGlimpse x C)
    change _ ≤ pr w P at hh
    linarith only [hh,hg,ht,hX]
  let v := onW w P
  have hv : IsLaw v := on_law hw.nz (lt_of_lt_of_le (half_pos he₀) hp)
  have he x (h' : v x≠0) : standard (s.ix x) ∧ ∀ i, compFor (s.ix x)
      (s.bag (s.ix x) i x) (imageP p x i) (Δ x) := h x (onW_ne h').2
  have ht' (x y : UnitType p n N) (hx : v x≠0) (hy : v y≠0) (i) :
      glimpse p y i (src (s.ix x)) := by
    have hh := he x hx
    exact glimpse_sub y i C _ (onW_ne hx).1.1 hh.1.2.2 ((onW_ne hy).1.2 i)
  have hUp := bySide_on m hw.nz hL P he₀ hp
  refine ⟨P,hp,Or.inr ⟨C,hC,fun x hx => ?_,fun i R => ?_⟩⟩
  · obtain h := ((he x hx).2 true).2
    rw [h]; exact covered_spelled (s.ix x) _ C (onW_ne hx).1.1
  exact (s.single_pitch he hv i R m hem hi (by unfold rhUp; positivity) hUp hd' ht hN).2
    (fun x hx y hy => ht' x y hx hy i)

end Bazaar
end HadwigerCounterexample

end

end OAI
