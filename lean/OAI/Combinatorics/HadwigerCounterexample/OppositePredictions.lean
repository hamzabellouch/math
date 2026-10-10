import OAI.Combinatorics.HadwigerCounterexample.SyntheticFailureBounds

namespace OAI

/-! # Opposite Predictions -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Function Filter Real
open scoped BigOperators
variable {p : Shape} {e d n N : ℕ}

def singleEx {I : Type} (x : Vec I) : Mat I Unit := Matrix.of (fun i _=>x i)

theorem single_jet {I : Type} [Fintype I] (x : Vec I) :
    singleEx x *ᵥ jet ()=x := by funext j; simp [singleEx,jet,Matrix.mulVec,dotProduct]
theorem single_ind {I : Type} [Fintype I] (x : Vec I) (h : weightsAff x) :
    Injective (singleEx x).mulVec := by
  classical
  obtain ⟨j,hj⟩ : ∃ j,x j≠0 := by
    by_contra! hz
    unfold weightsAff at h
    simp only [hz,Finset.sum_const_zero] at h; exact zero_ne_one h
  intro a b ha; funext k
  have hh := congr_fun ha j
  unfold singleEx Matrix.mulVec dotProduct at hh; simp at hh
  cases k; exact hh.resolve_right hj

private theorem collision_front (p : Shape) {r e : ℕ} (h : p.g*(2*r)<e)
    (hg : Odd p.g)
    (x : Display p (Hue e) N) (g : Augur p N)
    (hh : ∀ i,weightsAff i→∑ l:Tag p.g,libPredict p l g (beamMap e) x i=0)
    (hA : ∀ j:Sextant (2*r+1) e,∀ l,¬ havoc p l g (pullM (cartM j) (cartM j) (beamMap e))
      r (exhibit p (cartM j) x)) : False := by
  classical
  let Q (i : Vec (Hue e)) := evmat (beamMap e) i i
  let A (l : Tag p.g) := libAug p l g (beamMap e) x
  let B (i : Vec (Hue e)) := ∑ l : Tag p.g,A l i
  have he i (hi : weightsAff i) :
      B i=evmat (beamMap e) i i := by
    unfold B A libAug; rw [Finset.sum_add_distrib,hh i hi]
    simp only [Finset.sum_const,Finset.card_univ,Tag,Fintype.card_fin,odd_smul_bit hg,zero_add]
  have hz : ∑ l : Tag p.g, arches (A l)=arches B := by
    ext i j; rw [Matrix.sum_apply]; unfold arches
    simp only [Matrix.of_apply,B, ← Finset.sum_add_distrib]
  rw [arches_from B (beamMap e) he] at hz
  have hQ := arches_from Q (beamMap e) (fun x _=>rfl)
  have hi : arches Q=1 := arches_beam _
  rw [← hQ,hi] at hz
  have h1 l : (arches (A l)).rank ≤ 2*r := by
    apply Nat.le_of_lt_succ
    apply rank_torpedo
    intro f
    have hv := hA f l
    unfold havoc at hv
    rw [cart_cross p f l g x] at hv
    exact Nat.lt_succ_of_le (le_of_not_gt hv)
  have ht := mrk_sum_le univ (fun l:Tag p.g=> arches (A l))
  rw [hz,Matrix.rank_one,Fintype.card_fin] at ht
  have he' := ht.trans (Finset.sum_le_sum (g:=fun _=>2*r) (fun i _=>h1 i))
  simp only [Finset.sum_const,Finset.card_univ,Tag,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at he'
  exact not_lt_of_ge he' h

set_option maxHeartbeats 1600000 in
theorem screen_calendar (p : Shape) (r M : ℕ) (hM : 1 ≤ M) (L : ℝ) (hL : 0≤ L)
    (hr : 1≤p.r) (hj : 1≤p.j) (hg : Odd p.g) :
    ∃ ε : ℝ,0<ε ∧ ∀ᶠ n : ℕ in atTop, let N:= M*n; ∀ m : Mixer p n,2*num (Full p n)<N →
      ∀ (E : Finset (Tag p.g)), 2*r+1≤ ((p.g-1)/2)*(p.g-E.card)*p.r →
      ∀ (s : Label p.b) (g : Augur p N) (w : Wgt (Orient p n N)), IsLaw w →
      (∀ i,w i≤ L*raw m N i) → (∀ i,w i≠0 → screen p i s E r g ε) → False := by
  classical
  let e:=p.g*(2*r)+1
  let d:=2*r+1
  let B:=Vec (Hue e)
  let A:= B ⊕ (Sextant d e ×Tag p.g)
  have ha : 0<num A := by unfold num; positivity
  let u := 1/num A/2
  have hu : 0 < u := by positivity
  let b:= (p.g:ℝ)*fiddleRate p Unit
  let c:= fiddleRate p (Hue d)
  have hf (d : ℕ) : 0 ≤ fiddleRate p (Hue d) := mul_nonneg (Nat.cast_nonneg _)
    ((inv_pos_of_pos (labFee_pos ..)).le)
  have hc : 0≤c := hf d
  have hb : 0≤b := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
    ((inv_pos_of_pos (labFee_pos ..)).le))
  let t:=b+c+1
  have ht : 0<t := by unfold t; linarith
  let ε:=u/2/t
  have hε : 0<ε := by positivity
  have hh : c*ε ≤ u/2 ∧ b*ε≤u/2 := by
    have he : t*ε=u/2 := by unfold ε; field_simp
    unfold t at he
    constructor <;> nlinarith only [he,hε,hb,hc]
  refine ⟨ε,hε,?_⟩
  filter_upwards [magazine_calendar p Unit M hM hj L u hL hu,
    magazine_calendar p (Hue d) M hM hj L u hL hu,
    (cast_tops M hM).eventually (eventually_ge_atTop (2*num (Hue e)+1)),
    eventually_ge_atTop (2*p.r)] with n hn hF hB hU N m hN E hE s g w hw h h'
  let W:= Display p (Hue e) N; let Q:= displayLaw p (Hue e) N (beamMap e)
  change 2*num (Hue e)+1≤ (N:ℝ) at hB
  have hB : 2*num (Hue e)-(N:ℝ) ≤ -1 := by linarith only [hB]
  have hQ : IsLaw Q := display_law p (beamMap e) N hB
  let f:= Flavor.sharedOnly (g:=p.g); let z:=creed p E
  let P (i:A) (x:W) :=
    match i with
    | .inl i => weightsAff i ∧ ∑ j:Tag p.g,libPredict p j g (beamMap e) x i≠0
    | .inr (j,i) => havoc p i g (pullM (cartM j) (cartM j) (beamMap e)) r (exhibit p (cartM j) x)
  have he (i:A) : pr Q (P i) ≤ u := by
    rcases i with i|⟨i,j⟩
    · by_cases hi : weightsAff i
      · let V:=singleEx i; let G:=pullM V V (beamMap e)
        let R:=mute p g G
        have hv :
            P (.inl i)= (fun x=>R (exhibit p V x)) := by
          unfold P
          simp only [hi,true_and,R,mute,libPredict,G,evmat_pull,exhibit_color,
            V,single_jet]; rfl
        have hG : 0<p.g := by obtain ⟨_,hh⟩:=hg; omega
        let j:Tag p.g := ⟨0,hG⟩
        obtain ⟨a,ha⟩ := punch_real p j f G (G.rank_le_card_width.trans
          ((by simp : Fintype.card Unit ≤1).trans (sharedPunch p hr j)))
        rw [hv,←mapW_pr]
        unfold Q; rw [exhibit_law p _ _ (single_ind _ hi) hB, show pullM _ _ _ = _ from ha.symm]
        apply hn j s f m hN R a w hw h
        intro x hx
        have hz := mute_rate p j x g E s r m ε a hj hU (h' x hx)
        unfold R; rw [←ha]; exact hz.trans hh.2
      have ht : P (Sum.inl i)=(fun _=>False) := by funext; simp [P,hi]
      rw [ht]; exact (pr_false Q).le.trans hu.le
    let V:= cartM i; let G:=pullM V V (beamMap e)
    let R:= havoc p j g G r
    have hv :
        P (Sum.inr (i,j))=(fun x=>R (exhibit p V x)) := rfl
    have he : Injective V.mulVec := embedMat_inj (reflectSextant i).injective
    have h1 : d ≤ spacePunch p j z := hE.trans (purePunch p j E)
    obtain ⟨a,ha⟩ := punch_real p j z G ((beam_rank i).trans h1)
    rw [hv,←mapW_pr]
    unfold Q; rw [exhibit_law p _ _ he hB,show pullM _ _ _=_ from ha.symm]
    apply hF j s z m hN R a w hw h
    intro x hx
    have hz := havoc_rate p j x g E s r m ε a hj hU (h' x hx)
    unfold R; rw [←ha]; exact hz.trans hh.1
  have hh x : ∃ i,P i x := by
    by_contra! hh
    refine collision_front p (r:=r) (Nat.lt_succ_self _) hg x g ?_ ?_
    · intro i hi
      exact not_ne_iff.mp fun h=> hh (.inl i) ⟨hi,h⟩
    exact fun i j=>hh (Sum.inr (i,j))
  have hi := pr_exists_le hQ.nz P
  have he' := hi.trans ((Finset.sum_le_sum (fun i _=>he i)).trans_eq (by
    rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]))
  change pr Q _≤ num A*u at he'
  rw [show (fun x=>∃ i,P i x)=(fun x=>True) from funext (fun i=>propext ⟨fun _=> trivial,fun _=>hh i⟩),
    pr_true,hQ.total,show num A*u=(1/2:ℝ) by unfold u; field_simp] at he'
  linarith only [he']
end HadwigerCounterexample

end

end OAI
