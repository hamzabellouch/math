import OAI.Combinatorics.HadwigerCounterexample.BiasedRotationBounds

namespace OAI

/-! # Orientation Rank Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Submodule Function Filter Real
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
namespace Template
variable (v : Solo p)
variable {K s : ℕ}
def offBeat (v : Solo p) (P : AtomKey (p:=p) (v.t ()) N →Prop) (o : Orient p n N) :=
  fun z => P (v.desc z o)

theorem beat_round (v : Solo p) (P : AtomKey (p:=p) (v.t ()) N →Prop) (o : Orient p n N)
    (w f : Wgt (Knobs p.g n)) (hw : flowZ p w) (c : Flit n) :
    zsumPeak p w f (offBeat v P (Move.kite p c N o)) =
      zsumPeak p w (Move.zreroute p c f) (offBeat v P o) := by
  classical
  unfold zsumPeak offBeat
  have hh (y : Knobs p.g n) : w (Move.vault p c y)=w y := hw y _
  conv_rhs => rw [← avg_bij (Move.vault p c)]
  simp_rw [hh,Move.kite_keys,Move.zreroute,Equiv.symm_apply_apply]
theorem beat_morph (v : Solo p) (P : AtomKey (p:=p) (v.t ()) N →Prop) (o : Orient p n N)
    (w : Wgt (Knobs p.g n)) (hw : flowZ p w) (c : Flit n) :
    pr w (offBeat v P (Move.kite p c N o)) = pr w (offBeat v P o) := by
  have h := beat_round v P o w (fun _=>1) hw c
  simp only [zsumPeak,Move.zreroute,mul_one] at h
  exact h

def glow (m : Mixer p n) (w : Wgt (Knobs p.g n)) (A : AtomKey (p:=p) (v.t ()) N →Prop)
    (g δ : ℝ) (x : Profile p n) (o : Orient p n N) :=
  let P := offBeat v A o
  δ ≤ pr w P ∧ g*pr w P ≤ |zsumPeak p w (shanty v m x) P|

set_option maxHeartbeats 800000 in
theorem radiance_calendar (v : Solo p)
    (hs : 2*profileA p K<s) (hg : Odd p.g)
    (δ g : ℝ) (hδ : 0<δ)
    (hG : bp (-((p.J-s:ℕ):ℝ))*bp s < g) :
    ∀ᶠ n : ℕ in atTop,∀ (N : ℕ),2*num (Full p n)<N →
      ∀ m : Mixer p n, unaryGood m K s →
      ∀ w : Wgt (Knobs p.g n), IsLaw w → flowZ p w →
      ∀ P : AtomKey (p:=p) (v.t ()) N → Prop,
      pr (raw m N) (fun o => ∃ x, 0<totalRank x ∧ totalRank x≤ K ∧ v.glow m w P g δ x o) ≤
        bp (-(profileA p K:ℝ)*n) := by
  classical
  let d := profileA p K
  filter_upwards [rotor_levels v _ _ _ hs hg δ g hδ hG,profile_count p K]
    with n hn ht N hN m hM w hw h P
  let μ := raw m N
  let F x := v.glow m w P g δ x
  let L (x : Profile p n) := totalRank x≤K
  have hμ := raw_law m hN
  let b := bp (-(2*d:ℝ)*n)
  have h1 (x : Profile p n) (he : L x) (hy : 0<totalRank x) :
      pr μ (F x)≤b := by
    have hi (o : Orient p n N) :
        pr unif (fun c => F x (Move.kite p c N o))≤b := by
      unfold F glow
      simp_rw [beat_round _ _ _ _ _ h,beat_morph _ _ _ _ h]
      let f := offBeat v P o
      by_cases hb : δ≤pr w f
      · change pr unif (fun c => δ≤pr w f ∧ _)≤_
        simp only [hb,true_and]
        exact hn m hM x hy he w hw h f hb
      change pr unif (fun c => δ≤pr w f ∧ _)≤_
      simp only [hb,false_and,pr_false]; exact (bp_pos _).le
    have hz (c : Flit n) :
        pr μ (F x)=pr μ (fun o => F x (Move.kite p c N o)) := by
      unfold pr μ
      conv_lhs => rw [← avg_bij (Move.kite p c N)]
      simp_rw [Move.kite_weights]
    have hh :
        pr μ (F x)=avg unif (fun c => pr μ (fun o => F x (Move.kite p c N o))) := by
      simp_rw [←hz]; exact (unif_law.avg_const _).symm
    rw [hh]
    unfold pr; rw [avg_avg]; exact hμ.avg_le hi
  let Q (x : Profile p n) (o : Orient p n N) := 0<totalRank x∧L x∧F x o
  have hi x : pr μ (Q x)≤ ind (L x)*b := by
    by_cases he : L x
    · by_cases hx : 0<totalRank x
      · simpa only [Q,he,ind_true,one_mul,hx,true_and] using h1 x he hx
      simp only [Q,hx,false_and,he,true_and,pr_false,ind_true,one_mul]; exact (bp_pos _).le
    simp only [Q,he,false_and,and_false,ind_false,zero_mul,pr_false,le_refl]
  apply (pr_exists_le hμ.nz Q).trans
  refine (Finset.sum_le_sum (fun i _ => hi i)).trans ?_
  rw [← Finset.sum_mul]; change nbr L*b ≤ _
  refine (mul_le_mul_of_nonneg_right ht (bp_pos _).le).trans_eq ?_
  unfold d; rw [←bp_add]; congr 1; ring
end Template
end HadwigerCounterexample

end

end OAI
