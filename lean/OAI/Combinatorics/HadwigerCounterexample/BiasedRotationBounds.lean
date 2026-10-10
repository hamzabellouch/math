import OAI.Combinatorics.HadwigerCounterexample.OrthogonalSpectrumBounds

namespace OAI

/-! # Biased Rotation Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module Submodule Function LinearMap Filter Real
open scoped BigOperators
variable {p : Shape} {n : ℕ}

set_option maxHeartbeats 1200000 in
theorem spinning (p : Shape) (w : Wgt (Knobs p.g n))
    (f : Flit n→Wgt (Knobs p.g n)) (P : Knobs p.g n→Prop)
    (hw : IsLaw w) (hf : ∀ i j,|f i j|≤1) (h : flowZ p w)
    (b g δ : ℝ) (hb : 0≤b)
    (T : Space (Vec (Fin n))) (s l : ℕ) (hk : s<n)
    (hh : ∀ (c : Flit n) x i, |zchar p (f c) i x|≤b ∧
      (i∉ c.plume T → zchar p (f c) i x=0))
    (hδ : 0<δ) (ht : b*bp s < g) (hP : δ≤ pr w P)
    (hL : 1 < l * ((g-b*bp s)*δ)^2) :
    pr unif (fun c => g*pr w P ≤ |zsumPeak p w (f c) P|) ≤
      bp (1+((dim T:ℝ)+l*(dim T:ℝ)-n)*s) := by
  classical
  let M := g-b*bp s; have hM : 0<M := sub_pos.mpr ht
  let D c := g*pr w P ≤ |zsumPeak p w (f c) P|
  by_contra! H
  have progress (i : ℕ) (h' : i≤l) :
      ∃ (S : Space (Vec (Fin n))) (U : Wgt (Knobs p.g n)),
        zsafe p w U S ∧ dim S≤ i*dim T ∧ i*(M*δ) ≤ zsumPeak p w U P ∧
          avg w (fun x=>U x ^ 2) ≤ i := by
    induction i with
    | zero =>
      refine ⟨⊥,fun _=>0,?_,?_,?_,?_⟩
      · intro i t h; simp only [zero_mul,avg_zero]
      · simp [dim]
      · simp [zsumPeak,avg_zero]
      simp only [zero_pow (by decide : 2 ≠ 0),avg_zero,Nat.cast_zero,le_refl]
    | succ i ih =>
      obtain ⟨S,U,hS,hU,h1,h2⟩ := ih (by omega)
      let Q (c : Flit n) := s < dim (c.plume T ⊓ S : Space (Vec (Fin n)))
      have hh' : ∃ c : Flit n, D c ∧ ¬ Q c := by
        by_contra! hh
        have hz := (pr_mono unif_law.nz (fun c (h : D c) =>
          (hh c h).le)).trans (Move.plume_meets n s hk T S)
        have hy : (dim S:ℝ)≤ l*(dim T:ℝ) := by
          exact_mod_cast (hU.trans (Nat.mul_le_mul_right _ (by omega) : i*dim T ≤ l*dim T))
        apply (not_lt_of_ge (le_trans hz (bp_le ?_))) H
        nlinarith only [mul_le_mul_of_nonneg_right hy (Nat.cast_nonneg s : 0≤(s:ℝ))]
      obtain ⟨c,he,hc⟩ := hh'
      let W := c.plume T
      have hk : dim (S ⊓ W : Space (Vec (Fin n))) ≤ s := by
        have hh : dim (W⊓S : Space (Vec (Fin n))) ≤ s := le_of_not_gt hc
        rw [inf_comm]; exact hh
      obtain ⟨t,a,ha,hA,hy,hz⟩ := clear_band p w (f c) P hw (hf c) h b g hb he S W s hk (hh c)
      let Z i := a*zim p (f c) t i
      let C i := U i+Z i
      have hQ : avg w (fun i=>U i * Z i)=0 := by
        have he := hS (f c) t (fun i hi => (hA i hi).1)
        unfold Z; simp_rw [mul_left_comm _ a,avg_mul',he,mul_zero]
      refine ⟨S ⊔ W,C,?_,?_,?_,?_⟩
      · intro i s hh
        have hL := zsplit_orth p (f c) i w h t s (Finset.disjoint_left.mpr (fun j hj he =>
          hh j he ((show W≤S⊔W from le_sup_right) (hA j hj).2)))
        have he := hS i s (fun j hj h => hh j hj ((show S≤S⊔W from le_sup_left) h))
        unfold C Z; simp only [add_mul,mul_assoc,avg_add,avg_mul',he,hL,mul_zero,add_zero]
      · have h := Submodule.finrank_add_le_finrank_add_finrank S W
        refine le_trans h ?_
        change dim S+dim W≤_
        unfold W; rw [Move.plume_dim c T,Nat.add_mul,one_mul]
        omega
      · unfold zsumPeak C; simp_rw [mul_add,avg_add]
        change _≤zsumPeak p w U P+zsumPeak p w Z P
        change M*pr w P ≤ zsumPeak p w Z P at hy
        push_cast
        nlinarith only [h1,hy,mul_le_mul_of_nonneg_left hP hM.le]
      · have hh (i) : C i^2=U i^2+Z i^2+2*(U i*Z i) := by unfold C; ring
        simp_rw [hh,avg_add,avg_mul',hQ,mul_zero,add_zero]
        exact (add_le_add h2 hz).trans_eq (by push_cast; rfl)
  obtain ⟨S,U,_,_,hu,hq⟩ := progress l (le_refl _)
  have hh : ↑l * (M*δ) ≤ zsumPeak p w U P := hu
  have hx :
      zsumPeak p w U P ^2 ≤ l := by
    apply (avg_CS hw.nz (fun i=>ind (P i)) U).trans
    have hz (i : Knobs p.g n) : ind (P i)^2 ≤ 1 :=
      calc ind (P i)^2 ≤ 1^2 := pow_le_pow_left₀ (ind_nonneg _) (ind_le_one _) _
           _ = _ := one_pow _
    exact (mul_le_mul (hw.avg_le hz) hq (avg_nonneg hw.nz (fun _ => sq_nonneg _))
      zero_le_one).trans_eq (one_mul _)
  have hy := pow_le_pow_left₀ (by positivity) hh 2
  change 1<↑l*(M*δ)^2 at hL
  have hl : 0<l := by
    by_contra! he
    obtain rfl : l=0 := by omega
    norm_num at hL
  nlinarith only [hx,hy,mul_lt_mul_of_pos_left hL
    (Nat.cast_pos.mpr hl : (0:ℝ) < l)]

namespace Template
variable {K s A : ℕ}
theorem rotor_levels (v : Solo p) (K s a : ℕ)
    (hs : 2*a<s) (hg : Odd p.g)
    (δ g : ℝ) (hδ : 0<δ)
    (hG : bp (-((p.J-s:ℕ):ℝ))*bp s < g) :
    ∀ᶠ n : ℕ in atTop, ∀ m : Mixer p n, unaryGood m K s →
      ∀ x : Profile p n, 0<totalRank x → totalRank x ≤ K →
      ∀ w : Wgt (Knobs p.g n), IsLaw w → flowZ p w →
      ∀ P : Knobs p.g n → Prop, δ ≤ pr w P →
      pr unif (fun c => g*pr w P ≤|zsumPeak p w (v.rotor c m x) P|) ≤ bp (-(2*a:ℝ)*n) := by
  classical
  let b := bp (-((p.J-s:ℕ):ℝ))
  have hb : b*bp s<g := hG
  let t := ((g-b*bp s)*δ)^2
  have ht : 0<t := by apply pow_pos (mul_pos (sub_pos.mpr hb) hδ)
  obtain ⟨l,hl⟩ := exists_nat_gt (1/t)
  let d := 2*(p.J*(p.g-1)*(2*K))
  have ha : 0<(s:ℝ)-2*a := sub_pos.mpr (by exact_mod_cast hs)
  have hz : Tendsto (fun n:ℕ => (↑s-2*a:ℝ)*n) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos ha).mpr tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop s,hz.eventually (eventually_ge_atTop
    (1+((d:ℝ)+l*d)*s))] with n hn hN m hm x hx hK w hw hh P hP
  have he := spinning p w (fun c=>v.rotor c m x) P hw (by
    intro i j; unfold rotor Move.zreroute shanty; rw [wsign_abs]) hh b g δ
    (bp_pos _).le _ s l hn (fun c y i => v.rotor_budget c m x K s hg hm hK hx y i)
    hδ hb hP ((div_lt_iff₀ ht).mp hl)
  apply he.trans
  apply bp_le
  have hy :
      dim (v.scroll m x) ≤ d :=
    (scroll_dim v m x).trans (by unfold d; gcongr)
  have hx : ((dim (v.scroll m x)):ℝ) ≤ d := by exact_mod_cast hy
  change 1+((d:ℝ)+l*d)*s≤ ((s:ℝ)-2*a)*n at hN
  have hB := mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg l : 0≤(l:ℝ))
  nlinarith only [mul_le_mul_of_nonneg_right (add_le_add hx hB)
    (Nat.cast_nonneg s : 0≤(s:ℝ)),hN]
end Template
end HadwigerCounterexample

end

end OAI
