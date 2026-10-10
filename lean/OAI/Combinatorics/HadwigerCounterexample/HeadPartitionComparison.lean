import OAI.Combinatorics.HadwigerCounterexample.FullTemplateComparison

namespace OAI

/-! # Head Partition Comparison -/

noncomputable section
namespace HadwigerCounterexample
open Finset Filter Function
open scoped BigOperators
variable {p : Shape} {n N M : ℕ} {I : Type} [Fintype I] [DecidableEq I]

namespace Template
variable (v : Template p I)

set_option maxHeartbeats 800000 in
theorem shattered (v : Template p I) (j : I)
    (B L δ : ℝ) (hL : 0<L) (hB : 0≤B) (h : 2*B≤L) (hd : 0<δ) :
    ∃ r : ℕ,∀ N : ℕ,∀ q : I→F, ∀ U : Wgt (Keys (p:=p) v.t N),(∀ i, |U i|≤B) →
      ∃ l : ℕ,l≤r ∧ ∃ (a : AtomKey (p:=p) (v.t j) N→ Fin l)
        (b : Fin l→ Wgt (Keys (p:=p) (v.beyond j).t N)),
      (∀ i x,|b i x|≤B)∧
      let R i := curtain v q (U-patched v j a b) i / L
      (∀ i,|R i|≤1) ∧ chairCut v j R δ ∧ carried R (ownPart (p:=p) v.t q) := by
  classical
  obtain ⟨r,hr⟩ := plenty_cuts (δ*L) B (by positivity) hB
  refine ⟨r,fun N q U hU=>?_⟩
  let A:=Keys (p:=p) v.t N
  let E:=chairK v j N
  let f := Prod.fst ∘ E; let g:=Prod.snd ∘ E
  let P := ownPart (p:=p) v.t q (N:=N)
  let w := subW unif P
  have hw : SubLaw w := subLaw_sub unif_law.sub _
  obtain ⟨l,hl,a,b,he⟩ := hr A _ _ w U f g hw hU
  let T:= doubleBook f g a b
  let B' (i : Fin l) (x) := cashbook w T U (i,b x)
  have hx (i x) : |B' i x|≤B := cashbook_bound w hw.nz T U B hB hU _
  refine ⟨l,hl,a,B',hx,?_,?_,?_⟩
  · intro k
    change |ind (P k)* (U k-B' (a (k j)) ((E k).2))/L|≤1
    rw [abs_div,abs_of_pos hL,div_le_iff₀ hL,one_mul]
    by_cases hz : P k
    · rw [ind_one hz,one_mul]
      exact ((abs_sub ..).trans ((add_le_add (hU _) (hx _ _)).trans_eq (two_mul _).symm)).trans h
    rw [ind_zero hz,zero_mul,abs_zero]; exact hL.le
  · intro u hu t ht
    have hi :
        patched v j a B'=banner w T U := rfl
    let W (k:A) := (U k-banner w T U k)*(u (f k)*t (g k))
    have hh :
        avg unif (fun k:A=> curtain v q (U - patched v j a B') k / L * (u (f k)*t (g k))) =
          avg w W/L := by
      rw [hi]
      unfold avg curtain W w P; simp only [div_eq_mul_inv,Finset.sum_mul]; unfold subW
      exact sum_congr rfl fun i _=> by simp only [Pi.sub_apply]; ring
    change |avg unif (fun k:A=> curtain v q (U - patched v j a B') k / L * (u (f k)*t (g k)))|≤_
    rw [hh,abs_div,abs_of_pos hL,div_le_iff₀ hL]
    exact he u hu t ht
  intro i hi
  change ind _ * _/L=0; rw [ind_zero hi,zero_mul,zero_div]

theorem chair_board (v : Template p I) (j : I) (q : I→F) (U : Wgt (Keys (p:=p) v.t N))
    (L δ : ℝ) (hL : 0<L) (h : chairCut v j (fun i=> curtain v q U i/L) δ) :
    shadowed v q U (δ*L) := by
  classical
  intro f hf
  let E:=chairK v j N; let t:=fun i : Aside j=> f i.val
  let g := prodW t
  have hg (x): |g x|≤1 := by
    unfold g prodW; rw [abs_prod]
    exact (prod_le_prod₀ (fun _ _=>abs_nonneg _) (fun i _=>hf _ _)).trans_eq (by simp)
  let R := fun i=> curtain v q U i/L
  let V (i:Keys (p:=p) v.t N) := R i*(f j (E i).1*g (E i).2)
  have hh : |avg unif V|≤δ := h (f j) (hf j) g hg
  have hi : board v q U f=avg unif V*L := by
    unfold board; rw [←avg_mul]
    apply avg_congr; intro i _
    rw [chair_split _ _ j]
    change curtain v q U i*(f j (E i).1*g (E i).2)=_
    unfold V R; field_simp
  rw [hi,abs_mul,abs_of_pos hL]
  exact mul_le_mul_of_nonneg_right hh hL.le

theorem put_back (v : Template p I) (q : I→F) (U : Wgt (Keys (p:=p) v.t N)) (L : ℝ)
    (s : Script p I) (m : Mixer p n) (w f : I→Wgt (Knobs p.g n))
    (o : UnitType p n N) :
    scene v (propel v s m) (fun i=> curtain v q U i/L) w f o=
      astonish v q U s m w f o / L := by
  unfold astonish scene; rw [← avg_div]; exact avg_congr fun x _=>by unfold protean; ring
end Template
end HadwigerCounterexample

end

end OAI
