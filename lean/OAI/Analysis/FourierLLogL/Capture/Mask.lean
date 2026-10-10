import OAI.Analysis.FourierLLogL.Capture.MaskKernel
import OAI.Analysis.FourierLLogL.Finite.Tail
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Capture
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse
variable {p : Node} {M : ℕ}
open scoped Classical

lemma margins (p : Node) (hp : p.valid) : 0 ≤ p.a ∧ p.a+p.len ≤ 1 := by
  unfold a
  have he : 0 < p.len := p.len_pos
  refine ⟨by positivity,?_⟩
  calc
    _ = ↑(p.ix+1)*p.len := by push_cast; ring
    _ ≤ ↑(2^p.lev:ℕ)*p.len :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hp) he.le
    _ = _ := by unfold len; push_cast; rw [mul_comm,side_card]

lemma inner_strip (p : Node) (b : Bool) (i : ℕ) (x : Grid M)
    (hx : x∈(child p b).block M) (hh : ¬ flanked p i x) :
    let q := child p b; let r := p.len*side (reach i)
    q.a+r ≤ pos x ∧ pos x < q.a+q.len-r := by
  intro q r
  have hi (c : Bool) : ¬ (x∈(strip p i b c).block M) :=
    fun h => hh ⟨_,_,h⟩
  have h1 : (strip p i b false).a=q.a := extreme_left q _
  have h2 (c : Bool) : (strip p i b c).len=r := strip_length _ _ _ _
  have h3 : (strip p i b true).a + r=q.a+q.len := by
    rw [← h2 true]; exact extreme_right _ _
  have Hp : x∈q.block M:=hx
  constructor
  · by_contra! h
    apply hi false
    change pos x∈Ico _ _
    rw [h1,h2]
    exact ⟨Hp.1,h⟩
  · by_contra! h
    apply hi true
    change pos x∈Ico _ _
    rw [h2,h3]; exact ⟨by linarith,Hp.2⟩

lemma circle_near (p : Node) (hp : p.valid) (x y : Grid M) (r : ℝ)
    (hr : 0 < r) (hx : p.a+r ≤ pos x) (he : pos x ≤ p.a+p.len-r)
    (hy : Dyadic.diam (x-y)<r) : y∈p.block M := by
  have hp' := margins _ hp
  change p.a ≤ pos y ∧ pos y < p.a+p.len
  by_cases H : x-y=0
  · have h := sub_eq_zero.mp H; subst y; constructor <;> linarith
  rw [diam_min,min_lt_iff,pos_neg H] at hy
  rcases le_total x.val y.val with h|h
  · have h1 := pos_sub_val h
    rw [show y-x= -(x-y) by ring,pos_neg H] at h1
    rcases hy with hy|hy <;> constructor <;> linarith [pos_lt y,pos_lt (x-y),pos_nonneg y]
  have h1 := pos_sub_val h
  rcases hy with hy|hy <;> constructor <;> linarith [pos_nonneg y,pos_lt y,pos_nonneg (x-y)]

private def inland (p : Node) (r : ℝ) (x : Grid M) := ∀ y, Dyadic.diam (x-y)<r → y∈p.block M

private lemma limit_full {f : Grid M → ℝ} (s : ℝ) (h : 2^M ≤ s) : limitR f s := by
  intro x hx
  have H := rad_le_val x
  have hh : (x.val:ℝ) < 2^M := by exact_mod_cast ZMod.val_lt x
  linarith

private lemma smoothing_limit (P : Law (Grid M)) (q : Grid M → Prop) (r : ℝ)
    (h : limitR P r) : limitR (fun x => P.prob fun y => q (x-y)) r := by
  have He (x : Grid M) :
      P.prob (fun y => q (x-y)) = ∑ y, (if q y then P (x-y) else 0) := by
    rw [prob_eq]
    apply Fintype.sum_equiv ((Equiv.neg _).trans (Equiv.addLeft x))
    intro i
    have HH : x-i=x+ -i := sub_eq_add_neg x i
    change (if q (x-i) then P i else 0) = if q (x+ -i) then P (x-(x+ -i)) else 0; rw [← HH,sub_sub_self]
  unfold limitR limit; intro i hi
  simp_rw [He,Complex.ofReal_sum]
  rw [fc_sum _ (fun y x => (↑(if q y then P (x-y) else 0):ℂ))]
  apply Finset.sum_eq_zero; intro x hx
  by_cases H : q x
  · simp only [H,ite_true]
    rw [fc_right_translate (fun x => (P x:ℂ)) x i, h _ hi,mul_zero]
  · simp only [H,ite_false,fc, Complex.ofReal_zero,zero_mul,expU,Finset.sum_const_zero,smul_zero]

def band (p : Node) (i j : ℕ) : ℝ := (2:ℝ)^(p.lev+reach i+10)*(2*(j+10))

lemma make_mask (p : Node) (h : p.valid) (hp : p.lev < M) (b : Bool) (i j : ℕ) :
    let q := p.child b
    ∃ f : Grid M → ℝ, limitR f (band p i j) ∧ (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      (∀ x, x∈p.block M → ¬ (lanes p i M ∧ flanked p i x) →
        |(if x∈q.block M then (1:ℝ) else 0)-f x| ≤ side j) ∧
      expU (fun x => if x∈p.block M then 0 else f x) ≤ p.len*side j := by
  classical
  let s : ℝ := p.len*side (reach i)
  intro q
  have Hq := child_ok p h hp b
  have hpq := block_of_below (child_below p b) M
  let D := 2^(p.lev+reach i+10)
  have hD : 0<D := by unfold D; positivity
  have hD' : (0:ℝ) < D := Nat.cast_pos.mpr hD
  have hS : 0 < s := mul_pos p.len_pos (side_pos _)
  have He : band p i j = (D:ℝ)*(2*(j+10)) := by unfold D band; push_cast; rfl
  by_cases H : D ≤ 2^M
  case neg =>
    let f (x : Grid M) := if x∈q.block M then (1:ℝ) else 0
    have hj := side_pos j
    refine ⟨f,limit_full _ ?_, fun x => by unfold f; split_ifs <;> norm_num,fun x _ _ => by unfold f; simp [hj.le],?_⟩
    · rw [He]; have hx : (2:ℝ)^M ≤ D := by exact_mod_cast le_of_not_ge H
      nlinarith [Nat.cast_nonneg (α:=ℝ) j]
    have HE (x : Grid M) : (if x∈p.block M then 0 else f x) = 0 := by
      unfold f
      split_ifs with h hq
      · rfl
      · exact (h (hpq hq)).elim
      rfl
    simp_rw [HE,expU,Finset.sum_const_zero,smul_zero]; exact (mul_pos p.len_pos hj).le

  obtain ⟨P,hP,hT⟩ := boosted M D j hD H
  let r : ℝ := 16/D
  have hr : 0<r := div_pos (by norm_num) hD'
  have hb : lanes p i M := by
    have HE : p.lev+reach i+10 ≤ M :=
      (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp H
    unfold lanes; omega
  have hrS : 2*r ≤ s := by
    have he : s * D = 2^10 := by
      unfold D s len; push_cast
      rw [side_pow_two,side_pow_two,pow_add,pow_add]; field_simp
    unfold r; rw [← mul_div_assoc]; apply (div_le_iff₀ hD').mpr; rw [he]; norm_num
  let g (x : Grid M) := inland q r x
  let f (x : Grid M) := P.prob (fun i => g (x-i))
  have hHi (x : Grid M) (hx : g x) : x∈q.block M := by
    apply hx x
    simpa only [sub_self,diam,rad, neg_zero,ZMod.val_zero,min_self,Nat.cast_zero,mul_zero] using hr
  refine ⟨f,smoothing_limit _ _ _ ?_,fun x => ⟨prob_nonneg _ _,prob_le_one _ _⟩,?_,?_⟩
  · rw [He,show (D:ℝ)*(2*(j+10))=2*(D:ℝ)*(j+10) by ring]
    exact hP
  · intro x hx hE
    have hv : ¬ flanked p i x := fun hh => hE ⟨hb,hh⟩
    by_cases HH : x∈q.block M
    · have hi := inner_strip p b i x HH hv
      have hi (v : Grid M) (hv : Dyadic.diam v<r) : g (x-v) := by
        intro y hy
        refine circle_near q Hq.1 x y s hS hi.1 hi.2.le ?_
        have H := diam_add v (x-v-y)
        rw [show v+(x-v-y)=x-y by ring] at H; linarith
      rw [ite_eq_left HH, abs_of_nonneg (sub_nonneg.mpr (prob_le_one _ _))]
      rw [← prob_compl]
      refine (prob_mono _ _ _ fun i hv => ?_).trans hT
      exact le_of_not_gt (fun h => hv (hi i h))
    rw [ite_eq_right HH,zero_sub,abs_neg,abs_of_nonneg (prob_nonneg _ _)]
    apply le_trans _ hT
    refine prob_mono _ _ _ fun i hi => ?_
    apply le_of_not_gt; intro hi'
    apply HH
    apply hi x; rw [sub_sub_cancel_left,diam_even]; exact hi'
  rw [expU_ex]
  let U := uniform (Grid M)
  let G (x i : Grid M) := if x∈p.block M then (0:ℝ) else if g (x-i) then 1 else 0
  have heq (x : Grid M) : (if x∈p.block M then 0 else f x) = P.Ex (G x) := by
    unfold f prob G; split_ifs with hx
    rw [Ex_const]
    rfl
  have hg1 : U.prob g ≤ p.len := by
    rw [← prob_block (M:=M) (p:=p) ⟨h,hp.le⟩]
    apply prob_mono _ _ _ (fun i hi => hpq (hHi _ hi))
  have heq' (i : Grid M) : U.Ex (fun x => G x i) ≤ p.len*(if r ≤ Dyadic.diam i then 1 else 0) := by
    split_ifs with H
    · rw [mul_one]
      apply le_trans (b:=U.prob fun x => g (x-i))
      · unfold prob G; apply Ex_mono; intro x; split_ifs <;> norm_num
      rw [prob_translate g]; exact hg1
    have he (x : Grid M) : G x i=0 := by
      unfold G; split_ifs with h h'
      · rfl
      · refine (h (hpq (h' x ?_))).elim
        rw [sub_sub_cancel_left,diam_even]
        exact not_le.mp H
      rfl
    rw [funext he,Ex_const,mul_zero]
  simp_rw [heq,Ex_swap (uniform (Grid M)) P]
  apply le_trans (Ex_mono P heq')
  rw [Ex_lmul]
  apply mul_le_mul_of_nonneg_left _ p.len_pos.le
  apply le_trans _ hT

  rw [prob_eq]
  unfold Ex r
  simp

end FourierLLogL.Dyadic.Procedure.Capture

end OAI
