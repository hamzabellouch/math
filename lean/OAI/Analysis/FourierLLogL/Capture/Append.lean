import OAI.Analysis.FourierLLogL.Capture.Book

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Capture
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Chart

variable {M : ℕ}
open scoped Classical

def offset (i n : ℕ) := 16+i*2+n*2

def price (b : Bool) (i : ℕ) := amp i b^2/2048

private lemma leak_gate (i n : ℕ) (main : Bool) :
    side (offset i n) ≤ amp i main/128 ∧
    2^n*side (offset i n) ≤ side n*(amp i main/128) := by
  have hi : side i ^2 ≤ amp i main := (strength_bounds main (side_pos _) (side_le _)).2.2
  have he' := side_le n
  have he := side_pos n
  have hs : side (offset i n) = side 16 * side i^2*side n^2 := by simp [offset,side,pow_add,pow_mul]
  have hP : side 16 ≤ 1/128 := by norm_num [side]
  have hQ : 2^n*side n=(1:ℝ) := by rw [mul_comm,side_card]
  rw [hs]
  have hn' : side 16*side i^2 ≤ amp i main/128 := by
    calc
      _ ≤ (1/128)*amp i main := mul_le_mul hP hi (sq_nonneg _) (by norm_num)
      _ = _ := by ring
  constructor
  · refine le_trans (mul_le_of_le_one_right (mul_nonneg (side_pos _).le (sq_nonneg _)) ?_) hn'; nlinarith
  calc
    _ = side n*(side 16*side i^2) := by
        rw [show 2^n * (side 16*side i^2*side n^2) =
            (2^n * side n)*(side n*(side 16*side i^2)) by ring,hQ,one_mul]
    _ ≤ _ := by gcongr

private lemma boundary_leak (p : Node) (hp : p.ok M) (F g : Grid M → ℝ)
    (hF : ∀ x, 0 ≤ g x ∧ |F x| ≤ g x) (hG : expU F=0) (L : ℝ)
    (he : expU (fun x => if x∈p.block M then 0 else g x) ≤ L*p.len) :
    (p.dice M).Ex F ≤ L := by
  let f (x : Grid M) := if x∈p.block M then F x else 0
  let g' (x : Grid M) := if x∈p.block M then 0 else g x
  have hE (x : Grid M) : f x ≤ F x+g' x := by
    unfold f g'; split_ifs
    · rw [add_zero]
    · linarith [(abs_le.mp (hF x).2).1]
  have hX : expU f ≤ L*p.len := by
    apply le_trans (b:=expU (fun x => F x+g' x))
    · rw [expU_ex,expU_ex]; apply Ex_mono _ hE
    rw [expU_add,hG,zero_add]; exact he
  have hh : (p.dice M).Ex F = expU f / p.len := by
    rw [← avg_ex hp,avg]; rw [div_eq_inv_mul,smul_eq_mul]
    congr 2
  rw [hh]
  exact (div_le_iff₀ p.len_pos).mpr hX

theorem append_choose (main : Bool) (i : ℕ) {q : Scene M}
    (hp : q.here.valid) (he : q.here.lev < M) (ha : 0 ≤ q.wage) (hn : 0 < q.norm)
    (hm : 0 < q.mass) (hM : q.mass ≤ 2*q.norm) (hE : ¬ hazard q main i)
    (D : Chart M) (hD : D.Sound)
    (x : Grid M) (hx : intense main q (side i) x)
    (hX : ¬ atReach D.items (D.wide+band q.here i (offset i D.size)) x) :
    ∃ C : Chart M, C.items=insert x D.items ∧ D.size+1=C.size ∧
      C.wide=D.wide+band q.here i (offset i D.size) ∧ C.Sound ∧
      flex q main C.refs + price main i ≤ flex q main D.refs := by
  let r := offset i D.size
  let p := band q.here i r
  let a := amp i main; let t := a/128
  let P := tracker q main; let U := q.here.dice M
  have hR : 0 ≤ p := by unfold p band; positivity
  have h₀ : 0 < a := amp_pos _ _
  have hT : 0 < t := by unfold t; positivity
  have h₁ : a ≤ 1 := amp_hi _ _
  obtain ⟨g,hg,f,hf,hY,hZ,hW⟩ := masked_bias main x hp he ha hn hm hM hx hE r (leak_gate i D.size main).1
  let B := D.refs
  let Y (z y : Grid M) := f y * (g z * chi x y).re
  let L (z y : Grid M) := 1+t*Y z y
  let C : Chart M := ⟨fun z y => B z y*L z y, insert x D.items, D.wide+p⟩
  have HT (z y) : |Y z y| ≤ 1 := by
    unfold Y; rw [abs_mul]
    have hfy : |f y| ≤ 1 := by simpa only [abs_of_nonneg (hY y).1] using (hY y).2
    have hgy : |(g z * chi x y).re| ≤ 1 :=
      (Complex.abs_re_le_norm _).trans (by rw [norm_mul,norm_chi,mul_one]; exact hg _)
    exact (mul_le_mul_of_nonneg_right hfy (abs_nonneg _)).trans (by simpa using hgy)
  have HF (z y) : 1/2 ≤ L z y ∧ L z y ≤ 2 := by
    unfold L t; rcases abs_le.mp (HT z y) with ⟨hh1,hh2⟩; constructor <;> nlinarith
  have HH (z) :
      x∉D.items ∧ tinted C.items C.wide (C.refs z) := by
    convert tinted_extend _ _ _ _ _ (hD.radius z) hf hD.bound hR
      x hX ((t:ℂ)*g z) using 2
    · dsimp only [C,B,L,Y]
      funext y; rw [mul_assoc (a:=(t:ℂ)),Complex.re_ofReal_mul]; ring
  have HX : C.size=D.size+1 := Finset.card_insert_of_notMem (HH 0).1
  have HL : C.Sound := by
    constructor
    · exact add_nonneg hD.bound hR
    · intro z y
      rcases HF z y with ⟨hh1,hh2⟩
      rcases hD.total z y with ⟨HE1,HE2⟩
      have he := side_pos D.size
      rw [HX, side_succ,pow_succ]
      unfold C B
      dsimp only
      constructor <;> nlinarith
    intro z; exact (HH z).2
  refine ⟨C,rfl,HX.symm,rfl,HL,?_⟩
  have HE (z : Grid M) : log (normQ q C.refs z) - log (normQ q B z) ≤ t*(a/128) := by
    have hv (y) : |B z y*Y z y| ≤ 2^D.size * f y := by
      have he : 0 ≤ B z y := ((Chart.Sound.pos D hD) _ _).le
      have hM := hY y
      unfold Y; simp_rw [abs_mul,abs_of_nonneg he, abs_of_nonneg hM.1]
      rw [← mul_assoc]
      refine le_trans (mul_le_of_le_one_right (mul_nonneg he hM.1) ?_) ?_
      · exact (Complex.abs_re_le_norm _).trans (by rw [norm_mul,norm_chi,mul_one]; exact hg _)
      exact mul_le_mul_of_nonneg_right (hD.total _ _).2 hM.1
    have hh : U.Ex (fun y => B z y*Y z y) ≤ 2^D.size * side r := by
      apply boundary_leak _ ⟨hp,he.le⟩ _ (fun y => 2^D.size*f y)
        (fun i => ⟨by have hx := (hY i).1; positivity,hv i⟩)
      · unfold Y B; simp_rw [← mul_assoc]
        exact tinted_cancel (tinted_mul (hD.radius z) hf) hX _
      · rw [expU_ex]; rw [expU_ex] at hZ
        simp_rw [show ∀ x : Grid M, (if x∈q.here.block M then (0:ℝ) else 2^D.size*f x) =
          2^D.size*(if x∈q.here.block M then 0 else f x) from fun x => by split_ifs <;> ring, Ex_lmul]
        apply le_trans (mul_le_mul_of_nonneg_left hZ (by positivity))
        exact le_of_eq (by ring)
    have hn : normQ q C.refs z=normQ q B z+t* U.Ex (fun y => B z y*Y z y) := by
      change U.Ex _ = U.Ex _ + _
      rw [← Ex_lmul,← Ex_add]
      congr 1; funext i
      change B z i*(1+t*Y z i) = _
      ring
    have hG : side D.size ≤ normQ q B z :=
      le_trans (Ex_const U _).ge (Ex_mono U fun i => (hD.total _ _).1)
    have h₃ : 0 < normQ q B z := normQ_pos _ _ (Chart.Sound.pos D hD) _
    have h₄ : 0 < normQ q C.refs z := normQ_pos _ _ (Chart.Sound.pos C HL) _
    rw [← log_div h₄.ne' h₃.ne']
    apply le_trans (Real.log_le_sub_one_of_pos (div_pos h₄ h₃))
    have hl : 2^D.size * side r ≤ side D.size*(a/128) := (leak_gate _ _ main).2
    refine sub_le_iff_le_add.mpr ((div_le_iff₀ h₃).mpr ?_)
    nlinarith [hh.trans (hl.trans (mul_le_mul_of_nonneg_right hG (by positivity : 0 ≤ a/128)))]
  have h₃ : t*(a/8) - 2*t^2 ≤ P.Ex (fun i => log (L i.2 i.1)) := by
    let W (i : Grid M × Grid M) := Y i.2 i.1
    have hi (i : Grid M × Grid M) :
        t*W i - 2*t^2 ≤ log (L i.2 i.1) := by
      have hW := HT i.2 i.1
      have hX : |t* W i| ≤ t := by
        rw [abs_mul,abs_of_nonneg hT.le]
        exact mul_le_of_le_one_right hT.le hW
      have hF : log (1+t*W i) ≥ t*W i -2*(t*W i)^2 :=
        log_shift_bound _ (hX.trans (by unfold t; linarith))
      change _ ≤ log (1+t*W i)
      have hE := pow_le_pow_left₀ (abs_nonneg _) hX 2; rw [sq_abs] at hE
      linarith
    have HT := P.Ex_mono hi
    rw [Ex_sub,Ex_lmul,Ex_const] at HT
    change a/8 ≤ P.Ex W at hW
    nlinarith
  unfold flex
  let delta := fun (F : ProductRef M) (i : Grid M × Grid M) => log (normQ q F i.2)-log (F i.2 i.1)
  have HX (i : Grid M × Grid M) :
      delta C.refs i+log (L i.2 i.1) ≤ delta B i+t*(a/128) := by
    unfold delta
    have heq : C.refs i.2 i.1=B i.2 i.1*L i.2 i.1 := rfl
    rw [heq,Real.log_mul ((Chart.Sound.pos D hD) _ _).ne'
      (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (HF _ _).1).ne']
    linarith [HE i.2]
  have He := Ex_mono P HX
  rw [Ex_add,Ex_add,Ex_const] at He
  unfold price
  change _+ P.Ex (delta C.refs)+ a^2/2048 ≤ _ + P.Ex (delta D.refs)
  unfold t B at *
  nlinarith

end FourierLLogL.Dyadic.Procedure.Capture

end OAI
