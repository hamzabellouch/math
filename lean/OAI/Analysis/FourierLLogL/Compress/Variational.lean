import OAI.Analysis.FourierLLogL.Compress.Cost
/-! # Noisy variational construction -/

open Set Function Filter
open scoped BigOperators
noncomputable section
namespace OAI

namespace FourierLLogL.Compress
open Law Real
variable {ι α G : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype G] [AddCommGroup G]

abbrev Sample (ι α G : Type) := (ι → α) × G

def Emp (P : Law (Sample ι α G)) (a : α) : ℝ :=
  ∑ i, P.send (fun x => x.1 i) a

omit [AddCommGroup G] in
lemma Emp_cont : Continuous (fun P : Law (Sample ι α G) => Emp P) :=
  continuous_pi fun y => continuous_finsetSum _ fun _ _ => continuous_send_pdf _ y

omit [AddCommGroup G] in
lemma Emp_mixture (P Q : Law (Sample ι α G)) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Emp (mixture P Q t h0 h1) = t • Emp P + (1-t) • Emp Q := by
  classical
  funext x
  simp only [Pi.add_apply, Pi.smul_apply,smul_eq_mul,Emp,send_apply,prob,mixture_Ex,Finset.sum_add_distrib,← Finset.mul_sum]

/-- Average of exp(-c) on the sum-difference of 2T independent letters. -/
def heatMoment (ι : Type) [Fintype ι] [DecidableEq ι] (p : Law α) (tag : α → G) (c : G → ℝ) : ℝ :=
  let Q := pack (fun _ : ι => p)
  Q.Ex fun y => Q.Ex fun x => exp (-c (tot tag y - tot tag x))


variable [Nonempty α]

lemma trial_bill_uniform (tag : α → G) (c : G → ℝ)
    (p : Law (ι → α)) (z : G) :
    bill tag c (uniform α) (p.send (fun x => (x,z-tot tag x))) Prod.fst Prod.snd =
      Fintype.card ι * log (Fintype.card α) - p.entropy +
      p.Ex fun x => c (z-tot tag x) := by
  rw [bill_send]
  unfold bill
  have HH : ans tag (fun x : ι → α => x) (fun x => z - tot tag x) =
      (fun _ => z) := funext (fun x => by
        change tot tag x + (z-tot tag x) = z
        rw [add_comm,sub_add_cancel])
  change _ - Hcond p (fun x => x) (ans tag (fun x => x) (fun x => z - tot tag x)) + _ = _
  rw [HH,Hcond_constant,H_self]
  simp only [uniform_apply, log_inv, neg_neg,Ex_const,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

lemma exp_norm (a : α → ℝ) : 0 < ∑ x, exp (a x) :=
  Finset.sum_pos (fun _ _ => exp_pos _) Finset.univ_nonempty

/-- The scalar potential dual test used below. -/
lemma trial_cost_with_potential (tag : α → G) (c : G → ℝ)
    (E : ℝ) (h : ∀ p : Law α, exp (-E) ≤ heatMoment ι p tag c)
    (a : α → ℝ) :
    ∃ P : Law (Sample ι α G),
      bill tag c (uniform α) P Prod.fst Prod.snd +
        ∑ i : ι, (P.Ex (fun x => a (x.1 i))-(uniform α).Ex a) ≤ E := by
  classical
  let s : ℝ := ∑ x, exp (-a x)
  have hs : 0 < s := exp_norm _
  let p : Law α := proportional (fun x => exp (-a x)) (fun _ => exp_nonneg _) hs
  have hpos (x : α) : 0 < p x := div_pos (exp_pos _) hs
  let Q := pack fun _ : ι => p
  obtain ⟨y,_,hy⟩ := Q.exists_Ex_le fun y => Q.Ex fun x => exp (-c (tot tag y - tot tag x))
  let z := tot tag y
  let W (x) := Q x * exp (-c (z - tot tag x))
  have hpW (x) : 0 < W x := mul_pos ((pack_pos _ _).mpr fun _ => hpos _) (exp_pos _)
  let D := ∑ x, W x
  have hD : exp (-E) ≤ D := le_trans (h p) hy
  have hD' : 0 < D := (exp_pos _).trans_le hD
  let R := proportional W (fun x => (hpW x).le) hD'
  let n := (Fintype.card ι : ℝ)
  have hlogp (x : α) : log (p x) = -a x - log s := by
    dsimp only [p,s]
    rw [proportional_apply,log_div (exp_pos _).ne' hs.ne', log_exp]
  have hlogQ (x) : log (Q x) = ∑ i : ι, (-a (x i) - log s) := by
    dsimp only [Q]; rw [pack_apply,Real.log_prod (fun j _ => (hpos _).ne')]
    simp_rw [hlogp]
  have hlogR (x) :
      -log (R x) = (∑ i, a (x i)) + n*log s + c (z - tot tag x) + log D := by
    change -log (W x/D) = _
    rw [log_div (hpW x).ne' hD'.ne']
    unfold W; rw [log_mul ((pack_pos _ _).mpr fun _ => hpos _).ne'
      (exp_pos _).ne',hlogQ,log_exp, Finset.sum_sub_distrib,Finset.sum_const,Finset.sum_neg_distrib]
    unfold n; rw [Finset.card_univ,nsmul_eq_mul]; ring
  have hR : R.entropy =
      (∑ i, R.Ex (fun x => a (x i))) + n*log s + R.Ex (fun x => c (z-tot tag x)) + log D := by
    unfold entropy crossE; simp_rw [hlogR,Ex_add,Ex_finset_sum,Ex_const]
  refine ⟨R.send (fun x => (x,z-tot tag x)),?_⟩
  rw [trial_bill_uniform]
  simp_rw [Ex_send,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hce := Law.entropy_le_cross_aux (uniform α) p p.nonneg p.total.le (fun x _ => hpos _)
  rw [Law.entropy_uniform, crossE] at hce
  have Hpl (x : α) : -log (p x) = a x + log s := by rw [hlogp]; ring
  simp_rw [Hpl,Ex_add,Ex_const] at hce
  have HH : -E ≤ log D := by
    rw [← Real.exp_le_exp]; simpa only [Real.exp_log hD'] using hD
  change n*_ - _ + _ + (_ - n*_) ≤ E
  rw [hR]
  have Hn : 0 ≤ n := by dsimp [n]; positivity
  nlinarith

omit [AddCommGroup G] in
private lemma Emp_linear (P : Law (Sample ι α G))
    (L : (α → ℝ) →L[ℝ] ℝ) :
    L (Emp P - fun x => Fintype.card ι * uniform α x) =
      ∑ i : ι, (P.Ex (fun x => L (point (x.1 i) : α → ℝ)) -
        (uniform α).Ex (fun a => L (point a : α → ℝ))) := by
  classical
  have hh (Q : Law α) : L (fun a => Q a) = Q.Ex (fun a => L (point a : α → ℝ)) := by
    have hEq : (fun a => Q a) = ∑ i : α, Q i • (fun a => point i a) := by
      funext a
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,point_apply]
      simp
    nth_rw 1 [hEq]
    simp only [map_sum, map_smul, Ex]
    rfl
  have he : Emp P = ∑ i : ι, (fun y => P.send (fun x => x.1 i) y) := by
    funext; simp only [Finset.sum_apply, Emp]
  rw [map_sub,he,map_sum,show (fun x => Fintype.card ι * uniform α x) =
    (Fintype.card ι : ℝ) • (fun x => uniform α x) from rfl,map_smul]
  rw [hh (uniform α),Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hh, Ex_send]

/-- Version with uniform averaged one-letter marginal. -/
theorem noisy_avg (tag : α → G) (c : G → ℝ) (E : ℝ)
    (h : ∀ p : Law α, exp (-E) ≤ heatMoment ι p tag c) :
    ∃ P : Law (Sample ι α G),
      bill tag c (uniform α) P Prod.fst Prod.snd ≤ E ∧
      Emp P = fun x => Fintype.card ι * uniform α x := by
  classical
  let g (P : Law (Sample ι α G)) := Emp P - fun x => Fintype.card ι * uniform α x
  have hh : ∃ P, bill tag c (uniform α) P Prod.fst Prod.snd ≤ E ∧ g P = 0 := by
    refine Law.primal_feasible _ (bill_cont _ _ _ _ _) g (Emp_cont.sub continuous_const)
      (fun _ _ _ _ _ => bill_mixture_le _ _ _ _ _ _ _ _ _ _) ?_ ?_ E ?_
    · intro P Q t h0 h1
      unfold g; rw [Emp_mixture]
      module
    · let P : Law (ι → α) := pack (fun _ => uniform α)
      refine ⟨P.send (fun x => (x,(0:G))), ?_⟩
      unfold g
      rw [sub_eq_zero]
      ext1 x
      simp_rw [Emp,send_send]

      simp only [P,marginalPack, Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    intro L
    obtain ⟨P,hP⟩ := trial_cost_with_potential tag c E h
      (fun x => L (point x : α → ℝ))
    exact ⟨P,by unfold g; rw [Emp_linear]; exact hP⟩
  obtain ⟨P,h1,h2⟩ := hh
  exact ⟨P,h1,sub_eq_zero.mp h2⟩


def appPerm (e : Equiv.Perm ι) (x : Sample ι α G) : Sample ι α G :=
  ((fun i => x.1 (e i)), x.2)

def exch (P : Law (Sample ι α G)) := ∀ e : Equiv.Perm ι, P.send (appPerm e) = P

omit [AddCommGroup G] [Nonempty α] in
lemma same_marginal {P : Law (Sample ι α G)} (hx : exch P) (i j : ι) :
    P.send (fun a => a.1 i) = P.send (fun a => a.1 j) := by
  let e := Equiv.swap i j
  have H := congrArg (fun r : Law (Sample ι α G) => send r (fun a => a.1 i)) (hx e)
  rw [send_send] at H
  simpa [appPerm,e] using H.symm

omit [AddCommGroup G] [Nonempty α] in
lemma Emp_perm (P : Law (Sample ι α G)) (e : Equiv.Perm ι) :
    Emp (P.send (appPerm e)) = Emp P := by
  ext x
  unfold Emp
  simp_rw [send_send]
  exact Fintype.sum_equiv e _ (fun i : ι => P.send (fun a => a.1 i) x) (fun i => rfl)

/-- Symmetrize to obtain exact prescribed marginal in each coordinate. -/
theorem noisy_symm (tag : α → G) (c : G → ℝ) (E : ℝ)
    (h : ∀ p : Law α, exp (-E) ≤ heatMoment ι p tag c) :
    ∃ P : Law (Sample ι α G),
      bill tag c (uniform α) P Prod.fst Prod.snd ≤ E ∧ exch P ∧
      ∀ i : ι, P.send (fun x => x.1 i) = uniform α := by
  classical
  obtain ⟨P,hp,hp'⟩ := noisy_avg tag c E h
  let V := uniform (Equiv.Perm ι)
  let q (e : Equiv.Perm ι) := P.send (appPerm e)
  let R := V.through q
  have hx : exch R := by
    intro e
    apply ext_of_Ex; intro f
    rw [Ex_send]
    dsimp only [R,q]
    simp_rw [Ex_through,Ex_send]
    let g (d : Equiv.Perm ι) := P.Ex fun x => f (appPerm d x)
    change V.Ex (fun d => P.Ex (fun x => f (appPerm e (appPerm d x)))) = V.Ex g
    have heq (d : Equiv.Perm ι) : P.Ex (fun x => f (appPerm e (appPerm d x))) = g (d*e) := rfl
    simp_rw [heq,Ex]
    exact Fintype.sum_equiv (Equiv.mulRight e) _ _ (fun d => rfl)
  refine ⟨R,?_ ,hx,?_⟩
  · have hq (e : Equiv.Perm ι) :
        bill tag c (uniform α) (q e) Prod.fst Prod.snd ≤ E := by
      dsimp only [q]
      rw [bill_send]
      have HH := bill_subfamily tag c (uniform α) P Prod.fst Prod.snd (fun x _ i => by
        rw [uniform_apply]; positivity) e e.injective
      exact HH.trans hp
    exact le_trans (bill_through_le tag c _ _ _ _ _) ((V.Ex_mono hq).trans (V.Ex_const _).le)
  intro i; have : Nonempty ι := ⟨i⟩
  apply Law.ext; intro x
  have H (e) : Emp (q e) x = Fintype.card ι * (uniform α x) := by dsimp only [q]; rw [Emp_perm, hp']
  have H2 : Emp R x = V.Ex fun e => Emp (q e) x := by
    unfold Emp R
    simp_rw [send_apply,prob,Ex_through,Ex_finset_sum]
  have H3 : Emp R x = (Fintype.card ι : ℝ) * R.send (fun a => a.1 i) x := by
    calc
      _ = ∑ j : ι, R.send (fun a => a.1 i) x :=
        Finset.sum_congr rfl fun j _ => by rw [same_marginal hx j i]
      _ = _ := by simp
  simp_rw [H, V.Ex_const] at H2
  exact mul_left_cancel₀ (by positivity : (Fintype.card ι : ℝ) ≠ 0) (H3.symm.trans H2)

end FourierLLogL.Compress

end OAI
