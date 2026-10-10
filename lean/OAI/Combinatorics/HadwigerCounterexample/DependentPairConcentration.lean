import OAI.Combinatorics.HadwigerCounterexample.QueryConcentration

namespace OAI

/-! # Dependent Pair Concentration -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset Function
open scoped BigOperators
variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem outlier {w : Wgt A} (hw : ∀ x, 0 ≤ w x)
    {f : Wgt A} (m : ℝ) (c : ℝ) (hc : 0 < c) {d : ℝ}
    (h : avg w (fun x => (f x-m)^2)≤d) :
    pr w (fun x => c≤|f x-m|) ≤ d/c^2 := by
  refine (le_div_iff₀ (pow_pos hc 2)).mpr ?_
  rw [mul_comm]
  let g (x : A) := (f x-m)^2
  have hg x (h : c≤ |f x-m|) : c^2 ≤ g x := by
    unfold g; exact (pow_le_pow_left₀ hc.le h 2).trans_eq (sq_abs _)
  exact ((mul_le_mul_of_nonneg_left (pr_mono hw hg) (sq_nonneg c)).trans
    (le_avg_markov hw (fun x => sq_nonneg (f x-m)) _)).trans h

def approxData (μ : Wgt X) (f : X→ Wgt A) (c d : ℝ) :=
  ∀ h : Wgt A,(∀ x,|h x|≤1) →
    pr μ (fun x => c ≤ |avg (f x) h-avg (mixW μ f) h|)≤d

def thinData (μ : Wgt X) (f : X→ Wgt A) (τ c d : ℝ) :=
  ∀ P : A → Prop,pr (mixW μ f) P≤τ → pr μ (fun x => c≤pr (f x) P)≤d

omit [Fintype A] [Fintype B] in
theorem mix_data (f : X → Wgt A) (g : Y → Wgt B) (u : Wgt X) (v : Wgt Y) :
    mixW (pairW u v) (fun x => pairW (f x.1) (g x.2))=pairW (mixW u f) (mixW v g) := by
  classical
  funext i
  unfold mixW
  exact pairW_separate u (fun j => f j i.1) v (fun j => g j i.2)

set_option maxHeartbeats 800000 in
theorem paired_spread {μ : Wgt X} {ν : Wgt Y} {w : Wgt (X×Y)}
    (F : Wgt (A×B)) (f : X→ Wgt A) (g : Y→Wgt B)
    (hμ : IsLaw μ) (hν : IsLaw ν) (hw : IsLaw w)
    (hf : ∀ x, IsLaw (f x)) (hg : ∀ x,IsLaw (g x))
    (hF : ∀ x, |F x|≤1)
    (η d e τ : ℝ) (hη : 0<η) (hτ : 0<τ) (he : 0 ≤ e)
    (hA : approxData μ f η d) (hB : approxData ν g η d) (hQ : thinData ν g τ η e)
    (L H : ℝ) (hL : 0≤L) (hH : 0≤H)
    (hwA : ∀ x,mapW w Prod.fst x≤ L*μ x) (hwB : ∀ x,mapW w Prod.snd x≤ L*ν x)
    (h : ∀ x,w x≤H *pairW μ ν x) :
    let M x := avg (pairW (f x.1) (g x.2)) F
    pr w (fun x : X×Y => 5*η ≤|M x-avg (pairW μ ν) M|) ≤ L*(d+d/τ)+H*e := by
  classical
  let M (x : X × Y) := avg (pairW (f x.1) (g x.2)) F
  let pA := mixW μ f; let pB := mixW ν g
  have hpB := mixW_law hν hg
  let hfun (y : B) (x : A) := F (x,y)
  have hf1 y x : |hfun y x|≤1 := hF (x,y)
  let Lfun (y : B) := avg pA (hfun y)
  let Lx (x : X) (y : B) := avg (f x) (hfun y)
  have h1 {w : Wgt A} (hw : IsLaw w) y :
      |avg w (hfun y)| ≤1 := avg_bound1 hw _ (hf1 _)
  have hLa (x y) : |Lx x y|≤1 := h1 (hf x) y
  have hLb (y) : |Lfun y|≤1 := h1 (mixW_law hμ hf) y
  let bad (x : X) (y : B) := η ≤ |Lx x y-Lfun y|
  let Q (x : X) := τ ≤ pr pB (bad x)
  have h2 : pr μ Q≤d/τ := by
    have he' : avg μ (fun x => pr pB (bad x)) ≤ d := by
      unfold pr
      rw [avg_avg]
      exact hpB.avg_le (fun i => hA _ (hf1 i))
    apply (le_div_iff₀ hτ).mpr
    rw [mul_comm]
    exact le_trans (le_avg_markov hμ.nz (fun x => pr_nonneg
      (p:=bad x) hpB.nz) _) he'
  let R (y : Y) := η≤|avg (g y) Lfun-avg pB Lfun|
  have hR : pr ν R ≤ d := hB _ hLb
  let S := fun x : X×Y => ¬Q x.1 ∧ η ≤ pr (g x.2) (bad x.1)
  have hS : pr (pairW μ ν) S≤ e := by
    rw [pr,pairW_avg]
    refine hμ.avg_le (fun x => ?_)
    by_cases h : Q x
    · unfold S; simp only [h,not_true_eq_false,false_and,ind_false,avg_zero]
      exact he
    unfold S
    simp only [h,not_false_eq_true,true_and]
    exact hQ (bad x) (le_of_not_ge h)
  have ha (x : X × Y) (hh : ¬ (Q x.1 ∨ R x.2 ∨ S x)) :
      ¬ (5*η ≤|M x-avg (pairW μ ν) M|) := by
    have hy := not_or.mp hh
    have ht : pr (g x.2) (bad x.1) < η := lt_of_not_ge fun h =>
      (not_or.mp hy.2).2 ⟨hy.1,h⟩
    have hW y : |Lx x.1 y-Lfun y| ≤ η+2*ind (bad x.1 y) := by
      by_cases he' : bad x.1 y
      · rw [ind_one he',mul_one]
        exact (abs_sub ..).trans ((add_le_add (hLa ..) (hLb y)).trans (by linarith only [hη]))
      · rw [ind_zero he',mul_zero,add_zero]; exact le_of_not_ge he'
    have hW' :
        |avg (g x.2) (Lx x.1)-avg (g x.2) Lfun|<3*η := by
      rw [←avg_sub]
      apply lt_of_le_of_lt ((abs_avg_le (hg _).nz).trans (avg_mono (hg _).nz hW))
      rw [avg_add,(hg _).avg_const,avg_mul']
      unfold pr at ht; linarith only [ht]
    have hr : |avg (g x.2) Lfun -avg pB Lfun|<η := lt_of_not_ge ((not_or.mp hy.2).1)
    have eq1 (x : X×Y) : M x=avg (g x.2) (Lx x.1) := by
      unfold M; rw [pairW_avg,avg_avg]
    have eq2 :
        avg (pairW μ ν) M=avg pB Lfun := by
      rw [show avg (pairW μ ν) M= _ from (mixW_avg _ (fun x : X × Y => pairW (f x.1) (g x.2)) F).symm]
      rw [mix_data,pairW_avg,avg_avg]
    rw [eq1,eq2]
    apply not_le_of_gt
    exact ((abs_sub_le ..).trans_lt ((add_lt_add hW' hr).trans (by linarith)))
  have hh x :
      5*η ≤ |M x-avg (pairW μ ν) M| → Q x.1 ∨ R x.2 ∨ S x :=
    fun hz => Classical.byContradiction (fun h => ha x h hz)
  have hW : pr w (Q ∘ Prod.fst) ≤ L*(d/τ) := by
    simp only [comp_def]
    rw [show pr w _=pr (mapW w Prod.fst) Q from (mapW_pr w Prod.fst Q).symm]
    exact (pr_cap hwA _).trans (mul_le_mul_of_nonneg_left h2 hL)
  have hT : pr w (R ∘ Prod.snd) ≤ L*d := by
    simp only [comp_def]
    rw [show pr w _=pr (mapW w Prod.snd) R from (mapW_pr w Prod.snd R).symm]
    exact (pr_cap hwB _).trans (mul_le_mul_of_nonneg_left hR hL)
  have hG : pr w S ≤ H*e := (pr_cap h _).trans (mul_le_mul_of_nonneg_left hS hH)
  change pr w _ ≤ _
  apply le_trans (pr_mono hw.nz hh)
  apply le_trans (pr_or_le (p:=Q ∘ Prod.fst) (q:=fun x => R x.2 ∨ S x) hw.nz)
  apply (add_le_add hW ((pr_or_le (p:=R ∘ Prod.snd) (q:=S) hw.nz).trans (add_le_add hT hG))).trans
  linarith

end HadwigerCounterexample

end

end OAI
