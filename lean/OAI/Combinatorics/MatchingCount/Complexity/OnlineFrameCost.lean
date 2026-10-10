import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.TreeNumericCosts
import OAI.Combinatorics.MatchingCount.Complexity.TreePolynomialGrid
import OAI.Combinatorics.MatchingCount.Machines.OnlineFrame
import OAI.Combinatorics.MatchingCount.Complexity.OnlineCost

namespace OAI

namespace MatchingFPRAS.PhysicalStream.Experiment
variable {A : Type}
lemma worst_affine (p : Experiment A) (g : A→ℕ) (k c : ℕ) :
    p.worst (fun a=>k*g a+c)=k*p.worst g+c := by
  induction p with
  | done a => rfl
  | read p ih =>
    simp only [worst,ih]
    rcases le_total ((p false).worst g) ((p true).worst g) with h|h
    · rw [max_eq_right h,max_eq_right (Nat.add_le_add_right (Nat.mul_le_mul_left k h) c)]
    · rw [max_eq_left h,max_eq_left (Nat.add_le_add_right (Nat.mul_le_mul_left k h) c)]
  | delay n p ih => exact ih
lemma worst_const_add (p : Experiment A) (c : ℕ) (g : A→ℕ) :
    p.worst (fun a=>c+g a)=c+p.worst g := by
  simpa only [one_mul,Nat.add_comm c] using worst_affine p g 1 c
lemma worst_add_const (p : Experiment A) (g : A→ℕ) (c : ℕ) :
    p.worst (fun a=>g a+c)=p.worst g+c := by
  simpa only [one_mul] using worst_affine p g 1 c
lemma worst_add_le (p : Experiment A) (f g : A→ℕ) :
    p.worst (fun a=>f a+g a)≤p.worst f+p.worst g := by
  exact worst_le _ _ _ ((all_worst p f).and (all_worst p g) |>.mono (fun _ h=>Nat.add_le_add h.1 h.2))
end MatchingFPRAS.PhysicalStream.Experiment

namespace MatchingFPRAS.OnlineTree
open TreeTyped PhysicalStream Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]
lemma mapSecond_cost {f : B→Experiment C} (F : Realizer f) (x : A×B) :
    (mapSecond F).cost x=F.cost x.2+8*weight x.1+22 := rfl
omit [Codec B] in
lemma mapSecond_weight [Codec B] {f : B→Experiment C} (x : A×B) :
    ((f x.2).map (Prod.mk x.1)).worst weight=1+weight x.1+(f x.2).worst weight := by
  rw [Experiment.worst_map]
  simp only [Function.comp_def,weight_prod]
  exact Experiment.worst_const_add _ _ _
lemma work_mapSecond {f : B→Experiment C} {F : Realizer f} {m : B→ℕ} {n : A×B→ℕ}
    (hF : WorkBound F m) (p q : Polynomial ℕ)
    (hm : ∀ x,m x.2≤p.eval (n x)) (hw : ∀ x,weight x.1≤q.eval (n x)) :
    WorkBound (mapSecond F) n := by
  obtain ⟨r,hr⟩:=hF
  refine ⟨r.comp p+9*q+23,fun x=>?_⟩
  change (mapSecond F).cost x+((f x.2).map (Prod.mk x.1)).worst weight≤_
  rw [mapSecond_cost,mapSecond_weight]
  have h:=(hr x.2).trans (polynomial_eval_monotone r (hm x))
  dsimp only at h
  have hh:=hw x
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp,Polynomial.eval_ofNat]
  omega
lemma polynomial_mapSecond {f : B→Experiment C} {F : Realizer f} (hF : PolynomialTime F) :
    PolynomialTime (mapSecond (A:=A) F) :=
  work_mapSecond hF X X (fun x=>by simpa using weight_snd x) (fun x=>by simpa using weight_fst x)

lemma pair_cost {f : A→Experiment B} {g : A→Experiment C} (F : Realizer f) (G : Realizer g) (a : A) :
    (pair F G).cost a=F.cost a+G.cost a+45*weight a+26*(f a).worst weight+137 := by
  simp only [pair,Realizer.congr,composition,deterministic,mapSecond,TreeTyped.pair,
    TreeTyped.identity,TreeTyped.first,TreeTyped.second,Experiment.worst_map,
    Experiment.worst,Function.comp_def,id_eq]
  change 1+1+11*weight a+6*weight a+31+
    (F.cost a+8*weight a+22+(f a).worst (fun b=>
      3*weight a+7+(6*weight a+weight b+11)+11*weight (a,b)+6*weight b+31+
        (G.cost a+8*weight b+22)))=_
  simp only [weight_prod]
  have h : (fun b : B=>3*weight a+7+(6*weight a+weight b+11)+11*(1+weight a+weight b)+6*weight b+31+
        (G.cost a+8*weight b+22))=(fun b=>26*weight b+(20*weight a+G.cost a+82)) := by funext b; omega
  rw [h,Experiment.worst_affine]
  omega
omit [Codec A] in
lemma pair_weight [Codec A] {f : A→Experiment B} {g : A→Experiment C} (a : A) :
    ((f a).bind (fun b=>(g a).map (Prod.mk b))).worst weight=
      1+(f a).worst weight+(g a).worst weight := by
  rw [Experiment.worst_bind]
  simp only [Experiment.worst_map,Function.comp_def,weight_prod,
    Experiment.worst_const_add,Experiment.worst_add_const]
lemma work_pair {f : A→Experiment B} {g : A→Experiment C} {F : Realizer f} {G : Realizer g}
    {m : A→ℕ} (hF : WorkBound F m) (hG : WorkBound G m)
    (p : Polynomial ℕ) (hw : ∀ a,weight a≤p.eval (m a)) : WorkBound (pair F G) m := by
  obtain ⟨q,hq⟩:=hF
  obtain ⟨r,hr⟩:=hG
  refine ⟨27*q+r+45*p+138,fun a=>?_⟩
  change (pair F G).cost a+((f a).bind (fun b=>(g a).map (Prod.mk b))).worst weight≤_
  rw [pair_cost,pair_weight]
  have h1:=hq a
  have h2:=hr a
  have h3:=hw a
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  omega
lemma polynomial_pair {f : A→Experiment B} {g : A→Experiment C} {F : Realizer f} {G : Realizer g}
    (hF : PolynomialTime F) (hG : PolynomialTime G) : PolynomialTime (pair F G) :=
  work_pair hF hG X (by intro a; simp)
lemma work_choose {f g : A→Experiment B} {F : Realizer f} {G : Realizer g} {m : A→ℕ}
    (hF : WorkBound F m) (hG : WorkBound G m) : WorkBound (choose F G) m := by
  obtain ⟨p,hp⟩:=hF
  obtain ⟨q,hq⟩:=hG
  refine ⟨p+q+1,fun a=>?_⟩
  change 1+max (F.cost a) (G.cost a)+max ((f a).worst weight) ((g a).worst weight)≤_
  have h1:=hp a
  have h2:=hq a
  simp only [Polynomial.eval_add,Polynomial.eval_one]
  omega
lemma polynomial_choose {f g : A→Experiment B} {F : Realizer f} {G : Realizer g}
    (hF : PolynomialTime F) (hG : PolynomialTime G) : PolynomialTime (choose F G) := work_choose hF hG
end MatchingFPRAS.OnlineTree

end OAI
