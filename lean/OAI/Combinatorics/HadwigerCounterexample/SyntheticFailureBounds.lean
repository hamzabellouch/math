import OAI.Combinatorics.HadwigerCounterexample.ZeroDiscrepancyPrediction

namespace OAI

/-! # Synthetic Failure Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Function Filter Real
open scoped BigOperators
variable {p : Shape} {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] {n N d : ℕ}

theorem pr_mono_support (w : Wgt A) (hw : ∀ i, 0≤w i) {P Q : A→Prop}
    (h : ∀ i, w i≠0→P i→Q i) :
    pr w P ≤ pr w Q := by
  change ∑ i,w i*ind (P i) ≤ ∑ i,w i*ind (Q i)
  refine Finset.sum_le_sum fun i _=> ?_
  by_cases hi : w i=0
  · rw [hi,zero_mul,zero_mul]
  exact mul_le_mul_of_nonneg_left (ind_mono (h i hi)) (hw i)

def fiddleRate (p : Shape) (I : Type) [Fintype I] [DecidableEq I] :=
  num (Vec I)* (labFee p I)⁻¹

theorem fiddle_bound (p : Shape) (S : Knobs p.g n → Prop) (w : I→ Tickets p)
    (h : 2*p.r≤n) (ε : ℝ) (hS : pr (spins p n) S≤ ε) :
    pr (sketchLaw p n w) (fun i=> ∃ x,weightsAff x ∧ S (compound p i x))
      ≤ fiddleRate p I * ε := by
  classical
  let P (x : Vec I) := fun i : I → Knobs p.g n=> weightsAff x ∧ S (compound p i x)
  have hw := sketch_law p n w h
  have hi (i:Vec I) :
      pr (sketchLaw p n w) (P i) ≤ (labFee p I)⁻¹*ε := by
    have hg : 0 < labFee p I := labFee_pos ..
    by_cases he : weightsAff i
    · unfold P; simp only [he,true_and]; exact
        (sketch_point p n w h i he S).trans (mul_le_mul_of_nonneg_left hS (by positivity))
    have he' := (pr_nonneg (spins_law p n).nz).trans hS
    simp only [P,he,false_and,pr_false]; positivity
  exact (pr_exists_le hw.nz P).trans ((Finset.sum_le_sum (fun i _ => hi i)).trans_eq
    (by simp only [fiddleRate,num,Finset.sum_const,card_univ,nsmul_eq_mul,mul_assoc]))

def havoc (p : Shape) (l : Tag p.g) (g : Augur p N) (G : Mat (Hue d) (Hue d))
    (r : ℕ) (x : Display p (Hue d) N) := 2*r<(arches (libAug p l g G x)).rank

set_option maxHeartbeats 800000 in
theorem havoc_rate (p : Shape) (l : Tag p.g) (o : Orient p n N) (g : Augur p N) (E : Finset (Tag p.g))
    (s : Label p.b) (r : ℕ) (m : Mixer p n) (ε : ℝ)
    (a : Hue d → Tickets p) (hj : 1≤p.j) (hn : 2*p.r≤n)
    (hx : screen p o s E r g ε) :
    let f:= creed p E
    magazine p l s f (havoc p l g (labGram p l f a) r) a o ≤ fiddleRate p (Hue d)*ε := by
  classical
  intro f
  let G:= labGram p l f a
  obtain ⟨w,h1,h2⟩:=hx
  obtain ⟨M,hM,h⟩:=h2 l
  let P:= mismatch p g w l s f o
  let v:=sketchLaw p n a
  apply le_trans _ (fiddle_bound p P a hn ε (h1 l f))
  change pr v _≤ pr v _
  refine pr_mono_support v (sketch_law p n a hn).nz fun x hx hh=>?_
  by_contra! he
  let A:= incision p l s f x
  let T:=pullM A A M; let F:=libAug p l g G (drill p A o)
  have hi : pullM A A (selfM p n m.mixM) = G := sketch_matrix p l s f m a hj x hx
  have hz (y : Vec (Hue d)) (hy : weightsAff y) :
      F y=evmat T y y := by
    let t:=compound p x y
    have ht : ¬ P t := he y hy
    have heq : g l (evmat G y y) (libColor p l y (drill p A o))=
        dialed p l f t+evmat T y y := by
      rw [←hi,inc_diag _ l s f m x y hy hj,lib_see p l s f x y hy o]
      have he := Eq.symm (not_ne_iff.mp ht)
      refine he.trans ((h t).trans ?_)
      unfold T; rw [evmat_pull,inc_compound p l s f x y hy]
    unfold F libAug libPredict
    rw [heq,←hi,inc_diag _ l s f m x y hy hj]
    change dialed p l f t+_ + dialed p l f t=_
    rw [add_right_comm,char_two,zero_add]
  have hl := (arches_rank F T hz).trans (Nat.mul_le_mul_left 2 ((rank_lift_le ..).trans hM))
  exact Nat.not_lt_of_ge hl hh

def mute (p : Shape) (g : Augur p N) (G : Mat Unit Unit) (x : Display p Unit N) :=
  (∑ i:Tag p.g,libPredict p i g G x (jet ()))≠0

theorem common_lit (p : Shape) (j l : Tag p.g) (x : Knobs p.g n) :
    lit Flavor.sharedOnly j x=lit Flavor.sharedOnly l x := by
  classical
  funext i
  rcases i with ⟨x|x,i⟩
  · simp [lit,Flavor.keeps]
  simp [lit,Flavor.keeps]
theorem common_dial (p : Shape) (j l : Tag p.g) (x : Knobs p.g n) :
    dialed p j Flavor.sharedOnly x=dialed p l Flavor.sharedOnly x := by
  have hj := etaScan p j (0:Label p.b) Flavor.sharedOnly x
  have hl := etaScan p l (0:Label p.b) Flavor.sharedOnly x
  rw [common_lit p j l x] at hj; exact hj.trans hl.symm

set_option maxHeartbeats 800000 in
theorem mute_rate (p : Shape) (l : Tag p.g) (o : Orient p n N) (g : Augur p N) (E : Finset (Tag p.g))
    (s : Label p.b) (r : ℕ) (m : Mixer p n) (ε : ℝ)
    (a : Unit→ Tickets p) (hj : 1≤p.j) (hn : 2*p.r≤n)
    (hx : screen p o s E r g ε) :
    let f:= Flavor.sharedOnly
    magazine p l s f (mute p g (labGram p l f a)) a o ≤ p.g*fiddleRate p Unit*ε := by
  classical
  intro f; let G:=labGram p l f a
  obtain ⟨w,h1,h2⟩:=hx
  let P (i:Tag p.g):= mismatch p g w i s f o
  let Q := fun x=>∃ i,P i x
  let W:=sketchLaw p n a
  have he : pr (spins p n) Q≤p.g*ε := by
    refine (pr_exists_le (spins_law p n).nz P).trans ((sum_le_sum
      (fun i _=> h1 i f)).trans_eq ?_)
    simp only [Finset.sum_const,nsmul_eq_mul,card_univ,Tag,Fintype.card_fin]
  apply le_trans _ ((fiddle_bound p Q a hn (p.g*ε) he).trans_eq (by ring))
  change pr W _ ≤ pr W _
  refine pr_mono_support W (sketch_law p n a hn).nz fun x hx hh=>?_
  by_contra! H
  let A:= incision p l s f x
  let u:= jet ()
  have hu : weightsAff u := by simp [weightsAff,u,jet]
  let t:= compound p x u
  have ht : ∀ i,¬ P i t := not_exists.mp (H u hu)
  have hZ : pullM A A (selfM p n m.mixM) = G := sketch_matrix p l s f m a hj x hx
  have heq i :
      libPredict p i g G (drill p A o) u = w (atom p i s (lit f l t)) := by
    have hq : evmat G u u=dialed p i f t := by rw [←hZ,inc_diag _ l s f m x u hu hj];
                                                exact common_dial p l i t
    have hg : A=incision p i s f x := by
      ext y j; unfold A incision
      simp only [Matrix.of_apply,spring, f]
      rw [common_lit p l i]
    unfold libPredict; rw [hq,hg,lib_see p i s f x u hu o]
    rw [show lit f l t=lit f i t from common_lit p l i t]
    exact Eq.symm (not_ne_iff.mp (ht i))
  apply hh; change ∑ i:Tag p.g,libPredict p i g G (drill p A o) u=_
  simp_rw [heq,←map_sum,atom_union,map_zero]
end HadwigerCounterexample

end

end OAI
