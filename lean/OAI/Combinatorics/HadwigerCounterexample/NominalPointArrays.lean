import OAI.Combinatorics.HadwigerCounterexample.SyntheticSliceExperiments

namespace OAI

/-! # Nominal Point Arrays -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Function Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I J U : Type} [Fintype I] [Fintype J] [Fintype U]
variable [DecidableEq I] [DecidableEq J] [DecidableEq U]

def incision (p : Shape) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (x : I →Knobs p.g n) :
    Mat (Row p n) I := Matrix.of (fun i j=> spring p l s f (x j) i)
def sketchLaw (p : Shape) (n : ℕ) (a : I→ Tickets p) :=
    prodW (fun i => rung p n (a i))
theorem sketch_law (p : Shape) (n : ℕ) (a : I→ Tickets p) (h : 2*p.r≤n) :
    IsLaw (sketchLaw p n a) := prodW_law (fun _ =>ticketLaw n _ h)

omit [DecidableEq I] in
theorem sketch_matrix (p : Shape) (l s f) (m : Mixer p n) (a : I→ Tickets p)
    (hj : 1 ≤ p.j) (x : I→Knobs p.g n) (h : sketchLaw p n a x ≠0) :
    let A:= incision p l s f x
    pullM A A (selfM p n m.mixM)= Matrix.of (fun i j=>tabGram p l f (a i) (a j)) := by
  classical
  intro A
  have he i : punchField p (x i)=a i := by
    by_contra! hv
    refine h (Finset.prod_eq_zero (mem_univ i) (f:=fun i=>rung p n (a i) (x i)) ?_)
    unfold rung; rw [onW_val,ind_zero (show ¬ issued p _ _ from hv),mul_zero,zero_div]
  ext i j
  let E := selfM p n m.mixM
  have hi : (pullM A A E) i j=evmat E (spring p l s f (x i)) (spring p l s f (x j)) := by
    rw [pullM_def,Matrix.mul_assoc]; rfl
  rw [hi,tabGram_sound _ n l s f (x i) (x j) m hj,he,he]; rfl

def weightsAff (u : Vec I) := ∑ i,u i=(1:F)
def compound (p : Shape) (x : I →Knobs p.g n) (u : Vec I) := ∑ i:I,u i • x i

omit [DecidableEq I] in
set_option maxHeartbeats 600000 in
theorem inc_compound (p : Shape) (l s f) (x : I→ Knobs p.g n) (u : Vec I) (h : weightsAff u) :
    incision p l s f x *ᵥ u=spring p l s f (compound p x u) := by
  classical
  funext i
  rcases i with ⟨i,_|k⟩
  · unfold Matrix.mulVec dotProduct incision; simp only [Matrix.of_apply,spring,point_eval]
    change ∑ j,monoBit s i.val*1*_ = monoBit s i.val *1
    rw [← Finset.mul_sum,show ∑ i,u i=1 from h,mul_one]
  unfold Matrix.mulVec dotProduct incision; simp only [Matrix.of_apply,spring,point_eval]
  change ∑ j,monoBit s i.val*lit f l (x j) k*_ = monoBit s i.val* lit f l (compound p x u) k
  have hz :
      lit f l (compound p x u) k=∑ i,u i*lit f l (x i) k := by
    unfold lit compound
    by_cases h : f.keeps l k.1
    · simp only [Finset.sum_apply,ite_eq_left h,Pi.smul_apply,smul_eq_mul]
    simp only [ite_eq_right h,mul_zero,Finset.sum_const_zero]
  rw [hz,Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=> by ring

omit [DecidableEq I] in
theorem inc_diag (p : Shape) (l s f) (m : Mixer p n) (x : I →Knobs p.g n)
    (u : Vec I) (h : weightsAff u) (hj : 1 ≤ p.j) :
    let A:=incision p l s f x; let y:=compound p x u
    evmat (pullM A A (selfM p n m.mixM)) u u=dialed p l f y := by
  intro A y
  rw [evmat_pull,inc_compound p l s f x u h,←mpair_outer]
  exact (selfM_pair p hj _ (show mom p _ (lit f l y)∈ Wspace p n from Submodule.subset_span
    ⟨s,_,rfl⟩)).trans (etaScan p l s f y).symm

def labFee (p : Shape) (I : Type) [Fintype I] := (ticketsFee p)^Fintype.card I
theorem labFee_pos (p : Shape) (I : Type) [Fintype I] : 0<labFee p I := pow_pos (ticketsFee_pos _) _

def compoundAll (p : Shape) (n : ℕ) (i : Vec I) :
    (I →Knobs p.g n)→ₗ[F] Knobs p.g n where
  toFun x := compound p x i
  map_add' x y := by simp only [compound,Pi.add_apply,smul_add,sum_add_distrib]
  map_smul' b x := by
    simp only [compound,Pi.smul_apply, RingHom.id_apply,Finset.smul_sum]; exact
      Finset.sum_congr rfl (fun i _=> smul_comm _ _ _)

theorem sketch_point (p : Shape) (n : ℕ) (a:I→ Tickets p) (h : 2*p.r≤n)
    (u : Vec I) (he : weightsAff u) (P : Knobs p.g n→Prop) :
    pr (sketchLaw p n a) (fun x=> P (compound p x u)) ≤
      (labFee p I)⁻¹*pr (spins p n) P := by
  classical
  have hh x :
      sketchLaw p n a x≤(labFee p I)⁻¹*unif x := by
    unfold sketchLaw labFee
    rw [draws_unif]
    have hn i : spins p n (x i)=unif (x i) := by rw [spins,← draws_unif]
    apply le_trans (Finset.prod_le_prod₀ (fun i (_: i∈(univ:Finset I)) => (ticketLaw n _ h).nz
      (x i)) (fun i _=>(ticketCap n (a i) h (x i))))
    simp_rw [Finset.prod_mul_distrib,hn]
    simp only [Finset.prod_const, card_univ, inv_pow]
    exact le_rfl
  have hs : Surjective (compoundAll p n u) := by
    intro x
    refine ⟨fun y => x,?_⟩
    change ∑ i,u i • x=x
    rw [← Finset.sum_smul,show ∑ i,u i=1 from he,one_smul]
  have ht :
       pr unif (fun x => P (compound p x u))=pr (spins p n) P := by
    unfold spins
    rw [← draws_unif]
    change pr unif (fun x=>P (compoundAll p n u x))=_
    rw [← mapW_pr,map_unif_surjective _ hs]
  exact (pr_cap hh _).trans_eq (congrArg _ ht)
end HadwigerCounterexample

end

end OAI
