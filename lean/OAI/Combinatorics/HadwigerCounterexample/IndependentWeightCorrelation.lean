import OAI.Combinatorics.HadwigerCounterexample.RepeatedQueryBounds

namespace OAI

/-! # Independent Weight Correlation -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Function Finset
open scoped BigOperators
variable {I J T : Type} [Fintype I] [Fintype J] [Fintype T]
variable [DecidableEq I] [DecidableEq J] [DecidableEq T]
variable {N : ℕ}

def brightProd (f : I→ Wgt (Rack J N)) (x : Rack (I × J) N) :=
  ∏ i:I,f i (led i x)

private theorem brProd (f : I→ Wgt (Rack J N)) :
    avg unif (brightProd f)=∏ i,avg unif (f i) := by
  have he := (led_uniform (prodW f))
  exact he.trans (prodW_avg _ _)

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem lane_abs (f : I → Wgt (Rack J N)) (hf : ∀ i x,|f i x|≤1) (T : Finset I) (x) :
    |∏ i∈T,f i (led i x)|≤1 := by
  rw [Finset.abs_prod]; exact (Finset.prod_le_prod₀ (fun i _ => abs_nonneg _)
    (fun i _ => hf i _)).trans_eq (by simp)

omit [Fintype I] [Fintype J] [DecidableEq T] in
private theorem unchanged_true (i : I) {x : Rack (I×J) N} (e : T → I×J)
    (h : i ∉ heard e) (v : PlusRack T N) : led i (x+(upliftR e v,0)) = led i x := by
  apply Prod.ext
  · ext
    simp only [led,sectionR,Prod.fst_add,Matrix.submatrix_apply,Matrix.add_apply,
      heard_fresh v h,add_zero]
  ext; simp [led,sectionR]
omit [Fintype I] [Fintype J] [DecidableEq T] in
private theorem unchanged_false (i : I) {x : Rack (I×J) N}
    (e : T → I×J) (h : i ∉ heard e) (v : PlusRack T N) :
    led i (x+(0,upliftR e v)) = led i x := by
  apply Prod.ext
  · ext; simp [led,sectionR]
  ext
  simp only [led,sectionR,Prod.snd_add,Matrix.submatrix_apply,Matrix.add_apply,
    heard_fresh v h,add_zero]

theorem speed (M : Avenue I J)
    {i j : I} (hi : i ≠ j) {x y : J} (h : M (i,x) (j,y)=1)
    (f : I→ Wgt (Rack J N)) (hf : ∀ i x,|f i x|≤1) :
    |avg unif (fun x => phasedBy M x * brightProd f x)|≤ bp (- (N:ℝ)/2) := by
  classical
  let g (q : Rack (I×J) N) := f i (led i q)
  let P := Finset.univ.erase i
  let l (q : Rack (I×J) N) := ∏ i∈P,f i (led i q)
  have he q : brightProd f q=g q*l q := (Finset.mul_prod_erase _ _ (Finset.mem_univ _)).symm
  let X := fun _ : Unit => (i,x)
  let Y := fun _ : Unit => (j,y)
  have hr : M.submatrix X Y=1 := by ext a b; cases a; cases b; rw [Matrix.one_apply_eq]; exact h
  let r := fun _ : Rack (I×J) N => (1:ℝ)
  have hh q : phasedBy M q * brightProd f q=phasedBy M q*g q*l q*r q := by
    unfold r; rw [he]; ring
  simp_rw [hh]
  have hg q w : g (q+(0,upliftR Y w))=g q := by
    unfold g
    rw [unchanged_false i Y (by simp [heard,Y,hi]) w]
  have hl (q) w : l (q+(upliftR X w,0))=l q := Finset.prod_congr rfl (fun z hz => by
    rw [unchanged_true z X (by
      have hh := (Finset.mem_erase.mp hz).1
      simp [X,heard,hh]) w])
  refine (layerLeak M g l r X Y (fun q => hf i _) (lane_abs f hf P) hg hl (fun _ _ _ => rfl)).trans_eq ?_
  rw [hr,Matrix.rank_one]
  simp only [r,abs_one, Fintype.card_unit, Nat.cast_one,mul_one,unif_law.avg_const]

theorem speed_expand (f : I→ Wgt (Rack J N)) (hf : ∀ i x,|f i x|≤1)
    (E : Rail (I×J)) (Z : Vec E) (hx : ∀ i∈E,i.1.1≠i.2.1) :
    |avg unif (fun x => ind (traced x E Z)*brightProd f x)- bp (-(E.card:ℝ))*avg unif (brightProd f)| ≤
      bp (- (N:ℝ)/2) := by
  classical
  let F (v : Vec E) :=
    vectorPhase v Z * avg unif (fun x => phasedBy (ledgerM E v) x*brightProd f x)
  have hh : avg unif (fun x => ind (traced x E Z)*brightProd f x)=avg unif F := by
    simp_rw [rail_expand,←avg_mul]
    rw [avg_avg]; apply avg_congr
    intro x _
    unfold F
    rw [← avg_mul']
    refine avg_congr (fun i _ => ?_); ring
  let L := bp (- (N:ℝ)/2)
  let B (x : Vec E) := ind (x=0)*avg unif (brightProd f)
  have he x : |F x-B x| ≤ L := by
    unfold F B
    by_cases ht : x=0
    · subst x
      simp only [ledger_zero,layer_zero,one_mul,vectorPhase,zero_dotProduct,
        wsign_zero,ind_true,sub_self,abs_zero]
      exact (bp_pos _).le
    rw [ind_zero ht,zero_mul, sub_zero, abs_mul]
    obtain ⟨y,hy⟩ : ∃ y,x y=1 := by
      by_contra! h; exact ht (funext fun i => (bit_cases _).resolve_right (h _))
    let M := ledgerM E x
    obtain ⟨⟨⟨i,j⟩,k,l⟩,hY⟩ := y
    have hA : M (i,j) (k,l)=1 := by
      simp only [M,ledgerM,Matrix.of_apply,dite_eq_left hY]
      exact hy
    rw [vectorPhase,wsign_abs,one_mul]
    exact speed M (hx _ hY) hA f hf
  rw [hh]
  have hk :
      bp (-(E.card:ℝ))*avg unif (brightProd f)=avg unif B := by
    unfold B; rw [avg_mul]
    congr 1
    symm
    change pr unif (fun x : Vec E => x=0)=_
    rw [pr_point',unif_apply,card_space,dim_vec, Fintype.card_coe,bp_neg]
  rw [hk,← avg_sub]
  exact (abs_avg_le unif_law.nz).trans (unif_law.avg_le he)

end HadwigerCounterexample

end

end OAI
