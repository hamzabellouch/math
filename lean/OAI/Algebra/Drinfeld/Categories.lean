import OAI.Algebra.Drinfeld.Lattice

namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace CategoricalValues
open CategoryGauge

def swapObjects : Fin 3 → Fin 3 := ![1,0,2]
def rotateObjects : Fin 3 → Fin 3 := ![1,2,0]
def swapLie : L →ₗ⁅ℚ⁆ L := eval y x
def rotateLie : L →ₗ⁅ℚ⁆ L := eval y (-x-y)

structure Witness where
  three : CategoryGauge.Data ℚ L (Fin 3)
  four : CategoryGauge.Data ℚ T4 (Fin 5)
  swap : Compatible swapLie swapObjects three three
  rotate : Compatible rotateLie rotateObjects three three
  kill_x : loop three 0 x=0
  kill_y : loop three 1 y=0
  AD : EdgeCompatible (eval (t 0 2+t 1 2) (t 2 3)) 0 1 0 3 three four
  DE : EdgeCompatible (eval (t 0 1) (t 1 2+t 1 3)) 0 1 3 4 three four
  AB : EdgeCompatible (eval (t 0 1) (t 1 2)) 0 1 0 1 three four
  BC : EdgeCompatible (eval (t 0 1+t 0 2) (t 1 3+t 2 3)) 0 1 1 2 three four
  CE : EdgeCompatible (eval (t 1 2) (t 2 3)) 0 1 2 4 three four

def value (w : Witness) : L := unit w.three 0 1

theorem value_anti (w : Witness) : value w+eval y x (value w)=0 := by
  have h := w.swap.1 0 1
  change unit w.three 1 0=eval y x (value w) at h
  rw [←h]
  simp only [value,unit]
  abel

theorem rotate_squared : rotateLie.comp rotateLie=eval (-x-y) x := by
  apply FreeLieAlgebra.hom_ext
  intro i
  cases i
  · simp [rotateLie,eval,x,y]
  · simp [rotateLie,eval,x,y]
    abel

theorem value_cyclic (w : Witness) :
    value w+eval y (-x-y) (value w)+eval (-x-y) x (value w)=0 := by
  have h₁ := w.rotate.1 0 1
  have h₂ := w.rotate.1 1 2
  change unit w.three 1 2=rotateLie (value w) at h₁
  change unit w.three 2 0=rotateLie (unit w.three 1 2) at h₂
  rw [h₁] at h₂
  have hsq : rotateLie (rotateLie (value w))=eval (-x-y) x (value w) :=
    LieHom.congr_fun rotate_squared (value w)
  rw [hsq] at h₂
  change value w+rotateLie (value w)+eval (-x-y) x (value w)=0
  rw [←h₁,←h₂]
  simp only [value,unit]
  abel

theorem value_pentagon (w : Witness) :
    eval (t 0 1) (t 1 2+t 1 3) (value w)+eval (t 0 2+t 1 2) (t 2 3) (value w)=
      eval (t 1 2) (t 2 3) (value w)+eval (t 0 1+t 0 2) (t 1 3+t 2 3) (value w)+
        eval (t 0 1) (t 1 2) (value w) := by
  unfold value
  rw [←w.AD.1,←w.DE.1,←w.AB.1,←w.BC.1,←w.CE.1]
  simp only [unit]
  abel

theorem value_mem (w : Witness) : value w∈W :=
  ⟨value_anti w,value_cyclic w,value_pentagon w⟩

theorem source_derivation (w : Witness) : loop w.three 0=derivation (value w) := by
  apply derivation_ext
  · simpa only [derivation_apply,D_x] using w.kill_x
  · have h := loop_change w.three 0 1 y
    rw [w.kill_y] at h
    change 0=loop w.three 0 y+⁅value w,y⁆ at h
    simp only [derivation_apply,D_y]
    rw [←lie_skew y (value w)]
    exact eq_neg_of_add_eq_zero_left h.symm

def zero : Witness where
  three := CategoryGauge.zero
  four := CategoryGauge.zero
  swap := compatible_zero _ _
  rotate := compatible_zero _ _
  kill_x := zero_loop _ _
  kill_y := zero_loop _ _
  AD := edge_zero _ _ _ _ _
  DE := edge_zero _ _ _ _ _
  AB := edge_zero _ _ _ _ _
  BC := edge_zero _ _ _ _ _
  CE := edge_zero _ _ _ _ _

def add (w v : Witness) : Witness where
  three := CategoryGauge.add w.three v.three
  four := CategoryGauge.add w.four v.four
  swap := compatible_add _ _ w.swap v.swap
  rotate := compatible_add _ _ w.rotate v.rotate
  kill_x := by rw [add_loop,w.kill_x,v.kill_x,add_zero]
  kill_y := by rw [add_loop,w.kill_y,v.kill_y,add_zero]
  AD := edge_add _ w.AD v.AD
  DE := edge_add _ w.DE v.DE
  AB := edge_add _ w.AB v.AB
  BC := edge_add _ w.BC v.BC
  CE := edge_add _ w.CE v.CE

def smul (c : ℚ) (w : Witness) : Witness where
  three := CategoryGauge.smul c w.three
  four := CategoryGauge.smul c w.four
  swap := compatible_smul _ _ w.swap c
  rotate := compatible_smul _ _ w.rotate c
  kill_x := by rw [smul_loop,w.kill_x,smul_zero]
  kill_y := by rw [smul_loop,w.kill_y,smul_zero]
  AD := edge_smul _ w.AD c
  DE := edge_smul _ w.DE c
  AB := edge_smul _ w.AB c
  BC := edge_smul _ w.BC c
  CE := edge_smul _ w.CE c

def bracket (w v : Witness) : Witness where
  three := commutator w.three v.three
  four := commutator w.four v.four
  swap := compatible_commutator _ _ w.swap v.swap
  rotate := compatible_commutator _ _ w.rotate v.rotate
  kill_x := commutator_kills w.kill_x v.kill_x
  kill_y := commutator_kills w.kill_y v.kill_y
  AD := edge_commutator _ w.AD v.AD
  DE := edge_commutator _ w.DE v.DE
  AB := edge_commutator _ w.AB v.AB
  BC := edge_commutator _ w.BC v.BC
  CE := edge_commutator _ w.CE v.CE

theorem value_bracket (w v : Witness) : value (bracket w v)=ihara (value w) (value v) := by
  change unit (commutator w.three v.three) 0 1=_
  rw [unit_commutator,source_derivation,source_derivation]
  rfl

def values : IntegralFamily.Values where
  space :=
    { carrier := {p | ∃ w : Witness,value w=p}
      zero_mem' := ⟨zero,zero_unit _ _⟩
      add_mem' := by rintro p q ⟨w,rfl⟩ ⟨v,rfl⟩; exact ⟨add w v,add_unit _ _ _ _⟩
      smul_mem' := by rintro c p ⟨w,rfl⟩; exact ⟨smul c w,smul_unit _ _ _ _⟩ }
  le_W := by rintro p ⟨w,rfl⟩; exact value_mem w
  bracket := by rintro p q ⟨w,rfl⟩ ⟨v,rfl⟩; exact ⟨bracket w v,value_bracket w v⟩

end CategoricalValues

namespace GaugeCompatibility
open CategoryGauge

 theorem intertwine {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    (D : LieDerivation ℚ M M) (q : L) (a b : M)
    (hx : D a=0) (hy : D b=⁅b,eval a b q⁆) (p : L) :
    D (eval a b p)=eval a b (derivation q p) := by
  induction p using freeLie_induction with
  | h0 => simp only [map_zero]
  | hg i =>
    cases i
    · change D (eval a b x)=eval a b (derivation q x)
      simp only [eval_x,derivation_apply,D_x,map_zero,hx]
    · change D (eval a b y)=eval a b (derivation q y)
      simp only [eval_y,derivation_apply,D_y,LieHom.map_lie,hy]
  | ha p r hp hr => simp only [map_add,hp,hr]
  | hs s p hp => simp only [map_smul,hp]
  | hl p r hp hr => simp only [LieHom.map_lie,LieDerivation.apply_lie_eq_add,map_add,hp,hr]

 theorem compatible {M N O P : Type*} [LieRing M] [LieAlgebra ℚ M]
    [LieRing N] [LieAlgebra ℚ N] (g : Data ℚ M O) (k : Data ℚ N P)
    (F : M →ₗ⁅ℚ⁆ N) (f : O → P) (K : N)
    (hh : ∀ p,k.h (f p)=F (g.h p)+K)
    (hd : ∀ z,k.d (F z)+⁅K,F z⁆=F (g.d z)) : Compatible F f g k := by
  constructor
  · intro p q
    simp only [unit,hh,map_sub]
    abel
  · intro p z
    simp only [loop_apply,hh,add_lie,map_add,LieHom.map_lie]
    rw [←hd z]
    abel

end GaugeCompatibility

namespace ThreeSolutionCategory
open CategoricalValues CategoryGauge

def data (q : L) : Data ℚ L (Fin 3) :=
  ⟨derivation q,![0,q,q+rotateLie q]⟩

@[simp] theorem loop_zero (q : L) : loop (data q) 0=derivation q := by
  ext p
  simp [loop_apply,data]
@[simp] theorem value (q : L) : unit (data q) 0 1=q := by simp [unit,data]

 theorem anti {q : L} (hq : q∈W) : swapLie q= -q := by
  exact eq_neg_of_add_eq_zero_right hq.1

 theorem rotating_anti {q : L} (hq : q∈W) : swapLie (rotateLie q)=q+rotateLie q := by
  change eval y x (eval y (-x-y) q)=q+eval y (-x-y) q
  rw [map_eval,eval_y,map_sub,map_neg,eval_x,eval_y]
  have h := solution_three hq x y
  rw [eval_self,LieHom.id_apply,solution_swap hq (-x-y) x] at h
  have hs : -y-x= -x-y := by abel
  rw [hs]
  exact (eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using h)).symm

 theorem rotating_twice {q : L} (hq : q∈W) : rotateLie (q+rotateLie q)= -q := by
  rw [map_add]
  have hsq := LieHom.congr_fun rotate_squared q
  change rotateLie (rotateLie q)=eval (-x-y) x q at hsq
  rw [hsq]
  exact eq_neg_of_add_eq_zero_right (by simpa only [rotateLie,add_assoc] using hq.2.1)

 theorem swap {q : L} (hq : q∈W) : Compatible swapLie swapObjects (data q) (data q) := by
  apply GaugeCompatibility.compatible (data q) (data q) swapLie swapObjects q
  · intro i
    fin_cases i
    · simp [data,swapObjects]
    · change 0=swapLie q+q
      rw [anti hq,neg_add_cancel]
    · change q+rotateLie q=swapLie (q+rotateLie q)+q
      rw [map_add,anti hq,rotating_anti hq]
      abel
  · intro p
    have hh := GaugeCompatibility.intertwine (loop (data q) 1) q y x
      (by simp only [loop_apply,data,D_y,derivation_apply,Matrix.cons_val_one,Matrix.cons_val_zero]; rw [←lie_skew y q]; abel)
      (by
        simp only [loop_apply,data,derivation_apply,D_x,zero_add,Matrix.cons_val_one,Matrix.cons_val_zero]
        change ⁅q,x⁆=⁅x,swapLie q⁆
        rw [anti hq,lie_neg,←lie_skew x q,neg_neg]) p
    simpa only [loop_apply,data,Matrix.cons_val_one,Matrix.cons_val_zero,swapLie,rotateLie] using hh

 theorem rotate {n : ℕ} {q : L} (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    Compatible rotateLie rotateObjects (data q) (data q) := by
  have hs : ⁅x,q⁆=⁅-x-y,rotateLie q⁆ := by
    have hh := Differentiation.special_identity hq hqn hn x y
    have hanti : eval y x q= -q := anti hq
    rw [hanti,lie_neg] at hh
    exact neg_add_eq_zero.mp hh
  apply GaugeCompatibility.compatible (data q) (data q) rotateLie rotateObjects q
  · intro i
    fin_cases i
    · simp [data,rotateObjects]
    · change q+rotateLie q=rotateLie q+q
      exact add_comm _ _
    · change 0=rotateLie (q+rotateLie q)+q
      rw [rotating_twice hq,neg_add_cancel]
  · intro p
    have hh := GaugeCompatibility.intertwine (loop (data q) 1) q y (-x-y)
      (by simp only [loop_apply,data,D_y,derivation_apply,Matrix.cons_val_one,Matrix.cons_val_zero]; rw [←lie_skew y q]; abel)
      (by
        simp only [loop_apply,data,Matrix.cons_val_one,Matrix.cons_val_zero,map_sub,map_neg,
          derivation_apply,D_x,D_y,zero_add]
        change -⁅q,x⁆-(⁅y,q⁆+⁅q,y⁆)=⁅-x-y,rotateLie q⁆
        rw [←hs,←lie_skew x q,←lie_skew y q]
        abel) p
    simpa only [loop_apply,data,Matrix.cons_val_one,Matrix.cons_val_zero,swapLie,rotateLie] using hh

end ThreeSolutionCategory

namespace FourSolutionCategory
open T4Basic T4SolutionData CategoryGauge
variable {n : ℕ} {q : L}

def data (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : Data ℚ T4 (Fin 5) :=
  ⟨T4Derivation.derivation hq hqn hn,![0,A q,A q+B q,T4SolutionData.D q,T4SolutionData.D q+E q]⟩

 theorem edge (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (X Y : T4) (s t : Fin 5)
    (hu : unit (data hq hqn hn) s t=eval X Y q)
    (hx : loop (data hq hqn hn) s X=0)
    (hy : loop (data hq hqn hn) s Y=⁅Y,eval X Y q⁆) :
    EdgeCompatible (eval X Y) 0 1 s t (ThreeSolutionCategory.data q) (data hq hqn hn) := by
  constructor
  · rw [ThreeSolutionCategory.value]; exact hu
  · intro p
    rw [ThreeSolutionCategory.loop_zero]
    exact GaugeCompatibility.intertwine _ q X Y hx hy p

 theorem AB (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    EdgeCompatible (eval a b) 0 1 0 1 (ThreeSolutionCategory.data q) (data hq hqn hn) := by
  apply edge hq hqn hn
  · simp [data,unit,A]
  · simp [data,loop_apply]
  · simp [data,loop_apply,A]

 theorem AD (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    EdgeCompatible (eval (d+b) c) 0 1 0 3 (ThreeSolutionCategory.data q) (data hq hqn hn) := by
  apply edge hq hqn hn
  · simp [data,unit,T4SolutionData.D]
  · simp only [data,loop_apply,Matrix.cons_val_zero,zero_lie,add_zero,map_add,
      T4Derivation.derivation_d,T4Derivation.derivation_b,neg_add_cancel]
  · simp [data,loop_apply,T4SolutionData.D]

 theorem DE (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    EdgeCompatible (eval a (b+e)) 0 1 3 4 (ThreeSolutionCategory.data q) (data hq hqn hn) := by
  have hd := T4SolutionData.data hq hqn hn
  apply edge hq hqn hn
  · simp [data,unit,E]
  · rw [loop_apply]
    change T4Derivation.derivation hq hqn hn a+⁅T4SolutionData.D q,a⁆=0
    rw [T4Derivation.derivation_a,zero_add]
    exact commute_symm hd.aD
  · rw [loop_apply]
    change T4Derivation.derivation hq hqn hn (b+e)+⁅T4SolutionData.D q,b+e⁆=⁅b+e,E q⁆
    rw [map_add,T4Derivation.derivation_b,T4Derivation.derivation_e,lie_add,←lie_skew (b+e) (T4SolutionData.D q)]
    abel

 theorem BC (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    EdgeCompatible (eval (a+d) (e+c)) 0 1 1 2 (ThreeSolutionCategory.data q) (data hq hqn hn) := by
  have hd := T4SolutionData.data hq hqn hn
  apply edge hq hqn hn
  · simp [data,unit,B]
  · rw [loop_apply]
    change T4Derivation.derivation hq hqn hn (a+d)+⁅A q,a+d⁆=0
    rw [map_add,T4Derivation.derivation_a,T4Derivation.derivation_d,zero_add]
    calc
      _= -⁅a+b+d,A q⁆ := by simp only [add_lie,lie_add]; rw [←lie_skew a (A q),←lie_skew d (A q)]; abel
      _=0 := by rw [hd.KA,neg_zero]
  · rw [loop_apply]
    change T4Derivation.derivation hq hqn hn (e+c)+⁅A q,e+c⁆=⁅e+c,B q⁆
    rw [map_add,T4Derivation.derivation_e,T4Derivation.derivation_c]
    have hl := TangentBraid.velocity_L hd
    change ⁅b,A q⁆+⁅c,T4SolutionData.D q⁆+(⁅b+e,T4SolutionData.D q+E q⁆-⁅b,A q⁆)=⁅b+c+e,A q+B q⁆ at hl
    calc
      _=(⁅b,A q⁆+⁅c,T4SolutionData.D q⁆+(⁅b+e,T4SolutionData.D q+E q⁆-⁅b,A q⁆))-⁅b,A q⁆+⁅A q,e+c⁆ := by abel
      _=⁅b+c+e,A q+B q⁆-⁅b,A q⁆+⁅A q,e+c⁆ := by rw [hl]
      _=⁅e+c,B q⁆ := by
        simp only [add_lie,lie_add]
        rw [hd.bB,←lie_skew e (A q),←lie_skew c (A q)]
        abel

 theorem CE (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    EdgeCompatible (eval b c) 0 1 2 4 (ThreeSolutionCategory.data q) (data hq hqn hn) := by
  have hd := T4SolutionData.data hq hqn hn
  apply edge hq hqn hn
  · change (T4SolutionData.D q+E q)-(A q+B q)=C q
    rw [pentagon hq]
    abel
  · rw [loop_apply]
    change T4Derivation.derivation hq hqn hn b+⁅A q+B q,b⁆=0
    rw [T4Derivation.derivation_b,add_lie,←lie_skew b (A q),commute_symm hd.bB]
    abel
  · rw [loop_apply]
    change T4Derivation.derivation hq hqn hn c+⁅A q+B q,c⁆=⁅c,C q⁆
    rw [T4Derivation.derivation_c]
    have hc := TangentBraid.velocity_c hd
    change ⁅c,T4SolutionData.D q⁆=⁅c,A q+B q⁆+⁅c,C q⁆ at hc
    rw [hc,←lie_skew c (A q+B q)]
    abel

end FourSolutionCategory

namespace NormalizedFamily
open LieGrading UniversalEmbedding

theorem length_zero_piece (n : ℕ) : biPiece (R:=K) oddWeight (fun _ => 1) n 0=⊥ := by
  rw [←biTreeSpan_eq]
  apply le_antisymm ?_ bot_le
  apply Submodule.span_le.mpr
  rintro p ⟨t,_,ht,rfl⟩
  have h := treeDegree_pos (wt:=fun _ : ℕ => 1) (by intro; decide) t
  omega

theorem length_one_piece_le (k : ℕ) :
    biPiece (R:=K) oddWeight (fun _ => 1) (oddWeight k) 1≤
      Submodule.span K {FreeLieAlgebra.of K k} := by
  rw [←biTreeSpan_eq]
  apply Submodule.span_le.mpr
  rintro p ⟨t,ht,hr,rfl⟩
  cases t with
  | leaf j =>
    have hj : j=k := by
      simp only [treeDegree_leaf,oddWeight] at ht
      omega
    subst j
    exact Submodule.subset_span rfl
  | node t u =>
    have h₁ := treeDegree_pos (wt:=fun _ : ℕ => 1) (by intro; decide) t
    have h₂ := treeDegree_pos (wt:=fun _ : ℕ => 1) (by intro; decide) u
    simp only [treeDegree_node] at hr
    omega

theorem finrank_length_one_le (k : ℕ) :
    Module.finrank K (biPiece (R:=K) oddWeight (fun _ => 1) (oddWeight k) 1)≤1 := by
  have h := Submodule.finrank_mono (length_one_piece_le k)
  have h' := finrank_span_le_card (R:=K) ({FreeLieAlgebra.of K k} : Set (FreeLieAlgebra K ℕ))
  exact h.trans (by simpa using h')

abbrev OldDomain (n : ℕ) := (r : Fin (n+1)) → oldPiece n r.val

theorem finrank_odd_le (k : ℕ) :
    Module.finrank K (homogeneousLie (R:=K) oddWeight (oddWeight k))≤
      Module.finrank K (OldDomain (oddWeight k))+1 := by
  classical
  let n := oddWeight k
  rw [finrank_decomposition K oddWeight (fun _ => 1) n n (ReducedDimension.odd_length_bound n),Module.finrank_pi_fintype]
  have hterm (r : ℕ) :
      Module.finrank K (biPiece (R:=K) oddWeight (fun _ => 1) n r)≤
        Module.finrank K (oldPiece n r)+(if r=1 then 1 else 0) := by
    by_cases hr : 1<r
    · have he : oldPiece n r=biPiece (R:=K) oddWeight (fun _ => 1) n r := ite_eq_left hr
      rw [he]
      split_ifs <;> omega
    · have he : oldPiece n r=⊥ := ite_eq_right hr
      rw [he,finrank_bot,Nat.zero_add]
      by_cases hr1 : r=1
      · subst r
        rw [ite_eq_left rfl]
        exact finrank_length_one_le k
      · have hr0 : r=0 := by omega
        subst r
        rw [length_zero_piece,finrank_bot]
        split_ifs <;> omega
  have hs := Finset.sum_le_sum (fun (r : Fin (n+1)) (_ : r∈Finset.univ) => hterm r.val)
  rw [Finset.sum_add_distrib] at hs
  have hin : (1 : ℕ)<n+1 := by dsimp [n,oddWeight]; omega
  have hsum : (∑ r : Fin (n+1),if r.val=1 then (1:ℕ) else 0)=1 := by
    have hiff (r : Fin (n+1)) : r.val=1 ↔ r=⟨1,hin⟩ := by simp only [Fin.ext_iff]
    simp only [hiff]
    simp
  rwa [hsum] at hs

end NormalizedFamily

namespace IntegralFamily

section
open LieGrading AssociativeElimination UniversalEmbedding WordGrading
attribute [local instance] LieRing.ofAssociativeRing

variable (V : Values)

def depthPiece (n : ℕ) : Submodule ℚ (Wn n) :=
  piece V n ⊓ (above GenericIhara.depth 2).comap (embed.toLinearMap.comp (Wn n).subtype)

variable {V} (f : Family V)

theorem cast_depth (k : ℕ) : embed (cast f ℚ k)∈above GenericIhara.depth 1 :=
  GenericIhara.homogeneous_depth (by simp [oddWeight]) (cast_homogeneous f ℚ k)

theorem tree_depth_two (t : UniversalEmbedding.Tree ℕ) (ht : 1<treeDegree (fun _ => 1) t) :
    embed (GenericIhara.evalIhara (cast f ℚ) t.eval)∈above GenericIhara.depth 2 := by
  have h := GenericIhara.evalIhara_depth (cast f ℚ) (cast_depth f) (LieGrading.eval_homogeneous (fun _ => 1) t)
  exact WordGrading.space_mono (by intro w hw; change treeDegree (fun _ => 1) t≤degree GenericIhara.depth w at hw; omega) h

theorem tree_reduced_depth_mem {n : ℕ} (t : UniversalEmbedding.Tree ℕ)
    (ht : treeDegree oddWeight t=n) (hr : 1<treeDegree (fun _ => 1) t) :
    reducedValue f n ⟨t.eval,ht ▸ LieGrading.eval_homogeneous oddWeight t⟩∈
      SaturatedSolutions.reduction n (depthPiece V n) := by
  let q : homogeneousLie (R:=ℤ) RationalBound.wt n :=
    ⟨GenericIhara.evalIhara f.value t.eval,integral_eval_homogeneous f (ht ▸ LieGrading.eval_homogeneous oddWeight t)⟩
  have he : (LieDimension.castHom (R:=ℚ) q).val=GenericIhara.evalIhara (cast f ℚ) t.eval := by
    exact (GenericIhara.cast_evalIhara f.value t.eval).trans (congrArg _ (LieDimension.cast_eval t))
  have hW : (LieDimension.castHom (R:=ℚ) q).val∈Wn n := by
    constructor
    · rw [he]; exact V.le_W (rational_mem f t.eval)
    · change _∈weightPiece RationalBound.wt n
      rw [weightPiece_eq]; exact (LieDimension.castHom (R:=ℚ) q).property
  apply integral_reduction_mem (depthPiece V n) q hW ?_ _ ?_
  · constructor
    · change (LieDimension.castHom (R:=ℚ) q).val∈V.space
      rw [he]; exact rational_mem f t.eval
    · change embed (LieDimension.castHom (R:=ℚ) q).val∈above GenericIhara.depth 2
      rw [he]; exact tree_depth_two f t hr
  · change IntegralBaseChange.lie (S:=K) (GenericIhara.evalIhara f.value t.eval)=_
    rw [GenericIhara.cast_evalIhara,LieDimension.cast_eval]
    rfl

theorem bi_reduced_depth_mem {n r : ℕ} (hr : 1<r)
    (p : biPiece (R:=K) oddWeight (fun _ => 1) n r) :
    reducedValue f n ⟨p.val,p.property.1⟩∈SaturatedSolutions.reduction n (depthPiece V n) := by
  let E := SaturatedSolutions.reduction n (depthPiece V n)
  let T := E.map (ReducedDimension.solutions n).subtype
  have hp : p.val∈biTreeSpan (R:=K) oddWeight (fun _ => 1) n r :=
    (biTreeSpan_eq (R:=K) oddWeight (fun _ => 1) n r).symm ▸ p.property
  have hh : ∀ v,v∈biTreeSpan (R:=K) oddWeight (fun _ => 1) n r →
      GenericIhara.evalIhara (cast f K) v∈T := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨t,ht,hl,rfl⟩ := hq
      refine ⟨reducedValue f n ⟨t.eval,ht ▸ LieGrading.eval_homogeneous oddWeight t⟩,
        tree_reduced_depth_mem f t ht (by omega),rfl⟩
    | zero => rw [map_zero]; exact T.zero_mem
    | add p q _ _ hp hq => rw [map_add]; exact T.add_mem hp hq
    | smul c p _ hp => rw [map_smul]; exact T.smul_mem c hp
  obtain ⟨q,hq,he⟩ := hh p.val hp
  have he' : q=reducedValue f n ⟨p.val,p.property.1⟩ := Subtype.ext he
  rwa [←he']

theorem old_reduced_depth_mem {n r : ℕ} (p : NormalizedFamily.oldPiece n r) :
    reducedValue f n ⟨p.val,NormalizedFamily.oldPiece_le n r p.property⟩∈
      SaturatedSolutions.reduction n (depthPiece V n) := by
  by_cases hr : 1<r
  · have hp : p.val∈biPiece (R:=K) oddWeight (fun _ => 1) n r := by
      have he : NormalizedFamily.oldPiece n r=biPiece (R:=K) oddWeight (fun _ => 1) n r := ite_eq_left hr
      rw [←he]; exact p.property
    exact bi_reduced_depth_mem f hr ⟨p.val,hp⟩
  · have hp := NormalizedFamily.oldMap_low hr p
    subst p
    change reducedValue f n 0∈_
    rw [map_zero]
    exact Submodule.zero_mem _

end

section
open LieGrading AssociativeElimination UniversalEmbedding WordGrading
open ImageBound RowKernel QuadraticLeading RowTwo
attribute [local instance] LieRing.ofAssociativeRing

variable (V : Values)

structure Generator (k : ℕ) where
  value : FreeLieAlgebra ℤ Bool
  homogeneous : value∈homogeneousLie (fun _ => 1) (oddWeight k)
  member : IntegralBaseChange.lie (S:=ℚ) value∈V.space
  rep : FreeLieAlgebra K Slot
  under_rep : under rep=embed (IntegralBaseChange.lie (S:=K) value)
  above_rep : embed rep∈above bCount 1
  leading_rep : embed (leading 1 rep)=positiveInput (atom k)

variable {V}

def partialFamily (k : ℕ) (g : ∀ j,j<k → Generator V j) : Family V where
  value j := if h : j<k then (g j h).value else 0
  homogeneous j := by
    classical
    split_ifs with h
    · exact (g j h).homogeneous
    · exact Submodule.zero_mem _
  member j := by
    classical
    split_ifs with h
    · exact (g j h).member
    · rw [map_zero]; exact V.space.zero_mem

def partialData (k : ℕ) (g : ∀ j,j<k → Generator V j) : NormalizedFamily.Data where
  active j := j<k
  value := cast (partialFamily k g) K
  solution _ _ hp := reduced_solution (partialFamily k g) hp
  rep j := if h : j<k then (g j h).rep else 0
  under_rep j := by
    classical
    dsimp only [cast,partialFamily]
    split_ifs with h
    · exact (g j h).under_rep
    · simp only [map_zero]
  above_rep j h := by
    classical
    simpa only [dite_eq_left h] using (g j h).above_rep
  leading_rep j h := by
    classical
    simpa only [dite_eq_left h] using (g j h).leading_rep

variable (f : Family V) (g : NormalizedFamily.Data) (hg : g.value=cast f K)

include f hg in
theorem oldMap_mem {n r : ℕ} (p : NormalizedFamily.oldPiece n r) :
    NormalizedFamily.oldMap g n r p∈SaturatedSolutions.reduction n (depthPiece V n) := by
  have he : NormalizedFamily.oldMap g n r p=
      reducedValue f n ⟨p.val,NormalizedFamily.oldPiece_le n r p.property⟩ :=
    Subtype.ext (congrArg (fun v => GenericIhara.evalIhara v p.val) hg)
  rw [he]
  exact old_reduced_depth_mem f p

def oldToDepth (n : ℕ) : NormalizedFamily.OldDomain n →ₗ[K]
    SaturatedSolutions.reduction n (depthPiece V n) :=
  (Triangular.assemble (fun r : Fin (n+1) => NormalizedFamily.oldMap g n r.val)).codRestrict _ (by
    intro p
    rw [Triangular.assemble_apply]
    exact Submodule.sum_mem _ (fun r _ => oldMap_mem f g hg (p r)))

include f hg in
theorem old_rank_le (n : ℕ) (hn : 2<n) (ha : ∀ k,oddWeight k<n → g.active k) :
    Module.finrank K (NormalizedFamily.OldDomain n)≤Module.finrank ℚ (depthPiece V n) := by
  have hi : Function.Injective (oldToDepth f g hg n) := by
    intro p q he
    exact NormalizedFamily.old_assemble_injective g n (by omega) ha (congrArg Subtype.val he)
  have hh := LinearMap.finrank_le_finrank_of_injective hi
  rwa [SaturatedSolutions.finrank_reduction n (depthPiece V n) hn] at hh

theorem depth_rank_lt {n : ℕ} (p : Wn n) (hp : p∈piece V n)
    (hc : (embed p.val).coeff (GenericIhara.depthOneWord (n-1))≠0) :
    Module.finrank ℚ (depthPiece V n)<Module.finrank ℚ (piece V n) := by
  apply Submodule.finrank_lt_finrank_of_lt
  apply lt_of_le_not_ge inf_le_left
  intro h
  have hp' := (h hp).2
  exact hc (GenericIhara.depthOne_zero (by decide : 1<(2:ℕ)) hp' (n-1))

include f hg in
theorem dimension_sharp (k : ℕ) (ha : ∀ j,oddWeight j<oddWeight k → g.active j)
    (p : Wn (oddWeight k)) (hp : p∈piece V (oddWeight k))
    (hc : (embed p.val).coeff (GenericIhara.depthOneWord (oddWeight k-1))≠0) :
    Module.finrank ℚ (piece V (oddWeight k))=Module.finrank ℚ (Fn (oddWeight k)) := by
  have hn : 2<oddWeight k := by simp [oddWeight]
  have hlo := old_rank_le f g hg (oddWeight k) hn ha
  have hlt := depth_rank_lt p hp hc
  have hub : Module.finrank ℚ (Fn (oddWeight k))≤
      Module.finrank K (NormalizedFamily.OldDomain (oddWeight k))+1 := by
    change Module.finrank ℚ (weightPiece oddWeight (oddWeight k))≤_
    rw [weightPiece_eq,←LieDimension.finrank_homogeneous K oddWeight (oddWeight k)]
    exact NormalizedFamily.finrank_odd_le k
  have hupper := (Submodule.finrank_le (piece V (oddWeight k))).trans (RationalBound.finrank_Wn_le _ hn)
  omega

end

open LieGrading AssociativeElimination UniversalEmbedding WordGrading
open ImageBound RowKernel QuadraticLeading RowTwo
attribute [local instance] LieRing.ofAssociativeRing

variable (V : Values)

theorem generator_of_sharp (k : ℕ)
    (he : Module.finrank ℚ (piece V (oddWeight k))=Module.finrank ℚ (Fn (oddWeight k))) :
    Nonempty (Generator V k) := by
  have hn : 2<oddWeight k := by simp [oddWeight]
  let e : ReducedDimension.oddPiece (oddWeight k) 1 :=
    ⟨FreeLieAlgebra.of K k,LieGrading.eval_homogeneous oddWeight (.leaf k),
      LieGrading.eval_homogeneous (fun _ => 1) (.leaf k)⟩
  obtain ⟨p,hp⟩ := SaturatedSolutions.graded_surjective (oddWeight k) (piece V (oddWeight k)) hn he 1 (by omega) e
  obtain ⟨q,hq,hW,hV⟩ := SaturatedSolutions.reduction_lift (oddWeight k) (piece V (oddWeight k)) hn p.val
  refine ⟨⟨q.val,q.property,hV,ReducedDimension.representation (oddWeight k) (by omega) p.val.val,?_,?_,?_⟩⟩
  · rw [ReducedDimension.representation_under,←hq]
    rfl
  · exact p.property
  · have hs := ReducedDimension.gradedMap_spec (oddWeight k) hn 1
      (SaturatedSolutions.inclusionFiltration (oddWeight k) (piece V (oddWeight k)) (by omega) 1 p)
    have he' := congrArg (ReducedDimension.inclusion (oddWeight k) 1) hp
    change ReducedDimension.inclusion (oddWeight k) 1 (SaturatedSolutions.gradedMap (oddWeight k) (piece V (oddWeight k)) hn 1 p)=positiveInput (embed (FreeLieAlgebra.of K k)) at he'
    rw [AssociativeElimination.embed_of] at he'
    exact hs.symm.trans he'

def OddValues : Prop := ∀ k,∃ p : Wn (oddWeight k),p∈piece V (oddWeight k) ∧
  (embed p.val).coeff (GenericIhara.depthOneWord (oddWeight k-1))≠0

theorem generators_exist (hv : OddValues V) : ∀ k,Nonempty (Generator V k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k hi =>
    classical
    let g : ∀ j,j<k → Generator V j := fun j hj => Classical.choice (hi j hj)
    obtain ⟨p,hp,hc⟩ := hv k
    apply generator_of_sharp V k
    apply dimension_sharp (partialFamily k g) (partialData k g) rfl k ?_ p hp hc
    intro j hj
    change j<k
    simp only [oddWeight] at hj
    omega

noncomputable def generators (hv : OddValues V) (k : ℕ) : Generator V k :=
  Classical.choice (generators_exist V hv k)

def normalizedFamily (hv : OddValues V) : Family V where
  value k := (generators V hv k).value
  homogeneous k := (generators V hv k).homogeneous
  member k := (generators V hv k).member

def normalizedData (hv : OddValues V) : NormalizedFamily.Data where
  active _ := True
  value := cast (normalizedFamily V hv) K
  solution _ _ hp := reduced_solution (normalizedFamily V hv) hp
  rep k := (generators V hv k).rep
  under_rep k := (generators V hv k).under_rep
  above_rep k _ := (generators V hv k).above_rep
  leading_rep k _ := (generators V hv k).leading_rep

end IntegralFamily

end DeligneDrinfeld

end

end OAI
