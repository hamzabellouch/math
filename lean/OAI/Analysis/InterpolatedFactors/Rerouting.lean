import OAI.Analysis.InterpolatedFactors.Polar

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace FreeGroupFactorMain.CornerRerouting

section
variable {A : Type u_1} [Ring A] [StarRing A]

 def Supported (p x : A) : Prop := p*x=x ∧ x*p=x
 def lift (v t : A) : A := t+star v*t*v

omit [StarRing A] in
 theorem right_zero {p v : A} (h : v*(1-p)=v) : v*p=0 := by
  have hh : v-v*p=v := by simpa only [mul_sub,mul_one] using h
  exact sub_eq_self.mp hh

 theorem star_left_zero {p v : A} (hp : IsSelfAdjoint p) (h : v*p=0) : p*star v=0 := by
  have hh := congrArg star h
  simpa only [star_mul,hp.star_eq,star_zero] using hh

 theorem supported_star {p t : A} (hp : IsSelfAdjoint p) (ht : Supported p t) :
    Supported p (star t) := by
  constructor
  · simpa only [star_mul,hp.star_eq] using congrArg star ht.2
  · simpa only [star_mul,hp.star_eq] using congrArg star ht.1

 theorem supported_mul_star_zero {p v t : A} (hvp : v*p=0) (hp : IsSelfAdjoint p)
    (ht : Supported p t) : t*star v=0 := by
  calc
    _ = (t*p)*star v := by rw [ht.2]
    _ = t*(p*star v) := mul_assoc _ _ _
    _ = 0 := by rw [star_left_zero hp hvp,mul_zero]

omit [StarRing A] in
 theorem mul_supported_zero {p v t : A} (hvp : v*p=0) (ht : Supported p t) : v*t=0 := by
  calc
    _ = v*(p*t) := by rw [ht.1]
    _ = (v*p)*t := (mul_assoc _ _ _).symm
    _ = 0 := by rw [hvp,zero_mul]

 theorem lift_mul_supported {p v t y : A} (hvp : v*p=0) (hy : Supported p y) :
    lift v t*y=t*y := by
  unfold lift
  rw [add_mul,mul_assoc (star v*t),mul_supported_zero hvp hy,mul_zero,add_zero]

 theorem supported_mul_lift {p v t y : A} (hp : IsSelfAdjoint p) (hvp : v*p=0)
    (hy : Supported p y) : y*lift v t=y*t := by
  unfold lift
  rw [mul_add,← mul_assoc y,← mul_assoc y,supported_mul_star_zero hvp hp hy,
    zero_mul,zero_mul,add_zero]

 theorem lift_commute_supported {p v t y : A} (hp : IsSelfAdjoint p) (hvp : v*p=0)
    (hy : Supported p y) (h : Commute t y) : Commute (lift v t) y := by
  change lift v t*y=y*lift v t
  rw [lift_mul_supported hvp hy,supported_mul_lift hp hvp hy]
  exact h.eq

omit [StarRing A] in
 theorem square_zero {p v : A} (hpv : p*v=v) (hvp : v*p=0) : v*v=0 := by
  calc
    _ = v*(p*v) := by rw [hpv]
    _ = (v*p)*v := (mul_assoc _ _ _).symm
    _ = 0 := by rw [hvp,zero_mul]

 theorem range_mul {p v : A} (hi : star v*v=1-p) (hr : v*(1-p)=v) :
    (v*star v)*v=v := by rw [mul_assoc,hi,hr]

 theorem lift_commute_edge {p v t : A} (hpv : p*v=v) (hvp : v*p=0)
    (hi : star v*v=1-p) (hr : v*(1-p)=v) (ht : Supported p t)
    (htr : Commute t (v*star v)) : Commute (lift v t) v := by
  change lift v t*v=v*lift v t
  have hleft : lift v t*v=t*v := by
    unfold lift
    rw [add_mul,mul_assoc (star v*t),square_zero hpv hvp,mul_zero,add_zero]
  have hright : v*lift v t=t*v := by
    unfold lift
    rw [mul_add,mul_supported_zero hvp ht,zero_add,← mul_assoc v,← mul_assoc v,
      ← htr.eq,mul_assoc t,range_mul hi hr]
  exact hleft.trans hright.symm

 theorem star_lift (v t : A) : star (lift v t)=lift v (star t) := by
  simp only [lift,star_add,star_mul,star_star,mul_assoc]

 theorem lift_commute_edge_star {p v t : A} (hp : IsSelfAdjoint p)
    (hpv : p*v=v) (hvp : v*p=0) (hi : star v*v=1-p) (hr : v*(1-p)=v)
    (ht : Supported p t) (htr : Commute t (v*star v)) :
    Commute (lift v t) (star v) := by
  have hs : Commute (star t) (v*star v) := by
    simpa only [star_mul,star_star] using htr.star_star
  have hh := (lift_commute_edge hpv hvp hi hr (supported_star hp ht) hs).star_star
  simpa only [star_lift,star_star] using hh

 def diagonal (p s : A) : A := p*s*p
 def offDiagonal (p v s : A) : A := p*s*(1-p)*star v
 def remaining (p v s : A) : A := v*(1-p)*s*(1-p)*star v

omit [StarRing A] in
 theorem diagonal_supported {p s : A} (hp : IsIdempotentElem p) : Supported p (diagonal p s) := by
  constructor
  · simp only [diagonal,← mul_assoc,hp.eq]
  · simp only [diagonal,mul_assoc,hp.eq]

 theorem offDiagonal_supported {p v s : A} (hp : IsStarProjection p) (hpv : p*v=v) :
    Supported p (offDiagonal p v s) := by
  have hvsp : star v*p=star v := by
    simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hpv
  constructor
  · simp only [offDiagonal,← mul_assoc,hp.isIdempotentElem.eq]
  · simp only [offDiagonal,mul_assoc,hvsp]

 theorem remaining_supported {p v s : A} (hp : IsSelfAdjoint p) (hpv : p*v=v) :
    Supported p (remaining p v s) := by
  have hvsp : star v*p=star v := by
    simpa only [star_mul,hp.star_eq] using congrArg star hpv
  constructor
  · simp only [remaining,← mul_assoc,hpv]
  · simp only [remaining,mul_assoc,hvsp]

 theorem reconstruct {p v s : A} (hp : IsStarProjection p) (hi : star v*v=1-p)
    (hs : IsSelfAdjoint s) :
    s=diagonal p s + offDiagonal p v s*v + star v*star (offDiagonal p v s) +
      star v*remaining p v s*v := by
  have hq : (1-p)*(1-p)=1-p := hp.one_sub.isIdempotentElem.eq
  have h₁ : offDiagonal p v s*v=p*s*(1-p) := by
    simp only [offDiagonal,mul_assoc,hi]
    rw [hq]
  have h₂ : star v*star (offDiagonal p v s)=(1-p)*s*p := by
    unfold offDiagonal
    rw [star_mul,star_mul,star_mul,star_star,star_sub,star_one,
      hp.isSelfAdjoint.star_eq,hs.star_eq]
    simp only [← mul_assoc,hi,hq]
  have h₃ : star v*remaining p v s*v=(1-p)*s*(1-p) := by
    simp only [remaining,← mul_assoc,hi,hq]
    simp only [mul_assoc,hi]
    rw [← mul_assoc (1-p),hq,mul_assoc]
  rw [h₁,h₂,h₃,diagonal]
  noncomm_ring

 theorem lift_commute_generator {p v t s : A} (hp : IsStarProjection p)
    (hpv : p*v=v) (hr : v*(1-p)=v) (hi : star v*v=1-p)
    (ht : Supported p t) (hs : IsSelfAdjoint s)
    (htr : Commute t (v*star v)) (ha : Commute t (diagonal p s))
    (hb : Commute t (offDiagonal p v s)) (hbs : Commute t (star (offDiagonal p v s)))
    (hc : Commute t (remaining p v s)) : Commute (lift v t) s := by
  have hvp := right_zero hr
  have ha' := lift_commute_supported hp.isSelfAdjoint hvp (diagonal_supported hp.isIdempotentElem) ha
  have hb' := lift_commute_supported hp.isSelfAdjoint hvp (offDiagonal_supported hp hpv) hb
  have hbs' := lift_commute_supported hp.isSelfAdjoint hvp
    (supported_star hp.isSelfAdjoint (offDiagonal_supported hp hpv)) hbs
  have hc' := lift_commute_supported hp.isSelfAdjoint hvp (remaining_supported hp.isSelfAdjoint hpv) hc
  have hv' := lift_commute_edge hpv hvp hi hr ht htr
  have hvs' := lift_commute_edge_star hp.isSelfAdjoint hpv hvp hi hr ht htr
  rw [reconstruct hp hi hs]
  exact ((ha'.add_right (hb'.mul_right hv')).add_right (hvs'.mul_right hbs')).add_right
    ((hvs'.mul_right hc').mul_right hv')

end
section
variable {A : Type u_2} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {ι : Type u_3}

 theorem corner_bicommutant {p v x t : A} {s : ι → A}
    (hp : IsStarProjection p) (hpv : p*v=v) (hr : v*(1-p)=v) (hi : star v*v=1-p)
    (hx : x ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (insert p (Set.range s)) : Set A))
    (hxs : Supported p x) (ht : Supported p t) (hs : ∀ i, IsSelfAdjoint (s i))
    (htr : Commute t (v*star v)) (ha : ∀ i, Commute t (diagonal p (s i)))
    (hb : ∀ i, Commute t (offDiagonal p v (s i)))
    (hbs : ∀ i, Commute t (star (offDiagonal p v (s i))))
    (hc : ∀ i, Commute t (remaining p v (s i))) : Commute t x := by
  have hvp := right_zero hr
  have htp : Commute t p := ht.2.trans ht.1.symm
  have hpp : Supported p p := ⟨hp.isIdempotentElem.eq,hp.isIdempotentElem.eq⟩
  have hLP := lift_commute_supported hp.isSelfAdjoint hvp hpp htp
  have hLS (i : ι) : Commute (lift v t) (s i) :=
    lift_commute_generator hp hpv hr hi ht (hs i) htr (ha i) (hb i) (hbs i) (hc i)
  have hL : lift v t ∈ StarSubalgebra.centralizer ℂ (insert p (Set.range s)) := by
    rw [StarSubalgebra.mem_centralizer_iff]
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | ⟨i,rfl⟩
    · exact ⟨hLP.symm,by simpa only [hp.isSelfAdjoint.star_eq] using hLP.symm.eq⟩
    · exact ⟨(hLS i).symm,by simpa only [(hs i).star_eq] using (hLS i).symm.eq⟩
  have he := ((StarSubalgebra.mem_centralizer_iff ℂ).mp hx (lift v t) hL).1
  change t*x=x*t
  simpa only [lift_mul_supported hvp hxs,supported_mul_lift hp.isSelfAdjoint hvp hxs] using he

end
variable {A : Type u_4} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

theorem single_edge_corner_abelian {p v x a b : A}
    (hp : IsStarProjection p) (hpv : p*v=v) (hvr : v*(1-p)=v)
    (hvi : star v*v=1-p) (hpx : p*x=x) (hxr : x*(1-p)=x)
    (hd : IsSelfAdjoint (x*star v))
    (ha : a ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (insert p {x+star x}) : Set A))
    (hb : b ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (insert p {x+star x}) : Set A))
    (has : Supported p a) (hbs : Supported p b) : Commute a b := by
  have hxp : x*p=0 := right_zero hxr
  have hpsx : p*star x=0 := star_left_zero hp.isSelfAdjoint hxp
  have hsxp : star x*p=star x := by
    simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hpx
  have hqpx : (1-p)*x=0 := by rw [sub_mul,one_mul,hpx,sub_self]
  have hsxq : star x*(1-p)=0 := by rw [mul_sub,mul_one,hsxp,sub_self]
  let d := x*star v
  let r := v*star v
  have hsd : star d=d := hd
  have hsr : star r=r := by simp only [r,star_mul,star_star]
  have hdr : d*r=d := by
    dsimp [d,r]
    rw [mul_assoc x,← mul_assoc (star v),hvi,← mul_assoc,hxr]
  have hrd : r*d=d := by
    simpa only [star_mul,hsr,hsd] using congrArg star hdr
  have hrdc : Commute r d := hrd.trans hdr.symm
  have hpsv : star v*p=star v := by
    simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hpv
  have hds : Supported p d := by
    constructor
    · dsimp [d]; rw [← mul_assoc,hpx]
    · dsimp [d]; rw [mul_assoc,hpsv]
  have hrs : Supported p r := by
    constructor
    · dsimp [r]; rw [← mul_assoc,hpv]
    · dsimp [r]; rw [mul_assoc,hpsv]
  let s : Unit → A := fun _ => x+star x
  have hsa : ∀ i, IsSelfAdjoint (s i) := by
    intro i
    show star (x+star x)=x+star x
    simp only [star_add,star_star,add_comm]
  have hset : Set.range s={x+star x} := by ext z; simp [s]
  have hdiag (i : Unit) : diagonal p (s i)=0 := by
    dsimp [diagonal,s]
    rw [mul_add,hpx,hpsx,add_zero,hxp]
  have hoff (i : Unit) : offDiagonal p v (s i)=d := by
    dsimp [offDiagonal,s,d]
    rw [mul_add,hpx,hpsx,add_zero,hxr]
  have hrem (i : Unit) : remaining p v (s i)=0 := by
    dsimp [remaining,s]
    rw [mul_assoc v (1-p),mul_add,hqpx,zero_add,← mul_assoc,
      mul_assoc (v*(1-p)),hsxq,mul_zero,zero_mul]
  have hA : a ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (insert p (Set.range s)) : Set A) := by
    simpa only [hset] using ha
  have hB : b ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (insert p (Set.range s)) : Set A) := by
    simpa only [hset] using hb
  have had : Commute d a := by
    apply corner_bicommutant hp hpv hvr hvi hA has hds hsa hrdc.symm
    · intro i; rw [hdiag i]; exact Commute.zero_right _
    · intro i; rw [hoff i]
    · intro i; rw [hoff i,hsd]
    · intro i; rw [hrem i]; exact Commute.zero_right _
  have har : Commute r a := by
    apply corner_bicommutant hp hpv hvr hvi hA has hrs hsa (Commute.refl _)
    · intro i; rw [hdiag i]; exact Commute.zero_right _
    · intro i; rw [hoff i]; exact hrdc
    · intro i; rw [hoff i,hsd]; exact hrdc
    · intro i; rw [hrem i]; exact Commute.zero_right _
  apply corner_bicommutant hp hpv hvr hvi hB hbs has hsa har.symm
  · intro i; rw [hdiag i]; exact Commute.zero_right _
  · intro i; rw [hoff i]; exact had.symm
  · intro i; rw [hoff i,hsd]; exact had.symm
  · intro i; rw [hrem i]; exact Commute.zero_right _

end FreeGroupFactorMain.CornerRerouting
namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock Amplification.Polar
variable {ι : Type u_5} [DecidableEq ι]

def edgeAlgebra (u v : ℝ) (i : ι) : StarSubalgebra ℂ (Operator ι) :=
  StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ
      (insert P {offDiagonal u v i+star (offDiagonal u v i)}) : Set (Operator ι))

theorem edge_left_modulus_selfAdjoint (u v : ℝ) (i : ι) :
    IsSelfAdjoint (offDiagonal u v i*star (edgePolar u v i)) := by
  have hf := partialIsometry_factorization (offDiagonal u v i)
  change edgePolar u v i*modulus (offDiagonal u v i)=offDiagonal u v i at hf
  rw [← hf]
  change star ((edgePolar u v i*modulus (offDiagonal u v i))*star (edgePolar u v i))=_
  simp only [star_mul,star_star,modulus_star,mul_assoc]

theorem edge_corner_commutative (u v : ℝ) (hv : 0 ≤ v) (hvu : v<u) (i : ι)
    (a b : edgeAlgebra u v i)
    (ha : CornerRerouting.Supported P (a : Operator ι))
    (hb : CornerRerouting.Supported P (b : Operator ι)) :
    Commute (a : Operator ι) (b : Operator ι) :=
  CornerRerouting.single_edge_corner_abelian projection_P
    (edgePolar_left u v i) (edgePolar_right u v i) (edgePolar_initial u v hv hvu i)
    (offDiagonal_left u v i) (offDiagonal_right u v i)
    (edge_left_modulus_selfAdjoint u v i) a.property b.property ha hb

end
section
open FreeFock
variable {ι : Type u_6} [DecidableEq ι]

def rightInsertEmbedding (j : ι) (w : Path ι) : Path ι ↪ Path ι :=
  ⟨fun x => (x.1 ++ [(j,x.2)] ++ w.1,w.2), by
    rintro ⟨a,r⟩ ⟨b,s⟩ h
    have h₁ := List.append_cancel_right (Prod.mk.inj h).1
    have h₂ := List.append_singleton_inj.mp h₁
    exact Prod.ext h₂.1 (Prod.mk.inj h₂.2).2⟩

def rightInsert (j : ι) (w : Path ι) : Operator ι :=
  (hilbertEmbedding (rightInsertEmbedding j w)).toContinuousLinearMap

@[simp] theorem rightInsert_single (j : ι) (w x : Path ι) (z : ℂ) :
    rightInsert j w (lp.single 2 x z)=
      lp.single 2 (x.1++[(j,x.2)]++w.1,w.2) z :=
  hilbertEmbedding_single (rightInsertEmbedding j w) x z

theorem P_commute_rightInsert (j : ι) (w : Path ι) :
    Commute (P : Operator ι) (rightInsert j w) := by
  apply CoordinateProjection.commute_embedding
  rintro ⟨a,r⟩
  cases a with
  | nil => rfl
  | cons k a => cases k; rfl

theorem creation_commute_rightInsert (i j : ι) (r : Bool) (w : Path ι) :
    Commute (creation i r) (rightInsert j w) := by
  change _*_=_*_
  apply operator_basis_ext
  intro x
  simp only [mul_apply_eq_comp,rightInsert_single,creation_single,List.cons_append]

def vacuumTo (w : Path ι) (r : Bool) : Operator ι :=
  InnerProductSpace.rankOne ℂ (lp.single 2 w 1) (lp.single 2 ([],r) 1)

@[simp] theorem vacuumTo_nil (w : Path ι) (r s : Bool) (z : ℂ) :
    vacuumTo w r (lp.single 2 ([],s) z)=if r=s then lp.single 2 w z else 0 := by
  classical
  by_cases h : r=s
  · subst s
    ext x
    simp [vacuumTo,InnerProductSpace.rankOne_apply,lp.inner_single_left,
      lp.single_apply,Pi.single_apply]
  · simp [vacuumTo,InnerProductSpace.rankOne_apply,lp.inner_single_left,
      lp.single_apply,h]

@[simp] theorem vacuumTo_cons (w : Path ι) (r s e : Bool) (i : ι)
    (a : List (ι×Bool)) (z : ℂ) :
    vacuumTo w r (lp.single 2 ((i,s)::a,e) z)=0 := by
  simp [vacuumTo,InnerProductSpace.rankOne_apply,lp.inner_single_left,lp.single_apply]

theorem annihilation_rightInsert (i j : ι) (r : Bool) (w : Path ι) :
    star (creation i r)*rightInsert j w=rightInsert j w*star (creation i r)+
      if i=j then vacuumTo w r else 0 := by
  apply operator_basis_ext
  rintro ⟨a,e⟩
  cases a with
  | nil =>
    simp only [mul_apply_eq_comp,add_apply,rightInsert_single,List.nil_append,
      List.singleton_append,annihilation_single_cons,annihilation_single_nil,map_zero,zero_add]
    by_cases h : i=j
    · subst j
      simp [vacuumTo_nil]
    · simp only [Prod.mk.injEq,h,false_and,ite_false]
      rfl
  | cons k a =>
    rcases k with ⟨k,s⟩
    simp only [mul_apply_eq_comp,add_apply,rightInsert_single,List.cons_append,
      annihilation_single_cons]
    have hm : (if i=j then vacuumTo w r else 0) (lp.single 2 ((k,s)::a,e) 1)=0 := by
      split_ifs <;> simp
    rw [hm,add_zero]
    by_cases h : (i,r)=(k,s)
    · simp only [h,ite_true,rightInsert_single]
    · simp only [h,ite_false,map_zero]

theorem S_commute_rightInsert (u v : ℝ) (i j : ι) (hij : i≠j) (w : Path ι) :
    Commute (S u v i) (rightInsert j w) := by
  have ha (r : Bool) : Commute (star (creation i r)) (rightInsert j w) := by
    change _*_=_*_
    simpa only [hij,ite_false,add_zero] using annihilation_rightInsert i j r w
  simp only [S,star_add (R := Operator ι),star_smul,Complex.star_def,Complex.conj_ofReal]
  exact (((creation_commute_rightInsert i j true w).smul_left _).add_left
    ((creation_commute_rightInsert i j false w).smul_left _)).add_left
      (((ha true).smul_left _).add_left ((ha false).smul_left _))

def oldPaths (J : Set ι) : Set (Path ι) := {w | ∀ x∈w.1, x.1∈J}
def oldProjection (J : Set ι) : Operator ι := CoordinateProjection.proj (oldPaths J)
def oldAlgebra (u v : ℝ) (J : Set ι) : StarSubalgebra ℂ (Operator ι) :=
  StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ
    (insert P ((S u v) '' J)) : Set (Operator ι))

theorem oldProjection_commute_creation (J : Set ι) (i : ι) (hi : i∈J) (r : Bool) :
    Commute (oldProjection J) (creation i r) := by
  apply CoordinateProjection.commute_embedding
  intro w
  change (∀ x∈(i,r)::w.1, x.1∈J) ↔ (∀ x∈w.1, x.1∈J)
  simp [hi]

theorem oldProjection_commute_S (u v : ℝ) (J : Set ι) (i : ι) (hi : i∈J) :
    Commute (oldProjection J) (S u v i) := by
  have ha (r : Bool) := (oldProjection_commute_creation J i hi r).star_star
  have hp : star (oldProjection J)=oldProjection J := CoordinateProjection.star_proj _
  simp only [hp] at ha
  simp only [S,star_add (R := Operator ι),star_smul,Complex.star_def,Complex.conj_ofReal]
  exact (((oldProjection_commute_creation J i hi true).smul_right _).add_right
    ((oldProjection_commute_creation J i hi false).smul_right _)).add_right
      (((ha true).smul_right _).add_right ((ha false).smul_right _))

theorem oldProjection_mem_commutant (u v : ℝ) (J : Set ι) :
    oldProjection J ∈ StarSubalgebra.centralizer ℂ (insert P ((S u v) '' J)) := by
  rw [StarSubalgebra.mem_centralizer_iff]
  intro T hT
  rcases hT with hT | ⟨i,hi,rfl⟩
  · subst T
    have hc : Commute (oldProjection J) P := CoordinateProjection.commute _ _
    exact ⟨hc.eq.symm, by rw [projection_P.isSelfAdjoint.star_eq]; exact hc.eq.symm⟩
  · have hc := oldProjection_commute_S u v J i hi
    exact ⟨hc.eq.symm, by rw [(S_selfAdjoint u v i).star_eq]; exact hc.eq.symm⟩

theorem rightInsert_mem_oldCommutant (u v : ℝ) (J : Set ι)
    (j : ι) (hj : j∉J) (w : Path ι) :
    rightInsert j w ∈ StarSubalgebra.centralizer ℂ (insert P ((S u v) '' J)) := by
  rw [StarSubalgebra.mem_centralizer_iff]
  intro T hT
  rcases hT with hT | ⟨i,hi,rfl⟩
  · subst T
    have hc := P_commute_rightInsert j w
    exact ⟨hc.eq,by rw [projection_P.isSelfAdjoint.star_eq]; exact hc.eq⟩
  · have hij : i≠j := by rintro rfl; exact hj hi
    have hc := S_commute_rightInsert u v i j hij w
    exact ⟨hc.eq,by rw [(S_selfAdjoint u v i).star_eq]; exact hc.eq⟩

theorem annihilation_oldProjection (J : Set ι) (i : ι) (hi : i∉J) (r : Bool) :
    star (creation i r)*oldProjection J=0 := by
  apply operator_basis_ext
  rintro ⟨a,e⟩
  cases a with
  | nil => simp [mul_apply_eq_comp,oldProjection,CoordinateProjection.proj_single,
      oldPaths,annihilation_single_nil]
  | cons k a =>
    rcases k with ⟨j,s⟩
    by_cases h : ((j,s)::a,e)∈oldPaths J
    · have hj : j∈J := h (j,s) (List.mem_cons_self ..)
      have hij : i≠j := by rintro rfl; exact hi hj
      simp [mul_apply_eq_comp,oldProjection,CoordinateProjection.proj_single,h,
        annihilation_single_cons,Prod.mk.injEq,hij]
    · simp [mul_apply_eq_comp,oldProjection,CoordinateProjection.proj_single,h]

theorem old_root_fixed (u v : ℝ) (J : Set ι) (T : oldAlgebra u v J) (s : Bool) :
    oldProjection J ((T : Operator ι) (lp.single 2 ([],s) 1))=
      (T : Operator ι) (lp.single 2 ([],s) 1) := by
  have hc := ((StarSubalgebra.mem_centralizer_iff ℂ).mp T.property _
    (oldProjection_mem_commutant u v J)).1
  have ht := DFunLike.congr_fun hc (lp.single 2 ([],s) 1)
  simpa only [mul_apply_eq_comp,oldProjection,CoordinateProjection.proj_single,
    oldPaths,Set.mem_ofPred_eq,List.not_mem_nil,forall_const,false_implies,
    implies_true,ite_true] using ht

theorem annihilation_old_root (u v : ℝ) (J : Set ι) (i : ι) (hi : i∉J)
    (T : oldAlgebra u v J) (r s : Bool) :
    star (creation i r) ((T : Operator ι) (lp.single 2 ([],s) 1))=0 := by
  have ht := DFunLike.congr_fun (annihilation_oldProjection J i hi r)
    ((T : Operator ι) (lp.single 2 ([],s) 1))
  simpa only [mul_apply_eq_comp,old_root_fixed,zero_apply] using ht

@[simp] theorem vacuumTo_apply (w : Path ι) (r : Bool) (ξ : H ι) :
    vacuumTo w r ξ=ξ ([],r) • lp.single 2 w 1 := by
  simp [vacuumTo,InnerProductSpace.rankOne_apply,lp.inner_single_left,RCLike.inner_apply]

theorem fresh_creation_contraction (u v : ℝ) (J : Set ι)
    (i j : ι) (hi : i∉J) (hj : j∉J) (T : oldAlgebra u v J) (r s : Bool) :
    star (creation i r)*(T : Operator ι)*creation j s=
      if i=j then (((T : Operator ι) (lp.single 2 ([],s) 1)) ([],r)) • 1 else 0 := by
  apply operator_basis_ext
  intro w
  have hc := ((StarSubalgebra.mem_centralizer_iff ℂ).mp T.property _
    (rightInsert_mem_oldCommutant u v J j hj w)).1
  have ht := DFunLike.congr_fun hc (lp.single 2 ([],s) 1)
  simp only [mul_apply_eq_comp,rightInsert_single,List.nil_append,List.singleton_append] at ht
  have ha := DFunLike.congr_fun (annihilation_rightInsert i j r w)
    ((T : Operator ι) (lp.single 2 ([],s) 1))
  simp only [mul_apply_eq_comp,add_apply,annihilation_old_root u v J i hi T,
    map_zero,zero_add] at ha
  simp only [mul_apply_eq_comp,creation_single,← ht,ha]
  by_cases hij : i=j
  · simp only [hij,ite_true,vacuumTo_apply,_root_.smul_apply,one_apply_eq_self]
  · simp only [hij,ite_false,zero_apply]

theorem vacuumTrace_root_expansion (u v : ℝ) (T : Operator ι) :
    vacuumTrace u v T =
      (u:ℂ)*(u:ℂ)*(T (lp.single 2 ([],true) 1)) ([],true) +
      (u:ℂ)*(v:ℂ)*(T (lp.single 2 ([],false) 1)) ([],true) +
      (v:ℂ)*(u:ℂ)*(T (lp.single 2 ([],true) 1)) ([],false) +
      (v:ℂ)*(v:ℂ)*(T (lp.single 2 ([],false) 1)) ([],false) := by
  simp only [vacuumTrace,vacuum,map_add,map_smul,inner_add_left,inner_add_right,
    inner_smul_left,inner_smul_right,lp.inner_single_left,RCLike.inner_apply,
    map_one,Complex.conj_ofReal]
  ring

theorem fresh_C_contraction (u v : ℝ) (J : Set ι)
    (i j : ι) (hi : i∉J) (hj : j∉J) (T : oldAlgebra u v J) :
    star (C u v i)*(T : Operator ι)*C u v j=
      if i=j then vacuumTrace u v (T : Operator ι) • 1 else 0 := by
  simp only [C,star_add (R := Operator ι),star_smul,Complex.star_def,Complex.conj_ofReal,
    add_mul,mul_add,smul_mul_assoc,mul_smul_comm,
    fresh_creation_contraction u v J i j hi hj T]
  by_cases h : i=j
  · simp only [h,ite_true,smul_smul,
      ← add_smul (R := ℂ) (M := Operator ι)]
    rw [vacuumTrace_root_expansion]
    congr 1
    ring
  · simp only [h,ite_false,smul_zero (M := ℂ) (A := Operator ι),add_zero]

theorem fresh_block_covariance (u v : ℝ) (J : Set ι)
    (i j : ι) (hi : i∉J) (hj : j∉J) (a b c d : oldAlgebra u v J) :
    star ((a : Operator ι)*C u v i*(b : Operator ι))*
      ((c : Operator ι)*C u v j*(d : Operator ι))=
      if i=j then vacuumTrace u v (star (a : Operator ι)*(c : Operator ι)) •
        (star (b : Operator ι)*(d : Operator ι)) else 0 := by
  have hc := fresh_C_contraction u v J i j hi hj (star a*c)
  change star (C u v i)*(star (a : Operator ι)*(c : Operator ι))*C u v j=_ at hc
  calc
    _ = star (b : Operator ι)*
        (star (C u v i)*(star (a : Operator ι)*(c : Operator ι))*C u v j)*
        (d : Operator ι) := by simp only [star_mul,mul_assoc]
    _ = _ := by
      rw [hc]
      split_ifs <;> simp only [mul_smul_comm,smul_mul_assoc,mul_one,mul_zero,zero_mul]
      rfl

theorem fresh_C_annihilates_old_vacuum (u v : ℝ) (J : Set ι)
    (i : ι) (hi : i∉J) (T : oldAlgebra u v J) :
    star (C u v i) ((T : Operator ι) (vacuum u v))=0 := by
  simp only [vacuum,C,star_add (R := Operator ι),star_smul,Complex.star_def,Complex.conj_ofReal,
    map_add,map_smul,add_apply,_root_.smul_apply,
    annihilation_old_root u v J i hi T,smul_zero,add_zero]

end

section
open FreeFock
variable {ι : Type u_7} [DecidableEq ι]

def terminalVertex (r : Bool) : Operator ι := CoordinateProjection.proj {w | w.2=r}
def edgeCreation (i : ι) (r s : Bool) : Operator ι := creation i r*vertex s

theorem vertex_eq_proj (r : Bool) : (vertex r : Operator ι)=
    CoordinateProjection.proj {w | start w=r} := by
  classical
  apply operator_basis_ext
  intro w
  by_cases h : start w=r <;> simp [vertex_single,CoordinateProjection.proj_single,h]

@[simp] theorem vertex_star (r : Bool) : star (vertex r : Operator ι)=vertex r := by
  rw [vertex_eq_proj,CoordinateProjection.star_proj]
omit [DecidableEq ι] in
@[simp] theorem terminalVertex_star (r : Bool) : star (terminalVertex r : Operator ι)=terminalVertex r :=
  CoordinateProjection.star_proj _
@[simp] theorem terminalVertex_single (r : Bool) (w : Path ι) (z : ℂ) :
    terminalVertex r (lp.single 2 w z)=if w.2=r then lp.single 2 w z else 0 := by
  classical
  by_cases h : w.2=r <;> simp [terminalVertex,CoordinateProjection.proj_single,h]

@[simp] theorem edgeCreation_single (i : ι) (r s : Bool) (w : Path ι) (z : ℂ) :
    edgeCreation i r s (lp.single 2 w z)=
      if start w=s then lp.single 2 ((i,r)::w.1,w.2) z else 0 := by
  simp only [edgeCreation,mul_apply_eq_comp,vertex_single]
  split_ifs <;> simp only [creation_single,map_zero]

@[simp] theorem edgeAnnihilation_nil (i : ι) (r s e : Bool) (z : ℂ) :
    star (edgeCreation i r s) (lp.single 2 ([],e) z)=0 := by
  simp only [edgeCreation,star_mul,vertex_star,mul_apply_eq_comp,annihilation_single_nil,map_zero]

@[simp] theorem edgeAnnihilation_cons (i j : ι) (r s t e : Bool)
    (w : List (ι×Bool)) (z : ℂ) :
    star (edgeCreation i r s) (lp.single 2 ((j,t)::w,e) z)=
      if (i,r)=(j,t) ∧ start (w,e)=s then lp.single 2 (w,e) z else 0 := by
  simp only [edgeCreation,star_mul,vertex_star,mul_apply_eq_comp,annihilation_single_cons]
  by_cases h : (i,r)=(j,t) <;> simp [h]

 theorem vertex_commute_rightInsert (r : Bool) (j : ι) (w : Path ι) :
    Commute (vertex r : Operator ι) (rightInsert j w) := by
  rw [vertex_eq_proj]
  apply CoordinateProjection.commute_embedding
  rintro ⟨a,e⟩
  cases a with
  | nil => rfl
  | cons k a => cases k; rfl

 theorem terminalVertex_commute_creation (e : Bool) (i : ι) (r : Bool) :
    Commute (terminalVertex e : Operator ι) (creation i r) := by
  apply CoordinateProjection.commute_embedding
  intro w
  rfl

 theorem terminalVertex_commute_edgeCreation (e : Bool) (i : ι) (r s : Bool) :
    Commute (terminalVertex e : Operator ι) (edgeCreation i r s) :=
  (terminalVertex_commute_creation e i r).mul_right (by
    rw [vertex_eq_proj];exact CoordinateProjection.commute _ _)

 theorem edgeCreation_commute_rightInsert (i j : ι) (r s : Bool) (w : Path ι) :
    Commute (edgeCreation i r s) (rightInsert j w) :=
  (creation_commute_rightInsert i j r w).mul_left (vertex_commute_rightInsert s j w)

 def diagonalInsert (j : ι) (w : Path ι) : Operator ι :=
   rightInsert j w*terminalVertex (start w)

 theorem vertex_commute_diagonalInsert (r : Bool) (j : ι) (w : Path ι) :
    Commute (vertex r : Operator ι) (diagonalInsert j w) :=
  (vertex_commute_rightInsert r j w).mul_right (by
    rw [vertex_eq_proj];exact CoordinateProjection.commute _ _)

 theorem edgeCreation_commute_diagonalInsert (i j : ι) (r s : Bool) (w : Path ι) :
    Commute (edgeCreation i r s) (diagonalInsert j w) :=
  (edgeCreation_commute_rightInsert i j r s w).mul_right
    (terminalVertex_commute_edgeCreation (start w) i r s).symm

 theorem vacuumTo_terminal (w : Path ι) (r s : Bool) :
    vacuumTo w r*terminalVertex s=if r=s then vacuumTo w r else 0 := by
  apply operator_basis_ext
  rintro ⟨a,e⟩
  cases a with
  | nil =>
    cases r <;> cases s <;> cases e <;>
      simp [mul_apply_eq_comp,terminalVertex_single]
  | cons k a =>
    rcases k with ⟨i,t⟩
    simp only [mul_apply_eq_comp,terminalVertex_single]
    split_ifs <;> simp only [vacuumTo_cons,map_zero,zero_apply]

 theorem vertex_vacuumTo (w : Path ι) (r s : Bool) :
    vertex s*vacuumTo w r=if start w=s then vacuumTo w r else 0 := by
  apply ContinuousLinearMap.ext
  intro ξ
  simp only [mul_apply_eq_comp,vacuumTo_apply,map_smul,vertex_single]
  split_ifs <;> simp only [vacuumTo_apply,smul_zero,zero_apply]

 theorem crossAnnihilation_commute_diagonalInsert (i j : ι) (r s : Bool)
    (hrs : r≠s) (w : Path ι) :
    Commute (star (edgeCreation i r s)) (diagonalInsert j w) := by
  have hbase := annihilation_rightInsert i j r w
  have hterm := (terminalVertex_commute_creation (start w) i r).star_star
  simp only [terminalVertex_star] at hterm
  have hvertex := vertex_commute_rightInsert s j w
  have hvt : Commute (vertex s : Operator ι) (terminalVertex (start w)) := by
    rw [vertex_eq_proj];exact CoordinateProjection.commute _ _
  change _*_=_*_
  simp only [edgeCreation,star_mul,vertex_star,diagonalInsert]
  calc
    (vertex s*star (creation i r))*(rightInsert j w*terminalVertex (start w)) =
        vertex s*(star (creation i r)*rightInsert j w)*terminalVertex (start w) := by
          simp only [mul_assoc]
    _ = (rightInsert j w*terminalVertex (start w))*(vertex s*star (creation i r)) +
        vertex s*(if i=j then vacuumTo w r else 0)*terminalVertex (start w) := by
      rw [hbase,mul_add,add_mul]
      congr 1
      calc
        vertex s*(rightInsert j w*star (creation i r))*terminalVertex (start w) =
            rightInsert j w*(vertex s*star (creation i r)*terminalVertex (start w)) := by
              rw [← mul_assoc, hvertex.eq]; simp only [mul_assoc]
        _ = _ := by
          rw [mul_assoc (vertex s),← hterm.eq,← mul_assoc (vertex s),hvt.eq]
          simp only [mul_assoc]
    _ = _ := by
      have hz : vertex s*(if i=j then vacuumTo w r else 0)*terminalVertex (start w)=0 := by
        by_cases hij : i=j
        · rw [ite_eq_left hij,mul_assoc,vacuumTo_terminal]
          by_cases hr : r=start w
          · rw [ite_eq_left hr,vertex_vacuumTo,ite_eq_right (by simpa only [← hr] using hrs)]
          · rw [ite_eq_right hr,mul_zero]
        · rw [ite_eq_right hij,mul_zero,zero_mul]
      rw [hz,add_zero]

end

section
open FreeFock
variable {ι : Type u_8} [DecidableEq ι]

omit [DecidableEq ι] in
@[simp] theorem vertex_true : (vertex true : Operator ι)=P := rfl
omit [DecidableEq ι] in
@[simp] theorem vertex_false : (vertex false : Operator ι)=1-P := rfl

 theorem offDiagonal_edges (u v : ℝ) (i : ι) :
    offDiagonal u v i=(u:ℂ) • edgeCreation i true false+
      (v:ℂ) • star (edgeCreation i false true) := by
  rw [offDiagonal_formula]
  simp only [edgeCreation,star_mul,vertex_true,vertex_false,projection_P.isSelfAdjoint.star_eq]

 theorem offDiagonal_commute_diagonalInsert (u v : ℝ) (i j : ι) (w : Path ι) :
    Commute (offDiagonal u v i) (diagonalInsert j w) := by
  rw [offDiagonal_edges]
  exact ((edgeCreation_commute_diagonalInsert i j true false w).smul_left _).add_left
    ((crossAnnihilation_commute_diagonalInsert i j false true Bool.false_ne_true w).smul_left _)

 theorem offDiagonalStar_commute_diagonalInsert (u v : ℝ) (i j : ι) (w : Path ι) :
    Commute (star (offDiagonal u v i)) (diagonalInsert j w) := by
  rw [offDiagonal_edges]
  simp only [star_add (R := Operator ι),star_smul,star_star]
  exact ((crossAnnihilation_commute_diagonalInsert i j true false (by decide) w).smul_left _).add_left
    ((edgeCreation_commute_diagonalInsert i j false true w).smul_left _)

 theorem diagonalInsert_mem_edgeCommutant (u v : ℝ) (i j : ι) (w : Path ι) :
    diagonalInsert j w ∈ StarSubalgebra.centralizer ℂ
      (insert P {offDiagonal u v i+star (offDiagonal u v i)}) := by
  rw [StarSubalgebra.mem_centralizer_iff]
  intro T hT
  rcases hT with hT | hT
  · subst T
    have hc := vertex_commute_diagonalInsert true j w
    rw [vertex_true] at hc
    exact ⟨hc.eq,by rw [projection_P.isSelfAdjoint.star_eq];exact hc.eq⟩
  · have hT' : T=offDiagonal u v i+star (offDiagonal u v i) := hT
    subst T
    have hc := (offDiagonal_commute_diagonalInsert u v i j w).add_left
      (offDiagonalStar_commute_diagonalInsert u v i j w)
    exact ⟨hc.eq,by rw [(IsSelfAdjoint.add_star_self (R := Operator ι) _).star_eq];exact hc.eq⟩

 def alternatingList (e : Bool) : List (ι×Bool) → Prop
   | [] => True
   | (_,r)::a => r≠start (a,e) ∧ alternatingList e a
 def alternatingProjection : Operator ι :=
   CoordinateProjection.proj {w | alternatingList w.2 w.1}

 theorem alternatingProjection_pos (w : Path ι) (z : ℂ)
    (h : alternatingList w.2 w.1) :
    alternatingProjection (lp.single 2 w z)=lp.single 2 w z := by
  classical
  unfold alternatingProjection
  rw [CoordinateProjection.proj_single]
  apply ite_eq_left
  exact h

 theorem alternatingProjection_neg (w : Path ι) (z : ℂ)
    (h : ¬alternatingList w.2 w.1) :
    alternatingProjection (lp.single 2 w z)=0 := by
  classical
  unfold alternatingProjection
  rw [CoordinateProjection.proj_single]
  apply ite_eq_right
  exact h

 theorem alternating_commute_edgeCreation (i : ι) (r s : Bool) (hrs : r≠s) :
    Commute (alternatingProjection : Operator ι) (edgeCreation i r s) := by
  classical
  change _*_=_*_
  apply operator_basis_ext
  intro w
  simp only [mul_apply_eq_comp]
  by_cases hs : start w=s
  · have hneq : r≠start w := by simpa only [hs] using hrs
    by_cases ha : alternatingList w.2 w.1
    · have hn : alternatingList w.2 ((i,r)::w.1) := ⟨hneq,ha⟩
      rw [edgeCreation_single,ite_eq_left hs,alternatingProjection_pos _ _ hn,
        alternatingProjection_pos _ _ ha,edgeCreation_single,ite_eq_left hs]
    · have hn : ¬alternatingList w.2 ((i,r)::w.1) := fun h => ha h.2
      rw [edgeCreation_single,ite_eq_left hs,alternatingProjection_neg _ _ hn,
        alternatingProjection_neg _ _ ha,map_zero]
  · rw [edgeCreation_single,ite_eq_right hs,map_zero]
    by_cases ha : alternatingList w.2 w.1
    · rw [alternatingProjection_pos _ _ ha,edgeCreation_single,ite_eq_right hs]
    · rw [alternatingProjection_neg _ _ ha,map_zero]

 theorem alternating_commute_edgeAnnihilation (i : ι) (r s : Bool) (hrs : r≠s) :
    Commute (alternatingProjection : Operator ι) (star (edgeCreation i r s)) := by
  have h := (alternating_commute_edgeCreation i r s hrs).star_star
  simpa only [alternatingProjection,CoordinateProjection.star_proj] using h

 theorem alternating_mem_edgeCommutant (u v : ℝ) (i : ι) :
    (alternatingProjection : Operator ι) ∈ StarSubalgebra.centralizer ℂ
      (insert P {offDiagonal u v i+star (offDiagonal u v i)}) := by
  have hc : Commute (alternatingProjection : Operator ι) (offDiagonal u v i) := by
    rw [offDiagonal_edges]
    exact ((alternating_commute_edgeCreation i true false (by decide)).smul_right _).add_right
      ((alternating_commute_edgeAnnihilation i false true Bool.false_ne_true).smul_right _)
  have hcs := hc.star_star
  simp only [alternatingProjection,CoordinateProjection.star_proj] at hcs
  rw [StarSubalgebra.mem_centralizer_iff]
  intro T hT
  rcases hT with hT | hT
  · subst T
    have hh : Commute (alternatingProjection : Operator ι) P := CoordinateProjection.commute _ _
    exact ⟨hh.eq.symm,by rw [projection_P.isSelfAdjoint.star_eq];exact hh.eq.symm⟩
  · have hT' : T=offDiagonal u v i+star (offDiagonal u v i) := hT
    subst T
    have hh := hc.add_right hcs
    exact ⟨hh.eq.symm,by rw [(IsSelfAdjoint.add_star_self (R := Operator ι) _).star_eq];exact hh.eq.symm⟩

 theorem diagonal_annihilation_alternating (i : ι) (r : Bool) :
    star (edgeCreation i r r)*alternatingProjection=0 := by
  classical
  apply operator_basis_ext
  rintro ⟨a,e⟩
  simp only [mul_apply_eq_comp,zero_apply]
  cases a with
  | nil =>
    rw [alternatingProjection_pos _ _ (show alternatingList e [] from trivial),
      edgeAnnihilation_nil]
  | cons k a =>
    rcases k with ⟨j,s⟩
    by_cases ha : alternatingList e ((j,s)::a)
    · rw [alternatingProjection_pos _ _ ha,edgeAnnihilation_cons]
      apply ite_eq_right
      rintro ⟨heq,hs⟩
      exact ha.1 ((Prod.mk.inj heq).2.symm.trans hs.symm)
    · rw [alternatingProjection_neg _ _ ha,map_zero]

 theorem alternating_edge_root (u v : ℝ) (i : ι) (T : edgeAlgebra u v i) (s : Bool) :
    alternatingProjection ((T : Operator ι) (lp.single 2 ([],s) 1))=
      (T : Operator ι) (lp.single 2 ([],s) 1) := by
  have hc := ((StarSubalgebra.mem_centralizer_iff ℂ).mp T.property _
    (alternating_mem_edgeCommutant u v i)).1
  have ht := DFunLike.congr_fun hc (lp.single 2 ([],s) 1)
  simpa only [mul_apply_eq_comp,alternatingProjection_pos ([],s) 1
    (show alternatingList s [] from trivial)] using ht

 theorem diagonal_annihilation_edge_root (u v : ℝ) (i j : ι)
    (T : edgeAlgebra u v i) (r s : Bool) :
    star (edgeCreation j r r) ((T : Operator ι) (lp.single 2 ([],s) 1))=0 := by
  have ht := DFunLike.congr_fun (diagonal_annihilation_alternating j r)
    ((T : Operator ι) (lp.single 2 ([],s) 1))
  simpa only [mul_apply_eq_comp,alternating_edge_root,zero_apply] using ht

end
open FreeFock
variable {ι : Type u_9} [DecidableEq ι]

 theorem edgeAnnihilation_diagonalInsert_formula (i j : ι) (r s : Bool) (w : Path ι) :
    star (edgeCreation i r s)*diagonalInsert j w=
      diagonalInsert j w*star (edgeCreation i r s)+
        vertex s*(if i=j then vacuumTo w r else 0)*terminalVertex (start w) := by
  have hbase := annihilation_rightInsert i j r w
  have hterm := (terminalVertex_commute_creation (start w) i r).star_star
  simp only [terminalVertex_star] at hterm
  have hvertex := vertex_commute_rightInsert s j w
  have hvt : Commute (vertex s : Operator ι) (terminalVertex (start w)) := by
    rw [vertex_eq_proj];exact CoordinateProjection.commute _ _
  simp only [edgeCreation,star_mul,vertex_star,diagonalInsert]
  calc
    (vertex s*star (creation i r))*(rightInsert j w*terminalVertex (start w)) =
        vertex s*(star (creation i r)*rightInsert j w)*terminalVertex (start w) := by
          simp only [mul_assoc]
    _ = _ := by
      rw [hbase,mul_add,add_mul]
      congr 1
      calc
        vertex s*(rightInsert j w*star (creation i r))*terminalVertex (start w) =
            rightInsert j w*(vertex s*star (creation i r)*terminalVertex (start w)) := by
              rw [← mul_assoc, hvertex.eq]; simp only [mul_assoc]
        _ = _ := by
          rw [mul_assoc (vertex s),← hterm.eq,← mul_assoc (vertex s),hvt.eq]
          simp only [mul_assoc]

 theorem diagonalAnnihilation_diagonalInsert (i j : ι) (r : Bool) (w : Path ι) :
    star (edgeCreation i r r)*diagonalInsert j w=
      diagonalInsert j w*star (edgeCreation i r r)+
        if i=j ∧ start w=r then vacuumTo w r else 0 := by
  rw [edgeAnnihilation_diagonalInsert_formula]
  congr 1
  by_cases hij : i=j
  · rw [ite_eq_left hij,mul_assoc,vacuumTo_terminal]
    by_cases hr : start w=r
    · simp only [hr,ite_true,vertex_vacuumTo,hij,true_and]
    · simp only [ite_eq_right (Ne.symm hr),mul_zero,hij,true_and,hr,ite_false]
  · simp only [hij,ite_false,mul_zero,zero_mul,false_and]

 theorem diagonalInsert_nil (j : ι) (w : Path ι) (s : Bool) :
    diagonalInsert j w (lp.single 2 ([],s) 1)=
      if s=start w then lp.single 2 ((j,s)::w.1,w.2) 1 else 0 := by
  simp only [diagonalInsert,mul_apply_eq_comp,terminalVertex_single]
  split_ifs <;> simp only [rightInsert_single,List.nil_append,List.singleton_append,map_zero]

 theorem diagonal_edge_contraction (u v : ℝ) (i j k : ι)
    (T : edgeAlgebra u v i) (r s : Bool) :
    star (edgeCreation j r r)*(T : Operator ι)*edgeCreation k s s=
      if j=k ∧ r=s then
        (((T : Operator ι) (lp.single 2 ([],s) 1)) ([],r)) • vertex s else 0 := by
  apply operator_basis_ext
  intro w
  by_cases hs : start w=s
  · have hc := ((StarSubalgebra.mem_centralizer_iff ℂ).mp T.property _
      (diagonalInsert_mem_edgeCommutant u v i k w)).1
    have ht := DFunLike.congr_fun hc (lp.single 2 ([],s) 1)
    simp only [mul_apply_eq_comp,diagonalInsert_nil,hs,ite_true] at ht
    have ha := DFunLike.congr_fun (diagonalAnnihilation_diagonalInsert j k r w)
      ((T : Operator ι) (lp.single 2 ([],s) 1))
    simp only [mul_apply_eq_comp,add_apply,diagonal_annihilation_edge_root u v i j T,
      map_zero,zero_add,hs] at ha
    simp only [mul_apply_eq_comp,edgeCreation_single,hs,ite_true,← ht,ha]
    by_cases hjk : j=k
    · by_cases hrs : r=s
      · simp [hjk,hrs,vacuumTo_apply,_root_.smul_apply,vertex_single,hs]
      · simp only [hjk,true_and,Ne.symm hrs,hrs,ite_false,zero_apply]
    · simp only [hjk,false_and,ite_false,zero_apply]
  · simp only [mul_apply_eq_comp,edgeCreation_single,hs,ite_false,map_zero]
    split_ifs <;> simp only [_root_.smul_apply,vertex_single,hs,ite_false,smul_zero,zero_apply]

end FreeGroupFactorMain.WeightedFock

end

end OAI
