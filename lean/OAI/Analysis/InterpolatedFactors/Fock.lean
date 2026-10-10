import OAI.Analysis.InterpolatedFactors.CornerRepresentation

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15

noncomputable section
namespace FreeGroupFactorMain.FreeFock
open scoped ENNReal

abbrev Op (α : Type u_1) := Hilbert α →L[ℂ] Hilbert α
variable {α : Type u_2} {β : Type u_3} [DecidableEq α] [DecidableEq β]

 theorem operator_basis_ext (T U : Op α)
    (h : ∀ a, T (lp.single 2 a 1)=U (lp.single 2 a 1)) : T=U := by
  classical
  apply ContinuousLinearMap.ext
  intro ξ
  have hT := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) ξ).mapL T
  have hU := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) ξ).mapL U
  have he (a : α) : T (lp.single 2 a (ξ a))=U (lp.single 2 a (ξ a)) := by
    have hc : lp.single (E := fun _ : α => ℂ) 2 a (ξ a)=
        (ξ a) • lp.single (E := fun _ : α => ℂ) 2 a 1 := by
      ext b
      simp [lp.single_apply,Pi.single_apply]
    rw [hc,map_smul,map_smul,h]
  simp only [he] at hT
  exact hT.unique hU

 def basisEmbedding (a : α) : ℂ →ₗᵢ[ℂ] Hilbert α where
  toLinearMap := lp.lsingle (𝕜 := ℂ) (E := fun _ : α => ℂ) 2 a
  norm_map' z := lp.norm_single (E := fun _ : α => ℂ) (by norm_num : 0 < (2 : ℝ≥0∞)) a z

omit [DecidableEq α] in
 theorem embedding_orthogonal (f : α ↪ β) :
    OrthogonalFamily ℂ (fun _ : α => ℂ) (fun a => basisEmbedding (f a)) := by
  classical
  intro a b hab z w
  change inner ℂ (lp.single (E := fun _ : β => ℂ) 2 (f a) z) (lp.single (E := fun _ : β => ℂ) 2 (f b) w)=0
  have hn : f a ≠ f b := fun he => hab (f.injective he)
  simp [lp.inner_single_left,lp.single_apply,hn]

 def hilbertEmbedding (f : α ↪ β) : Hilbert α →ₗᵢ[ℂ] Hilbert β :=
  (embedding_orthogonal f).linearIsometry

@[simp] theorem hilbertEmbedding_single (f : α ↪ β) (a : α) (z : ℂ) :
    hilbertEmbedding f (lp.single 2 a z)=lp.single 2 (f a) z :=
  (embedding_orthogonal f).linearIsometry_apply_single z

 abbrev Fock (α : Type u_4) := Hilbert (List α)
 abbrev Operator (α : Type u_5) := Op (List α)

 def consEmbedding (a : α) : List α ↪ List α := ⟨List.cons a,fun _ _ h => (List.cons.inj h).2⟩

 def creation (a : α) : Operator α := (hilbertEmbedding (consEmbedding a)).toContinuousLinearMap

@[simp] theorem creation_single (a : α) (w : List α) (z : ℂ) :
    creation a (lp.single 2 w z)=lp.single 2 (a::w) z := by
  exact hilbertEmbedding_single (consEmbedding a) w z

 theorem creation_norm (a : α) (ξ : Fock α) : ‖creation a ξ‖=‖ξ‖ :=
  (hilbertEmbedding (consEmbedding a)).norm_map ξ

 theorem annihilation_single_nil (a : α) (z : ℂ) :
    star (creation a) (lp.single 2 [] z)=0 := by
  classical
  ext w
  have hi := ContinuousLinearMap.adjoint_inner_right (creation a) (lp.single 2 w 1) (lp.single 2 [] z)
  rw [creation_single,lp.inner_single_left,lp.inner_single_left] at hi
  simpa [ContinuousLinearMap.star_eq_adjoint,RCLike.inner_apply,lp.single_apply] using hi

 theorem annihilation_single_cons (a b : α) (w : List α) (z : ℂ) :
    star (creation a) (lp.single 2 (b::w) z)=if a=b then lp.single 2 w z else 0 := by
  classical
  ext v
  have hi := ContinuousLinearMap.adjoint_inner_right (creation a) (lp.single 2 v 1) (lp.single 2 (b::w) z)
  rw [creation_single,lp.inner_single_left,lp.inner_single_left] at hi
  change (star (creation a) (lp.single 2 (b::w) z)) v=_
  have he : (star (creation a) (lp.single 2 (b::w) z)) v=(lp.single (E := fun _ : List α => ℂ) 2 (b::w) z) (a::v) := by
    simpa [ContinuousLinearMap.star_eq_adjoint,RCLike.inner_apply] using hi
  rw [he]
  by_cases hab : a=b
  · subst b
    simp only [lp.single_apply,Pi.single_apply,List.cons.injEq,true_and,ite_true]
  · simp only [lp.single_apply,Pi.single_apply,List.cons.injEq,hab,false_and,ite_false,lp.coeFn_zero,Pi.zero_apply]

 theorem annihilation_creation (a b : α) :
    star (creation a)*creation b=if a=b then 1 else 0 := by
  classical
  apply operator_basis_ext (α := List α)
  intro w
  rw [mul_apply_eq_comp]
  rw [creation_single,annihilation_single_cons]
  by_cases h : a=b <;> simp [h]

 def semicircular (a : α) : Operator α := creation a+star (creation a)

 theorem semicircular_selfAdjoint (a : α) : IsSelfAdjoint (semicircular a) := by
  change star (creation a+star (creation a))=creation a+star (creation a)
  simp only [star_add (R := Operator α),star_star,add_comm]

 def vacuum : Fock α := lp.single 2 [] 1

@[simp] theorem semicircular_vacuum (a : α) : semicircular a vacuum=lp.single 2 [a] 1 := by
  change creation a (lp.single 2 [] 1)+star (creation a) (lp.single 2 [] 1)=_
  rw [creation_single,annihilation_single_nil,add_zero]

 def vacuumTrace (T : Operator α) : ℂ := inner ℂ vacuum (T vacuum)

 theorem vacuumTrace_one : vacuumTrace (1 : Operator α)=1 := by
  classical
  simp only [vacuumTrace,vacuum,one_apply_eq_self,lp.inner_single_left,lp.single_apply_self]
  norm_num

 theorem vacuumTrace_semicircular (a : α) : vacuumTrace (semicircular a)=0 := by
  classical
  rw [vacuumTrace,semicircular_vacuum]
  simp [vacuum,lp.inner_single_left,lp.single_apply]

end FreeGroupFactorMain.FreeFock
namespace FreeGroupFactorMain.CoordinateProjection

variable {α : Type u_6} [DecidableEq α]
open scoped Classical

@[simp] theorem proj_single (s : Set α) (a : α) (z : ℂ) :
    proj s (lp.single 2 a z)=if a ∈ s then lp.single (E := fun _ : α => ℂ) 2 a z else 0 := by
  classical
  ext b
  by_cases ha : a ∈ s
  · by_cases hb : b=a <;> simp [proj_apply,Set.indicator,lp.single_apply,ha,hb]
  · by_cases hb : b=a <;> simp [proj_apply,Set.indicator,lp.single_apply,ha,hb]

 theorem projection (s : Set α) : IsStarProjection (proj s) := by
  refine ⟨?_,star_proj s⟩
  apply FreeFock.operator_basis_ext
  intro a
  simp only [mul_apply_eq_comp,proj_single]
  split_ifs <;> simp_all

 theorem commute (s t : Set α) : Commute (proj s) (proj t) := by
  change _ * _ = _ * _
  apply FreeFock.operator_basis_ext
  intro a
  simp only [mul_apply_eq_comp,proj_single]
  split_ifs <;> simp_all

 theorem commute_embedding (s : Set α) (f : α ↪ α)
    (hf : ∀ a, f a ∈ s ↔ a ∈ s) :
    Commute (proj s) (FreeFock.hilbertEmbedding f).toContinuousLinearMap := by
  change _ * _ = _ * _
  apply FreeFock.operator_basis_ext
  intro a
  change proj s (FreeFock.hilbertEmbedding f (lp.single 2 a 1))=
    FreeFock.hilbertEmbedding f (proj s (lp.single 2 a 1))
  rw [FreeFock.hilbertEmbedding_single,proj_single,proj_single]
  simp only [hf]
  split_ifs <;> simp_all

end FreeGroupFactorMain.CoordinateProjection

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock
variable {ι : Type u_7} [DecidableEq ι]

abbrev Path (ι : Type u_8) := List (ι × Bool) × Bool
abbrev H (ι : Type u_9) := Hilbert (Path ι)
abbrev Operator (ι : Type u_10) := Op (Path ι)

def start (w : Path ι) : Bool := match w.1 with
  | [] => w.2
  | (_,r)::_ => r

def prepend (i : ι) (r : Bool) : Path ι ↪ Path ι :=
  ⟨fun w => ((i,r)::w.1,w.2), by
    rintro ⟨v,s⟩ ⟨w,t⟩ h
    have he := Prod.mk.inj h
    exact Prod.ext (List.cons.inj he.1).2 he.2⟩

def creation (i : ι) (r : Bool) : Operator ι :=
  (hilbertEmbedding (prepend i r)).toContinuousLinearMap

@[simp] theorem creation_single (i : ι) (r : Bool) (w : Path ι) (z : ℂ) :
    creation i r (lp.single 2 w z)=lp.single 2 ((i,r)::w.1,w.2) z :=
  hilbertEmbedding_single (prepend i r) w z

 theorem annihilation_single_nil (i : ι) (r s : Bool) (z : ℂ) :
    star (creation i r) (lp.single 2 ([],s) z)=0 := by
  ext w
  have hi := ContinuousLinearMap.adjoint_inner_right (creation i r)
    (lp.single 2 w 1) (lp.single 2 ([],s) z)
  rw [creation_single,lp.inner_single_left,lp.inner_single_left] at hi
  simpa [ContinuousLinearMap.star_eq_adjoint,RCLike.inner_apply,lp.single_apply] using hi

 theorem annihilation_single_cons (i j : ι) (r s e : Bool)
    (w : List (ι × Bool)) (z : ℂ) :
    star (creation i r) (lp.single 2 ((j,s)::w,e) z)=
      if (i,r)=(j,s) then lp.single 2 (w,e) z else 0 := by
  ext v
  have hi := ContinuousLinearMap.adjoint_inner_right (creation i r)
    (lp.single 2 v 1) (lp.single 2 ((j,s)::w,e) z)
  rw [creation_single,lp.inner_single_left,lp.inner_single_left] at hi
  have he : (star (creation i r) (lp.single 2 ((j,s)::w,e) z)) v=
      (lp.single (E := fun _ : Path ι => ℂ) 2 ((j,s)::w,e) z) ((i,r)::v.1,v.2) := by
    simpa [ContinuousLinearMap.star_eq_adjoint,RCLike.inner_apply] using hi
  rw [he]
  rcases v with ⟨v,t⟩
  by_cases hab : (i,r)=(j,s)
  · simp only [lp.single_apply,Pi.single_apply,Prod.mk.injEq,List.cons.injEq,hab,
      true_and,ite_true]
  · simp only [lp.single_apply,Pi.single_apply,Prod.mk.injEq,List.cons.injEq,hab,
      false_and,ite_false,lp.coeFn_zero,Pi.zero_apply]

def P : Operator ι := CoordinateProjection.proj {w : Path ι | start w=true}
def K : Operator ι := CoordinateProjection.proj
  {w : Path ι | w.2=true ∧ ∀ x ∈ w.1, x.2=true}

theorem projection_P : IsStarProjection (P : Operator ι) := CoordinateProjection.projection _
theorem projection_K : IsStarProjection (K : Operator ι) := CoordinateProjection.projection _
theorem K_commute_P : Commute (K : Operator ι) P := CoordinateProjection.commute _ _

theorem K_commute_creation (i : ι) : Commute (K : Operator ι) (creation i true) := by
  apply CoordinateProjection.commute_embedding
  intro w
  change (w.2=true ∧ ∀ x ∈ ((i,true)::w.1), x.2=true) ↔
    (w.2=true ∧ ∀ x ∈ w.1, x.2=true)
  simp

theorem P_creation_false (i : ι) : (P : Operator ι)*creation i false=0 := by
  apply operator_basis_ext
  intro w
  simp [mul_apply_eq_comp,creation_single,P,CoordinateProjection.proj_single,start]

def S (u v : ℝ) (i : ι) : Operator ι :=
  (u:ℂ) • creation i true + (v:ℂ) • creation i false +
  star ((u:ℂ) • creation i true + (v:ℂ) • creation i false)

theorem S_selfAdjoint (u v : ℝ) (i : ι) : IsSelfAdjoint (S u v i) := by
  exact IsSelfAdjoint.add_star_self (R := Operator ι) _

def compressed (u v : ℝ) (i : ι) : Operator ι := P*S u v i*P

theorem compressed_formula (u v : ℝ) (i : ι) :
    compressed u v i=(u:ℂ) • (P*creation i true*P + P*star (creation i true)*P) := by
  have hf : star (creation i false)*(P : Operator ι)=0 := by
    have h := congrArg star (P_creation_false i)
    simpa only [star_mul,projection_P.isSelfAdjoint.star_eq,star_zero (Operator ι)] using h
  simp only [compressed,S,mul_add,add_mul,star_add (R := Operator ι),star_smul,Complex.star_def,
    Complex.conj_ofReal,mul_smul_comm,smul_mul_assoc,mul_assoc,P_creation_false,hf,
    mul_zero,zero_mul,smul_zero,add_zero,smul_add]

theorem K_commute_compressed (u v : ℝ) (i : ι) : Commute (K : Operator ι) (compressed u v i) := by
  rw [compressed_formula]
  have hc := K_commute_creation i
  have hs : Commute (K : Operator ι) (star (creation i true)) := by
    have h := hc.star_star
    rw [projection_K.isSelfAdjoint.star_eq] at h
    exact h
  exact ((K_commute_P.mul_right hc).mul_right K_commute_P |>.add_right
    ((K_commute_P.mul_right hs).mul_right K_commute_P)).smul_right _

end

section
open FreeFock
variable {ι : Type u_11} [DecidableEq ι]

@[simp] theorem P_single (w : Path ι) (z : ℂ) :
    (P : Operator ι) (lp.single 2 w z)=if start w=true then lp.single 2 w z else 0 :=
by
  classical
  have hp := CoordinateProjection.proj_single {w : Path ι | start w=true} w z
  simp only [Set.mem_ofPred_eq] at hp
  unfold P
  by_cases h : start w=true
  · rw [ite_eq_left h]
    rw [ite_eq_left h] at hp
    exact hp
  · rw [ite_eq_right h]
    rw [ite_eq_right h] at hp
    exact hp

@[simp] theorem P_nil_true (z : ℂ) : (P : Operator ι) (lp.single 2 ([],true) z)=
    lp.single 2 ([],true) z := by simp [start]

@[simp] theorem P_nil_false (z : ℂ) : (P : Operator ι) (lp.single 2 ([],false) z)=0 := by simp [start]

@[simp] theorem P_cons (i : ι) (r e : Bool) (w : List (ι×Bool)) (z : ℂ) :
    (P : Operator ι) (lp.single 2 ((i,r)::w,e) z)=
      if r=true then lp.single 2 ((i,r)::w,e) z else 0 := by
  rw [P_single]
  change (if r=true then _ else _) = _
  split_ifs <;> rfl

@[simp] theorem K_nil_true (z : ℂ) : (K : Operator ι) (lp.single 2 ([],true) z)=
    lp.single 2 ([],true) z := by simp [K,CoordinateProjection.proj_single]

@[simp] theorem K_mixed (a b : ι) (z : ℂ) :
    (K : Operator ι) (lp.single 2 ([(a,true),(b,false)],true) z)=0 := by
  simp [K,CoordinateProjection.proj_single]

def excursion (u v : ℝ) (a b : ι) : Operator ι := P*S u v a*(1-P)*S u v b*P

theorem S_nil (u v : ℝ) (i : ι) (e : Bool) (z : ℂ) :
    S u v i (lp.single 2 ([],e) z)=
      (u:ℂ) • lp.single 2 ([(i,true)],e) z +
      (v:ℂ) • lp.single 2 ([(i,false)],e) z := by
  simp only [S,add_apply,star_add (R := Operator ι),star_smul,Complex.star_def,Complex.conj_ofReal,
    _root_.smul_apply,creation_single,annihilation_single_nil,smul_zero,add_zero]

theorem S_cons_distinct (u v : ℝ) (a b : ι) (hab : a≠b)
    (r e : Bool) (w : List (ι×Bool)) (z : ℂ) :
    S u v a (lp.single 2 ((b,r)::w,e) z)=
      (u:ℂ) • lp.single 2 ((a,true)::(b,r)::w,e) z +
      (v:ℂ) • lp.single 2 ((a,false)::(b,r)::w,e) z := by
  simp only [S,add_apply,star_add (R := Operator ι),star_smul,Complex.star_def,Complex.conj_ofReal,
    _root_.smul_apply,creation_single,annihilation_single_cons,Prod.mk.injEq,hab,
    false_and,ite_false,smul_zero,add_zero]

theorem excursion_start (u v : ℝ) (a b : ι) (hab : a≠b) :
    excursion u v a b (lp.single 2 ([],true) 1)=
      ((u:ℂ)*(v:ℂ)) • lp.single 2 ([(a,true),(b,false)],true) 1 := by
  simp only [excursion,mul_apply_eq_comp,P_nil_true,S_nil,map_add,map_smul,
    sub_apply,one_apply_eq_self,P_cons,Bool.false_eq_true,ite_false,ite_true,
    sub_self,sub_zero,smul_zero,zero_add,map_zero]
  rw [S_cons_distinct u v a b hab]
  simp only [map_add,map_smul,P_cons,Bool.false_eq_true,ite_false,ite_true,
    smul_zero,add_zero,smul_smul]
  rw [mul_comm]

def compressedAlgebra (u v : ℝ) : StarSubalgebra ℂ (Operator ι) :=
  StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ (Set.range (compressed u v : ι → Operator ι)) : Set (Operator ι))

theorem compressed_selfAdjoint (u v : ℝ) (i : ι) :
    IsSelfAdjoint (compressed u v i) := by
  change star (P*S u v i*P)=P*S u v i*P
  simp only [star_mul,projection_P.isSelfAdjoint.star_eq,(S_selfAdjoint u v i).star_eq,mul_assoc]

theorem K_in_compressedCommutant (u v : ℝ) :
    (K : Operator ι) ∈ StarSubalgebra.centralizer ℂ (Set.range (compressed u v : ι → Operator ι)) := by
  rw [StarSubalgebra.mem_centralizer_iff]
  rintro _ ⟨i,rfl⟩
  refine ⟨(K_commute_compressed u v i).eq.symm,?_⟩
  rw [(compressed_selfAdjoint u v i).star_eq]
  exact (K_commute_compressed u v i).eq.symm

theorem excursion_not_in_compressedAlgebra (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (a b : ι) (hab : a≠b) : excursion u v a b ∉ compressedAlgebra u v := by
  intro h
  have hc := ((StarSubalgebra.mem_centralizer_iff ℂ).mp h _ (K_in_compressedCommutant u v)).1
  have he := DFunLike.congr_fun hc (lp.single 2 ([],true) 1)
  simp only [mul_apply_eq_comp,excursion_start u v a b hab,K_nil_true,map_smul,
    K_mixed,smul_zero] at he
  have hw := congrArg (fun ξ : H ι => ξ ([(a,true),(b,false)],true)) he
  simp only [lp.coeFn_zero,Pi.zero_apply,lp.coeFn_smul,Pi.smul_apply,
    lp.single_apply_self,smul_eq_mul,mul_one] at hw
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hu) (Complex.ofReal_ne_zero.mpr hv) hw.symm

def ambientAlgebra (u v : ℝ) : StarSubalgebra ℂ (Operator ι) :=
  StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ
    (insert P (Set.range (S u v : ι → Operator ι))) : Set (Operator ι))

theorem P_mem_ambient (u v : ℝ) : (P : Operator ι) ∈ ambientAlgebra u v :=
  StarAlgebra.adjoin_le_centralizer_centralizer ℂ _
    (StarAlgebra.subset_adjoin ℂ _ (Set.mem_insert _ _))

theorem S_mem_ambient (u v : ℝ) (i : ι) : S u v i ∈ ambientAlgebra u v :=
  StarAlgebra.adjoin_le_centralizer_centralizer ℂ _
    (StarAlgebra.subset_adjoin ℂ _ (Set.mem_insert_of_mem _ (Set.mem_range_self i)))

theorem excursion_mem_ambient (u v : ℝ) (a b : ι) :
    excursion u v a b ∈ ambientAlgebra u v := by
  unfold excursion
  exact (ambientAlgebra u v).mul_mem ((ambientAlgebra u v).mul_mem
    ((ambientAlgebra u v).mul_mem ((ambientAlgebra u v).mul_mem
      (P_mem_ambient u v) (S_mem_ambient u v a))
      ((ambientAlgebra u v).sub_mem (ambientAlgebra u v).one_mem (P_mem_ambient u v)))
    (S_mem_ambient u v b)) (P_mem_ambient u v)

theorem excursion_in_corner (u v : ℝ) (a b : ι) :
    P*excursion u v a b=excursion u v a b ∧
    excursion u v a b*P=excursion u v a b := by
  have hp : (P : Operator ι)*P=P := projection_P.isIdempotentElem.eq
  constructor
  · simp only [excursion,← mul_assoc,hp]
  · simp only [excursion,mul_assoc,hp]

theorem compression_generation_obstruction (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (a b : ι) (hab : a≠b) :
    ∃ E : Operator ι, E ∈ ambientAlgebra u v ∧ P*E=E ∧ E*P=E ∧ E ∉ compressedAlgebra u v := by
  exact ⟨excursion u v a b,excursion_mem_ambient u v a b,
    (excursion_in_corner u v a b).1,(excursion_in_corner u v a b).2,
    excursion_not_in_compressedAlgebra u v hu hv a b hab⟩

end

section
open FreeFock
variable {ι : Type u_12}

def appendPath (w : Path ι) (i : ι) (r : Bool) : Path ι := (w.1++[(i,w.2)],r)
def reverseList : List (ι × Bool) → Bool → Path ι
  | [],e => ([],e)
  | (i,r)::w,e => appendPath (reverseList w e) i r

def reversePath (w : Path ι) : Path ι := reverseList w.1 w.2

@[simp] theorem reverse_nil (e : Bool) : reversePath (([],e) : Path ι)=([],e) := rfl
@[simp] theorem reverse_cons (i : ι) (r e : Bool) (w : List (ι×Bool)) :
    reversePath ((i,r)::w,e)=appendPath (reversePath (w,e)) i r := rfl

@[simp] theorem start_appendPath (w : Path ι) (i : ι) (r : Bool) :
    start (appendPath w i r)=start w := by
  rcases w with ⟨w,e⟩
  cases w <;> rfl

theorem reverse_append (w : List (ι×Bool)) (i : ι) (r e : Bool) :
    reversePath (w++[(i,r)],e)=prepend i e (reversePath (w,r)) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    rcases p with ⟨j,s⟩
    change appendPath (reversePath (w++[(i,r)],e)) j s=
      prepend i e (appendPath (reversePath (w,r)) j s)
    rw [ih]
    rfl

theorem reversePath_involutive : Function.Involutive (reversePath : Path ι → Path ι) := by
  rintro ⟨w,e⟩
  induction w generalizing e with
  | nil => rfl
  | cons p w ih =>
    rcases p with ⟨i,r⟩
    rw [reverse_cons]
    change reversePath ((reversePath (w,e)).1++[(i,(reversePath (w,e)).2)],r)=_
    rw [reverse_append]
    change prepend i r (reversePath (reversePath (w,e)))=_
    rw [ih]
    rfl

@[simp] theorem end_reverse (w : Path ι) : (reversePath w).2=start w := by
  rcases w with ⟨w,e⟩
  cases w with
  | nil => rfl
  | cons a w => cases a; rfl

@[simp] theorem start_reverse (w : Path ι) : start (reversePath w)=w.2 := by
  have h := end_reverse (reversePath w)
  rw [reversePath_involutive] at h
  exact h.symm

@[simp] theorem reversePath_reverse (w : Path ι) : reversePath (reversePath w)=w :=
  reversePath_involutive w

variable [DecidableEq ι]

def reverseEmbedding : Path ι ↪ Path ι := ⟨reversePath,reversePath_involutive.injective⟩
def reverseIsometry : H ι →ₗᵢ[ℂ] H ι := hilbertEmbedding reverseEmbedding
def reverseOperator : Operator ι := reverseIsometry.toContinuousLinearMap

@[simp] theorem reverseOperator_single (w : Path ι) (z : ℂ) :
    reverseOperator (lp.single 2 w z)=lp.single 2 (reversePath w) z :=
  hilbertEmbedding_single reverseEmbedding w z

theorem reverseOperator_square : (reverseOperator : Operator ι)*reverseOperator=1 := by
  apply operator_basis_ext
  intro w
  simp [mul_apply_eq_comp,reverseOperator_single]

theorem reverseOperator_involutive (ξ : H ι) : reverseOperator (reverseOperator ξ)=ξ :=
  DFunLike.congr_fun reverseOperator_square ξ

def reverseEquiv : H ι ≃ₗᵢ[ℂ] H ι :=
  LinearIsometryEquiv.ofSurjective reverseIsometry (fun ξ =>
    ⟨reverseOperator ξ,reverseOperator_involutive ξ⟩)

@[simp] theorem reverseEquiv_apply (ξ : H ι) : reverseEquiv ξ=reverseOperator ξ := rfl
@[simp] theorem reverseEquiv_symm_apply (ξ : H ι) : reverseEquiv.symm ξ=reverseOperator ξ := by
  apply reverseEquiv.injective
  rw [LinearIsometryEquiv.apply_symm_apply,reverseEquiv_apply,reverseOperator_involutive]

def reverseConj : Operator ι ≃⋆ₐ[ℂ] Operator ι := reverseEquiv.conjStarAlgEquiv

@[simp] theorem reverseConj_apply (T : Operator ι) (ξ : H ι) :
    reverseConj T ξ=reverseOperator (T (reverseOperator ξ)) := by
  simp only [reverseConj,LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    reverseEquiv_apply,reverseEquiv_symm_apply]

def appendEmbedding (i : ι) (r : Bool) : Path ι ↪ Path ι :=
  ⟨fun w => appendPath w i r, by
    intro w v h
    apply reversePath_involutive.injective
    have he := congrArg reversePath h
    change reversePath (w.1++[(i,w.2)],r)=reversePath (v.1++[(i,v.2)],r) at he
    rw [reverse_append,reverse_append] at he
    exact (prepend i r).injective he⟩

def rightCreation (i : ι) (r : Bool) : Operator ι :=
  (hilbertEmbedding (appendEmbedding i r)).toContinuousLinearMap

@[simp] theorem rightCreation_single (i : ι) (r : Bool) (w : Path ι) (z : ℂ) :
    rightCreation i r (lp.single 2 w z)=lp.single 2 (appendPath w i r) z :=
  hilbertEmbedding_single (appendEmbedding i r) w z

theorem reverseConj_creation (i : ι) (r : Bool) :
    reverseConj (creation i r)=rightCreation i r := by
  apply operator_basis_ext
  intro w
  simp only [reverseConj_apply,reverseOperator_single,creation_single,rightCreation_single,
    reverse_cons,Prod.eta,reversePath_reverse]

def rightP : Operator ι := CoordinateProjection.proj {w : Path ι | w.2=true}

theorem reverseConj_P : reverseConj (P : Operator ι)=rightP := by
  apply operator_basis_ext
  intro w
  simp only [reverseConj_apply,reverseOperator_single,P_single,start_reverse,
    rightP,CoordinateProjection.proj_single,Set.mem_ofPred_eq]
  split_ifs <;> simp [reverseOperator_single]

def vacuum (u v : ℝ) : H ι := (u:ℂ) • lp.single 2 ([],true) 1 +
  (v:ℂ) • lp.single 2 ([],false) 1

@[simp] theorem reverse_vacuum (u v : ℝ) : reverseOperator (vacuum u v : H ι)=vacuum u v := by
  simp only [vacuum,map_add,map_smul,reverseOperator_single,reverse_nil]

 theorem right_creation_commute (i j : ι) (r s : Bool) :
    Commute (creation i r) (rightCreation j s) := by
  change _*_=_*_
  apply operator_basis_ext
  intro w
  simp only [mul_apply_eq_comp,creation_single,rightCreation_single,appendPath]
  rfl

 theorem P_commute_rightCreation (i : ι) (r : Bool) :
    Commute (P : Operator ι) (rightCreation i r) := by
  apply CoordinateProjection.commute_embedding
  intro w
  change start (appendPath w i r)=true ↔ start w=true
  rw [start_appendPath]

 theorem rightP_commute_creation (i : ι) (r : Bool) :
    Commute (rightP : Operator ι) (creation i r) := by
  apply CoordinateProjection.commute_embedding
  intro w
  rfl

 theorem P_commute_rightP : Commute (P : Operator ι) rightP := CoordinateProjection.commute _ _

end

section
open FreeFock
variable {ι : Type u_13} [DecidableEq ι]

def vacuumMatrix (r s : Bool) : Operator ι :=
  InnerProductSpace.rankOne ℂ (lp.single 2 ([],s) 1) (lp.single 2 ([],r) 1)

@[simp] theorem vacuumMatrix_nil (r s e : Bool) (z : ℂ) :
    (vacuumMatrix r s : Operator ι) (lp.single 2 ([],e) z)=
      if r=e then lp.single 2 ([],s) z else 0 := by
  classical
  by_cases hr : r=e
  · subst e
    ext w
    simp [vacuumMatrix,InnerProductSpace.rankOne_apply,lp.inner_single_left,
      lp.single_apply,Pi.single_apply]
  · simp [vacuumMatrix,InnerProductSpace.rankOne_apply,lp.inner_single_left,
      lp.single_apply,hr]

@[simp] theorem vacuumMatrix_cons (r s e : Bool) (i : ι) (t : Bool)
    (w : List (ι×Bool)) (z : ℂ) :
    (vacuumMatrix r s : Operator ι) (lp.single 2 ((i,t)::w,e) z)=0 := by
  simp [vacuumMatrix,InnerProductSpace.rankOne_apply,lp.inner_single_left,lp.single_apply]

@[simp] theorem star_vacuumMatrix (r s : Bool) :
    star (vacuumMatrix r s : Operator ι)=vacuumMatrix s r := by
  simp only [vacuumMatrix,ContinuousLinearMap.star_eq_adjoint,InnerProductSpace.adjoint_rankOne]

 theorem annihilation_rightCreation (i j : ι) (r s : Bool) :
    star (creation i r)*rightCreation j s=
      rightCreation j s*star (creation i r)+(if i=j then vacuumMatrix r s else 0) := by
  apply operator_basis_ext
  rintro ⟨w,e⟩
  cases w with
  | nil =>
    simp only [mul_apply_eq_comp,add_apply,rightCreation_single,appendPath,List.nil_append,
      annihilation_single_cons,annihilation_single_nil,map_zero,zero_add]
    by_cases hij : i=j
    · subst j
      simp [vacuumMatrix_nil]
    · simp only [Prod.mk.injEq,hij,false_and,ite_false]
      rfl
  | cons a w =>
    rcases a with ⟨k,t⟩
    simp only [mul_apply_eq_comp,add_apply,rightCreation_single,appendPath,List.cons_append,
      annihilation_single_cons]
    have hm : (if i=j then (vacuumMatrix r s : Operator ι) else 0)
        (lp.single 2 ((k,t)::w,e) 1)=0 := by
      split_ifs <;> simp
    rw [hm,add_zero]
    by_cases h : (i,r)=(k,t)
    · simp only [h,ite_true,rightCreation_single,appendPath]
    · simp only [h,ite_false,map_zero]

def C (u v : ℝ) (i : ι) : Operator ι :=
  (u:ℂ) • creation i true+(v:ℂ) • creation i false

def rightC (u v : ℝ) (i : ι) : Operator ι :=
  (u:ℂ) • rightCreation i true+(v:ℂ) • rightCreation i false

theorem reverseConj_C (u v : ℝ) (i : ι) : reverseConj (C u v i)=rightC u v i := by
  simp only [C,rightC,map_add,map_smul,reverseConj_creation]

theorem S_eq (u v : ℝ) (i : ι) : S u v i=C u v i+star (C u v i) := rfl

def rightS (u v : ℝ) (i : ι) : Operator ι := rightC u v i+star (rightC u v i)

theorem reverseConj_S (u v : ℝ) (i : ι) : reverseConj (S u v i)=rightS u v i := by
  have hs : reverseConj (star (C u v i)) = star (reverseConj (C u v i)) :=
    reverseConj.map_star' (C u v i)
  simp only [S_eq,map_add,hs,reverseConj_C,rightS]

def vacuumCorrection (u v : ℝ) : Operator ι :=
  ((u:ℂ)^2) • vacuumMatrix true true +
  ((u:ℂ)*(v:ℂ)) • vacuumMatrix true false +
  ((u:ℂ)*(v:ℂ)) • vacuumMatrix false true +
  ((v:ℂ)^2) • vacuumMatrix false false

theorem vacuumCorrection_selfAdjoint (u v : ℝ) :
    IsSelfAdjoint (vacuumCorrection u v : Operator ι) := by
  change star (vacuumCorrection u v)=vacuumCorrection u v
  simp only [vacuumCorrection,star_add (R := Operator ι),star_smul,star_vacuumMatrix,Complex.star_def,
    map_pow,map_mul,Complex.conj_ofReal]
  abel

theorem C_commute_rightC (u v : ℝ) (i j : ι) : Commute (C u v i) (rightC u v j) := by
  unfold C rightC
  exact (((right_creation_commute i j true true).smul_left _).smul_right _ |>.add_right
    (((right_creation_commute i j true false).smul_left _).smul_right _)).add_left
      ((((right_creation_commute i j false true).smul_left _).smul_right _ |>.add_right
        (((right_creation_commute i j false false).smul_left _).smul_right _)))

theorem C_annihilation_rightC (u v : ℝ) (i j : ι) :
    star (C u v i)*rightC u v j=rightC u v j*star (C u v i)+
      (if i=j then vacuumCorrection u v else 0) := by
  simp only [C,rightC,star_add (R := Operator ι),star_smul,Complex.star_def,Complex.conj_ofReal,
    add_mul,mul_add,smul_mul_assoc,mul_smul_comm,annihilation_rightCreation,smul_add,
    smul_smul]
  by_cases hij : i=j
  · simp only [hij,ite_true,vacuumCorrection]
    module
  · simp only [hij,ite_false,add_zero]
    module

 omit [DecidableEq ι] in
theorem add_star_commute_of_correction {A B D : Operator ι}
    (hAB : A*B=B*A) (h : star A*B=B*star A+D) (hD : star D=D) :
    Commute (A+star A) (B+star B) := by
  have habs : star A*star B=star B*star A := by
    have he := congrArg star hAB
    simpa only [star_mul] using he.symm
  have has : A*star B=star B*A-D := by
    have he := congrArg star h
    simp only [star_mul,star_star,star_add (R := Operator ι),hD] at he
    exact eq_sub_iff_add_eq.mpr he.symm
  change _*_=_*_
  rw [add_mul,mul_add,mul_add,hAB,has,h,habs]
  simp only [mul_add,add_mul]
  abel

 theorem S_commute_rightS (u v : ℝ) (i j : ι) :
    Commute (S u v i) (rightS u v j) := by
  rw [S_eq,rightS]
  apply add_star_commute_of_correction (C_commute_rightC u v i j).eq
    (C_annihilation_rightC u v i j)
  split_ifs
  · exact (vacuumCorrection_selfAdjoint u v).star_eq
  · exact star_zero (Operator ι)

 theorem rightP_projection : IsStarProjection (rightP : Operator ι) := CoordinateProjection.projection _

 theorem P_commute_rightS (u v : ℝ) (i : ι) : Commute (P : Operator ι) (rightS u v i) := by
  have hc : Commute (P : Operator ι) (rightC u v i) :=
    ((P_commute_rightCreation i true).smul_right _).add_right
      ((P_commute_rightCreation i false).smul_right _)
  have hs := hc.star_star
  rw [projection_P.isSelfAdjoint.star_eq] at hs
  exact hc.add_right hs

 theorem rightP_commute_S (u v : ℝ) (i : ι) : Commute (rightP : Operator ι) (S u v i) := by
  have hc : Commute (rightP : Operator ι) (C u v i) :=
    ((rightP_commute_creation i true).smul_right _).add_right
      ((rightP_commute_creation i false).smul_right _)
  have hs := hc.star_star
  rw [rightP_projection.isSelfAdjoint.star_eq] at hs
  exact hc.add_right hs

end

section
open FreeFock
open scoped ComplexConjugate
variable {ι : Type u_14} [DecidableEq ι]

def ambientCommutant (u v : ℝ) : StarSubalgebra ℂ (Operator ι) :=
  StarSubalgebra.centralizer ℂ (insert P (Set.range (S u v : ι → Operator ι)))

def Good (u v : ℝ) (A : Operator ι) : Prop :=
  A ∈ ambientAlgebra u v ∧ reverseConj A ∈ ambientCommutant u v ∧
    reverseConj A (vacuum u v)=star A (vacuum u v)

theorem good_one (u v : ℝ) : Good u v (1 : Operator ι) := by
  refine ⟨(ambientAlgebra u v).one_mem,?_,?_⟩
  · rw [map_one]; exact (ambientCommutant u v).one_mem
  · simp only [map_one,star_one]

theorem good_zero (u v : ℝ) : Good u v (0 : Operator ι) := by
  refine ⟨(ambientAlgebra u v).zero_mem,?_,?_⟩
  · rw [map_zero]; exact (ambientCommutant u v).zero_mem
  · simp only [map_zero,star_zero (Operator ι)]

theorem good_add {u v : ℝ} {A B : Operator ι} (hA : Good u v A) (hB : Good u v B) :
    Good u v (A+B) := by
  refine ⟨(ambientAlgebra u v).add_mem hA.1 hB.1,?_,?_⟩
  · rw [map_add]; exact (ambientCommutant u v).add_mem hA.2.1 hB.2.1
  · simp only [map_add,add_apply,star_add (R := Operator ι),hA.2.2,hB.2.2]

theorem good_sub {u v : ℝ} {A B : Operator ι} (hA : Good u v A) (hB : Good u v B) :
    Good u v (A-B) := by
  refine ⟨(ambientAlgebra u v).sub_mem hA.1 hB.1,?_,?_⟩
  · rw [map_sub]; exact (ambientCommutant u v).sub_mem hA.2.1 hB.2.1
  · simp only [map_sub,sub_apply,star_sub (R := Operator ι),hA.2.2,hB.2.2]

theorem good_smul {u v : ℝ} {A : Operator ι} (c : ℝ) (hA : Good u v A) :
    Good u v ((c:ℂ) • A) := by
  refine ⟨(ambientAlgebra u v).smul_mem hA.1 _,?_,?_⟩
  · rw [map_smul]; exact (ambientCommutant u v).smul_mem hA.2.1 _
  · simp only [map_smul,_root_.smul_apply,star_smul,Complex.star_def,
      Complex.conj_ofReal,hA.2.2]

theorem good_mul {u v : ℝ} {A B : Operator ι} (hA : Good u v A) (hB : Good u v B) :
    Good u v (A*B) := by
  refine ⟨(ambientAlgebra u v).mul_mem hA.1 hB.1,?_,?_⟩
  · rw [map_mul]; exact (ambientCommutant u v).mul_mem hA.2.1 hB.2.1
  · have hc := ((StarSubalgebra.mem_centralizer_iff ℂ).mp
      (star_mem hB.1) _ hA.2.1).1
    rw [map_mul,mul_apply_eq_comp,hB.2.2,← mul_apply_eq_comp,hc,
      mul_apply_eq_comp,hA.2.2,star_mul,mul_apply_eq_comp]

theorem reverseConj_vacuum (A : Operator ι) (u v : ℝ) :
    reverseConj A (vacuum u v)=reverseOperator (A (vacuum u v)) := by
  rw [reverseConj_apply,reverse_vacuum]

theorem rightP_mem_commutant (u v : ℝ) : (rightP : Operator ι) ∈ ambientCommutant u v := by
  rw [ambientCommutant,StarSubalgebra.mem_centralizer_iff]
  intro A hA
  rcases Set.mem_insert_iff.mp hA with hA | ⟨i,rfl⟩
  · subst A
    refine ⟨(CoordinateProjection.commute _ _).eq,?_⟩
    rw [projection_P.isSelfAdjoint.star_eq]
    exact (CoordinateProjection.commute _ _).eq
  · refine ⟨(rightP_commute_S u v i).eq.symm,?_⟩
    rw [(S_selfAdjoint u v i).star_eq]
    exact (rightP_commute_S u v i).eq.symm

theorem rightS_mem_commutant (u v : ℝ) (j : ι) : rightS u v j ∈ ambientCommutant u v := by
  rw [ambientCommutant,StarSubalgebra.mem_centralizer_iff]
  intro A hA
  rcases Set.mem_insert_iff.mp hA with hA | ⟨i,rfl⟩
  · subst A
    refine ⟨(P_commute_rightS u v j).eq,?_⟩
    rw [projection_P.isSelfAdjoint.star_eq]
    exact (P_commute_rightS u v j).eq
  · refine ⟨(S_commute_rightS u v i j).eq,?_⟩
    rw [(S_selfAdjoint u v i).star_eq]
    exact (S_commute_rightS u v i j).eq

theorem good_P (u v : ℝ) : Good u v (P : Operator ι) := by
  refine ⟨P_mem_ambient u v,?_,?_⟩
  · rw [reverseConj_P]; exact rightP_mem_commutant u v
  · rw [reverseConj_vacuum,projection_P.isSelfAdjoint.star_eq]
    simp only [vacuum,map_add,map_smul,P_nil_true,P_nil_false,smul_zero,add_zero,
      reverseOperator_single,reverse_nil]

theorem good_S (u v : ℝ) (i : ι) : Good u v (S u v i) := by
  refine ⟨S_mem_ambient u v i,?_,?_⟩
  · rw [reverseConj_S]; exact rightS_mem_commutant u v i
  · rw [reverseConj_vacuum,(S_selfAdjoint u v i).star_eq]
    simp only [vacuum,map_add,map_smul,S_nil,reverseOperator_single,reverse_cons,
      reverse_nil,appendPath,List.nil_append,smul_add,smul_smul]
    module

def vertex (r : Bool) : Operator ι := if r then P else 1-P

def weight (u v : ℝ) (r : Bool) : ℝ := if r then u else v

theorem good_vertex (u v : ℝ) (r : Bool) : Good u v (vertex r : Operator ι) := by
  cases r
  · exact good_sub (good_one u v) (good_P u v)
  · exact good_P u v

theorem weight_ne_zero {u v : ℝ} (hu : u≠0) (hv : v≠0) (r : Bool) : weight u v r ≠ 0 := by
  cases r <;> assumption

@[simp] theorem vertex_single (r : Bool) (w : Path ι) (z : ℂ) :
    (vertex r : Operator ι) (lp.single 2 w z)=if start w=r then lp.single 2 w z else 0 := by
  cases r <;> cases h : start w <;> simp [vertex,P_single,h]

 theorem vertex_S_nil (u v : ℝ) (i : ι) (r e : Bool) :
    (vertex r : Operator ι) (S u v i (lp.single 2 ([],e) 1))=
      ((weight u v r):ℂ) • lp.single 2 ([(i,r)],e) 1 := by
  rw [S_nil]
  simp only [map_add,map_smul]
  cases r <;> simp only [vertex_single,start,weight,Bool.false_eq_true,Bool.true_eq_false,
    ite_true,ite_false,smul_zero,zero_add,add_zero]

 theorem S_cons (u v : ℝ) (i j : ι) (s e : Bool) (w : List (ι×Bool)) :
    S u v i (lp.single 2 ((j,s)::w,e) 1)=
      (u:ℂ) • lp.single 2 ((i,true)::(j,s)::w,e) 1+
      (v:ℂ) • lp.single 2 ((i,false)::(j,s)::w,e) 1+
      (if i=j then ((weight u v s):ℂ) • lp.single 2 (w,e) 1 else 0) := by
  simp only [S,star_add (R := Operator ι),star_smul,Complex.star_def,Complex.conj_ofReal,add_apply,
    _root_.smul_apply,creation_single,annihilation_single_cons,Prod.mk.injEq]
  cases s <;> by_cases hij : i=j <;> simp [hij,weight]

 theorem vertex_S_cons (u v : ℝ) (i j : ι) (r s e : Bool) (w : List (ι×Bool)) :
    (vertex r : Operator ι) (S u v i (lp.single 2 ((j,s)::w,e) 1))=
      ((weight u v r):ℂ) • lp.single 2 ((i,r)::(j,s)::w,e) 1+
      (if i=j then ((weight u v s):ℂ) • (vertex r : Operator ι) (lp.single 2 (w,e) 1) else 0) := by
  rw [S_cons,map_add,map_add]
  cases r <;> cases s <;> by_cases hij : i=j <;>
    simp only [hij,ite_true,ite_false,map_smul,map_zero,vertex_single,start,weight,
      Bool.false_eq_true,Bool.true_eq_false,smul_zero,zero_add,add_zero]

 theorem vertex_vacuum (u v : ℝ) (r : Bool) :
    (vertex r : Operator ι) (vacuum u v)=((weight u v r):ℂ) • lp.single 2 ([],r) 1 := by
  simp only [vacuum,map_add,map_smul]
  cases r <;> simp only [vertex_single,start,weight,Bool.false_eq_true,Bool.true_eq_false,
    ite_true,ite_false,smul_zero,zero_add,add_zero]

 theorem good_basis (u v : ℝ) (hu : u≠0) (hv : v≠0) (w : Path ι) :
    ∃ A : Operator ι, Good u v A ∧ A (vacuum u v)=lp.single 2 w 1 := by
  have h : ∀ l : List (ι×Bool),
      (∀ e, ∃ A : Operator ι, Good u v A ∧ A (vacuum u v)=lp.single 2 (l,e) 1) ∧
      (∀ i r e, ∃ A : Operator ι, Good u v A ∧ A (vacuum u v)=lp.single 2 ((i,r)::l,e) 1) := by
    intro l
    induction l with
    | nil =>
      have root (e : Bool) : ∃ A : Operator ι, Good u v A ∧
          A (vacuum u v)=lp.single 2 ([],e) 1 := by
        refine ⟨(((weight u v e)⁻¹:ℝ):ℂ) • vertex e,good_smul _ (good_vertex u v e),?_⟩
        rw [_root_.smul_apply,vertex_vacuum,smul_smul]
        simp only [Complex.ofReal_inv,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
          (weight_ne_zero hu hv e)),one_smul]
      refine ⟨root,?_⟩
      intro i r e
      obtain ⟨A,hA,he⟩ := root e
      refine ⟨(((weight u v r)⁻¹:ℝ):ℂ) • (vertex r*S u v i*A),
        good_smul _ (good_mul (good_mul (good_vertex u v r) (good_S u v i)) hA),?_⟩
      simp only [_root_.smul_apply,mul_apply_eq_comp,he,vertex_S_nil,smul_smul,
        Complex.ofReal_inv,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
          (weight_ne_zero hu hv r)),one_smul]
    | cons b l ih =>
      rcases b with ⟨j,s⟩
      refine ⟨ih.2 j s,?_⟩
      intro i r e
      obtain ⟨A,hA,heA⟩ := ih.2 j s e
      obtain ⟨B,hB,heB⟩ := ih.1 e
      let D : Operator ι := if i=j then ((weight u v s):ℂ) • (vertex r*B) else 0
      have hD : Good u v D := by
        dsimp [D]
        split_ifs
        · exact good_smul _ (good_mul (good_vertex u v r) hB)
        · exact good_zero u v
      have heD : D (vacuum u v)=if i=j then ((weight u v s):ℂ) •
          (vertex r : Operator ι) (lp.single 2 (l,e) 1) else 0 := by
        dsimp [D]
        split_ifs
        · change ((weight u v s):ℂ) • ((vertex r : Operator ι) (B (vacuum u v)))=_
          rw [heB]
          ext x
          simp only [lp.coeFn_smul,Pi.smul_apply]
          rfl
        · rfl
      refine ⟨(((weight u v r)⁻¹:ℝ):ℂ) • (vertex r*S u v i*A-D),
        good_smul _ (good_sub (good_mul (good_mul (good_vertex u v r) (good_S u v i)) hA) hD),?_⟩
      simp only [_root_.smul_apply,sub_apply,mul_apply_eq_comp,heA,vertex_S_cons,
        heD,add_sub_cancel_right,smul_smul,Complex.ofReal_inv,
        inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (weight_ne_zero hu hv r)),one_smul]
  exact (h w.1).1 w.2

end

open FreeFock
open scoped ComplexConjugate
variable {ι : Type u_15} [DecidableEq ι]

 theorem good_star {u v : ℝ} {A : Operator ι} (hA : Good u v A) :
    Good u v (star A) := by
  refine ⟨star_mem hA.1,?_,?_⟩
  · have hs : reverseConj (star A) = star (reverseConj A) := reverseConj.map_star' A
    rw [hs]; exact star_mem hA.2.1
  · rw [reverseConj_vacuum,star_star,← hA.2.2,reverseConj_vacuum,
      reverseOperator_involutive]

 theorem good_right_basis (u v : ℝ) (hu : u≠0) (hv : v≠0) (w : Path ι) :
    ∃ B : Operator ι, B ∈ ambientCommutant u v ∧
      B (vacuum u v)=lp.single 2 w 1 ∧ star B (vacuum u v)=lp.single 2 (reversePath w) 1 := by
  obtain ⟨A,hA,heA⟩ := good_basis u v hu hv (reversePath w)
  refine ⟨reverseConj A,hA.2.1,?_,?_⟩
  · rw [reverseConj_vacuum,heA,reverseOperator_single,reversePath_reverse]
  · have hs : reverseConj (star A) = star (reverseConj A) := reverseConj.map_star' A
    rw [← hs,(good_star hA).2.2,star_star,heA]

 theorem ambient_separating (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (T : ambientAlgebra (ι := ι) u v) (hT : (T : Operator ι) (vacuum u v)=0) : T=0 := by
  apply Subtype.ext
  apply operator_basis_ext
  intro w
  obtain ⟨B,hB,heB,_⟩ := good_right_basis u v hu hv w
  have hc := ((StarSubalgebra.mem_centralizer_iff ℂ).mp T.property _ hB).1
  have he := DFunLike.congr_fun hc (vacuum u v)
  simp only [mul_apply_eq_comp,heB,hT,map_zero] at he
  exact he.symm

 theorem ambient_star_vector (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (T : ambientAlgebra (ι := ι) u v) (w : Path ι) :
    ((star (T : Operator ι)) (vacuum u v)) w=
      conj (((T : Operator ι) (vacuum u v)) (reversePath w)) := by
  obtain ⟨B,hB,heB,hesB⟩ := good_right_basis u v hu hv w
  have hc := ((StarSubalgebra.mem_centralizer_iff ℂ).mp T.property _ hB).1
  have hec := DFunLike.congr_fun hc (vacuum u v)
  simp only [mul_apply_eq_comp,heB] at hec
  have he : inner ℂ (lp.single 2 w 1) ((star (T : Operator ι)) (vacuum u v))=
      inner ℂ ((T : Operator ι) (vacuum u v)) (lp.single 2 (reversePath w) 1) := by
    calc
      _ = inner ℂ ((T : Operator ι) (lp.single 2 w 1)) (vacuum u v) := by
        rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
      _ = inner ℂ (B ((T : Operator ι) (vacuum u v))) (vacuum u v) := by rw [hec]
      _ = inner ℂ ((T : Operator ι) (vacuum u v)) ((star B) (vacuum u v)) := by
        rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
      _ = _ := by rw [hesB]
  simpa [lp.inner_single_left,lp.inner_single_right,RCLike.inner_apply] using he

 def vacuumTrace (u v : ℝ) (T : Operator ι) : ℂ := inner ℂ (vacuum u v) (T (vacuum u v))

 theorem ambient_trace_mul (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (S T : ambientAlgebra (ι := ι) u v) :
    vacuumTrace u v ((S : Operator ι)*(T : Operator ι))=
      vacuumTrace u v ((T : Operator ι)*(S : Operator ι)) := by
  have hf (A B : ambientAlgebra (ι := ι) u v) :
      vacuumTrace u v ((A : Operator ι)*(B : Operator ι))=
        ∑' w : Path ι, ((A : Operator ι) (vacuum u v)) (reversePath w)*
          ((B : Operator ι) (vacuum u v)) w := by
    unfold vacuumTrace
    rw [mul_apply_eq_comp,← ContinuousLinearMap.adjoint_inner_left]
    change inner ℂ ((star (A : Operator ι)) (vacuum u v)) ((B : Operator ι) (vacuum u v))=_
    rw [lp.inner_eq_tsum]
    congr 1
    funext w
    rw [ambient_star_vector u v hu hv]
    simp [RCLike.inner_apply,mul_comm]
  rw [hf,hf]
  let e : Path ι ≃ Path ι := ⟨reversePath,reversePath,
    reversePath_involutive,reversePath_involutive⟩
  have hs := e.tsum_eq (fun w : Path ι => ((T : Operator ι) (vacuum u v)) (reversePath w)*
    ((S : Operator ι) (vacuum u v)) w)
  change (∑' w : Path ι, ((T : Operator ι) (vacuum u v)) (reversePath (reversePath w))*
    ((S : Operator ι) (vacuum u v)) (reversePath w))=_ at hs
  simpa only [reversePath_reverse,mul_comm] using hs

 theorem vacuumTrace_star_mul (u v : ℝ) (T : Operator ι) :
    vacuumTrace u v (star T*T)=inner ℂ (T (vacuum u v)) (T (vacuum u v)) := by
  simp only [vacuumTrace,mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

 theorem ambient_trace_faithful (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (T : ambientAlgebra (ι := ι) u v)
    (hT : vacuumTrace u v (star (T : Operator ι)*(T : Operator ι))=0) : T=0 := by
  rw [vacuumTrace_star_mul,inner_self_eq_zero] at hT
  exact ambient_separating u v hu hv T hT

 theorem vacuumTrace_one (u v : ℝ) : vacuumTrace u v (1 : Operator ι)=((u^2+v^2:ℝ):ℂ) := by
  simp only [vacuumTrace,one_apply_eq_self,vacuum,inner_add_left,inner_add_right,
    inner_smul_left,inner_smul_right,lp.inner_single_left]
  simp [lp.single_apply,RCLike.inner_apply,pow_two]

 theorem vacuumTrace_P (u v : ℝ) : vacuumTrace u v (P : Operator ι)=((u^2:ℝ):ℂ) := by
  simp only [vacuumTrace,vacuum,map_add,map_smul,P_nil_true,P_nil_false,smul_zero,
    add_zero,inner_add_left,inner_smul_left,inner_smul_right,lp.inner_single_left]
  simp [lp.single_apply,RCLike.inner_apply,pow_two]

 theorem tracial_compression_generation_obstruction (u v : ℝ)
    (hu : u≠0) (hv : v≠0) (hunit : u^2+v^2=1) (a b : ι) (hab : a≠b) :
    vacuumTrace u v (1 : Operator ι)=1 ∧
    (∀ S T : ambientAlgebra (ι := ι) u v,
      vacuumTrace u v ((S : Operator ι)*(T : Operator ι))=
        vacuumTrace u v ((T : Operator ι)*(S : Operator ι))) ∧
    (∀ T : ambientAlgebra (ι := ι) u v,
      vacuumTrace u v (star (T : Operator ι)*(T : Operator ι))=0 → T=0) ∧
    (∃ E : Operator ι, E ∈ ambientAlgebra u v ∧ P*E=E ∧ E*P=E ∧ E ∉ compressedAlgebra u v) := by
  refine ⟨?_,ambient_trace_mul u v hu hv,ambient_trace_faithful u v hu hv,
    compression_generation_obstruction u v hu hv a b hab⟩
  rw [vacuumTrace_one,hunit,Complex.ofReal_one]

end FreeGroupFactorMain.WeightedFock

end

end OAI
