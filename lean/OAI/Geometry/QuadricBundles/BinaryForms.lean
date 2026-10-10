import OAI.Geometry.QuadricBundles.Noncollapse

namespace OAI

universe u1 u2 u3 u4

noncomputable section

namespace QuadricCounterexample.BinaryForms
open MvPolynomial Finsupp
open scoped BigOperators
noncomputable section
variable {R : Type u1} [CommRing R]

abbrev Form (n : ℕ) := Fin (n+1) → R
abbrev Poly := MvPolynomial (Fin 2) R

def exponent (n : ℕ) (k : Fin (n+1)) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 k.val+Finsupp.single 1 (n-k.val)
@[simp] lemma exponent_zero (n : ℕ) (k : Fin (n+1)) : exponent n k 0=k.val := by
  simp [exponent]
@[simp] lemma exponent_one (n : ℕ) (k : Fin (n+1)) : exponent n k 1=n-k.val := by
  simp [exponent]
lemma exponent_injective (n : ℕ) : Function.Injective (exponent n) := by
  intro a b h
  apply Fin.ext
  simpa using congrArg (fun e ↦ e 0) h
lemma degree_binary (e : Fin 2 →₀ ℕ) : e.degree=e 0+e 1 := by
  simp [Finsupp.degree_eq_sum,Fin.sum_univ_two]
lemma exponent_degree (n : ℕ) (k : Fin (n+1)) : (exponent n k).degree=n := by
  rw [degree_binary,exponent_zero,exponent_one]
  omega
lemma exponent_of_degree (e : Fin 2 →₀ ℕ) {n : ℕ} (he : e.degree=n) :
    ∃ k : Fin (n+1),exponent n k=e := by
  rw [degree_binary] at he
  refine ⟨⟨e 0,by omega⟩,?_⟩
  ext i
  fin_cases i
  · simp
  · simp
    omega

def polynomial (n : ℕ) (a : Form (R := R) n) : Poly (R := R) :=
  ∑ k : Fin (n+1), monomial (exponent n k) (a k)
def coefficients (n : ℕ) (p : Poly (R := R)) : Form (R := R) n :=
  fun k ↦ p.coeff (exponent n k)

lemma polynomial_homogeneous (n : ℕ) (a : Form (R := R) n) :
    (polynomial n a).IsHomogeneous n := by
  apply IsHomogeneous.sum
  intro k _
  exact isHomogeneous_monomial _ (exponent_degree n k)
@[simp] lemma coefficients_polynomial (n : ℕ) (a : Form (R := R) n) :
    coefficients n (polynomial n a)=a := by
  ext k
  simp only [coefficients,polynomial,coeff_sum,coeff_monomial]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [show exponent n j≠exponent n k from fun h ↦ hj (exponent_injective n h)]
  · simp
lemma polynomial_coefficients {n : ℕ} {p : Poly (R := R)} (hp : p.IsHomogeneous n) :
    polynomial n (coefficients n p)=p := by
  ext e
  by_cases he : e.degree=n
  · obtain ⟨k,rfl⟩ := exponent_of_degree e he
    exact congrFun (coefficients_polynomial n (coefficients n p)) k
  · rw [IsHomogeneous.coeff_eq_zero (polynomial_homogeneous n _) he,hp.coeff_eq_zero he]
lemma polynomial_injective (n : ℕ) : Function.Injective (polynomial (R := R) n) := by
  intro a b h
  simpa using congrArg (coefficients n) h
lemma polynomial_add (n : ℕ) (a b : Form (R := R) n) :
    polynomial n (a+b)=polynomial n a+polynomial n b := by
  simp [polynomial,Finset.sum_add_distrib]
lemma polynomial_smul (n : ℕ) (c : R) (a : Form (R := R) n) :
    polynomial n (c • a)=c • polynomial n a := by
  simp [polynomial,Finset.smul_sum,smul_monomial]
@[simp] lemma polynomial_zero (n : ℕ) : polynomial (R := R) n 0=0 := by simp [polynomial]
lemma coefficients_add (n : ℕ) (p q : Poly (R := R)) :
    coefficients n (p+q)=coefficients n p+coefficients n q := by ext; simp [coefficients]
lemma coefficients_smul (n : ℕ) (c : R) (p : Poly (R := R)) :
    coefficients n (c • p)=c • coefficients n p := by ext; simp [coefficients]

def equivHomogeneous (n : ℕ) : Form (R := R) n ≃ₗ[R] homogeneousSubmodule (Fin 2) R n where
  toFun a := ⟨polynomial n a,polynomial_homogeneous n a⟩
  invFun p := coefficients n p
  left_inv := coefficients_polynomial n
  right_inv p := Subtype.ext (polynomial_coefficients p.property)
  map_add' a b := Subtype.ext (polynomial_add n a b)
  map_smul' c a := Subtype.ext (polynomial_smul n c a)

lemma eval_polynomial (n : ℕ) (a : Form (R := R) n) (v : Fin 2 → R) :
    MvPolynomial.eval v (polynomial n a)=∑ k : Fin (n+1), a k*v 0^k.val*v 1^(n-k.val) := by
  simp only [polynomial,eval_sum,eval_monomial]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finsupp.prod_fintype]
  · simp [Fin.prod_univ_two]; ring
  · simp

lemma coefficients_monomial_diff {n : ℕ} {p : Poly (R := R)}
    (hp : p.IsHomogeneous (n+1)) (i : Fin 2) :
    (p.divMonomial (Finsupp.single i 1)).IsHomogeneous n := by
  intro e he
  have h := hp (show p.coeff (Finsupp.single i 1+e)≠0 from he)
  simp only [map_add,Finsupp.weight_single,Pi.one_apply,smul_eq_mul,mul_one] at h
  omega

lemma homogeneous_projection {n : ℕ} {p : Poly (R := R)} (hp : p.IsHomogeneous n) :
    MvPolynomial.eval₂ MvPolynomial.C ![0,X 1] p=
      C (MvPolynomial.eval ![0,1] p)*X 1^n := by
  rw [← polynomial_coefficients hp]
  simp only [polynomial,eval₂_sum,eval₂_monomial,eval_sum,eval_monomial]
  have hexp (k : Fin (n+1)) (x y : Poly (R := R)) :
      (exponent n k).prod (fun i v ↦ (![x,y] : Fin 2 → Poly (R := R)) i^v)=x^k.val*y^(n-k.val) := by
    rw [Finsupp.prod_fintype]
    · simp [Fin.prod_univ_two]
    · simp
  have hexp' (k : Fin (n+1)) :
      (exponent n k).prod (fun i v ↦ (![0,1] : Fin 2 → R) i^v)=(0 : R)^k.val := by
    rw [Finsupp.prod_fintype]
    · simp [Fin.prod_univ_two]
    · simp
  simp only [hexp',map_sum,map_mul,map_pow,map_zero,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k.val=0
  · simp [hk]
  · simp [zero_pow hk]

end
end QuadricCounterexample.BinaryForms

namespace QuadricCounterexample.BinaryForms
open MvPolynomial Matrix
open scoped BigOperators
noncomputable section

def kernelForm (h d : ℂ) : Poly (R := ℂ) := C d*X 0-C h*X 1
def liftForm (u v : ℂ) : Poly (R := ℂ) := C u*X 0+C v*X 1
lemma kernelForm_homogeneous (h d : ℂ) : (kernelForm h d).IsHomogeneous 1 :=
  (isHomogeneous_C_mul_X d 0).sub (isHomogeneous_C_mul_X h 1)
lemma liftForm_homogeneous (u v : ℂ) : (liftForm u v).IsHomogeneous 1 :=
  (isHomogeneous_C_mul_X u 0).add (isHomogeneous_C_mul_X v 1)
@[simp] lemma eval_kernelForm (h d : ℂ) (x : Fin 2 → ℂ) :
    MvPolynomial.eval x (kernelForm h d)=d*x 0-h*x 1 := by simp [kernelForm]
@[simp] lemma eval_liftForm (u v : ℂ) (x : Fin 2 → ℂ) :
    MvPolynomial.eval x (liftForm u v)=u*x 0+v*x 1 := by simp [liftForm]
lemma kernelForm_ne_zero (h d u v : ℂ) (hu : u*h+v*d=1) : kernelForm h d≠0 := by
  intro hh
  have h1 := congrArg (MvPolynomial.eval ![1,0]) hh
  have h2 := congrArg (MvPolynomial.eval ![0,1]) hh
  simp only [eval_kernelForm,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    mul_one,mul_zero,sub_zero,zero_sub] at h1 h2
  have h3 : h=0 := neg_eq_zero.mp h2
  simp [h1,h3] at hu

def adaptedPolynomials (h d u v : ℂ) : (t : ℕ) → Fin (2*t+1) → Poly (R := ℂ)
  | 0 => fun _ ↦ 1
  | t+1 => Fin.snoc (n:=2*t+2) (Fin.snoc (n:=2*t+1)
      (fun k ↦ kernelForm h d*X 1*adaptedPolynomials h d u v t k)
      (kernelForm h d*X 0^(2*t+1))) (liftForm u v^(2*(t+1)))
lemma adaptedPolynomials_homogeneous (h d u v : ℂ) (t : ℕ) (k : Fin (2*t+1)) :
    (adaptedPolynomials h d u v t k).IsHomogeneous (2*t) := by
  induction t with
  | zero => exact isHomogeneous_one (Fin 2) ℂ
  | succ t ih =>
    refine Fin.lastCases (n:=2*t+2) ?_ (fun k ↦ ?_) k
    · simpa only [adaptedPolynomials,Fin.snoc_last,one_mul] using (liftForm_homogeneous u v).pow (2*(t+1))
    · refine Fin.lastCases (n:=2*t+1) ?_ (fun k ↦ ?_) k
      · simpa only [adaptedPolynomials,Fin.snoc_castSucc,Fin.snoc_last,show 1+(2*t+1)=2*(t+1) by omega] using
          (kernelForm_homogeneous h d).mul (isHomogeneous_X_pow 0 (2*t+1))
      · simpa only [adaptedPolynomials,Fin.snoc_castSucc,show 1+1+2*t=2*(t+1) by omega] using
          ((kernelForm_homogeneous h d).mul (isHomogeneous_X ℂ 1)).mul (ih k)

lemma sum_snoc_two {n : ℕ} (a : Fin (n+2) → ℂ) (f : Fin n → Poly (R := ℂ))
    (p q : Poly (R := ℂ)) :
    (∑ k, a k • Fin.snoc (Fin.snoc f p) q k)=
      (∑ k : Fin n, a k.castSucc.castSucc • f k)+
        a (Fin.last n).castSucc • p+a (Fin.last (n+1)) • q := by
  rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last]

lemma polynomial_sum_smul {ι : Type u2} [Fintype ι] (a : ι → ℂ)
    (p : Poly (R := ℂ)) (f : ι → Poly (R := ℂ)) :
    (∑ i,a i • (p*f i))=p*(∑ i,a i • f i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [MvPolynomial.smul_eq_C_mul]
  ring
lemma eval_sum_smul {ι : Type u3} [Fintype ι] (a : ι → ℂ) (f : ι → Poly (R := ℂ))
    (x : Fin 2 → ℂ) : MvPolynomial.eval x (∑ i,a i • f i)=∑ i,a i*MvPolynomial.eval x (f i) := by
  simp [MvPolynomial.smul_eq_C_mul]

lemma adaptedPolynomials_independent (h d u v : ℂ) (hu : u*h+v*d=1) (t : ℕ) :
    LinearIndependent ℂ (adaptedPolynomials h d u v t) := by
  rw [Fintype.linearIndependent_iff]
  induction t with
  | zero =>
    intro c hc k
    have hk : k=0 := Fin.ext (by omega)
    subst k
    have hx := congrArg (MvPolynomial.eval ![0,0]) hc
    simpa [adaptedPolynomials,Fin.sum_univ_one] using hx
  | succ t ih =>
    intro c hc k
    simp only [adaptedPolynomials] at hc
    have hs := sum_snoc_two (n:=2*t+1) c
      (fun k ↦ kernelForm h d*X 1*adaptedPolynomials h d u v t k)
      (kernelForm h d*X 0^(2*t+1)) (liftForm u v^(2*(t+1)))
    have hc2 := hs.symm.trans hc
    let c₀ : Fin (2*t+1) → ℂ := fun k ↦ c k.castSucc.castSucc
    let p : Poly (R := ℂ) := ∑ k,c₀ k • adaptedPolynomials h d u v t k
    have hc' : kernelForm h d*X 1*p+
        c (Fin.last (2*t+1)).castSucc • (kernelForm h d*X 0^(2*t+1))+
        c (Fin.last (2*t+2)) • liftForm u v^(2*(t+1))=0 := by
      simpa only [polynomial_sum_smul,c₀,p] using hc2
    have hlast : c (Fin.last (2*t+2))=0 := by
      have he := congrArg (MvPolynomial.eval ![h,d]) hc'
      simpa [MvPolynomial.smul_eq_C_mul,hu,mul_comm d h] using he
    have hrem : kernelForm h d*(X 1*p+C (c (Fin.last (2*t+1)).castSucc)*X 0^(2*t+1))=0 := by
      rw [hlast,zero_smul,add_zero] at hc'
      simp only [MvPolynomial.smul_eq_C_mul] at hc'
      linear_combination hc'
    have hrem' : X (R := ℂ) 1*p+C (c (Fin.last (2*t+1)).castSucc)*X 0^(2*t+1)=0 :=
      (mul_eq_zero.mp hrem).resolve_left (kernelForm_ne_zero h d u v hu)
    have hpen : c (Fin.last (2*t+1)).castSucc=0 := by
      have he := congrArg (MvPolynomial.eval ![1,0]) hrem'
      simpa using he
    have hp : p=0 := by
      rw [hpen,map_zero,zero_mul,add_zero] at hrem'
      exact (mul_eq_zero.mp hrem').resolve_left (X_ne_zero 1)
    have hold : ∀ k,c₀ k=0 := ih c₀ hp
    refine Fin.lastCases hlast (fun j ↦ ?_) k
    exact Fin.lastCases hpen (fun l ↦ hold l) j

def adaptedMatrix (h d u v : ℂ) (t : ℕ) : Matrix (Fin (2*t+1)) (Fin (2*t+1)) ℂ :=
  fun a b ↦ coefficients (2*t) (adaptedPolynomials h d u v t b) a
lemma adaptedMatrix_columns (h d u v : ℂ) (t : ℕ) (k : Fin (2*t+1)) :
    polynomial (2*t) ((adaptedMatrix h d u v t).col k)=adaptedPolynomials h d u v t k :=
  polynomial_coefficients (adaptedPolynomials_homogeneous h d u v t k)
lemma adaptedMatrix_independent (h d u v : ℂ) (hu : u*h+v*d=1) (t : ℕ) :
    LinearIndependent ℂ (adaptedMatrix h d u v t).col := by
  let f : Form (R := ℂ) (2*t) →ₗ[ℂ] Poly (R := ℂ) :=
    (homogeneousSubmodule (Fin 2) ℂ (2*t)).subtype.comp (equivHomogeneous (R := ℂ) (2*t)).toLinearMap
  have he : (fun k ↦ f ((adaptedMatrix h d u v t).col k))=adaptedPolynomials h d u v t :=
    funext (adaptedMatrix_columns h d u v t)
  apply LinearIndependent.of_comp f
  change LinearIndependent ℂ (fun k ↦ f ((adaptedMatrix h d u v t).col k))
  rw [he]
  exact adaptedPolynomials_independent h d u v hu t
lemma adaptedMatrix_isUnit (h d u v : ℂ) (hu : u*h+v*d=1) (t : ℕ) :
    IsUnit (adaptedMatrix h d u v t) := by
  rw [← Matrix.mulVec_injective_iff_isUnit,Matrix.mulVec_injective_iff]
  exact adaptedMatrix_independent h d u v hu t

end
end QuadricCounterexample.BinaryForms

namespace QuadricCounterexample.BinaryForms
open MvPolynomial Matrix
open scoped BigOperators
noncomputable section

def substitute (T : Matrix (Fin 2) (Fin 2) ℂ) : Poly (R := ℂ) →ₐ[ℂ] Poly (R := ℂ) :=
  MvPolynomial.aeval (fun b ↦ ∑ a : Fin 2,C (T a b)*X a)
@[simp] lemma substitute_X (T : Matrix (Fin 2) (Fin 2) ℂ) (b : Fin 2) :
    substitute T (X b)=∑ a : Fin 2,C (T a b)*X a := by simp [substitute]
@[simp] lemma substitute_C (T : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) :
    substitute T (C c)=C c := by simp [substitute]
lemma substitute_comp (T U : Matrix (Fin 2) (Fin 2) ℂ) (p : Poly (R := ℂ)) :
    substitute T (substitute U p)=substitute (T*U) p := by
  have he : (substitute T).comp (substitute U)=substitute (T*U) := by
    apply MvPolynomial.algHom_ext
    intro b
    simp only [AlgHom.comp_apply,substitute_X,map_sum,map_mul,substitute_C,
      Matrix.mul_apply,map_sum,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro c _
    ring
  exact DFunLike.congr_fun he p
@[simp] lemma substitute_one (p : Poly (R := ℂ)) : substitute 1 p=p := by
  have he : substitute 1=AlgHom.id ℂ (Poly (R := ℂ)) := by
    apply MvPolynomial.algHom_ext
    intro b
    simp [Matrix.one_apply]
  exact DFunLike.congr_fun he p
lemma substitute_homogeneous (T : Matrix (Fin 2) (Fin 2) ℂ) {n : ℕ}
    {p : Poly (R := ℂ)} (hp : p.IsHomogeneous n) : (substitute T p).IsHomogeneous n := by
  rw [← polynomial_coefficients hp]
  unfold polynomial
  rw [map_sum]
  apply IsHomogeneous.sum
  intro k _
  have hh : ∀ b : Fin 2,(substitute T (X b)).IsHomogeneous 1 := by
    intro b
    rw [substitute_X]
    apply IsHomogeneous.sum
    intro a _
    exact isHomogeneous_C_mul_X (T a b) a
  have hm : monomial (exponent n k) (coefficients n p k)=
      C (coefficients n p k)*X 0^k.val*X 1^(n-k.val) := by
    unfold exponent
    rw [monomial_add_single,← C_mul_X_pow_eq_monomial]
  rw [hm,map_mul,map_mul,map_pow,map_pow,substitute_C]
  convert ((isHomogeneous_C _ _).mul ((hh 0).pow k.val)).mul ((hh 1).pow (n-k.val)) using 1;
    simp only [one_mul,zero_add,Nat.add_sub_of_le (Nat.le_of_lt_succ k.isLt)]

lemma polynomial_linearCombination {ι : Type u4} [Fintype ι] (n : ℕ)
    (c : ι → ℂ) (a : ι → Form (R := ℂ) n) :
    polynomial n (∑ i,c i • a i)=∑ i,c i • polynomial n (a i) := by
  change ((equivHomogeneous (R := ℂ) n) (∑ i,c i • a i)).val=_
  rw [map_sum]
  simp only [AddSubmonoidClass.coe_finsetSum,map_smul,SetLike.val_smul]
  rfl

lemma polynomial_mulVec (n : ℕ) (T : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (a : Form (R := ℂ) n) :
    polynomial n (T.mulVec a)=∑ k,a k • polynomial n (T.col k) := by
  rw [← polynomial_linearCombination]
  congr 1
  ext j
  simp only [mulVec,dotProduct,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,col,transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

def symmetricMatrix (n : ℕ) (T : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  fun a b ↦ coefficients n (substitute T (monomial (exponent n b) 1)) a
lemma polynomial_symmetricMatrix_col (n : ℕ) (T : Matrix (Fin 2) (Fin 2) ℂ) (b : Fin (n+1)) :
    polynomial n ((symmetricMatrix n T).col b)=substitute T (monomial (exponent n b) 1) := by
  exact polynomial_coefficients (substitute_homogeneous T (isHomogeneous_monomial _ (exponent_degree n b)))
lemma polynomial_symmetricMatrix (n : ℕ) (T : Matrix (Fin 2) (Fin 2) ℂ) (a : Form (R := ℂ) n) :
    polynomial n ((symmetricMatrix n T).mulVec a)=substitute T (polynomial n a) := by
  rw [polynomial_mulVec]
  simp_rw [polynomial_symmetricMatrix_col]
  unfold polynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← map_smul]
  simp only [smul_monomial,smul_eq_mul,mul_one]
lemma symmetricMatrix_mul (n : ℕ) (T U : Matrix (Fin 2) (Fin 2) ℂ) :
    symmetricMatrix n (T*U)=symmetricMatrix n T*symmetricMatrix n U := by
  apply Matrix.ext_of_mulVec_single
  intro b
  apply polynomial_injective n
  rw [← mulVec_mulVec,polynomial_symmetricMatrix,polynomial_symmetricMatrix,polynomial_symmetricMatrix,
    substitute_comp]
@[simp] lemma symmetricMatrix_one (n : ℕ) : symmetricMatrix n (1 : Matrix (Fin 2) (Fin 2) ℂ)=1 := by
  apply Matrix.ext_of_mulVec_single
  intro b
  apply polynomial_injective n
  simp only [polynomial_symmetricMatrix,substitute_one,one_mulVec]
lemma eval_substitute (T : Matrix (Fin 2) (Fin 2) ℂ) (p : Poly (R := ℂ)) (v : Fin 2 → ℂ) :
    MvPolynomial.eval v (substitute T p)=MvPolynomial.eval (T.transpose.mulVec v) p := by
  change (MvPolynomial.eval v).comp (substitute T).toRingHom p=_
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro c; simp
  · intro b; fin_cases b <;> simp
end
end QuadricCounterexample.BinaryForms

namespace QuadricCounterexample.BinaryForms
open MvPolynomial Matrix
open scoped BigOperators
noncomputable section

lemma adaptedMatrix_det_unit (h d u v : ℂ) (hu : u*h+v*d=1) (t : ℕ) :
    IsUnit (adaptedMatrix h d u v t).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (adaptedMatrix_isUnit h d u v hu t)

lemma polynomial_adapted_mulVec (h d u v : ℂ) (t : ℕ) (c : Form (R := ℂ) (2*t)) :
    polynomial (2*t) ((adaptedMatrix h d u v t).mulVec c)=
      ∑ k,c k • adaptedPolynomials h d u v t k := by
  rw [polynomial_mulVec]
  simp_rw [adaptedMatrix_columns]

lemma adapted_combination_succ (h d u v : ℂ) (t : ℕ) (c : Form (R := ℂ) (2*(t+1))) :
    polynomial (2*(t+1)) ((adaptedMatrix h d u v (t+1)).mulVec c)=
      kernelForm h d*X 1*polynomial (2*t) ((adaptedMatrix h d u v t).mulVec
        (fun k ↦ c k.castSucc.castSucc))+
      c (Fin.last (2*t+1)).castSucc • (kernelForm h d*X 0^(2*t+1))+
      c (Fin.last (2*t+2)) • liftForm u v^(2*(t+1)) := by
  rw [polynomial_adapted_mulVec,polynomial_adapted_mulVec]
  simp only [adaptedPolynomials]
  exact (sum_snoc_two (n:=2*t+1) c _ _ _).trans (by rw [polynomial_sum_smul])

lemma eval_adapted_combination (h d u v : ℂ) (hu : u*h+v*d=1) (t : ℕ)
    (c : Form (R := ℂ) (2*(t+1))) :
    MvPolynomial.eval ![h,d] (polynomial (2*(t+1)) ((adaptedMatrix h d u v (t+1)).mulVec c))=
      c (Fin.last (2*t+2)) := by
  rw [adapted_combination_succ]
  simp [MvPolynomial.smul_eq_C_mul,hu,mul_comm d h]

def adaptedCoordinates (h d u v : ℂ) (t : ℕ) (p : Poly (R := ℂ)) : Form (R := ℂ) (2*t) :=
  (adaptedMatrix h d u v t)⁻¹.mulVec (coefficients (2*t) p)
lemma adaptedCoordinates_smul (h d u v : ℂ) (t : ℕ) (c : ℂ) (p : Poly (R := ℂ)) :
    adaptedCoordinates h d u v t (c • p)=c • adaptedCoordinates h d u v t p := by
  unfold adaptedCoordinates
  rw [coefficients_smul,Matrix.mulVec_smul]

lemma polynomial_adaptedCoordinates (h d u v : ℂ) (hu : u*h+v*d=1) (t : ℕ)
    {p : Poly (R := ℂ)} (hp : p.IsHomogeneous (2*t)) :
    polynomial (2*t) ((adaptedMatrix h d u v t).mulVec (adaptedCoordinates h d u v t p))=p := by
  rw [adaptedCoordinates,mulVec_mulVec,Matrix.mul_nonsing_inv _ (adaptedMatrix_det_unit h d u v hu t),one_mulVec]
  exact polynomial_coefficients hp
lemma adaptedCoordinates_combination (h d u v : ℂ) (hu : u*h+v*d=1) (t : ℕ)
    (c : Form (R := ℂ) (2*t)) :
    adaptedCoordinates h d u v t (polynomial (2*t) ((adaptedMatrix h d u v t).mulVec c))=c := by
  rw [adaptedCoordinates,coefficients_polynomial,mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (adaptedMatrix_det_unit h d u v hu t),one_mulVec]
lemma adaptedCoordinates_last (h d u v : ℂ) (hu : u*h+v*d=1) (t : ℕ)
    {p : Poly (R := ℂ)} (hp : p.IsHomogeneous (2*(t+1))) :
    adaptedCoordinates h d u v (t+1) p (Fin.last (2*t+2))=MvPolynomial.eval ![h,d] p := by
  rw [← polynomial_adaptedCoordinates h d u v hu (t+1) hp,
    eval_adapted_combination h d u v hu t,adaptedCoordinates_combination h d u v hu]

lemma adaptedCoordinates_residual (h d u v : ℂ) (hu : u*h+v*d=1) (t : ℕ)
    {p : Poly (R := ℂ)} (hp : p.IsHomogeneous (2*t)) :
    adaptedCoordinates h d u v (t+1) (kernelForm h d*X 1*p)=
      Fin.snoc (n:=2*t+2) (Fin.snoc (n:=2*t+1) (adaptedCoordinates h d u v t p) 0) 0 := by
  let c : Form (R := ℂ) (2*(t+1)) := Fin.snoc (n:=2*t+2) (Fin.snoc (n:=2*t+1) (adaptedCoordinates h d u v t p) 0) (0 : ℂ)
  have he : polynomial (2*(t+1)) ((adaptedMatrix h d u v (t+1)).mulVec c)=kernelForm h d*X 1*p := by
    rw [adapted_combination_succ]
    simp only [c,Fin.snoc_last,Fin.snoc_castSucc,zero_smul,add_zero]
    rw [polynomial_adaptedCoordinates h d u v hu t hp]
  rw [← he,adaptedCoordinates_combination h d u v hu]

lemma adaptedCoordinates_penultimate (h d u v : ℂ) (hu : u*h+v*d=1) (t : ℕ)
    {p : Poly (R := ℂ)} (hp : p.IsHomogeneous (2*t+1)) :
    adaptedCoordinates h d u v (t+1) (kernelForm h d*p) (Fin.last (2*t+1)).castSucc=
      MvPolynomial.eval ![1,0] p := by
  have hhp : (kernelForm h d*p).IsHomogeneous (2*(t+1)) := by
    convert (kernelForm_homogeneous h d).mul hp using 1; omega
  let c := adaptedCoordinates h d u v (t+1) (kernelForm h d*p)
  have hc0 : c (Fin.last (2*t+2))=0 := by
    change adaptedCoordinates h d u v (t+1) (kernelForm h d*p) (Fin.last (2*t+2))=0
    rw [adaptedCoordinates_last h d u v hu t hhp]
    simp [mul_comm d h]
  have he := polynomial_adaptedCoordinates h d u v hu (t+1) hhp
  change polynomial (2*(t+1)) ((adaptedMatrix h d u v (t+1)).mulVec c)=kernelForm h d*p at he
  rw [adapted_combination_succ,hc0,zero_smul,add_zero,MvPolynomial.smul_eq_C_mul] at he
  have he' : kernelForm h d*(X 1*polynomial (2*t) ((adaptedMatrix h d u v t).mulVec
      (fun k ↦ c k.castSucc.castSucc))+C (c (Fin.last (2*t+1)).castSucc)*X 0^(2*t+1))=
        kernelForm h d*p := by linear_combination he
  have he'' := mul_left_cancel₀ (kernelForm_ne_zero h d u v hu) he'
  have hev := congrArg (MvPolynomial.eval ![1,0]) he''
  simpa using hev
end
end QuadricCounterexample.BinaryForms

namespace QuadricCounterexample.BinaryForms
open MvPolynomial Matrix
open scoped BigOperators
noncomputable section
structure FlagFrame where
  h : ℂ
  d : ℂ
  u : ℂ
  v : ℂ
  bezout : u*h+v*d=1
namespace FlagFrame
def matrix (F : FlagFrame) (t : ℕ) := adaptedMatrix F.h F.d F.u F.v t
def column (F : FlagFrame) (t : ℕ) := adaptedPolynomials F.h F.d F.u F.v t
def coords (F : FlagFrame) (t : ℕ) := adaptedCoordinates F.h F.d F.u F.v t
lemma det_unit (F : FlagFrame) (t : ℕ) : IsUnit (F.matrix t).det :=
  adaptedMatrix_det_unit F.h F.d F.u F.v F.bezout t
end FlagFrame

structure FlagChange (F G : FlagFrame) where
  T : Matrix (Fin 2) (Fin 2) ℂ
  kernel : ℂ
  bottom : ℂ
  top : ℂ
  quotient : ℂ
  kernel_change : substitute T (kernelForm G.h G.d)=C kernel*kernelForm F.h F.d
  bottom_change : substitute T (X 1)=C bottom*X 1
  top_projection : MvPolynomial.eval ![1,0] (substitute T (X 0))=top
  lift_quotient : MvPolynomial.eval ![F.h,F.d] (substitute T (liftForm G.u G.v))=quotient
namespace FlagChange
variable {F G : FlagFrame} (H : FlagChange F G)
def matrix (t : ℕ) : Matrix (Fin (2*t+1)) (Fin (2*t+1)) ℂ :=
  (F.matrix t)⁻¹*symmetricMatrix (2*t) H.T*G.matrix t
lemma matrix_col (t : ℕ) (b : Fin (2*t+1)) :
    (H.matrix t).col b=F.coords t (substitute H.T (G.column t b)) := by
  have hcol {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (b : Fin n) :
      (A*B).col b=A.mulVec (B.col b) := rfl
  unfold matrix FlagFrame.coords adaptedCoordinates
  rw [hcol,← mulVec_mulVec]
  congr 1
  have hh := congrArg (coefficients (2*t))
    (polynomial_symmetricMatrix (2*t) H.T ((G.matrix t).col b))
  rw [coefficients_polynomial] at hh
  exact hh.trans (congrArg (coefficients (2*t) ∘ substitute H.T)
    (adaptedMatrix_columns G.h G.d G.u G.v t b))
lemma matrix_entry (t : ℕ) (a b : Fin (2*t+1)) :
    H.matrix t a b=F.coords t (substitute H.T (G.column t b)) a :=
  congrFun (H.matrix_col t b) a
lemma matrix_column_residual (t : ℕ) (b : Fin (2*t+1)) :
    (H.matrix (t+1)).col b.castSucc.castSucc=
      (H.kernel*H.bottom) • Fin.snoc (n:=2*t+2) (Fin.snoc (n:=2*t+1) ((H.matrix t).col b) 0) 0 := by
  rw [H.matrix_col]
  simp only [FlagFrame.column,adaptedPolynomials,Fin.snoc_castSucc]
  rw [map_mul,map_mul,H.kernel_change,H.bottom_change]
  have he : C H.kernel*kernelForm F.h F.d*(C H.bottom*X 1)*substitute H.T (G.column t b)=
      (H.kernel*H.bottom) • (kernelForm F.h F.d*X 1*substitute H.T (G.column t b)) := by
    rw [MvPolynomial.smul_eq_C_mul,map_mul]; ring
  dsimp only [FlagFrame.column] at he
  rw [he,FlagFrame.coords,adaptedCoordinates_smul,
    adaptedCoordinates_residual F.h F.d F.u F.v F.bezout t
      (substitute_homogeneous H.T (adaptedPolynomials_homogeneous G.h G.d G.u G.v t b))]
  rw [H.matrix_col]
  rfl

lemma matrix_pen_last (t : ℕ) :
    H.matrix (t+1) (Fin.last (2*t+2)) (Fin.last (2*t+1)).castSucc=0 := by
  rw [H.matrix_entry]
  simp only [FlagFrame.column,adaptedPolynomials,Fin.snoc_castSucc,Fin.snoc_last]
  change adaptedCoordinates F.h F.d F.u F.v (t+1)
    (substitute H.T (kernelForm G.h G.d*X 0^(2*t+1))) _=0
  have hp : (kernelForm G.h G.d*X 0^(2*t+1)).IsHomogeneous (2*(t+1)) := by
    convert (kernelForm_homogeneous G.h G.d).mul (isHomogeneous_X_pow (R:=ℂ) 0 (2*t+1)) using 1; omega
  rw [adaptedCoordinates_last F.h F.d F.u F.v F.bezout t (substitute_homogeneous H.T hp)]
  rw [map_mul,H.kernel_change]
  simp [mul_comm F.d F.h]
lemma matrix_pen_diag (t : ℕ) :
    H.matrix (t+1) (Fin.last (2*t+1)).castSucc (Fin.last (2*t+1)).castSucc=
      H.kernel*H.top^(2*t+1) := by
  rw [H.matrix_entry]
  simp only [FlagFrame.column,adaptedPolynomials,Fin.snoc_castSucc,Fin.snoc_last]
  rw [map_mul,H.kernel_change,map_pow]
  have he : C H.kernel*kernelForm F.h F.d*(substitute H.T (X 0))^(2*t+1)=
      kernelForm F.h F.d*(C H.kernel*(substitute H.T (X 0))^(2*t+1)) := by ring
  rw [he,FlagFrame.coords,adaptedCoordinates_penultimate F.h F.d F.u F.v F.bezout t]
  · simp only [map_mul,eval_C,map_pow,H.top_projection]
  · have hh := substitute_homogeneous H.T (isHomogeneous_X_pow (R:=ℂ) 0 (2*t+1))
    simpa only [map_pow] using hh.C_mul H.kernel
lemma matrix_last_diag (t : ℕ) :
    H.matrix (t+1) (Fin.last (2*t+2)) (Fin.last (2*t+2))=H.quotient^(2*(t+1)) := by
  rw [H.matrix_entry]
  simp only [FlagFrame.column,adaptedPolynomials,Fin.snoc_last]
  rw [FlagFrame.coords,adaptedCoordinates_last F.h F.d F.u F.v F.bezout t
    (substitute_homogeneous H.T (by simpa only [one_mul] using
      (liftForm_homogeneous G.u G.v).pow (2*(t+1))))]
  rw [map_pow,map_pow,H.lift_quotient]

def graded : (t : ℕ) → Fin (2*t+1) → ℂ
  | 0 => fun _ ↦ 1
  | t+1 => Fin.snoc (n:=2*t+2) (Fin.snoc (n:=2*t+1)
      (fun k ↦ (H.kernel*H.bottom)*graded t k) (H.kernel*H.top^(2*t+1))) (H.quotient^(2*(t+1)))
lemma matrix_zero : H.matrix 0=1 := by
  ext a b
  have ha : a=0 := Fin.ext (by omega)
  have hb : b=0 := Fin.ext (by omega)
  subst a; subst b
  rw [H.matrix_entry]
  change adaptedCoordinates F.h F.d F.u F.v 0 (substitute H.T 1) 0=1
  simp only [map_one]
  have he : (1 : Poly (R := ℂ))=polynomial 0 ((adaptedMatrix F.h F.d F.u F.v 0).mulVec (fun _ ↦ 1)) := by
    rw [polynomial_adapted_mulVec F.h F.d F.u F.v 0 (fun _ ↦ 1)]
    simp [adaptedPolynomials]
  rw [he,adaptedCoordinates_combination F.h F.d F.u F.v F.bezout]
lemma triangular_diagonal (t : ℕ) :
    (∀ a b : Fin (2*t+1),b<a → H.matrix t a b=0) ∧
    (∀ a : Fin (2*t+1),H.matrix t a a=H.graded t a) := by
  induction t with
  | zero =>
    constructor
    · intro a b h; have := a.isLt; have := b.isLt; omega
    · intro a; rw [H.matrix_zero]; simp [graded]
  | succ t ih =>
    have he (a : Fin (2*(t+1)+1)) (b : Fin (2*t+1)) := congrFun (H.matrix_column_residual t b) a
    constructor
    · intro a b hb
      revert hb
      refine Fin.lastCases (n:=2*t+2) (fun hb ↦ ?_) (fun b hb ↦ ?_) b
      · exact False.elim (by have := a.isLt; simp only [Fin.lt_def,Fin.val_last] at hb; omega)
      · revert hb
        refine Fin.lastCases (n:=2*t+1) (fun hb ↦ ?_) (fun b hb ↦ ?_) b
        · have ha : a=Fin.last (2*t+2) := Fin.ext (by
            have := a.isLt
            simp only [Fin.lt_def,Fin.val_castSucc,Fin.val_last] at hb ⊢
            omega)
          subst a
          exact H.matrix_pen_last t
        · revert hb
          refine Fin.lastCases (n:=2*t+2) (fun _ ↦ ?_) (fun a hb ↦ ?_) a
          · simpa only [Matrix.col_apply,Pi.smul_apply,smul_eq_mul,Fin.snoc_last,mul_zero] using he (Fin.last (2*t+2)) b
          · revert hb
            refine Fin.lastCases (n:=2*t+1) (fun _ ↦ ?_) (fun a hb ↦ ?_) a
            · simpa only [Matrix.col_apply,Pi.smul_apply,smul_eq_mul,Fin.snoc_castSucc,Fin.snoc_last,mul_zero]
                using he (Fin.last (2*t+1)).castSucc b
            · have hab : b<a := by exact hb
              simpa only [Matrix.col_apply,Pi.smul_apply,smul_eq_mul,Fin.snoc_castSucc,ih.1 a b hab,mul_zero]
                using he a.castSucc.castSucc b
    · intro a
      refine Fin.lastCases (n:=2*t+2) ?_ (fun a ↦ ?_) a
      · simpa only [graded,Fin.snoc_last] using H.matrix_last_diag t
      · refine Fin.lastCases (n:=2*t+1) ?_ (fun a ↦ ?_) a
        · simpa only [graded,Fin.snoc_castSucc,Fin.snoc_last] using H.matrix_pen_diag t
        · simpa only [Matrix.col_apply,Pi.smul_apply,smul_eq_mul,Fin.snoc_castSucc,graded,ih.2 a]
            using he a.castSucc.castSucc a
end FlagChange
end
end QuadricCounterexample.BinaryForms

end

end OAI
