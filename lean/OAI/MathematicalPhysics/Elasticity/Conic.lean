import OAI.MathematicalPhysics.Elasticity.CommonFrame

namespace OAI

section
noncomputable section
open scoped BigOperators Matrix
namespace ElasticityConic
open ElasticityFrame

/-- Polynomial coordinates on the finite chart of the actual constrained
rank-three fiber, including its scalar component. -/
def finiteCoordinates (z : ℂ) (p : Amp) : Fin 3 → ℂ :=
  ![(p.1 0-Complex.I*p.1 1)/2,p.1 2-z*((p.1 0-Complex.I*p.1 1)/2),p.2]
def finiteVector (z : ℂ) (c : Fin 3 → ℂ) : Amp :=
  (c 0 • h₁ 1 z+c 1 • h₂ 1 z,c 2)
lemma finiteVector_normal (z : ℂ) (c : Fin 3 → ℂ) :
    ElasticityFrame.normal (theta 1 z) (finiteVector z c)=0 := by
  change dotProduct (theta 1 z) (c 0 • h₁ 1 z+c 1 • h₂ 1 z)=0
  rw [dotProduct_add,dotProduct_smul,dotProduct_smul,theta_dot_h₁,theta_dot_h₂]
  simp only [smul_zero,add_zero]
lemma finiteCoordinates_vector (z : ℂ) (c : Fin 3 → ℂ) :
    finiteCoordinates z (finiteVector z c)=c := by
  ext i
  fin_cases i <;> simp [finiteCoordinates,finiteVector,h₁,h₂,smul_eq_mul]
  · linear_combination -(c 0+z*c 1)*Complex.I_sq/2
  · linear_combination z*(c 0+z*c 1)*Complex.I_sq/2
lemma finiteVector_coordinates (z : ℂ) (p : Amp)
    (hp : ElasticityFrame.normal (theta 1 z) p=0) :
    finiteVector z (finiteCoordinates z p)=p := by
  have hh : (1-z^2)*p.1 0+Complex.I*(1+z^2)*p.1 1+2*z*p.1 2=0 := by
    simpa [ElasticityFrame.normal,theta,Fin.sum_univ_three] using hp
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [finiteVector,finiteCoordinates,h₁,h₂,smul_eq_mul]
    · linear_combination -hh/2
    · linear_combination Complex.I*hh/2-p.1 1*Complex.I_sq
    · ring
  · rfl

def finiteChart (z : ℂ) : (Fin 3 → ℂ) ≃ₗ[ℂ] Fiber (theta 1 z) where
  toFun c := ⟨finiteVector z c,finiteVector_normal z c⟩
  invFun p := finiteCoordinates z p.val
  left_inv := finiteCoordinates_vector z
  right_inv p := Subtype.ext (finiteVector_coordinates z p.val p.property)
  map_add' c d := by
    apply Subtype.ext
    apply Prod.ext
    · change (c 0+d 0) • h₁ 1 z+(c 1+d 1) • h₂ 1 z=(c 0 • h₁ 1 z+c 1 • h₂ 1 z)+(d 0 • h₁ 1 z+d 1 • h₂ 1 z)
      simp only [add_smul]
      abel
    · rfl
  map_smul' a c := by
    apply Subtype.ext
    apply Prod.ext
    · change (a*c 0) • h₁ 1 z+(a*c 1) • h₂ 1 z=a • (c 0 • h₁ 1 z+c 1 • h₂ 1 z)
      simp only [smul_add,mul_smul]
    · rfl
end ElasticityConic

end
end
section
noncomputable section
open scoped BigOperators Matrix
namespace ElasticityConic
open ElasticityFrame

def chartZ₀ (b : Bool) (z : ℂ) : ℂ := if b then z else 1
def chartZ₁ (b : Bool) (z : ℂ) : ℂ := if b then 1 else z
def chartTheta (b : Bool) (z : ℂ) := theta (chartZ₀ b z) (chartZ₁ b z)
def chartVector (b : Bool) (z : ℂ) (c : Fin 3 → ℂ) : Amp :=
  (c 0 • h₁ (chartZ₀ b z) (chartZ₁ b z)+c 1 • h₂ (chartZ₀ b z) (chartZ₁ b z),c 2)
def chartCoord {A : Type*} [AddCommGroup A] [Module ℂ A] (b : Bool) (z : ℂ) (p : Fin 3 → A) (s : A) : Fin 3 → A :=
  if b then
    let c := -(1/2 : ℂ) • (p 0+Complex.I • p 1)
    ![p 2-z • c,c,s]
  else
    let c := (1/2 : ℂ) • (p 0-Complex.I • p 1)
    ![c,p 2-z • c,s]
lemma chartVector_normal (b : Bool) (z : ℂ) (c : Fin 3 → ℂ) :
    ElasticityFrame.normal (chartTheta b z) (chartVector b z c)=0 := by
  change dotProduct (theta _ _) (c 0 • h₁ _ _+c 1 • h₂ _ _)=0
  rw [dotProduct_add,dotProduct_smul,dotProduct_smul,theta_dot_h₁,theta_dot_h₂]
  simp only [smul_zero,add_zero]
lemma chartCoord_vector (b : Bool) (z : ℂ) (c : Fin 3 → ℂ) :
    chartCoord b z (chartVector b z c).1 (chartVector b z c).2=c := by
  ext i
  cases b <;> fin_cases i <;>
    simp [chartCoord,chartVector,chartZ₀,chartZ₁,h₁,h₂,smul_eq_mul]
  · linear_combination -(c 0+z*c 1)*Complex.I_sq/2
  · linear_combination z*(c 0+z*c 1)*Complex.I_sq/2
  · linear_combination z*(z*c 0+c 1)*Complex.I_sq/2
  · linear_combination -(z*c 0+c 1)*Complex.I_sq/2
lemma chartVector_coord (b : Bool) (z : ℂ) (p : Amp)
    (hp : ElasticityFrame.normal (chartTheta b z) p=0) :
    chartVector b z (chartCoord b z p.1 p.2)=p := by
  have hh := hp
  cases b
  · have hc : chartCoord false z p.1 p.2=finiteCoordinates z p := by
      ext i
      fin_cases i <;> simp [chartCoord,finiteCoordinates,smul_eq_mul,div_eq_mul_inv,mul_comm]
    rw [hc]
    exact finiteVector_coordinates z p hp
  · have he : (z^2-1)*p.1 0+Complex.I*(z^2+1)*p.1 1+2*z*p.1 2=0 := by
      simpa [ElasticityFrame.normal,chartTheta,theta,chartZ₀,chartZ₁,Fin.sum_univ_three] using hh
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [chartVector,chartCoord,chartZ₀,chartZ₁,h₁,h₂,smul_eq_mul]
      · linear_combination he/2
      · linear_combination Complex.I*he/2-p.1 1*Complex.I_sq
      · ring
    · rfl

def conicChart (b : Bool) (z : ℂ) : (Fin 3 → ℂ) ≃ₗ[ℂ] Fiber (chartTheta b z) where
  toFun c := ⟨chartVector b z c,chartVector_normal b z c⟩
  invFun p := chartCoord b z p.val.1 p.val.2
  left_inv := chartCoord_vector b z
  right_inv p := Subtype.ext (chartVector_coord b z p.val p.property)
  map_add' c d := by
    apply Subtype.ext
    apply Prod.ext
    · change (c 0+d 0) • h₁ _ _+(c 1+d 1) • h₂ _ _=
        (c 0 • h₁ _ _+c 1 • h₂ _ _)+(d 0 • h₁ _ _+d 1 • h₂ _ _)
      simp only [add_smul]
      abel
    · rfl
  map_smul' a c := by
    apply Subtype.ext
    apply Prod.ext
    · change (a*c 0) • h₁ _ _+(a*c 1) • h₂ _ _=a • (c 0 • h₁ _ _+c 1 • h₂ _ _)
      simp only [smul_add,mul_smul]
    · rfl
lemma chartTheta_ne_zero (b : Bool) (z : ℂ) : chartTheta b z≠0 := by
  cases b
  · exact theta_ne_zero (Or.inl one_ne_zero)
  · exact theta_ne_zero (Or.inr one_ne_zero)
lemma chartTheta_null (b : Bool) (z : ℂ) : ∑ i,chartTheta b z i*chartTheta b z i=0 :=
  theta_null _ _
end ElasticityConic

end
end
section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityAugmented
variable {n : Type*} [Fintype n] [DecidableEq n]
def smoothEval (x : X) : Smooth →+* ℂ :=
  (Pi.evalRingHom (fun _ : X => ℂ) x).comp Smooth.val.toRingHom
/-- Entrywise evaluation is an honest matrix ring homomorphism. -/
def matrixEval (x : X) : Matrix n n Smooth →+* Matrix n n ℂ :=
  (smoothEval x).mapMatrix
@[simp] lemma matrixEval_apply (x : X) (A : Matrix n n Smooth) (i j : n) :
    matrixEval x A i j=(A i j : X → ℂ) x := rfl

def matrixD (θ : Fin 3 → ℂ) (A : Matrix n n Smooth) : Matrix n n Smooth :=
  fun i j => thetaDerivation θ (A i j)
omit [DecidableEq n] in
lemma matrixD_mul (θ : Fin 3 → ℂ) (A B : Matrix n n Smooth) :
    matrixD θ (A*B)=matrixD θ A*B+A*matrixD θ B := by
  ext i j
  simp only [matrixD,Matrix.mul_apply,Matrix.add_apply,map_sum,Derivation.leibniz,
    smul_eq_mul,Finset.sum_add_distrib]
  simp only [mul_comm,add_comm]
omit [Fintype n] in
lemma matrixD_one (θ : Fin 3 → ℂ) : matrixD θ (1 : Matrix n n Smooth)=0 := by
  ext i j
  simp only [matrixD,Matrix.one_apply,Matrix.zero_apply]
  split_ifs <;> simp

lemma smoothMatrix_isUnit (A : Matrix n n Smooth) (hA : ∀ x,IsUnit (matrixEval x A)) :
    IsUnit A.det := by
  have hd (x : X) : (A.det : X → ℂ) x≠0 := by
    have he := (smoothEval x).map_det A
    change (A.det : X → ℂ) x=(matrixEval x A).det at he
    rw [he]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (hA x)).ne_zero
  exact isUnit_iff_exists_inv'.mpr ⟨smoothInv A.det hd,smoothInv_mul A.det hd⟩

/-- Smooth comparison from actual columns; only the original frame needs
invertibility. Equations are initially local and preserve their real domain. -/
theorem smooth_matrix_comparison {B K : Set X} (hK : IsClosed K)
    (θ : Fin 3 → ℂ) (M₀ M₁ Y₀ Y₁ : Matrix n n Smooth)
    (hY : ∀ x,IsUnit (matrixEval x Y₀))
    (he₀ : ∀ x∈B,matrixEval x (matrixD θ Y₀)=matrixEval x (M₀*Y₀))
    (he₁ : ∀ x∈B,matrixEval x (matrixD θ Y₁)=matrixEval x (M₁*Y₁))
    (hs : ∀ x∉K,matrixEval x Y₁=matrixEval x Y₀) :
    ∃ G : Matrix n n Smooth,
      (∀ i j,tsupport ((G i j-(1 : Matrix n n Smooth) i j : Smooth) : X → ℂ)⊆K) ∧
      (∀ x∈B,matrixEval x (matrixD θ G)=matrixEval x (M₁*G-G*M₀)) := by
  let G := Y₁*Y₀⁻¹
  have hd := smoothMatrix_isUnit Y₀ hY
  have hG : G*Y₀=Y₁ := by dsimp [G]; rw [mul_assoc,Matrix.nonsing_inv_mul _ hd,mul_one]
  have hDG : matrixD θ G*Y₀+G*matrixD θ Y₀=matrixD θ Y₁ := by
    rw [← matrixD_mul,hG]
  refine ⟨G,?_,?_⟩
  · intro i j
    apply closure_minimal _ hK
    intro x hx
    by_contra hn
    have he : matrixEval x G=1 := by
      dsimp [G]
      rw [map_mul,hs x hn,← map_mul,Matrix.mul_nonsing_inv _ hd,map_one]
    apply hx
    change (G i j : X → ℂ) x-((1 : Matrix n n Smooth) i j : X → ℂ) x=0
    have hentry := congrArg (fun A : Matrix n n ℂ => A i j) he
    change matrixEval x G i j-matrixEval x 1 i j=0
    rw [map_one,hentry,sub_self]
  · intro x hx
    have he := congrArg (matrixEval x) hDG
    simp only [map_add,map_mul] at he
    rw [he₀ x hx,he₁ x hx] at he
    simp only [map_mul] at he
    have hGX := congrArg (matrixEval x) hG
    simp only [map_mul] at hGX
    have hh : (matrixEval x (matrixD θ G)-matrixEval x (M₁*G-G*M₀))*matrixEval x Y₀=0 := by
      simp only [map_sub,map_mul]
      calc
        _ = matrixEval x (matrixD θ G)*matrixEval x Y₀+
            matrixEval x G*(matrixEval x M₀*matrixEval x Y₀)-
            matrixEval x M₁*(matrixEval x G*matrixEval x Y₀) := by noncomm_ring
        _ = 0 := by rw [he,hGX,sub_self]
    have hinv := congrArg (fun A : Matrix n n ℂ => A*matrixEval x (Y₀⁻¹)) hh
    rw [mul_assoc,← map_mul,Matrix.mul_nonsing_inv _ hd,map_one,mul_one,zero_mul] at hinv
    exact sub_eq_zero.mp hinv
end ElasticityAugmented

end
end
section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityConic
open ElasticityAugmented

def chartMatrix (b : Bool) (z : ℂ) (T : Smooth) (Q : Fin 3 → Smooth) : Matrix (Fin 3) (Fin 3) Smooth :=
  !![0,0,(chartZ₀ b z) • 1; 0,0,(chartZ₁ b z) • 1;
    (∑ i,h₁ (chartZ₀ b z) (chartZ₁ b z) i • Q i),
    (∑ i,h₂ (chartZ₀ b z) (chartZ₁ b z) i • Q i),T]
lemma chartCoord_apply (b : Bool) (z : ℂ) (p : Fin 3 → Smooth) (s : Smooth) (x : X) (i : Fin 3) :
    ((chartCoord b z p s i : Smooth) : X → ℂ) x=chartCoord b z (fun j => (p j : X → ℂ) x) ((s : X → ℂ) x) i := by
  cases b <;> fin_cases i <;> rfl
lemma chartCoord_deriv (θ : Fin 3 → ℂ) (b : Bool) (z : ℂ) (p : Fin 3 → Smooth) (s : Smooth) (i : Fin 3) :
    thetaDerivation θ (chartCoord b z p s i)=
      chartCoord b z (fun j => thetaDerivation θ (p j)) (thetaDerivation θ s) i := by
  cases b <;> fin_cases i <;>
    simp [chartCoord,map_sub,map_add]
lemma chartCoord_2 {A : Type*} [AddCommGroup A] [Module ℂ A]
    (b : Bool) (z : ℂ) (p : Fin 3 → A) (s : A) : chartCoord b z p s 2=s := by
  cases b <;> rfl
lemma chartCoord_top (b : Bool) (z s t : ℂ) (i : Fin 3) (hi : i≠2) :
    chartCoord b z (fun j => chartTheta b z j*s) t i=
      (if i=0 then chartZ₀ b z else chartZ₁ b z)*s := by
  have hc : i=0 ∨ i=1 := by omega
  cases b <;> rcases hc with rfl | rfl <;>
    simp [chartCoord,chartTheta,theta,chartZ₀,chartZ₁,smul_eq_mul]
  · linear_combination -(1+z^2)*s*Complex.I_sq/2
  · linear_combination z*(1+z^2)*s*Complex.I_sq/2
  · linear_combination z*(z^2+1)*s*Complex.I_sq/2
  · linear_combination -(z^2+1)*s*Complex.I_sq/2

/-- The chart connection is exactly the physical normal transport, rather
than a freely chosen augmented comparison equation. -/
lemma chart_transport_at (b : Bool) (z : ℂ) (T : Smooth) (Q p : Fin 3 → Smooth) (s : Smooth) (x : X)
    (hn : ElasticityFrame.normal (chartTheta b z) ((fun i => (p i : X → ℂ) x),(s : X → ℂ) x)=0)
    (hp : ∀ i,(direction (A := Smooth) coord (chartTheta b z) (p i) : X → ℂ) x=
      chartTheta b z i*(s : X → ℂ) x)
    (hs : (direction (A := Smooth) coord (chartTheta b z) s : X → ℂ) x=
      ((T*s+∑ i,Q i*p i : Smooth) : X → ℂ) x) (i : Fin 3) :
    (thetaDerivation (chartTheta b z) (chartCoord b z p s i) : X → ℂ) x=
      (matrixEval x (chartMatrix b z T Q)*ᵥ(fun j => ((chartCoord b z p s j : Smooth) : X → ℂ) x)) i := by
  rw [chartCoord_deriv,chartCoord_apply]
  simp only [thetaDerivation_apply,hp,hs]
  by_cases hi : i=2
  · subst i
    rw [chartCoord_2]
    have hd := congrArg Prod.fst (chartVector_coord b z
      ((fun j => (p j : X → ℂ) x),(s : X → ℂ) x) hn)
    have hdp (j : Fin 3) : (p j : X → ℂ) x=
        chartCoord b z (fun k => (p k : X → ℂ) x) ((s : X → ℂ) x) 0*h₁ (chartZ₀ b z) (chartZ₁ b z) j+
        chartCoord b z (fun k => (p k : X → ℂ) x) ((s : X → ℂ) x) 1*h₂ (chartZ₀ b z) (chartZ₁ b z) j := by
      exact (congrFun hd j).symm
    simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_three,chartMatrix,matrixEval_apply,
      Matrix.of_apply,Matrix.cons_val_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons,
      Subalgebra.coe_add,Subalgebra.coe_mul,Subalgebra.coe_smul,Pi.add_apply,Pi.mul_apply,Pi.smul_apply,
      smul_eq_mul,chartCoord_apply,chartCoord_2]
    rw [hdp 0,hdp 1,hdp 2]
    ring
  · rw [chartCoord_top b z _ _ i hi]
    have hc : i=0 ∨ i=1 := by omega
    rcases hc with rfl | rfl <;>
      simp [Matrix.mulVec,dotProduct,chartMatrix,Fin.sum_univ_three,chartCoord_2]
end ElasticityConic

end
end
section
noncomputable section
open Set
open scoped BigOperators
namespace ElasticityParameter
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma commutator_flatten {R : Type*} [CommRing R]
    (M₂ M₁ G : n → n → R) (i j : n) :
    (∑ k, (M₂ i k*G k j-G i k*M₁ k j))=
      ∑ q : n × n, ((if q.2=j then M₂ i q.1 else 0)-
        (if q.1=i then M₁ q.2 j else 0))*G q.1 q.2 := by
  rw [Fintype.sum_prod_type]
  simp only [sub_mul,Finset.sum_sub_distrib,ite_mul,zero_mul]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [mul_comm]

/-- The comparison equation on a holomorphic fiber chart forces holomorphy
in the parameter. Nullity supplies the injective real characteristic planes;
no compact-kernel or holomorphy premise for the unknown is present. -/
theorem matrix_holomorphic_of_supported_comparison
    (θ : Fin 3 → Smooth (X × ℂ))
    (hθx : ∀ r x z, (θ r : X × ℂ → ℂ) (x,z)=(θ r : X × ℂ → ℂ) (0,z))
    (hθ : ∀ r x, Differentiable ℂ (fun z => (θ r : X × ℂ → ℂ) (x,z)))
    (hnull : ∀ z, ∑ r, (θ r : X × ℂ → ℂ) (0,z)*(θ r : X × ℂ → ℂ) (0,z)=0)
    (hne : ∀ z, (fun r => (θ r : X × ℂ → ℂ) (0,z))≠0)
    (M₂ M₁ G : n → n → Smooth (X × ℂ))
    (hM₂ : ∀ i j x, Differentiable ℂ (fun z => (M₂ i j : X × ℂ → ℂ) (x,z)))
    (hM₁ : ∀ i j x, Differentiable ℂ (fun z => (M₁ i j : X × ℂ → ℂ) (x,z)))
    (he : ∀ i j, ∑ r, θ r*delta (basis r,0) (G i j)=
      ∑ k, (M₂ i k*G k j-G i k*M₁ k j))
    {S : Set X} (hS : IsCompact S)
    (hs : ∀ i j x, x∉S → ∀ z, (G i j : X × ℂ → ℂ) (x,z)=if i=j then 1 else 0) :
    ∀ i j x, Differentiable ℂ (fun z => (G i j : X × ℂ → ℂ) (x,z)) := by
  let a : (n × n) → (n × n) → Smooth (X × ℂ) := fun p q =>
    (if q.2=p.2 then M₂ p.1 q.1 else 0)-(if q.1=p.1 then M₁ q.2 p.2 else 0)
  have ha (p q : n × n) (x : X) :
      Differentiable ℂ (fun z => (a p q : X × ℂ → ℂ) (x,z)) := by
    dsimp only [a]
    split_ifs <;> simp only [Subalgebra.coe_sub,Pi.sub_apply,Subalgebra.coe_zero,Pi.zero_apply]
    · exact (hM₂ _ _ x).sub (hM₁ _ _ x)
    · exact (hM₂ _ _ x).sub (differentiable_const 0)
    · exact (differentiable_const 0).sub (hM₁ _ _ x)
    · exact (differentiable_const 0).sub (differentiable_const 0)
  have h := holomorphic_of_supported_transport basis θ hθx hθ
    (fun z => null_plane_injective _ (hnull z) (hne z)) a ha
    (fun p : n × n => G p.1 p.2) (fun p => (he p.1 p.2).trans
      (commutator_flatten M₂ M₁ G p.1 p.2)) hS
    (fun p : n × n => if p.1=p.2 then 1 else 0) (fun p => hs p.1 p.2)
  exact fun i j => h (i,j)
end ElasticityParameter

end
end
section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityAugmented
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma supported_matrix_eq_one {K : Set X} (G : Matrix n n Smooth)
    (hs : ∀ i j,tsupport ((G i j-(1 : Matrix n n Smooth) i j : Smooth) : X → ℂ)⊆K)
    (x : X) (hx : x∉K) : matrixEval x G=1 := by
  ext i j
  have hz := image_eq_zero_of_notMem_tsupport (fun hh => hx (hs i j hh))
  change (G i j : X → ℂ) x-((1 : Matrix n n Smooth) i j : X → ℂ) x=0 at hz
  have he : ((1 : Matrix n n Smooth) i j : X → ℂ) x=(1 : Matrix n n ℂ) i j := by
    have hh := congrArg (fun A : Matrix n n ℂ => A i j) (map_one (matrixEval (n := n) x))
    exact hh
  rw [he] at hz
  exact sub_eq_zero.mp hz

lemma globalize_matrix_comparison {B K : Set X} (hK : IsClosed K) (hKB : K⊆B)
    (θ : Fin 3 → ℂ) (M₀ M₁ G : Matrix n n Smooth)
    (hs : ∀ i j,tsupport ((G i j-(1 : Matrix n n Smooth) i j : Smooth) : X → ℂ)⊆K)
    (he : ∀ x∈B,matrixEval x (matrixD θ G)=matrixEval x (M₁*G-G*M₀))
    (hM : ∀ x∉K,matrixEval x M₀=matrixEval x M₁) :
    matrixD θ G=M₁*G-G*M₀ := by
  ext i j x
  by_cases hx : x∈B
  · exact congrArg (fun A : Matrix n n ℂ => A i j) (he x hx)
  · have hn : x∉K := fun hh => hx (hKB hh)
    have hG := supported_matrix_eq_one G hs x hn
    have hD : matrixEval x (matrixD θ G)=0 := by
      ext a b
      have hh := eqOn_direction hK.isOpen_compl θ (G a b) ((1 : Matrix n n Smooth) a b)
        (fun y hy => (congrArg (fun A : Matrix n n ℂ => A a b) (supported_matrix_eq_one G hs y hy)).trans
          (congrArg (fun A : Matrix n n ℂ => A a b) (map_one (matrixEval (n := n) y))).symm) hn
      change (thetaDerivation θ (G a b) : X → ℂ) x=(thetaDerivation θ ((1 : Matrix n n Smooth) a b) : X → ℂ) x at hh
      rw [show thetaDerivation θ ((1 : Matrix n n Smooth) a b)=0 from congrFun (congrFun (matrixD_one (n := n) θ) a) b] at hh
      exact hh
    have hh : matrixEval x (matrixD θ G)=matrixEval x (M₁*G-G*M₀) := by
      simp only [map_sub,map_mul,hD,hG,mul_one,one_mul,hM x hn,sub_self]
    exact congrArg (fun A : Matrix n n ℂ => A i j) hh

lemma matrixD_eval (θ : Fin 3 → ℂ) (G : Matrix n n Smooth) (x : X) (i j : n) :
    matrixEval x (matrixD θ G) i j=∑ r,θ r*fderiv ℝ (G i j : X → ℂ) x (ElasticityParameter.basis r) := by
  simp only [matrixEval_apply,matrixD,thetaDerivation_apply,direction,smooth_sum_eval,
    Subalgebra.coe_smul,Pi.smul_apply,smul_eq_mul]
  rfl

/-- The supported comparison is unique using the actual characteristic-plane
compact kernel theorem, not invertibility of the transferred frame. -/
theorem supported_matrix_unique (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
    (M₀ M₁ G H : Matrix n n Smooth)
    (heG : matrixD θ G=M₁*G-G*M₀) (heH : matrixD θ H=M₁*H-H*M₀)
    (hc : ∀ i j,HasCompactSupport ((G i j-H i j : Smooth) : X → ℂ)) : G=H := by
  let a : (n × n) → (n × n) → X → ℂ := fun p q x =>
    (if q.2=p.2 then (M₁ p.1 q.1 : X → ℂ) x else 0)-
      (if q.1=p.1 then (M₀ q.2 p.2 : X → ℂ) x else 0)
  have ha (p q : n × n) : Continuous (a p q) := by
    have h1 : Continuous (fun x : X => if q.2=p.2 then (M₁ p.1 q.1 : X → ℂ) x else 0) := by
      split_ifs
      · exact (show ContDiff ℝ (⊤ : ℕ∞) (M₁ p.1 q.1 : X → ℂ) from (M₁ p.1 q.1).property).continuous
      · exact continuous_const
    have h0 : Continuous (fun x : X => if q.1=p.1 then (M₀ q.2 p.2 : X → ℂ) x else 0) := by
      split_ifs
      · exact (show ContDiff ℝ (⊤ : ℕ∞) (M₀ q.2 p.2 : X → ℂ) from (M₀ q.2 p.2).property).continuous
      · exact continuous_const
    exact h1.sub h0
  have he : matrixD θ (G-H)=M₁*(G-H)-(G-H)*M₀ := by
    have hd : matrixD θ (G-H)=matrixD θ G-matrixD θ H := by funext i j; exact map_sub _ _ _
    rw [hd,heG,heH]
    simp only [mul_sub,sub_mul]
    abel
  have hz := ElasticityPlanar.spatial_compact_kernel
    (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ)
    (ElasticityParameter.null_plane_injective θ hθ hne) a ha
    (fun p : n × n => ((G p.1 p.2-H p.1 p.2 : Smooth) : X → ℂ))
    (fun p => (G p.1 p.2-H p.1 p.2 : Smooth).property) (fun p => hc p.1 p.2)
    (fun p x => ?_)
  · ext i j x
    exact sub_eq_zero.mp (hz (i,j) x)
  · rw [ElasticityParameter.characteristicPlane_principal]
    have hh := congrArg (fun A : Matrix n n Smooth => matrixEval x A p.1 p.2) he
    rw [matrixD_eval] at hh
    simp only [map_sub,map_mul,Matrix.sub_apply,Matrix.mul_apply,← Finset.sum_sub_distrib] at hh
    exact hh.trans (ElasticityParameter.commutator_flatten (matrixEval x M₁) (matrixEval x M₀)
      (matrixEval x (G-H)) p.1 p.2)
end ElasticityAugmented

end
end
section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityConic
open ElasticityAugmented

/-- Convert the actual physical rank-three fiber basis to a chart matrix;
there is no assumption that the transferred columns are a basis. -/
theorem chart_frame_comparison {U K : Set X} (hK : IsClosed K) (hKU : K⊆U)
    (b : Bool) (z : ℂ) (T : Fin 2 → Smooth) (Q : Fin 2 → Fin 3 → Smooth)
    (p : Fin 2 → Fin 3 → Fin 3 → Smooth) (s : Fin 2 → Fin 3 → Smooth)
    (B : X → Module.Basis (Fin 3) ℂ (ElasticityFrame.Fiber (chartTheta b z)))
    (hn : ∀ q ν,normal (chartTheta b z) (p q ν)=0)
    (he : ∀ q ν x,x∈U →
      (∀ i,(direction (A := Smooth) coord (chartTheta b z) (p q ν i) : X → ℂ) x=
        chartTheta b z i*(s q ν : X → ℂ) x) ∧
      (direction (A := Smooth) coord (chartTheta b z) (s q ν) : X → ℂ) x=
        ((T q*s q ν+∑ i,Q q i*p q ν i : Smooth) : X → ℂ) x)
    (hs : ∀ ν x,x∉K → (∀ i,(p 0 ν i : X → ℂ) x=(p 1 ν i : X → ℂ) x) ∧
      (s 0 ν : X → ℂ) x=(s 1 ν : X → ℂ) x)
    (hB : ∀ ν x,((B x ν : ElasticityFrame.Fiber (chartTheta b z)) : ElasticityFrame.Amp)=
      ((fun i => (p 0 ν i : X → ℂ) x),(s 0 ν : X → ℂ) x))
    (hT : ∀ x∉K,(T 0 : X → ℂ) x=(T 1 : X → ℂ) x)
    (hQ : ∀ i x,x∉K → (Q 0 i : X → ℂ) x=(Q 1 i : X → ℂ) x) :
    ∃ G : Matrix (Fin 3) (Fin 3) Smooth,
      (∀ i j,tsupport ((G i j-(1 : Matrix (Fin 3) (Fin 3) Smooth) i j : Smooth) : X → ℂ)⊆K) ∧
      matrixD (chartTheta b z) G=chartMatrix b z (T 1) (Q 1)*G-G*chartMatrix b z (T 0) (Q 0) := by
  let Y : Fin 2 → Matrix (Fin 3) (Fin 3) Smooth := fun q i ν => chartCoord b z (p q ν) (s q ν) i
  have hunit (x : X) : IsUnit (matrixEval x (Y 0)) := by
    apply Matrix.linearIndependent_cols_iff_isUnit.mp
    let C := (B x).map (conicChart b z).symm
    have hCb : (C : Fin 3 → Fin 3 → ℂ)=(fun ν => (matrixEval x (Y 0)).col ν) := by
      funext ν i
      change chartCoord b z (B x ν).val.1 (B x ν).val.2 i=_
      rw [hB]
      exact (chartCoord_apply b z (p 0 ν) (s 0 ν) x i).symm
    change LinearIndependent ℂ (fun ν => (matrixEval x (Y 0)).col ν)
    exact hCb ▸ C.linearIndependent
  have hEq (q x) (hx : x∈U) :
      matrixEval x (matrixD (chartTheta b z) (Y q))=
        matrixEval x (chartMatrix b z (T q) (Q q)*Y q) := by
    ext i ν
    have hn' : ElasticityFrame.normal (chartTheta b z)
        ((fun i => (p q ν i : X → ℂ) x),(s q ν : X → ℂ) x)=0 := by
      have hh := congrArg (fun f : Smooth => (f : X → ℂ) x) (hn q ν)
      change (∑ i,chartTheta b z i*(p q ν i : X → ℂ) x)=0
      simpa only [normal,dotProduct,smooth_sum_eval,
        Subalgebra.coe_smul,Pi.smul_apply,smul_eq_mul,Subalgebra.coe_zero,Pi.zero_apply] using hh
    have hh := chart_transport_at b z (T q) (Q q) (p q ν) (s q ν) x hn' (he q ν x hx).1 (he q ν x hx).2 i
    rw [map_mul]
    exact hh
  have hext (x : X) (hx : x∉K) : matrixEval x (Y 1)=matrixEval x (Y 0) := by
    ext i ν
    change ((chartCoord b z (p 1 ν) (s 1 ν) i : Smooth) : X → ℂ) x=
      ((chartCoord b z (p 0 ν) (s 0 ν) i : Smooth) : X → ℂ) x
    rw [chartCoord_apply,chartCoord_apply,(hs ν x hx).2,funext ((hs ν x hx).1)]
  obtain ⟨G,hGs,hGe⟩ := smooth_matrix_comparison hK (chartTheta b z)
    (chartMatrix b z (T 0) (Q 0)) (chartMatrix b z (T 1) (Q 1)) (Y 0) (Y 1)
    hunit (hEq 0) (hEq 1) hext
  refine ⟨G,hGs,globalize_matrix_comparison hK hKU (chartTheta b z) _ _ G hGs hGe ?_⟩
  intro x hx
  ext i j
  change ((chartMatrix b z (T 0) (Q 0) i j : Smooth) : X → ℂ) x=
    ((chartMatrix b z (T 1) (Q 1) i j : Smooth) : X → ℂ) x
  have hq : ∀ k,(Q 0 k : X → ℂ) x=(Q 1 k : X → ℂ) x := fun k => hQ k x hx
  fin_cases i <;> fin_cases j <;> simp [chartMatrix,smooth_sum_eval,hq,hT x hx]
end ElasticityConic

end
end
section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace Elasticity
open ElasticityAugmented ElasticityCGO ElasticityConic
open ElasticityCoeffBounds (ExteriorConstant)

/-- Supported global commutator comparison on EACH conic chart, constructed
from equality of the physical DN map on the original domain. -/
theorem dn_conic_comparison {Ω : Set X} (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω)
    (r₀ : ℝ) (hr₀ : 1≤r₀) (hK : closure Ω⊆Metric.closedBall 0 r₀)
    (lam m : Fin 2 → X → ℝ)
    (hl : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (lam q)) (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q))
    (hp : ∀ q x,0 < m q x ∧ 0<3*lam q x+2*m q x)
    (hcll : ∀ q,ExteriorConstant (smoothOfReal (lam q) (hl q)))
    (hclm : ∀ q,ExteriorConstant (smoothOfReal (m q) (hm q)))
    (he : ∀ x∉Ω,lam 0 x=lam 1 x ∧ m 0 x=m 1 x)
    (hDN : DN Ω (lam 0) (m 0)=DN Ω (lam 1) (m 1)) (b : Bool) (z : ℂ) :
    let k := fun q => smoothOfReal (lam q) (hl q)+smoothOfReal (m q) (hm q)
    let r := fun q => positiveRoot (m q) (hm q) (fun x => (hp q x).1)
    let hr := fun q => positiveRoot_nonzero (m q) (hm q) (fun x => (hp q x).1)
    ∀ hk : ∀ q x,(k q : X → ℂ) x≠0,
    ∀ hL : ∀ q x,((k q+r q*r q : Smooth) : X → ℂ) x≠0,
    let M := fun q => chartMatrix b z (transportT (chartTheta b z) (k q) (r q) (hk q) (hL q))
      (transportQ (chartTheta b z) (k q) (r q) (hr q) (hk q) (hL q))
    ∃ G : Matrix (Fin 3) (Fin 3) Smooth,
      (∀ i j,tsupport ((G i j-(1 : Matrix (Fin 3) (Fin 3) Smooth) i j : Smooth) : X → ℂ)⊆closure Ω) ∧
      matrixD (chartTheta b z) G=M 1*G-G*M 0 := by
  intro k r hr hk hL M
  obtain ⟨hk',hL',p,s,B,hn,hE,hs,hB⟩ := dn_common_normal_frame hΩ hOB r₀ hr₀ hK (chartTheta b z)
    (chartTheta_null b z) (chartTheta_ne_zero b z) lam m hl hm hp hcll hclm he hDN
  have hkE : EqOn (k 0 : X → ℂ) (k 1) (closure Ω)ᶜ := by
    intro y hy
    have hy' : y∉Ω := fun hyΩ => hy (subset_closure hyΩ)
    change (lam 0 y : ℂ)+(m 0 y : ℂ)=(lam 1 y : ℂ)+(m 1 y : ℂ)
    rw [(he y hy').1,(he y hy').2]
  have hrE : EqOn (r 0 : X → ℂ) (r 1) (closure Ω)ᶜ := by
    intro y hy
    change (Real.sqrt (m 0 y) : ℂ)=(Real.sqrt (m 1 y) : ℂ)
    rw [(he y (fun hyΩ => hy (subset_closure hyΩ))).2]
  have hMQ := eqOn_transport isClosed_closure.isOpen_compl (chartTheta b z) (k 0) (k 1) (r 0) (r 1)
    (hr 0) (hr 1) (hk 0) (hk 1) (hL 0) (hL 1) hkE hrE
  exact chart_frame_comparison isClosed_closure (hK.trans (Metric.closedBall_subset_ball (by linarith))) b z
    (fun q => transportT (chartTheta b z) (k q) (r q) (hk q) (hL q))
    (fun q => transportQ (chartTheta b z) (k q) (r q) (hr q) (hk q) (hL q))
    p s B hn hE hs hB (fun x hx => hMQ.1 hx) (fun i x hx => hMQ.2 i hx)
end Elasticity

end
end

end OAI
