import OAI.Geometry.QuadricBundles.ProjectiveEquations

namespace OAI

universe u1 u2 u3

noncomputable section

namespace QuadricCounterexample
open Set MvPolynomial Matrix LaurentCech BinaryForms PolynomialGeneration
open scoped BigOperators
noncomputable section

namespace AlgebraicRankTwoBundle
variable (V : AlgebraicRankTwoBundle)
lemma dualTransition_self (i : ℕ) (x : QuadricSurface) (hx : x∈V.domain i) :
    V.dualTransition i i x=1 := by
  unfold dualTransition
  rw [V.transition_self i x hx,Matrix.transpose_one]
lemma dualTransition_mul (i j k : ℕ) (x : QuadricSurface)
    (hi : x∈V.domain i) (hj : x∈V.domain j) (hk : x∈V.domain k) :
    V.dualTransition i j x*V.dualTransition j k x=V.dualTransition i k x := by
  unfold dualTransition
  rw [← Matrix.transpose_mul,V.transition_mul k j i x hk hj hi]
lemma dualTransition_nonzero (i j : ℕ) (x : QuadricSurface)
    (hi : x∈V.domain i) (hj : x∈V.domain j) {v : FiberCoordinates} (hv : v≠0) :
    (V.dualTransition i j x).mulVec v≠0 := by
  intro hz
  have hh := congrArg (V.dualTransition j i x).mulVec hz
  rw [Matrix.mulVec_mulVec,V.dualTransition_mul j i j x hj hi hj,V.dualTransition_self j x hj,
    Matrix.one_mulVec,Matrix.mulVec_zero] at hh
  exact hv hh
end AlgebraicRankTwoBundle
lemma sectionVector_compatible {V : AlgebraicRankTwoBundle} {n N : ℕ}
    (s : Fin N → SymmetricSection V n) (i j : ℕ) (x : QuadricSurface)
    (hi : x∈V.domain i) (hj : x∈V.domain j) (v : FiberCoordinates) :
    sectionVector s i x ((V.dualTransition i j x).mulVec v)=sectionVector s j x v := by
  ext a
  exact (s a).compatible i j x hi hj v

structure StandardBundleCover (V : AlgebraicRankTwoBundle) : Prop where
  domain : ∀ i x,x∈V.domain i ↔ i<4 ∧ x∈range (affineQuadric (V.chart i))
  surj : ∀ a : StandardChart,∃ i : ℕ,i<4 ∧ V.chart i=a

namespace StandardBundleCover
variable {V : AlgebraicRankTwoBundle} (H : StandardBundleCover V)
def chartIndex (a : StandardChart) : ℕ := (H.surj a).choose
lemma chartIndex_lt (a : StandardChart) : H.chartIndex a<4 := (H.surj a).choose_spec.1
lemma chartIndex_chart (a : StandardChart) : V.chart (H.chartIndex a)=a := (H.surj a).choose_spec.2
lemma chartIndex_mem (a : StandardChart) (z : BaseCoordinates) : affineQuadric a z∈V.domain (H.chartIndex a) := by
  rw [H.domain,H.chartIndex_chart]
  exact ⟨H.chartIndex_lt a,⟨z,rfl⟩⟩
end StandardBundleCover

structure SegreSectionSystem (V : AlgebraicRankTwoBundle) (n : ℕ) (ι : Type u1) [Fintype ι] where
  cover : StandardBundleCover V
  generation : PolynomialGeneration n ι
  sections : ProjectiveIndex ι → SymmetricSection V n
  value_eq : ∀ i x,x∈V.domain i → ∀ v : FiberCoordinates,
    sectionVector sections i x v=generation.value (V.chart i) (coordQuadric (V.chart i) x) v

namespace SegreSectionSystem
variable {V : AlgebraicRankTwoBundle} {n : ℕ} {ι : Type u2} [Fintype ι] (S : SegreSectionSystem V n ι)
lemma nonzero (i : ℕ) (x : QuadricSurface) (hx : x∈V.domain i) {v : FiberCoordinates} (hv : v≠0) :
    sectionVector S.sections i x v≠0 := by
  rw [S.value_eq i x hx]
  exact S.generation.value_nonzero _ _ hv
lemma pivot_domain (i : ℕ) (hi : i<4) (j : ℕ) (x : QuadricSurface) (hx : x∈V.domain j)
    (v : FiberCoordinates) (q : ι) (hq : sectionVector S.sections j x v (index (V.chart i,q))≠0) :
    x∈V.domain i := by
  rw [S.value_eq j x hx] at hq
  change S.generation.stencil (V.chart j) (coordQuadric (V.chart j) x) (veronese n v) _≠0 at hq
  rw [S.generation.stencil_index] at hq
  have ho := (segreFactor_ne_zero_iff (V.chart i) (V.chart j) (coordQuadric (V.chart j) x)).mp
    (mul_ne_zero_iff.mp hq).1
  rw [S.cover.domain]
  refine ⟨hi,?_⟩
  rw [← affineQuadric_mem_range] at ho
  simpa only [affineQuadric_coord ((S.cover.domain j x).mp hx).2] using ho
lemma localize_pivot (j : ProjectiveIndex ι) (i : ℕ) (x : QuadricSurface) (hx : x∈V.domain i)
    (v : FiberCoordinates) (hv : v≠0) (hj : sectionVector S.sections i x v j≠0) :
    ∃ z : BaseCoordinates,∃ w : FiberCoordinates,w≠0 ∧
      sectionVector S.sections i x v=S.generation.value (label j).1 z w := by
  let a := (label j).1
  let k := S.cover.chartIndex a
  have hk : x∈V.domain k := by
    apply S.pivot_domain k (S.cover.chartIndex_lt a) i x hx v (label j).2
    simpa only [k,S.cover.chartIndex_chart,a,Prod.eta,index_label] using hj
  refine ⟨coordQuadric a x,(V.dualTransition k i x).mulVec v,
    V.dualTransition_nonzero k i x hk hx hv,?_⟩
  rw [← sectionVector_compatible S.sections k i x hk hx v,S.value_eq k x hk]
  simp only [k,S.cover.chartIndex_chart,a]

lemma pivot_coordinates (i : ℕ) (x : QuadricSurface) (hx : x∈V.domain i) (v : FiberCoordinates)
    (q : ι) (hq : sectionVector S.sections i x v (index (V.chart i,q))≠0) :
    patchCoordinates (V.chart i) q (normalize (index (V.chart i,q)) (sectionVector S.sections i x v))=
      coordQuadric (V.chart i) x := by
  rw [S.value_eq i x hx] at hq ⊢
  exact S.generation.patchCoordinates_stencil _ _ _ _ hq
lemma pivot_recovery (i : ℕ) (x : QuadricSurface) (hx : x∈V.domain i) (v : FiberCoordinates)
    (q : ι) (hq : sectionVector S.sections i x v (index (V.chart i,q))≠0) :
    S.generation.patchRecovery (V.chart i) q (normalize (index (V.chart i,q)) (sectionVector S.sections i x v))=
      (sectionVector S.sections i x v (index (V.chart i,q)))⁻¹ • veronese n v := by
  rw [S.value_eq i x hx] at hq ⊢
  exact S.generation.patchRecovery_stencil _ _ _ _ hq
lemma exists_pivot (i : ℕ) (x : QuadricSurface) (hx : x∈V.domain i) (v : FiberCoordinates) (hv : v≠0) :
    ∃ q : ι,sectionVector S.sections i x v (index (V.chart i,q))≠0 := by
  have hn := S.generation.matrix_nonzero (V.chart i) (coordQuadric (V.chart i) x) (veronese_nonzero n hv)
  by_contra hh
  apply hn
  ext q
  have he : sectionVector S.sections i x v (index (V.chart i,q))=0 := by
    by_contra he; exact hh ⟨q,he⟩
  rw [S.value_eq i x hx] at he
  simpa only [PolynomialGeneration.value,S.generation.stencil_self,Pi.zero_apply] using he

lemma injective (hn : 0<n) (i j : ℕ) (x y : QuadricSurface) (hx : x∈V.domain i) (hy : y∈V.domain j)
    (v w : FiberCoordinates) (hv : v≠0) (hw : w≠0) (c : ℂ) (hc : c≠0)
    (h : sectionVector S.sections i x v=c • sectionVector S.sections j y w) :
    x=y ∧ ∃ d : ℂ,d≠0 ∧ v=d • ((V.dualTransition i j x).mulVec w) := by
  obtain ⟨q,hq⟩ := S.exists_pivot i x hx v hv
  have hqy : sectionVector S.sections j y w (index (V.chart i,q))≠0 := by
    rw [h] at hq
    exact (mul_ne_zero_iff.mp hq).2
  have hyi := S.pivot_domain i ((S.cover.domain i x).mp hx).1 j y hy w q hqy
  let w' := (V.dualTransition i j y).mulVec w
  have hw' : w'≠0 := V.dualTransition_nonzero i j y hyi hy hw
  have hchange : sectionVector S.sections i y w'=sectionVector S.sections j y w :=
    sectionVector_compatible S.sections i j y hyi hy w
  have hpq : sectionVector S.sections i y w' (index (V.chart i,q))≠0 := by rwa [hchange]
  have hnorm : normalize (index (V.chart i,q)) (sectionVector S.sections i x v)=
      normalize (index (V.chart i,q)) (sectionVector S.sections i y w') := by
    rw [h,normalize_smul _ _ c hc,hchange]
  have hz := congrArg (patchCoordinates (V.chart i) q) hnorm
  rw [S.pivot_coordinates i x hx v q hq,S.pivot_coordinates i y hyi w' q hpq] at hz
  have hxy : x=y := by
    have he := congrArg (affineQuadric (V.chart i)) hz
    simpa only [affineQuadric_coord ((S.cover.domain i x).mp hx).2,
      affineQuadric_coord ((S.cover.domain i y).mp hyi).2] using he
  refine ⟨hxy,?_⟩
  subst y
  have hlocal : sectionVector S.sections i x v=c • sectionVector S.sections i x w' := by rwa [hchange]
  have hblock := congrArg (block (V.chart i)) hlocal
  rw [S.value_eq i x hx,S.value_eq i x hx] at hblock
  have he : (S.generation.matrix (V.chart i) (coordQuadric (V.chart i) x)).transpose.mulVec (veronese n v)=
      c • (S.generation.matrix (V.chart i) (coordQuadric (V.chart i) x)).transpose.mulVec (veronese n w') := by
    ext r
    simpa only [block,PolynomialGeneration.value,Pi.smul_apply,S.generation.stencil_self] using congrFun hblock r
  have hre := congrArg (S.generation.recover (V.chart i) (coordQuadric (V.chart i) x)).mulVec he
  rw [Matrix.mulVec_smul,S.generation.recover_matrix,S.generation.recover_matrix] at hre
  exact veronese_projective_injective n hn v w' hw' c hc hre
end SegreSectionSystem
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set MvPolynomial Matrix LaurentCech BinaryForms PolynomialGeneration
open scoped BigOperators
noncomputable section

lemma lineFactor_add (a b : ℕ × ℕ) (i j : StandardChart) (z : BaseCoordinates) :
    lineFactor (a.1+b.1,a.2+b.2) i j z=lineFactor a i j z*lineFactor b i j z := by
  simp only [lineFactor,pow_add]
  ring
lemma lineFactor_diagonal (n : ℕ) (i j : StandardChart) (z : BaseCoordinates) :
    lineFactor (n,n) i j z=(firstFactor i j z*secondFactor i j z)^n := by simp only [lineFactor,mul_pow]
lemma eval_polynomial_smul_vector (n : ℕ) (p : Form (R:=ℂ) n) (c : ℂ) (v : FiberCoordinates) :
    MvPolynomial.eval (c • v) (polynomial n p)=c^n*MvPolynomial.eval v (polynomial n p) := by
  simp only [eval_polynomial,Pi.smul_apply,smul_eq_mul,mul_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hk : k.val+(n-k.val)=n := by omega
  calc
    _ = (c^k.val*c^(n-k.val))*(p k*v 0^k.val*v 1^(n-k.val)) := by ring
    _ = _ := by rw [← pow_add,hk]
lemma eval_polynomial_smul_coeff (n : ℕ) (p : Form (R:=ℂ) n) (c : ℂ) (v : FiberCoordinates) :
    MvPolynomial.eval v (polynomial n (c • p))=c*MvPolynomial.eval v (polynomial n p) := by
  simp only [eval_polynomial,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring
lemma polynomial_eval_dot (n : ℕ) (p : Form (R:=ℂ) n) (v : FiberCoordinates) :
    MvPolynomial.eval v (polynomial n p)=dotProduct p (veronese n v) := by
  rw [eval_polynomial]
  unfold dotProduct veronese
  apply Finset.sum_congr rfl
  intro k _
  ring

namespace EqualizerData
variable (D : EqualizerData)
lemma powerTwist_cover (m : ℕ) (hm : 0 < m) : StandardBundleCover (powerPullbackTwist D.bundle m hm) where
  domain i x := by
    change x∈principalChart (standardChartNat i) (pullbackPolynomial m (standardEquationNat i)) ↔ _
    by_cases hi : i<4
    · simp only [standardEquationNat,ite_eq_left hi,pullbackPolynomial,map_one,principalChart_one]
      exact ⟨fun h ↦ ⟨hi,h⟩,fun h ↦ h.2⟩
    · simp [standardEquationNat,hi,pullbackPolynomial,principalChart,baseEval]
  surj := standardChartNat_surj

def fullSymmetricCoefficient (m e t : ℕ) (he : 3*m≤e)
    (a i : StandardChart) (q : SymmetricGeneratorIndex t) : Fin (2*t+1) → BasePolynomial :=
  fun k ↦ lineGenerator (1,1) a i*(D.symmetricGeneration m e t he).coefficient i k q
lemma fullSymmetricCoefficient_value (m e t : ℕ) (he : 3*m≤e)
    (a i : StandardChart) (q : SymmetricGeneratorIndex t) (z : BaseCoordinates) :
    (fun k ↦ baseEval (D.fullSymmetricCoefficient m e t he a i q k) z)=
      segreFactor a i z • (D.symmetricGeneratorValue m e t he i z).col q := by
  ext k
  simp only [fullSymmetricCoefficient,baseEval_mul,Pi.smul_apply,smul_eq_mul]
  change segreFactor a i z*(D.symmetricGeneration m e t he).matrix i z k q=_
  rw [D.symmetricGeneration_matrix]
  rfl
lemma fullSymmetricCoefficient_compatible (m e t : ℕ) (he : 3*m≤e)
    (a i j : StandardChart) (q : SymmetricGeneratorIndex t) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) :
    (fun k ↦ baseEval (D.fullSymmetricCoefficient m e t he a i q k) z)=
      lineFactor (e+1,e+1) i j z • (symmetricMatrix (2*t) (D.coordinateTransition i j (powerCoordinates m z))).mulVec
        (fun k ↦ baseEval (D.fullSymmetricCoefficient m e t he a j q k) (coordinateChange i j z)) := by
  rw [D.fullSymmetricCoefficient_value,D.fullSymmetricCoefficient_value,D.symmetricGeneratorValue_compatible m e t he i j hz q,
    Matrix.mulVec_smul,smul_smul,smul_smul]
  congr 1
  have h := lineGenerator_compatible (1,1) a i j hz
  change lineFactor (1,1) i j z*segreFactor a j (coordinateChange i j z)=segreFactor a i z at h
  rw [← h,show (e+1,e+1)=(e+1,e+1) from rfl,lineFactor_add (e,e) (1,1)]
  ring

lemma powerTwist_transition (m : ℕ) (hm : 0 < m) (i j : ℕ) (x : QuadricSurface)
    (hx : x∈(powerPullbackTwist D.bundle m hm).domain i) :
    (powerPullbackTwist D.bundle m hm).transition i j x=
      (firstFactor (standardChartNat i) (standardChartNat j) (coordQuadric (standardChartNat i) x)*
       secondFactor (standardChartNat i) (standardChartNat j) (coordQuadric (standardChartNat i) x)) •
      D.coordinateTransition (standardChartNat i) (standardChartNat j)
        (powerCoordinates m (coordQuadric (standardChartNat i) x)) := by
  have hr := ((D.powerTwist_cover m hm).domain i x).mp hx |>.2
  have he := affineQuadric_coord hr
  conv_lhs => rw [← he]
  simp only [powerPullbackTwist,bundle,globalTransition,powerQuadric_affine hm,coordQuadric_affine]
  congr 1
  rw [firstFactor_transition,secondFactor_transition]
  rfl

def ampleSection (m : ℕ) (hm : 0 < m) (e t : ℕ) (he : 3*m≤e) (hen : e+1=2*t)
    (a : StandardChart) (q : SymmetricGeneratorIndex t) : SymmetricSection (powerPullbackTwist D.bundle m hm) (2*t) where
  coefficient := fun i k z ↦ baseEval (D.fullSymmetricCoefficient m e t he a (standardChartNat i) q k) z
  regular := fun i k ↦ algebraicallyRegular_polynomial _ _
  compatible := by
    intro i j x hi hj v
    let E := powerPullbackTwist D.bundle m hm
    let ci := standardChartNat i
    let cj := standardChartNat j
    let z := coordQuadric cj x
    have hjr : x∈range (affineQuadric cj) := ((D.powerTwist_cover m hm).domain j x).mp hj |>.2
    have hir : x∈range (affineQuadric ci) := ((D.powerTwist_cover m hm).domain i x).mp hi |>.2
    have hz : z∈coordinateOverlap cj ci := coord_mem_overlap cj ci hjr hir
    have hchange : coordinateChange cj ci z=coordQuadric ci x := by
      rw [← coordinateChange_coord]
      change coordQuadric ci (affineQuadric cj (coordQuadric cj x))=_
      rw [affineQuadric_coord hjr]
    have hQ := D.fullSymmetricCoefficient_compatible m e t he a cj ci q hz
    rw [hchange,hen] at hQ
    let p : Form (R:=ℂ) (2*t) := fun k ↦ baseEval (D.fullSymmetricCoefficient m e t he a ci q k) (coordQuadric ci x)
    let T := D.coordinateTransition cj ci (powerCoordinates m z)
    let l := firstFactor cj ci z*secondFactor cj ci z
    have hdual : E.dualTransition i j x=l • T.transpose := by
      unfold AlgebraicRankTwoBundle.dualTransition
      rw [D.powerTwist_transition m hm j i x hj,Matrix.transpose_smul]
    change (∑ k : Fin (2*t+1),p k*((E.dualTransition i j x).mulVec v 0)^k.val*
      ((E.dualTransition i j x).mulVec v 1)^(2*t-k.val))=_
    rw [← eval_polynomial,hdual,Matrix.smul_mulVec,eval_polynomial_smul_vector]
    rw [← eval_polynomial]
    change _=MvPolynomial.eval v (polynomial (2*t) (fun k ↦ baseEval (D.fullSymmetricCoefficient m e t he a cj q k) z))
    rw [hQ,lineFactor_diagonal,eval_polynomial_smul_coeff,polynomial_symmetricMatrix,eval_substitute]

lemma ampleSection_value (m : ℕ) (hm : 0 < m) (e t : ℕ) (he : 3*m≤e) (hen : e+1=2*t)
    (a : StandardChart) (q : SymmetricGeneratorIndex t) (i : ℕ) (x : QuadricSurface) (v : FiberCoordinates) :
    (D.ampleSection m hm e t he hen a q).value i x v=
      (D.symmetricGeneration m e t he).value (standardChartNat i) (coordQuadric (standardChartNat i) x) v (index (a,q)) := by
  change (∑ k : Fin (2*t+1),baseEval (D.fullSymmetricCoefficient m e t he a (standardChartNat i) q k)
    (coordQuadric (standardChartNat i) x)*v 0^k.val*v 1^(2*t-k.val))=_
  rw [← eval_polynomial,D.fullSymmetricCoefficient_value,eval_polynomial_smul_coeff,polynomial_eval_dot]
  rw [PolynomialGeneration.value,PolynomialGeneration.stencil_index,D.symmetricGeneration_matrix]
  rfl

def ampleSystem (m : ℕ) (hm : 0 < m) (e t : ℕ) (he : 3*m≤e) (hen : e+1=2*t) :
    SegreSectionSystem (powerPullbackTwist D.bundle m hm) (2*t) (SymmetricGeneratorIndex t) where
  cover := D.powerTwist_cover m hm
  generation := D.symmetricGeneration m e t he
  sections := fun j ↦ D.ampleSection m hm e t he hen (label j).1 (label j).2
  value_eq := by
    intro i x _ v
    ext j
    change (D.ampleSection m hm e t he hen (label j).1 (label j).2).value i x v=_
    rw [D.ampleSection_value,index_label]
    rfl
end EqualizerData
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set MvPolynomial Matrix LaurentCech BinaryForms PolynomialGeneration
open scoped BigOperators
noncomputable section
namespace SegreSectionSystem
variable {V : AlgebraicRankTwoBundle} {n : ℕ} {ι : Type u3} [Fintype ι] (S : SegreSectionSystem V n ι)

lemma cone_algebraic (hn : 0<n) :
    ProjectiveAlgebraicCone ({0} ∪ {y | ∃ i x,x∈V.domain i ∧ ∃ v : FiberCoordinates,v≠0 ∧
      ∃ c : ℂ,c≠0 ∧ y=c • sectionVector S.sections i x v}) := by
  apply S.generation.algebraicCone_of_localization hn _ (Or.inl rfl)
  · intro a z v hv c hc
    let i := S.cover.chartIndex a
    have hx := S.cover.chartIndex_mem a z
    refine Or.inr ⟨i,affineQuadric a z,hx,v,hv,c,hc,?_⟩
    rw [S.value_eq i _ hx]
    simp only [i,S.cover.chartIndex_chart,coordQuadric_affine]
  · intro j y hy hj
    rcases hy with hy|⟨i,x,hx,v,hv,c,hc,rfl⟩
    · exact (hj (congrFun hy j)).elim
    · have hs : sectionVector S.sections i x v j≠0 := (mul_ne_zero_iff.mp hj).2
      obtain ⟨z,w,hw,he⟩ := S.localize_pivot j i x hx v hv hs
      exact ⟨z,w,hw,c,hc,congrArg (c • ·) he⟩

def inverseNumerator (hn : 0<n) (i : ℕ) (q : ι) (b : Fin 2) :
    Fin 3 → MvPolynomial (ProjectiveIndex ι) ℂ :=
  ![X (index (flipFirst (V.chart i),q)),X (index (flipSecond (V.chart i),q)),
    S.generation.recoveryPolynomial (V.chart i) q (veroneseAdjacent n hn b)]
def inverseDenominator (i : ℕ) (q : ι) (b : Fin 2) :
    Fin 3 → MvPolynomial (ProjectiveIndex ι) ℂ :=
  ![1,1,S.generation.recoveryPolynomial (V.chart i) q (veroneseEndpoint n b)]
lemma recoveryPolynomial_value (i : ℕ) (x : QuadricSurface) (hx : x∈V.domain i)
    (v : FiberCoordinates) (q : ι) (hq : sectionVector S.sections i x v (index (V.chart i,q))≠0)
    (k : Fin (n+1)) :
    MvPolynomial.eval (normalize (index (V.chart i,q)) (sectionVector S.sections i x v))
      (S.generation.recoveryPolynomial (V.chart i) q k)=
      (sectionVector S.sections i x v (index (V.chart i,q)))⁻¹*veronese n v k := by
  rw [S.generation.eval_recoveryPolynomial,S.pivot_recovery i x hx v q hq]
  rfl
lemma inverseDenominator_value (i : ℕ) (x : QuadricSurface) (hx : x∈V.domain i)
    (v : FiberCoordinates) (q : ι) (hq : sectionVector S.sections i x v (index (V.chart i,q))≠0)
    (b : Fin 2) :
    MvPolynomial.eval (normalize (index (V.chart i,q)) (sectionVector S.sections i x v))
      (S.inverseDenominator i q b 2)=
      (sectionVector S.sections i x v (index (V.chart i,q)))⁻¹*(v b)^n := by
  change MvPolynomial.eval _ (S.generation.recoveryPolynomial (V.chart i) q (veroneseEndpoint n b))=_
  rw [S.recoveryPolynomial_value i x hx v q hq,veronese_endpoint]
lemma inverseDenominator_nonzero (i : ℕ) (x : QuadricSurface) (hx : x∈V.domain i)
    (v : FiberCoordinates) (q : ι) (hq : sectionVector S.sections i x v (index (V.chart i,q))≠0)
    (b : Fin 2) (hb : v b≠0) (k : Fin 3) :
    MvPolynomial.eval (normalize (index (V.chart i,q)) (sectionVector S.sections i x v))
      (S.inverseDenominator i q b k)≠0 := by
  fin_cases k
  · simp [inverseDenominator]
  · simp [inverseDenominator]
  · change MvPolynomial.eval _ (S.inverseDenominator i q b 2)≠0
    rw [S.inverseDenominator_value i x hx v q hq b]
    exact mul_ne_zero (inv_ne_zero hq) (pow_ne_zero _ hb)
lemma inverseFormula (hn : 0<n) (i : ℕ) (x : QuadricSurface) (hx : x∈V.domain i)
    (v : FiberCoordinates) (q : ι) (hq : sectionVector S.sections i x v (index (V.chart i,q))≠0)
    (b : Fin 2) (hb : v b≠0) (k : Fin 3) :
    (![ (coordQuadric (V.chart i) x).1,(coordQuadric (V.chart i) x).2,v (1-b)/v b] : Fin 3 → ℂ) k=
    MvPolynomial.eval (normalize (index (V.chart i,q)) (sectionVector S.sections i x v))
      (S.inverseNumerator hn i q b k)/
    MvPolynomial.eval (normalize (index (V.chart i,q)) (sectionVector S.sections i x v))
      (S.inverseDenominator i q b k) := by
  have hz := S.pivot_coordinates i x hx v q hq
  fin_cases k
  · change (coordQuadric (V.chart i) x).1= MvPolynomial.eval _ (X (index (flipFirst (V.chart i),q))) / MvPolynomial.eval _ 1
    simpa only [eval_X,map_one,div_one,patchCoordinates] using (congrArg Prod.fst hz).symm
  · change (coordQuadric (V.chart i) x).2= MvPolynomial.eval _ (X (index (flipSecond (V.chart i),q))) / MvPolynomial.eval _ 1
    simpa only [eval_X,map_one,div_one,patchCoordinates] using (congrArg Prod.snd hz).symm
  · change v (1-b)/v b=MvPolynomial.eval _ (S.generation.recoveryPolynomial (V.chart i) q (veroneseAdjacent n hn b)) /
      MvPolynomial.eval _ (S.generation.recoveryPolynomial (V.chart i) q (veroneseEndpoint n b))
    rw [S.recoveryPolynomial_value i x hx v q hq,S.recoveryPolynomial_value i x hx v q hq,
      mul_div_mul_left _ _ (inv_ne_zero hq),veronese_adjacent_ratio n hn v b hb]

lemma local_inverse (hn : 0<n) (i : ℕ) (x : QuadricSurface) (hx : x∈V.domain i)
    (v : FiberCoordinates) (hv : v≠0) :
    ∃ j : ProjectiveIndex ι,∃ b : Fin 2,v b≠0 ∧ sectionVector S.sections i x v j≠0 ∧
    ∃ p q : Fin 3 → MvPolynomial (ProjectiveIndex ι) ℂ,
      (∀ k,MvPolynomial.eval (normalize j (sectionVector S.sections i x v)) (q k)≠0) ∧
      ∀ i' x',x'∈V.domain i' → ∀ v' : FiberCoordinates,v'≠0 →
        sectionVector S.sections i' x' v' j≠0 →
        (∀ k,MvPolynomial.eval (normalize j (sectionVector S.sections i' x' v')) (q k)≠0) →
        x'∈V.domain i ∧ ((V.dualTransition i i' x').mulVec v') b≠0 ∧
        (∀ k : Fin 3,
          (![ (coordQuadric (V.chart i) x').1,(coordQuadric (V.chart i) x').2,
            ((V.dualTransition i i' x').mulVec v') (1-b)/((V.dualTransition i i' x').mulVec v') b] : Fin 3 → ℂ) k=
          MvPolynomial.eval (normalize j (sectionVector S.sections i' x' v')) (p k)/
          MvPolynomial.eval (normalize j (sectionVector S.sections i' x' v')) (q k)) := by
  obtain ⟨r,hr⟩ := S.exists_pivot i x hx v hv
  obtain ⟨b,hb⟩ : ∃ b,v b≠0 := by
    by_contra hh
    apply hv
    ext b
    by_contra hh'
    exact hh ⟨b,hh'⟩
  refine ⟨index (V.chart i,r),b,hb,hr,S.inverseNumerator hn i r b,S.inverseDenominator i r b,
    S.inverseDenominator_nonzero i x hx v r hr b hb,?_⟩
  intro i' x' hx' v' _ hj hden
  have hxi := S.pivot_domain i ((S.cover.domain i x).mp hx).1 i' x' hx' v' r hj
  let w := (V.dualTransition i i' x').mulVec v'
  have hchange : sectionVector S.sections i x' w=sectionVector S.sections i' x' v' :=
    sectionVector_compatible S.sections i i' x' hxi hx' v'
  have hp : sectionVector S.sections i x' w (index (V.chart i,r))≠0 := by rwa [hchange]
  have h2 := hden 2
  rw [← hchange,S.inverseDenominator_value i x' hxi w r hp b] at h2
  have hwb : w b≠0 := by
    intro hz
    exact ((mul_ne_zero_iff.mp h2).2) (by rw [hz,zero_pow (by omega : n≠0)])
  refine ⟨hxi,hwb,fun k ↦ ?_⟩
  rw [← hchange]
  exact S.inverseFormula hn i x' hxi w r hp b hwb k

theorem closedEmbedding (hn : 0<n) : GivesClosedProjectiveEmbedding S.sections := by
  refine ⟨fun i x hi v hv ↦ S.nonzero i x hi hv,?_,S.cone_algebraic hn,?_⟩
  · intro i j x y hx hy v w hv hw h
    obtain ⟨c,hc,he⟩ := h
    exact S.injective hn i j x y hx hy v w hv hw c hc he
  · exact S.local_inverse hn
end SegreSectionSystem
end
end QuadricCounterexample

end

end OAI
