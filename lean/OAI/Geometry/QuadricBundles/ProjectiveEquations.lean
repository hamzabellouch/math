import OAI.Geometry.QuadricBundles.PolynomialGeneration

namespace OAI

universe u1 u2 u3

noncomputable section

namespace QuadricCounterexample.BinaryForms
open MvPolynomial Matrix
open scoped BigOperators
noncomputable section

def veronese (n : ℕ) (v : Fin 2 → ℂ) : Fin (n+1) → ℂ := fun k ↦ v 0^k.val*v 1^(n-k.val)
@[simp] lemma veronese_zero (n : ℕ) (v : Fin 2 → ℂ) : veronese n v 0=v 1^n := by simp [veronese]
@[simp] lemma veronese_last (n : ℕ) (v : Fin 2 → ℂ) : veronese n v (Fin.last n)=v 0^n := by simp [veronese]
lemma veronese_nonzero (n : ℕ) {v : Fin 2 → ℂ} (hv : v≠0) : veronese n v≠0 := by
  intro h
  have h0 := congrFun h (0 : Fin (n+1))
  have h1 := congrFun h (Fin.last n)
  simp only [veronese_zero,veronese_last,Pi.zero_apply] at h0 h1
  apply hv
  ext k
  fin_cases k
  · exact eq_zero_of_pow_eq_zero h1
  · exact eq_zero_of_pow_eq_zero h0

def veroneseOne (n : ℕ) (hn : 0<n) : Fin (n+1) := ⟨1,by omega⟩
lemma veronese_ratio (n : ℕ) (hn : 0<n) (v : Fin 2 → ℂ) (h : v 1≠0) :
    veronese n v (veroneseOne n hn)/veronese n v 0=v 0/v 1 := by
  simp only [veronese,veroneseOne,Fin.val_zero,pow_zero,one_mul,Nat.sub_zero,pow_one]
  rw [show v 1^n=v 1^(n-1)*v 1 by rw [← pow_succ]; congr 1; omega]
  field_simp

def VeroneseRelations (n : ℕ) (hn : 0<n) (w : Fin (n+1) → ℂ) : Prop :=
  (∀ k,w k^n=w (Fin.last n)^k.val*w 0^(n-k.val)) ∧
  ∀ k : Fin n,w k.succ*w 0=w k.castSucc*w (veroneseOne n hn)
lemma veronese_relations (n : ℕ) (hn : 0<n) (c : ℂ) (v : Fin 2 → ℂ) :
    VeroneseRelations n hn (c • veronese n v) := by
  constructor
  · intro k
    change (c*veronese n v k)^n=(c*veronese n v (Fin.last n))^k.val*(c*veronese n v 0)^(n-k.val)
    rw [veronese_zero,veronese_last]
    simp only [veronese,mul_pow]
    have hk : k.val+(n-k.val)=n := by omega
    calc
      _ = (c^k.val*c^(n-k.val))*((v 0^n)^k.val*(v 1^n)^(n-k.val)) := by
        rw [← pow_add,hk]
        simp only [← pow_mul,Nat.mul_comm]
      _ = _ := by ring
  · intro k
    change (c*veronese n v k.succ)*(c*veronese n v 0)=
      (c*veronese n v k.castSucc)*(c*veronese n v (veroneseOne n hn))
    rw [veronese_zero]
    simp only [veronese,veroneseOne,Fin.val_succ,Fin.val_castSucc,pow_one]
    have hk := k.isLt
    have ha : v 1^(n-k.val)=v 1^(n-(k.val+1))*v 1 := by
      rw [← pow_succ]; congr 1; omega
    have hb : v 1^n=v 1^(n-1)*v 1 := by
      rw [← pow_succ]; congr 1; omega
    rw [ha,hb,pow_succ]
    ring
lemma VeroneseRelations.reconstruct (n : ℕ) (hn : 0<n) (w : Fin (n+1) → ℂ)
    (hw : w≠0) (h : VeroneseRelations n hn w) :
    ∃ c : ℂ,c≠0 ∧ ∃ v : Fin 2 → ℂ,v≠0 ∧ w=c • veronese n v := by
  by_cases h0 : w 0=0
  · have hi (k : Fin (n+1)) (hk : k.val<n) : w k=0 := by
      have he := h.1 k
      rw [h0,zero_pow (by omega : n-k.val≠0),mul_zero] at he
      exact eq_zero_of_pow_eq_zero he
    have hn0 : w (Fin.last n)≠0 := by
      intro hz
      apply hw
      ext k
      by_cases hk : k.val=n
      · have he : k=Fin.last n := Fin.ext hk
        simpa only [he,Pi.zero_apply] using hz
      · exact hi k (by omega)
    refine ⟨w (Fin.last n),hn0,![1,0],by simp,?_⟩
    ext k
    by_cases hk : k.val=n
    · have he : k=Fin.last n := Fin.ext hk
      subst k
      simp [veronese]
    · have hkn : n-k.val≠0 := by omega
      simp [veronese,hi k (by omega),zero_pow hkn]
  · have hc (k : Fin (n+1)) : w k=w 0*(w (veroneseOne n hn)/w 0)^k.val := by
      induction k using Fin.inductionOn with
      | zero => simp
      | succ k ih =>
        have he := h.2 k
        rw [ih] at he
        apply mul_right_cancel₀ h0
        calc
          w k.succ*w 0 = w 0*(w (veroneseOne n hn)/w 0)^k.val*w (veroneseOne n hn) := he
          _ = (w 0*(w (veroneseOne n hn)/w 0)^k.succ.val)*w 0 := by
            simp only [Fin.val_succ,pow_succ]
            field_simp
    refine ⟨w 0,h0,![w (veroneseOne n hn)/w 0,1],by simp,?_⟩
    ext k
    simpa [veronese] using hc k

def veroneseEndpoint (n : ℕ) (b : Fin 2) : Fin (n+1) := if b=0 then Fin.last n else 0
def veroneseAdjacent (n : ℕ) (hn : 0<n) (b : Fin 2) : Fin (n+1) :=
  if b=0 then ⟨n-1,by omega⟩ else veroneseOne n hn
lemma veronese_endpoint (n : ℕ) (v : Fin 2 → ℂ) (b : Fin 2) :
    veronese n v (veroneseEndpoint n b)=v b^n := by
  fin_cases b <;> simp [veroneseEndpoint]
lemma veronese_adjacent_ratio (n : ℕ) (hn : 0<n) (v : Fin 2 → ℂ) (b : Fin 2)
    (hb : v b≠0) :
    veronese n v (veroneseAdjacent n hn b)/veronese n v (veroneseEndpoint n b)=v (1-b)/v b := by
  fin_cases b
  · change veronese n v (veroneseAdjacent n hn 0)/veronese n v (veroneseEndpoint n 0)=v 1/v 0
    simp only [veroneseAdjacent,veroneseEndpoint,ite_true,veronese_last]
    simp only [veronese]
    rw [show n-(n-1)=1 by omega,pow_one]
    rw [show v 0^n=v 0^(n-1)*v 0 by rw [← pow_succ]; congr 1; omega]
    change v 0≠0 at hb
    field_simp [hb]
  · change veronese n v (veroneseAdjacent n hn 1)/veronese n v (veroneseEndpoint n 1)=v 0/v 1
    simpa only [veroneseAdjacent,veroneseEndpoint,show (1 : Fin 2)≠0 by decide,
      ite_false] using veronese_ratio n hn v hb
lemma binary_proportional_of_ratio (v w : Fin 2 → ℂ) (b : Fin 2) (hv : v b≠0) (hw : w b≠0)
    (h : v (1-b)/v b=w (1-b)/w b) : ∃ c : ℂ,c≠0 ∧ v=c • w := by
  refine ⟨v b/w b,div_ne_zero hv hw,?_⟩
  ext k
  by_cases hk : k=b
  · subst k; simp [Pi.smul_apply,smul_eq_mul,hw]
  · have he : k=1-b := by fin_cases k <;> fin_cases b <;> simp_all
    subst k
    have hh := (div_eq_div_iff hv hw).mp h
    simp only [Pi.smul_apply,smul_eq_mul]
    calc
      _ = (w (1-b)*v b)/w b := (eq_div_iff hw).mpr hh
      _ = _ := by ring
lemma veronese_projective_injective (n : ℕ) (hn : 0<n) (v w : Fin 2 → ℂ)
    (hw : w≠0) (c : ℂ) (hc : c≠0) (h : veronese n v=c • veronese n w) :
    ∃ d : ℂ,d≠0 ∧ v=d • w := by
  obtain ⟨b,hb⟩ : ∃ b,w b≠0 := by
    by_contra hh
    apply hw
    ext b
    by_contra hbb
    exact hh ⟨b,hbb⟩
  have he := congrFun h (veroneseEndpoint n b)
  simp only [Pi.smul_apply,smul_eq_mul,veronese_endpoint] at he
  have hv : v b≠0 := by
    intro hz
    rw [hz,zero_pow (by omega)] at he
    exact (mul_ne_zero hc (pow_ne_zero _ hb)) he.symm
  apply binary_proportional_of_ratio v w b hv hb
  rw [← veronese_adjacent_ratio n hn v b hv,← veronese_adjacent_ratio n hn w b hb]
  rw [h]
  simp only [Pi.smul_apply,smul_eq_mul,mul_div_mul_left _ _ hc]

end
end QuadricCounterexample.BinaryForms

namespace QuadricCounterexample
open Set MvPolynomial Matrix LaurentCech BinaryForms
open scoped BigOperators
noncomputable section

def flipFirst (i : StandardChart) : StandardChart := (1-i.1,i.2)
def flipSecond (i : StandardChart) : StandardChart := (i.1,1-i.2)
def segreFactor (a i : StandardChart) (z : BaseCoordinates) : ℂ :=
  baseEval (lineGenerator (1,1) a i) z
@[simp] lemma segreFactor_self (i : StandardChart) (z : BaseCoordinates) : segreFactor i i z=1 := by
  rw [segreFactor,eval_lineGenerator,lineFactor_self]
@[simp] lemma segreFactor_flipFirst (i : StandardChart) (z : BaseCoordinates) :
    segreFactor (flipFirst i) i z=z.1 := by
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [segreFactor,eval_lineGenerator,lineFactor,flipFirst,firstFactor,secondFactor,scalarFactor]
@[simp] lemma segreFactor_flipSecond (i : StandardChart) (z : BaseCoordinates) :
    segreFactor (flipSecond i) i z=z.2 := by
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [segreFactor,eval_lineGenerator,lineFactor,flipSecond,firstFactor,secondFactor,scalarFactor]
lemma segreFactor_ne_zero_iff (a i : StandardChart) (z : BaseCoordinates) :
    segreFactor a i z≠0 ↔ z∈coordinateOverlap i a := by
  rw [coordinateOverlap_iff]
  simp only [segreFactor,eval_lineGenerator,lineFactor,firstFactor,secondFactor,scalarFactor,pow_one]
  rw [mul_ne_zero_iff]
  constructor
  · rintro ⟨h₁,h₂⟩
    constructor
    · by_cases h : i.1=a.1
      · exact Or.inl h
      · exact Or.inr (by simpa only [ite_eq_right h] using h₁)
    · by_cases h : i.2=a.2
      · exact Or.inl h
      · exact Or.inr (by simpa only [ite_eq_right h] using h₂)
  · rintro ⟨h₁,h₂⟩
    constructor
    · rcases h₁ with h₁|h₁
      · simp [h₁]
      · split_ifs <;> simp_all
    · rcases h₂ with h₂|h₂
      · simp [h₂]
      · split_ifs <;> simp_all

namespace PolynomialGeneration
variable {n : ℕ} {ι : Type u1} [Fintype ι] (B : PolynomialGeneration n ι)
abbrev ProjectiveIndex (ι : Type u2) [Fintype ι] := Fin (Fintype.card (StandardChart × ι))
def index : (StandardChart × ι) ≃ ProjectiveIndex ι := Fintype.equivFin _
def label (j : ProjectiveIndex ι) : StandardChart × ι := (index (ι:=ι)).symm j
@[simp] lemma label_index (a : StandardChart) (q : ι) : label (index (a,q))=(a,q) := Equiv.symm_apply_apply _ _
@[simp] lemma index_label (j : ProjectiveIndex ι) : index (label j)=j := Equiv.apply_symm_apply _ _

def stencil (i : StandardChart) (z : BaseCoordinates) (w : Fin (n+1) → ℂ) : ProjectiveIndex ι → ℂ :=
  fun j ↦ segreFactor (label j).1 i z*((B.matrix i z).transpose.mulVec w) (label j).2
def value (i : StandardChart) (z : BaseCoordinates) (v : FiberCoordinates) : ProjectiveIndex ι → ℂ :=
  B.stencil i z (veronese n v)
@[simp] lemma stencil_index (i a : StandardChart) (z : BaseCoordinates) (w : Fin (n+1) → ℂ) (q : ι) :
    B.stencil i z w (index (a,q))=segreFactor a i z*((B.matrix i z).transpose.mulVec w) q := by
  simp [stencil]
@[simp] lemma stencil_self (i : StandardChart) (z : BaseCoordinates) (w : Fin (n+1) → ℂ) (q : ι) :
    B.stencil i z w (index (i,q))=((B.matrix i z).transpose.mulVec w) q := by
  simp
lemma stencil_smul (i : StandardChart) (z : BaseCoordinates) (w : Fin (n+1) → ℂ) (c : ℂ) :
    B.stencil i z (c • w)=c • B.stencil i z w := by
  ext j
  simp only [stencil,Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul]
  ring
lemma stencil_nonzero (i : StandardChart) (z : BaseCoordinates) {w : Fin (n+1) → ℂ} (hw : w≠0) :
    B.stencil i z w≠0 := by
  intro hh
  apply B.matrix_nonzero i z hw
  ext q
  simpa only [stencil_self,Pi.zero_apply] using congrFun hh (index (i,q))
lemma value_nonzero (i : StandardChart) (z : BaseCoordinates) {v : FiberCoordinates} (hv : v≠0) :
    B.value i z v≠0 := B.stencil_nonzero i z (veronese_nonzero n hv)

def normalize (j : ProjectiveIndex ι) (y : ProjectiveIndex ι → ℂ) : ProjectiveIndex ι → ℂ := fun k ↦ y k/y j
lemma normalize_smul (j : ProjectiveIndex ι) (y : ProjectiveIndex ι → ℂ) (c : ℂ) (hc : c≠0) :
    normalize j (c • y)=normalize j y := by
  ext k
  simp only [normalize,Pi.smul_apply,smul_eq_mul,mul_div_mul_left _ _ hc]
lemma normalize_pivot (j : ProjectiveIndex ι) (y : ProjectiveIndex ι → ℂ) (hy : y j≠0) :
    normalize j y j=1 := div_self hy

def patchCoordinates (i : StandardChart) (q : ι) (y : ProjectiveIndex ι → ℂ) : BaseCoordinates :=
  (y (index (flipFirst i,q)),y (index (flipSecond i,q)))
def block (i : StandardChart) (y : ProjectiveIndex ι → ℂ) : ι → ℂ := fun q ↦ y (index (i,q))
def patchRecovery (i : StandardChart) (q : ι) (y : ProjectiveIndex ι → ℂ) : Fin (n+1) → ℂ :=
  (B.recover i (patchCoordinates i q y)).mulVec (block i y)
lemma patchCoordinates_stencil (i : StandardChart) (z : BaseCoordinates) (w : Fin (n+1) → ℂ) (q : ι)
    (hq : B.stencil i z w (index (i,q))≠0) :
    patchCoordinates i q (normalize (index (i,q)) (B.stencil i z w))=z := by
  have hq' : ((B.matrix i z).transpose.mulVec w) q≠0 := by simpa only [stencil_self] using hq
  simp only [patchCoordinates,normalize,stencil_index,segreFactor_self,one_mul,
    segreFactor_flipFirst,segreFactor_flipSecond,mul_div_cancel_right₀ _ hq']
lemma patchRecovery_stencil (i : StandardChart) (z : BaseCoordinates) (w : Fin (n+1) → ℂ) (q : ι)
    (hq : B.stencil i z w (index (i,q))≠0) :
    B.patchRecovery i q (normalize (index (i,q)) (B.stencil i z w))=
      (B.stencil i z w (index (i,q)))⁻¹ • w := by
  unfold patchRecovery
  rw [B.patchCoordinates_stencil i z w q hq]
  have hb : block i (normalize (index (i,q)) (B.stencil i z w))=
      (B.stencil i z w (index (i,q)))⁻¹ • (B.matrix i z).transpose.mulVec w := by
    ext r
    simp only [block,normalize,stencil_self,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
  rw [hb,Matrix.mulVec_smul,B.recover_matrix]
end PolynomialGeneration
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set MvPolynomial
open scoped BigOperators
noncomputable section

lemma exists_homogenizeAt {N : ℕ} (j : Fin N) (p : MvPolynomial (Fin N) ℂ) :
    ∃ d : ℕ,∃ h : MvPolynomial (Fin N) ℂ,h.IsHomogeneous d ∧
      ∀ y : Fin N → ℂ,y j≠0 → MvPolynomial.eval y h=(y j)^d*MvPolynomial.eval (fun k ↦ y k/y j) p := by
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨0,C c,isHomogeneous_C _ _,fun _ _ ↦ by simp⟩
  | add p q hp hq =>
    obtain ⟨d,h,hh,he⟩ := hp
    obtain ⟨e,k,hk,ke⟩ := hq
    refine ⟨d+e,X j^e*h+X j^d*k,?_,?_⟩
    · apply IsHomogeneous.add
      · simpa only [add_comm] using (isHomogeneous_X_pow j e).mul hh
      · exact (isHomogeneous_X_pow j d).mul hk
    · intro y hy
      rw [map_add,map_add,map_mul,map_mul,map_pow,map_pow,eval_X,he y hy,ke y hy,pow_add]
      ring
  | mul_X p k hp =>
    obtain ⟨d,h,hh,he⟩ := hp
    refine ⟨d+1,h*X k,hh.mul (isHomogeneous_X ℂ k),?_⟩
    intro y hy
    rw [map_mul,map_mul,eval_X,eval_X,he y hy,pow_succ]
    field_simp

lemma projectiveCone_of_patch_equations {N : ℕ} (C : Set (Fin N → ℂ)) (hzero : 0∈C)
    (E : Fin N → Set (MvPolynomial (Fin N) ℂ))
    (hE : ∀ j y,y j≠0 → (y∈C ↔ ∀ p∈E j,MvPolynomial.eval (fun k ↦ y k/y j) p=0)) :
    ProjectiveAlgebraicCone C := by
  choose degree hom homogeneous evaluate using fun j p ↦ exists_homogenizeAt (N:=N) j p
  let equations : Set (MvPolynomial (Fin N) ℂ) :=
    {q | ∃ j p,p∈E j ∧ q=X j*hom j p}
  refine ⟨equations,?_,?_⟩
  · rintro q ⟨j,p,_,rfl⟩
    exact ⟨1+degree j p,(isHomogeneous_X ℂ j).mul (homogeneous j p)⟩
  · ext y
    constructor
    · intro hy q hq
      obtain ⟨j,p,hp,rfl⟩ := hq
      rw [map_mul,eval_X]
      by_cases hj : y j=0
      · rw [hj,zero_mul]
      · rw [evaluate j p y hj,(hE j y hj).mp hy p hp,mul_zero,mul_zero]
    · intro hy
      by_cases hz : y=0
      · simpa only [hz] using hzero
      · obtain ⟨j,hj⟩ : ∃ j,y j≠0 := by
          by_contra hn
          apply hz
          ext j
          by_contra hh
          exact hn ⟨j,hh⟩
        apply (hE j y hj).mpr
        intro p hp
        have h := hy (X j*hom j p) ⟨j,p,hp,rfl⟩
        rw [map_mul,eval_X,evaluate j p y hj] at h
        exact (mul_eq_zero.mp h).resolve_left hj |> fun h ↦ (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hj)
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set MvPolynomial Matrix LaurentCech BinaryForms
open scoped BigOperators
noncomputable section
namespace PolynomialGeneration
variable {n : ℕ} {ι : Type u3} [Fintype ι] (B : PolynomialGeneration n ι)

lemma normalize_eq_smul (j : ProjectiveIndex ι) (y : ProjectiveIndex ι → ℂ) :
    normalize j y=(y j)⁻¹ • y := by
  ext k
  simp [normalize,div_eq_mul_inv,mul_comm]
lemma stencil_zero (i : StandardChart) (z : BaseCoordinates) : B.stencil i z 0=0 := by
  ext j
  simp [stencil]

def liftPatchPolynomial (i : StandardChart) (q : ι) (p : BasePolynomial) :
    MvPolynomial (ProjectiveIndex ι) ℂ :=
  MvPolynomial.bind₁ (fun k : Fin 2 ↦ if k=0 then X (index (flipFirst i,q)) else X (index (flipSecond i,q))) p
lemma eval_liftPatchPolynomial (i : StandardChart) (q : ι) (p : BasePolynomial) (y : ProjectiveIndex ι → ℂ) :
    MvPolynomial.eval y (liftPatchPolynomial i q p)=baseEval p (patchCoordinates i q y) := by
  change MvPolynomial.eval₂Hom (RingHom.id ℂ) _ ((MvPolynomial.bind₁ _) p)=_
  rw [MvPolynomial.eval₂Hom_bind₁]
  change MvPolynomial.eval _ p=MvPolynomial.eval _ p
  apply congrArg (fun f : Fin 2 → ℂ ↦ MvPolynomial.eval f p)
  funext k
  fin_cases k <;> simp [patchCoordinates]

def recoveryPolynomial (i : StandardChart) (q : ι) (k : Fin (n+1)) :
    MvPolynomial (ProjectiveIndex ι) ℂ :=
  ∑ r : ι,liftPatchPolynomial i q (B.recovery i k r)*X (index (i,r))
lemma eval_recoveryPolynomial (i : StandardChart) (q : ι) (k : Fin (n+1)) (y : ProjectiveIndex ι → ℂ) :
    MvPolynomial.eval y (B.recoveryPolynomial i q k)=B.patchRecovery i q y k := by
  simp only [recoveryPolynomial,map_sum,map_mul,eval_X,eval_liftPatchPolynomial]
  rfl

def patchEquations (hn : 0<n) (i : StandardChart) (q : ι) :
    Set (MvPolynomial (ProjectiveIndex ι) ℂ) :=
  range (fun j : ProjectiveIndex ι ↦
    X j-liftPatchPolynomial i q (lineGenerator (1,1) (label j).1 i)*
      ∑ k : Fin (n+1),liftPatchPolynomial i q (B.coefficient i k (label j).2)*B.recoveryPolynomial i q k) ∪
  range (fun k : Fin (n+1) ↦ B.recoveryPolynomial i q k^n-
    B.recoveryPolynomial i q (Fin.last n)^k.val*B.recoveryPolynomial i q 0^(n-k.val)) ∪
  range (fun k : Fin n ↦ B.recoveryPolynomial i q k.succ*B.recoveryPolynomial i q 0-
    B.recoveryPolynomial i q k.castSucc*B.recoveryPolynomial i q (veroneseOne n hn))
lemma patchEquations_iff (hn : 0<n) (i : StandardChart) (q : ι) (y : ProjectiveIndex ι → ℂ) :
    (∀ p∈B.patchEquations hn i q,MvPolynomial.eval y p=0) ↔
      y=B.stencil i (patchCoordinates i q y) (B.patchRecovery i q y) ∧
      VeroneseRelations n hn (B.patchRecovery i q y) := by
  simp only [patchEquations,Set.mem_union,or_imp,forall_and,Set.forall_mem_range,map_sub,map_mul,
    map_sum,map_pow,eval_X,eval_liftPatchPolynomial,eval_recoveryPolynomial,sub_eq_zero]
  change ((∀ j,y j=B.stencil i (patchCoordinates i q y) (B.patchRecovery i q y) j) ∧
    (∀ k,(B.patchRecovery i q y k)^n=(B.patchRecovery i q y (Fin.last n))^k.val*
      (B.patchRecovery i q y 0)^(n-k.val))) ∧
    (∀ k : Fin n,B.patchRecovery i q y k.succ*B.patchRecovery i q y 0=
      B.patchRecovery i q y k.castSucc*B.patchRecovery i q y (veroneseOne n hn)) ↔ _
  rw [← funext_iff]
  exact and_assoc
lemma normalized_value_equations (hn : 0<n) (i : StandardChart) (q : ι) (z : BaseCoordinates)
    (v : FiberCoordinates) (h : B.value i z v (index (i,q))≠0) :
    ∀ p∈B.patchEquations hn i q,MvPolynomial.eval (normalize (index (i,q)) (B.value i z v)) p=0 := by
  rw [B.patchEquations_iff]
  simp only [value]
  rw [B.patchCoordinates_stencil i z _ q h,B.patchRecovery_stencil i z _ q h]
  constructor
  · rw [B.stencil_smul,normalize_eq_smul]
  · exact veronese_relations n hn _ v
lemma patchEquations_reconstruct (hn : 0<n) (i : StandardChart) (q : ι) (y : ProjectiveIndex ι → ℂ)
    (hy : y (index (i,q))=1) (h : ∀ p∈B.patchEquations hn i q,MvPolynomial.eval y p=0) :
    ∃ z : BaseCoordinates,∃ v : FiberCoordinates,v≠0 ∧ ∃ c : ℂ,c≠0 ∧ y=c • B.value i z v := by
  obtain ⟨he,hv⟩ := (B.patchEquations_iff hn i q y).mp h
  have hw : B.patchRecovery i q y≠0 := by
    intro hz
    rw [hz,B.stencil_zero] at he
    have hj := congrFun he (index (i,q))
    rw [hy] at hj
    exact one_ne_zero hj
  obtain ⟨c,hc,v,hv',hw'⟩ := hv.reconstruct n hn _ hw
  refine ⟨patchCoordinates i q y,v,hv',c,hc,?_⟩
  calc
    y = B.stencil i (patchCoordinates i q y) (B.patchRecovery i q y) := he
    _ = c • B.value i (patchCoordinates i q y) v := by rw [hw',B.stencil_smul]; rfl

theorem algebraicCone_of_localization (hn : 0<n) (C : Set (ProjectiveIndex ι → ℂ))
    (hzero : 0∈C)
    (himage : ∀ i z v,v≠0 → ∀ c : ℂ,c≠0 → c • B.value i z v∈C)
    (hlocal : ∀ j y,y∈C → y j≠0 → ∃ z : BaseCoordinates,∃ v : FiberCoordinates,v≠0 ∧
      ∃ c : ℂ,c≠0 ∧ y=c • B.value (label j).1 z v) :
    ProjectiveAlgebraicCone C := by
  apply projectiveCone_of_patch_equations C hzero (fun j ↦ B.patchEquations hn (label j).1 (label j).2)
  intro j y hy
  have hj : index ((label j).1,(label j).2)=j := index_label j
  constructor
  · intro hC
    obtain ⟨z,v,_,c,hc,rfl⟩ := hlocal j y hC hy
    have hv : B.value (label j).1 z v j≠0 := by
      exact (mul_ne_zero_iff.mp hy).2
    rw [show (fun k ↦ (c • B.value (label j).1 z v) k/(c • B.value (label j).1 z v) j)=
      normalize j (c • B.value (label j).1 z v) from rfl,normalize_smul j _ c hc]
    simpa only [hj] using B.normalized_value_equations hn (label j).1 (label j).2 z v (by rw [hj]; exact hv)
  · intro h
    obtain ⟨z,v,hv,c,hc,he⟩ := B.patchEquations_reconstruct hn (label j).1 (label j).2
      (normalize j y) (by rw [hj]; exact normalize_pivot j y hy) h
    have hey : y=(y j*c) • B.value (label j).1 z v := by
      rw [normalize_eq_smul] at he
      have hh := congrArg (fun a : ProjectiveIndex ι → ℂ ↦ y j • a) he
      simpa only [smul_smul,mul_inv_cancel₀ hy,one_smul] using hh
    rw [hey]
    exact himage _ _ _ hv _ (mul_ne_zero hy hc)
end PolynomialGeneration
end
end QuadricCounterexample

end

end OAI
