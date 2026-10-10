import OAI.Combinatorics.EuclideanRamsey.DerivedFractions

namespace OAI

universe uIndex

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace

namespace EuclideanRamsey
open scoped BigOperators
abbrev LetterGroup := FreeGroup FiniteEuclidean
variable {ι : Type uIndex}

inductive UnitWords (a : ι → FiniteEuclidean) : (ι → LetterGroup) → ℕ → Prop
  | diag (g : LetterGroup) : UnitWords a (fun _ => g) 0
  | copy (b : ι → FiniteEuclidean) (h : ∀ i j,‖b i-b j‖=‖a i-a j‖) :
      UnitWords a (fun i => FreeGroup.of (b i)) 1
  | mul {u v m n} : UnitWords a u m → UnitWords a v n → UnitWords a (u*v) (m+n)
def unitGraded (a : ι → FiniteEuclidean) : GradedPaths ι LetterGroup where
  Holds := UnitWords a
  diag := .diag
  mul := .mul

def CopyPath (a : ι → FiniteEuclidean) (u : ℝ) (b : ι → FiniteEuclidean) : Prop :=
  0≤u ∧ ∀ i j,‖b i-b j‖^2=u*‖a i-a j‖^2

inductive Path (a : ι → FiniteEuclidean) : (ι → LetterGroup) → ℝ → Prop
  | diag (g : LetterGroup) : Path a (fun _ => g) 0
  | copy {u : ℝ} (b : ι → FiniteEuclidean) (h : CopyPath a u b) :
      Path a (fun i => FreeGroup.of (b i)) u
  | mul {u v lmb μ} : Path a u lmb → Path a v μ → Path a (u*v) (lmb+μ)
lemma UnitWords.path {a : ι → FiniteEuclidean} {w n} (h : UnitWords a w n) : Path a w n := by
  induction h with
  | diag g => simpa only [Nat.cast_zero] using (Path.diag (a:=a) g)
  | copy b hb =>
    simpa only [Nat.cast_one] using (Path.copy (a:=a) (u:=1) b ⟨zero_le_one,by intro i j; simp [hb i j]⟩)
  | mul _ _ ihu ihv => simpa only [Nat.cast_add] using ihu.mul ihv
lemma Path.nonneg {a : ι → FiniteEuclidean} {w lmb} (h : Path a w lmb) : 0≤lmb := by
  induction h with
  | diag => exact le_rfl
  | copy _ h => exact h.1
  | mul _ _ ih1 ih2 => exact add_nonneg ih1 ih2

lemma extend_pair_E (a : ι → FiniteEuclidean) (i j : ι) (z z' : FiniteEuclidean)
    (h : ‖z'-z‖=‖a j-a i‖) :
    ∃ b : ι → FiniteEuclidean,b i=z ∧ b j=z' ∧ ∀ k l,‖b k-b l‖=‖a k-a l‖ := by
  let v := a j-a i
  let w := z'-z
  let R := (ℝ ∙ (v-w))ᗮ.reflection
  refine ⟨fun k => z+R (a k-a i),by simp,?_,?_⟩
  · have he : R v=w := Submodule.reflection_sub h.symm
    simpa [v,w] using congrArg (fun t => z+t) he
  · intro k l
    simp only [add_sub_add_left_eq_sub,← map_sub,sub_sub_sub_cancel_right,
      LinearIsometryEquiv.norm_map]

lemma unit_pair_inverse (a : ι → FiniteEuclidean) : PairInverse (unitGraded a).monoid := by
  intro i j _ u hu
  obtain ⟨m,hm⟩ := hu
  change UnitWords a u m at hm
  suffices ∃ v n,UnitWords a v n ∧ v i=(u i)⁻¹ ∧ v j=(u j)⁻¹ by
    obtain ⟨v,n,hv,hi,hj⟩ := this
    exact ⟨v,⟨n,hv⟩,by rw [hi]; exact mul_inv_cancel _,by rw [hj]; exact mul_inv_cancel _⟩
  induction hm with
  | diag g => exact ⟨_,0,.diag g⁻¹,rfl,rfl⟩
  | copy b hb =>
    obtain ⟨c,hci,hcj,hc⟩ := extend_pair_E a i j (b j) (b i) (by
      rw [hb i j,norm_sub_rev (a i) (a j)])
    let x := FreeGroup.of (b i)
    let y := FreeGroup.of (b j)
    refine ⟨(fun _ => x⁻¹)*(fun k => FreeGroup.of (c k))*(fun _ => y⁻¹),1,?_,?_,?_⟩
    · simpa using ((UnitWords.diag x⁻¹).mul (.copy c hc)).mul (.diag y⁻¹)
    · simp [x,y,hci]
    · simp [x,y,hcj]
  | @mul u v m n hu hv ihu ihv =>
    obtain ⟨u',m',hu',hui,huj⟩ := ihu
    obtain ⟨v',n',hv',hvi,hvj⟩ := ihv
    exact ⟨v'*u',n'+m',hv'.mul hu',by simp [hui,hvi],by simp [huj,hvj]⟩

def pairHom (i j : ι) : (ι → LetterGroup) →* LetterGroup×LetterGroup where
  toFun u := (u i,u j)
  map_one' := rfl
  map_mul' _ _ := rfl

def pairGroup (a : ι → FiniteEuclidean) (i j : ι) (hij : i≠j) : Subgroup (LetterGroup×LetterGroup) where
  toSubmonoid := (unitGraded a).monoid.map (pairHom i j)
  inv_mem' := by
    rintro _ ⟨u,hu,rfl⟩
    obtain ⟨v,hv,hi,hj⟩ := unit_pair_inverse a i j hij u hu
    exact ⟨v,hv,Prod.ext (by
      change v i=(u i)⁻¹
      apply mul_left_cancel (a:=u i)
      simpa using hi) (by
      change v j=(u j)⁻¹
      apply mul_left_cancel (a:=u j)
      simpa using hj)⟩
lemma pairGroup_diag (a : ι → FiniteEuclidean) (i j : ι) (hij : i≠j) (g : LetterGroup) :
    (g,g)∈pairGroup a i j hij := by
  classical
  exact ⟨_,(unitGraded a).diagonal g,rfl⟩

def pairLeft (a : ι → FiniteEuclidean) (i j : ι) (hij : i≠j) : Subgroup LetterGroup :=
  (pairGroup a i j hij).comap (MonoidHom.inl LetterGroup LetterGroup)
instance pairLeft_normal (a : ι → FiniteEuclidean) (i j : ι) (hij : i≠j) :
    (pairLeft a i j hij).Normal := by
  constructor
  intro g hg k
  change (k*g*k⁻¹,1)∈pairGroup a i j hij
  have h := (pairGroup a i j hij).mul_mem
    ((pairGroup a i j hij).mul_mem (pairGroup_diag a i j hij k) hg)
    (pairGroup_diag a i j hij k⁻¹)
  simpa using h

lemma pairLeft_edge (a : ι → FiniteEuclidean) (i j : ι) (hij : i≠j)
    (x y : FiniteEuclidean) (hxy : ‖x-y‖=‖a i-a j‖) :
    FreeGroup.of x*(FreeGroup.of y)⁻¹∈pairLeft a i j hij := by
  obtain ⟨b,hbi,hbj,hb⟩ := extend_pair_E a i j x y (by
    simpa only [norm_sub_rev y x,norm_sub_rev (a j) (a i)] using hxy)
  have hcopy : (FreeGroup.of x,FreeGroup.of y)∈pairGroup a i j hij := by
    refine ⟨(fun k => FreeGroup.of (b k)),⟨1,UnitWords.copy b hb⟩,?_⟩
    exact Prod.ext (congrArg FreeGroup.of hbi) (congrArg FreeGroup.of hbj)
  have h := (pairGroup a i j hij).mul_mem hcopy (pairGroup_diag a i j hij (FreeGroup.of y)⁻¹)
  simpa [pairLeft,MonoidHom.inl_apply] using h

lemma unit_pair_coverage (a : ι → FiniteEuclidean) (ha : Function.Injective a) :
    PairCoverage (unitGraded a).monoid (AugKernel FiniteEuclidean) := by
  intro i j hij g hg h hh
  have hr : 0<‖a i-a j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun he => hij (ha he)))
  have hle : AugKernel FiniteEuclidean≤pairLeft a i j hij := by
    apply augmentation_kernel_le 0
    intro x y
    apply FiniteEuclidean.unit_distance_constant _ hr
      (fun z => (QuotientGroup.mk' (pairLeft a i j hij)) (FreeGroup.of z))
    intro x y hxy
    apply QuotientGroup.eq_iff_div_mem.mpr
    simpa only [div_eq_mul_inv] using pairLeft_edge a i j hij x y hxy
  have hleft : (g,1)∈pairGroup a i j hij := hle hg
  have hright : (1,h)∈pairGroup a i j hij := by
    have h := (pairGroup a i j hij).mul_mem (pairGroup_diag a i j hij h)
      (hle ((AugKernel FiniteEuclidean).inv_mem hh))
    simpa using h
  have hp := (pairGroup a i j hij).mul_mem hleft hright
  have hp' : (g,h)∈(unitGraded a).monoid.map (pairHom i j) := by
    change (g,h)∈pairGroup a i j hij
    simpa using hp
  obtain ⟨v,hv,hv'⟩ := hp'
  exact ⟨v,hv,congrArg Prod.fst hv',congrArg Prod.snd hv'⟩
end EuclideanRamsey
namespace EuclideanRamsey
open scoped BigOperators
abbrev Strings := FreeMonoid FiniteEuclidean

def stringEnergy : List FiniteEuclidean → List FiniteEuclidean → ℝ
  | x::l,y::k => ‖x-y‖^2+stringEnergy l k
  | _,_ => 0
@[simp] lemma stringEnergy_self (l : List FiniteEuclidean) : stringEnergy l l=0 := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [stringEnergy,ih]
lemma stringEnergy_append (l k l' k' : List FiniteEuclidean) (h : l.length=k.length) :
    stringEnergy (l++l') (k++k')=stringEnergy l k+stringEnergy l' k' := by
  induction l generalizing k with
  | nil => have hk : k=[] := List.length_eq_zero_iff.mp h.symm; subst k; simp [stringEnergy]
  | cons x l ih =>
    cases k with
    | nil => simp at h
    | cons y k =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at h
      simp only [List.cons_append,stringEnergy,ih k h,add_assoc]

lemma stringEnergy_eq_sum (l k : List FiniteEuclidean) (h : l.length=k.length) :
    stringEnergy l k = ∑ i : Fin l.length,‖l.get i-k.get (i.cast h)‖^2 := by
  induction l generalizing k with
  | nil => simp [stringEnergy]
  | cons x l ih =>
    cases k with
    | nil => simp at h
    | cons y k =>
      have h' : l.length=k.length := Nat.add_right_cancel h
      change _ = ∑ i : Fin (l.length+1), ‖(x::l).get i-(y::k).get (i.cast h)‖^2
      rw [Fin.sum_univ_succ]
      simpa only [stringEnergy,List.get_eq_getElem,List.getElem_cons_zero,List.getElem_cons_succ,
        Fin.val_zero,Fin.val_succ,Fin.val_cast] using congrArg (fun t => ‖x-y‖^2+t) (ih k h')

lemma flatten_energy (l k : List FiniteEuclidean) (h : l.length=k.length) :
    ‖FiniteEuclidean.flatten l-FiniteEuclidean.flatten k‖^2=stringEnergy l k := by
  rw [FiniteEuclidean.flatten_distance l k h,stringEnergy_eq_sum l k h]

variable {ι : Type uIndex}
def StringFamily (a : ι → FiniteEuclidean) (u : ℝ) (x : ι → Strings) : Prop :=
  (∀ i j,(x i).toList.length=(x j).toList.length) ∧
  ∀ i j,stringEnergy (x i).toList (x j).toList=u*‖a i-a j‖^2
lemma StringFamily.common (a : ι → FiniteEuclidean) (x : Strings) :
    StringFamily a 0 (fun _ => x) := by constructor <;> intros <;> simp [stringEnergy_self]
lemma StringFamily.single {a : ι → FiniteEuclidean} {u : ℝ} {b : ι → FiniteEuclidean}
    (h : CopyPath a u b) : StringFamily a u (fun i => FreeMonoid.of (b i)) := by
  refine ⟨fun _ _ => rfl,?_⟩
  intro i j
  change ‖b i-b j‖^2+0=u*‖a i-a j‖^2
  simpa only [add_zero] using h.2 i j
lemma StringFamily.mul {a : ι → FiniteEuclidean} {u v : ℝ} {x y : ι → Strings}
    (hx : StringFamily a u x) (hy : StringFamily a v y) : StringFamily a (u+v) (x*y) := by
  refine ⟨?_,?_⟩
  · intro i j
    change ((x i).toList++(y i).toList).length=((x j).toList++(y j).toList).length
    simp only [List.length_append,hx.1 i j,hy.1 i j]
  · intro i j
    change stringEnergy ((x i).toList++(y i).toList) ((x j).toList++(y j).toList)=_
    rw [stringEnergy_append _ _ _ _ (hx.1 i j),hx.2,hy.2,add_mul]
lemma StringFamily.congruent {a : ι → FiniteEuclidean} {x : ι → Strings}
    (h : StringFamily a 1 x) :
    ∀ i j,‖FiniteEuclidean.flatten (x i).toList-FiniteEuclidean.flatten (x j).toList‖=‖a i-a j‖ := by
  intro i j
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [flatten_energy _ _ (h.1 i j),h.2,one_mul]
end EuclideanRamsey

end

end OAI
