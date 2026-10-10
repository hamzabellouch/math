import OAI.Geometry.QuadricBundles.LaurentCech

namespace OAI

universe u1 u2

noncomputable section

namespace QuadricCounterexample
open Set MvPolynomial Matrix
open scoped BigOperators
noncomputable section

lemma UniformlyRegularOn.finset_sum {ι : Type u1} (s : Finset ι)
    {U : Set BaseCoordinates} {f : ι → BaseCoordinates → ℂ}
    (hf : ∀ i∈s,UniformlyRegularOn U (f i)) :
    UniformlyRegularOn U (fun z ↦ ∑ i∈s,f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using uniformlyRegular_const U 0
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using (hf a (Finset.mem_insert_self a s)).add
      (ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))
lemma UniformlyRegularOn.fintype_sum {ι : Type u2} [Fintype ι]
    {U : Set BaseCoordinates} {f : ι → BaseCoordinates → ℂ}
    (hf : ∀ i,UniformlyRegularOn U (f i)) :
    UniformlyRegularOn U (fun z ↦ ∑ i,f i z) :=
  UniformlyRegularOn.finset_sum Finset.univ (fun i _ ↦ hf i)

namespace LaurentCech
lemma scalarFactor_mul_one_overlap (i j k : Fin 2) {z : ℂ} (hz : i=j ∨ z≠0) :
    scalarFactor i j z*scalarFactor j k (scalarCoordinateChange i j z)=scalarFactor i k z := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [scalarFactor,scalarCoordinateChange]
lemma lineFactor_mul_one_overlap (d : ℕ × ℕ) (i j k : Chart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) :
    lineFactor d i j z*lineFactor d j k (coordinateChange i j z)=lineFactor d i k z := by
  have h1 := scalarFactor_mul_one_overlap i.1 j.1 k.1 ((coordinateOverlap_iff i j z).mp hz).1
  have h2 := scalarFactor_mul_one_overlap i.2 j.2 k.2 ((coordinateOverlap_iff i j z).mp hz).2
  unfold lineFactor firstFactor secondFactor coordinateChange
  calc
    _ = (scalarFactor i.1 j.1 z.1*scalarFactor j.1 k.1 (scalarCoordinateChange i.1 j.1 z.1))^d.1*
      (scalarFactor i.2 j.2 z.2*scalarFactor j.2 k.2 (scalarCoordinateChange i.2 j.2 z.2))^d.2 := by
        simp only [mul_pow]; ring
    _ = _ := by rw [h1,h2]
@[simp] lemma lineFactor_self (d : ℕ × ℕ) (i : Chart) (z : BaseCoordinates) :
    lineFactor d i i z=1 := by simp [lineFactor,firstFactor,secondFactor,scalarFactor]

def lineGenerator (d : ℕ × ℕ) (anchor i : Chart) : BasePolynomial :=
  (if i.1=anchor.1 then 1 else X 0^d.1)*(if i.2=anchor.2 then 1 else X 1^d.2)
lemma eval_lineGenerator (d : ℕ × ℕ) (anchor i : Chart) (z : BaseCoordinates) :
    baseEval (lineGenerator d anchor i) z=lineFactor d i anchor z := by
  simp only [lineGenerator,lineFactor,firstFactor,secondFactor,scalarFactor,baseEval_mul]
  split_ifs <;> simp [baseEval]
lemma lineGenerator_compatible (d : ℕ × ℕ) (anchor i j : Chart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) :
    lineFactor d i j z*baseEval (lineGenerator d anchor j) (coordinateChange i j z)=
      baseEval (lineGenerator d anchor i) z := by
  simp only [eval_lineGenerator]
  exact lineFactor_mul_one_overlap d i j anchor hz
end LaurentCech

open LaurentCech

structure TriangularCechBundle (r : ℕ) where
  degree : Fin r → ℕ × ℕ
  matrix : Chart → Chart → BaseCoordinates → Matrix (Fin r) (Fin r) ℂ
  regular : ∀ i j a b,UniformlyRegularOn (coordinateOverlap i j) (fun z ↦ matrix i j z a b)
  self : ∀ i z,matrix i i z=1
  cocycle : ∀ i j k z,z∈coordinateOverlap i j → z∈coordinateOverlap i k →
    matrix i j z*matrix j k (coordinateChange i j z)=matrix i k z
  triangular : ∀ i j z,z∈coordinateOverlap i j → ∀ a b,b<a → matrix i j z a b=0
  diagonal : ∀ i j z,z∈coordinateOverlap i j → ∀ a,matrix i j z a a=lineFactor (degree a) i j z

namespace TriangularCechBundle
variable {r : ℕ} (B : TriangularCechBundle r)
def polynomialValue (q : Chart → Fin r → BasePolynomial) (i : Chart) (z : BaseCoordinates) : Fin r → ℂ :=
  fun k ↦ baseEval (q i k) z

def delta (q : Chart → Fin r → BasePolynomial) (i j : Chart) (z : BaseCoordinates) : Fin r → ℂ :=
  (B.matrix i j z).mulVec (polynomialValue q j (coordinateChange i j z))-polynomialValue q i z
lemma delta_regular (q : Chart → Fin r → BasePolynomial) (i j : Chart) (a : Fin r) :
    UniformlyRegularOn (coordinateOverlap i j) (fun z ↦ B.delta q i j z a) := by
  apply UniformlyRegularOn.sub _ (uniformlyRegular_polynomial _ (q i a))
  change UniformlyRegularOn (coordinateOverlap i j) (fun z ↦ ∑ b, B.matrix i j z a b*baseEval (q j b) (coordinateChange i j z))
  apply UniformlyRegularOn.fintype_sum
  intro b
  exact (B.regular i j a b).mul ((uniformlyRegular_polynomial univ (q j b)).comp
    (coordinateChange_fst_regular i j) (coordinateChange_snd_regular i j) (fun _ _ ↦ mem_univ _))
lemma delta_cocycle (q : Chart → Fin r → BasePolynomial) (i j k : Chart) {z : BaseCoordinates}
    (hj : z∈coordinateOverlap i j) (hk : z∈coordinateOverlap i k) :
    B.delta q i j z+(B.matrix i j z).mulVec (B.delta q j k (coordinateChange i j z))=B.delta q i k z := by
  unfold delta
  rw [mulVec_sub, mulVec_mulVec, B.cocycle i j k z hj hk,coordinateChange_comp i j k hj]
  abel
lemma delta_add (q p : Chart → Fin r → BasePolynomial) (i j : Chart) (z : BaseCoordinates) :
    B.delta (q+p) i j z=B.delta q i j z+B.delta p i j z := by
  have hq (a : Chart) (w : BaseCoordinates) :
      polynomialValue (q+p) a w=polynomialValue q a w+polynomialValue p a w := by
    ext b; simp [polynomialValue]
  simp only [delta,hq,mulVec_add]
  abel
lemma delta_zero (i j : Chart) (z : BaseCoordinates) : B.delta 0 i j z=0 := by
  have h (i : Chart) (z : BaseCoordinates) : polynomialValue (0 : Chart → Fin r → BasePolynomial) i z=0 := by
    ext a; simp [polynomialValue]
  simp only [delta,h,mulVec_zero,sub_self]
lemma row_of_high_zero (i j : Chart) {z : BaseCoordinates} (hz : z∈coordinateOverlap i j)
    (k : Fin r) (v : Fin r → ℂ) (hv : ∀ a,k<a → v a=0) :
    (B.matrix i j z).mulVec v k=lineFactor (B.degree k) i j z*v k := by
  change (∑ a : Fin r, B.matrix i j z k a*v a)=_
  rw [Finset.sum_eq_single k]
  · rw [B.diagonal i j z hz k]
  · intro a _ ha
    rcases lt_or_gt_of_ne ha with ha | ha
    · rw [B.triangular i j z hz k a ha,zero_mul]
    · rw [hv a ha,mul_zero]
  · simp

structure Cocycle where
  value : Chart → Chart → BaseCoordinates → Fin r → ℂ
  regular : ∀ i j a,UniformlyRegularOn (coordinateOverlap i j) (fun z ↦ value i j z a)
  compatible : ∀ i j k z,z∈coordinateOverlap i j → z∈coordinateOverlap i k →
    value i j z+(B.matrix i j z).mulVec (value j k (coordinateChange i j z))=value i k z

def coboundary (q : Chart → Fin r → BasePolynomial) : B.Cocycle where
  value := B.delta q
  regular := B.delta_regular q
  compatible := fun _ _ _ _ hj hk ↦ B.delta_cocycle q _ _ _ hj hk

def Cocycle.sub (f g : B.Cocycle) : B.Cocycle where
  value i j z := f.value i j z-g.value i j z
  regular i j a := (f.regular i j a).sub (g.regular i j a)
  compatible i j k z hj hk := by
    rw [mulVec_sub]
    have hf := f.compatible i j k z hj hk
    have hg := g.compatible i j k z hj hk
    linear_combination hf-hg

theorem solve_upTo (b : ℕ) (hb : b≤r) (f : B.Cocycle)
    (hf : ∀ i j z,z∈coordinateOverlap i j → ∀ a : Fin r,b≤a.val → f.value i j z a=0) :
    ∃ q : Chart → Fin r → BasePolynomial,
      (∀ i a,b≤a.val → q i a=0) ∧
      ∀ i j z,z∈coordinateOverlap i j → f.value i j z=B.delta q i j z := by
  induction b generalizing f with
  | zero =>
    refine ⟨0,fun _ _ _ ↦ rfl,?_⟩
    intro i j z hz
    rw [B.delta_zero]
    ext a
    exact hf i j z hz a (Nat.zero_le _)
  | succ b ih =>
    let k : Fin r := ⟨b,by omega⟩
    have hc : ∀ i j l z,z∈coordinateOverlap i j → z∈coordinateOverlap i l →
        f.value i j z k+lineFactor (B.degree k) i j z*f.value j l (coordinateChange i j z) k=
          f.value i l z k := by
      intro i j l z hj hl
      have h := congrFun (f.compatible i j l z hj hl) k
      dsimp only [Pi.add_apply] at h
      rw [B.row_of_high_zero i j hj k _ (fun a ha ↦
        hf j l _ (coordinateOverlap_third i j l hj hl) a (by exact ha))] at h
      exact h
    obtain ⟨p,hp⟩ := split_regular_line_cocycle (B.degree k) (fun i j z ↦ f.value i j z k)
      (fun i j ↦ f.regular i j k) hc
    let q₀ : Chart → Fin r → BasePolynomial := fun i a ↦ if a=k then p i else 0
    have hq (i : Chart) (z : BaseCoordinates) (a : Fin r) :
        polynomialValue q₀ i z a=if a=k then baseEval (p i) z else 0 := by
      simp only [polynomialValue,q₀]; split_ifs <;> simp
    have hδ (i j : Chart) (z : BaseCoordinates) (hz : z∈coordinateOverlap i j) (a : Fin r)
        (ha : k≤a) :
        B.delta q₀ i j z a=if a=k then f.value i j z k else 0 := by
      unfold delta
      simp only [Pi.sub_apply]
      rw [B.row_of_high_zero i j hz a _ (fun c hc ↦ by rw [hq]; simp [ne_of_gt (lt_of_le_of_lt ha hc)])]
      rw [hq,hq]
      by_cases h : a=k
      · subst a; simp only [ite_true]; exact (hp i j z hz).symm
      · simp [h]
    let g := Cocycle.sub B f (B.coboundary q₀)
    have hg : ∀ i j z,z∈coordinateOverlap i j → ∀ a : Fin r,b≤a.val → g.value i j z a=0 := by
      intro i j z hz a ha
      change f.value i j z a-B.delta q₀ i j z a=0
      rw [hδ i j z hz a ha]
      by_cases h : a=k
      · simp [h]
      · have hlt : b+1≤a.val := by have hne : a.val≠b := fun he ↦ h (Fin.ext he); omega
        simp [h,hf i j z hz a hlt]
    obtain ⟨q,hq0,hqe⟩ := ih (by omega) g hg
    refine ⟨q+q₀,?_,?_⟩
    · intro i a ha
      have hak : a≠k := by intro h; subst a; dsimp [k] at ha; omega
      simp [hq0 i a (by omega),q₀,hak]
    · intro i j z hz
      rw [B.delta_add]
      have h := hqe i j z hz
      change f.value i j z-B.delta q₀ i j z=B.delta q i j z at h
      exact sub_eq_iff_eq_add.mp h

theorem solve (f : B.Cocycle) : ∃ q : Chart → Fin r → BasePolynomial,
    ∀ i j z,z∈coordinateOverlap i j → f.value i j z=B.delta q i j z := by
  obtain ⟨q,_,hq⟩ := B.solve_upTo r le_rfl f (fun _ _ _ _ a ha ↦ False.elim (by omega))
  exact ⟨q,hq⟩
end TriangularCechBundle
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set MvPolynomial Matrix LaurentCech
open scoped BigOperators
noncomputable section
namespace TriangularCechBundle
variable {r : ℕ} (B : TriangularCechBundle r)

structure Section where
  polynomial : Chart → Fin r → BasePolynomial
  compatible : ∀ i j z,z∈coordinateOverlap i j →
    (B.matrix i j z).mulVec (polynomialValue polynomial j (coordinateChange i j z))=
      polynomialValue polynomial i z

lemma delta_sub (q p : Chart → Fin r → BasePolynomial) (i j : Chart) (z : BaseCoordinates) :
    B.delta (q-p) i j z=B.delta q i j z-B.delta p i j z := by
  have h (a : Chart) (w : BaseCoordinates) :
      polynomialValue (q-p) a w=polynomialValue q a w-polynomialValue p a w := by
    ext b; simp [polynomialValue]
  simp only [delta,h,mulVec_sub]
  abel

theorem exists_generator (anchor : Chart) (k : Fin r) :
    ∃ s : B.Section,
      (∀ i a,k<a → s.polynomial i a=0) ∧
      (∀ i,s.polynomial i k=lineGenerator (B.degree k) anchor i) := by
  let l : Chart → Fin r → BasePolynomial := fun i a ↦
    if a=k then lineGenerator (B.degree k) anchor i else 0
  have hl (i : Chart) (z : BaseCoordinates) (a : Fin r) :
      polynomialValue l i z a=if a=k then baseEval (lineGenerator (B.degree k) anchor i) z else 0 := by
    simp only [polynomialValue,l]; split_ifs <;> simp
  have hd : ∀ i j z,z∈coordinateOverlap i j → ∀ a : Fin r,k.val≤a.val → B.delta l i j z a=0 := by
    intro i j z hz a ha
    unfold delta
    simp only [Pi.sub_apply]
    rw [B.row_of_high_zero i j hz a _ (fun b hb ↦ by
      rw [hl]
      have hbk : b≠k := fun he ↦ by subst b; exact (not_lt_of_ge ha) hb
      simp [hbk])]
    rw [hl,hl]
    by_cases h : a=k
    · subst a
      simp only [ite_true]
      exact sub_eq_zero.mpr (lineGenerator_compatible (B.degree k) anchor i j hz)
    · simp [h]
  obtain ⟨q,hq,hqe⟩ := B.solve_upTo k.val (Nat.le_of_lt k.isLt) (B.coboundary l) hd
  have hcomp : ∀ i j z,z∈coordinateOverlap i j → B.delta (l-q) i j z=0 := by
    intro i j z hz
    rw [B.delta_sub]
    exact sub_eq_zero.mpr (hqe i j z hz)
  refine ⟨⟨l-q,fun i j z hz ↦ sub_eq_zero.mp (hcomp i j z hz)⟩,?_,?_⟩
  · intro i a ha
    change l i a-q i a=0
    simp [l,ne_of_gt ha,hq i a (Nat.le_of_lt ha)]
  · intro i
    change l i k-q i k=_
    simp [l,hq i k le_rfl]

def generator (anchor : Chart) (k : Fin r) : B.Section := (B.exists_generator anchor k).choose
lemma generator_high (anchor i : Chart) (k a : Fin r) (ha : k<a) :
    (B.generator anchor k).polynomial i a=0 := (B.exists_generator anchor k).choose_spec.1 i a ha
lemma generator_diagonal (anchor i : Chart) (k : Fin r) :
    (B.generator anchor k).polynomial i k=lineGenerator (B.degree k) anchor i :=
  (B.exists_generator anchor k).choose_spec.2 i

def generatorMatrix (anchor i : Chart) : Matrix (Fin r) (Fin r) BasePolynomial :=
  fun a k ↦ (B.generator anchor k).polynomial i a
lemma generatorMatrix_self_det (i : Chart) : (B.generatorMatrix i i).det=1 := by
  unfold generatorMatrix
  rw [Matrix.det_of_isUpperTriangular (fun a k ha ↦ B.generator_high i i k a ha)]
  apply Finset.prod_eq_one
  intro k _
  change (B.generator i k).polynomial i k=1
  rw [B.generator_diagonal]
  simp [lineGenerator]
lemma generatorMatrix_self_isUnit (i : Chart) : IsUnit (B.generatorMatrix i i) := by
  rw [Matrix.isUnit_iff_isUnit_det,B.generatorMatrix_self_det]
  exact isUnit_one

theorem generated (i : Chart) (z : BaseCoordinates) (v : Fin r → ℂ) :
    ∃ c : Fin r → ℂ, ∀ a, ∑ k,c k*baseEval ((B.generator i k).polynomial i a) z=v a := by
  let A : Matrix (Fin r) (Fin r) ℂ := fun a k ↦ baseEval ((B.generator i k).polynomial i a) z
  have hA : A.det=1 := by
    rw [Matrix.det_of_isUpperTriangular (fun a k ha ↦ by dsimp [A]; rw [B.generator_high i i k a ha]; simp)]
    apply Finset.prod_eq_one
    intro k _
    dsimp [A]
    rw [B.generator_diagonal]
    simp [lineGenerator]
  obtain ⟨c,hc⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det A).mpr (hA ▸ isUnit_one)) v
  refine ⟨c,fun a ↦ ?_⟩
  have h := congrFun hc a
  simpa only [Matrix.mulVec, dotProduct,mul_comm] using h
end TriangularCechBundle
end
end QuadricCounterexample

end

end OAI
