import OAI.NumberTheory.PrimeGaps.RestrictedWeights

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem tensorProfile_extendPerm {n d : ℕ} (e : Equiv.Perm (Fin n))
    (f : (Fin n → ℝ) → ℝ) (g : (Fin d → ℝ) → ℝ)
    (hf : ∀ y,f (y ∘ e)=f y) (v : Fin (n+d) → ℝ) :
    tensorProfile f g (v ∘ extendPerm e d)=tensorProfile f g v := by
  simp only [tensorProfile,Function.comp_apply,extendPerm_left,extendPerm_right]
  congr 1
  exact hf (fun i => v (i.castAdd d))

noncomputable def extendLabels {n : ℕ} {α : Type*} (a : Fin n → α) (d : ℕ) :
    Fin (n+d) → α ⊕ Fin d := Fin.append (Sum.inl ∘ a) Sum.inr

@[simp] theorem extendLabels_left {n d : ℕ} {α : Type*} (a : Fin n → α) (i : Fin n) :
    extendLabels a d (i.castAdd d)=Sum.inl (a i) := by simp [extendLabels]

@[simp] theorem extendLabels_right {n d : ℕ} {α : Type*} (a : Fin n → α) (i : Fin d) :
    extendLabels a d (i.natAdd n)=Sum.inr i := by simp [extendLabels]

theorem extendLabels_injective {n : ℕ} {α : Type*} (a : Fin n → α) (d : ℕ)
    (ha : Function.Injective a) : Function.Injective (extendLabels a d) := by
  intro i j h
  cases i using Fin.addCases <;> cases j using Fin.addCases <;>
    simp only [extendLabels_left,extendLabels_right,Sum.inl.injEq,Sum.inr.injEq,
      Sum.inl_ne_inr,Sum.inr_ne_inl] at h
  · exact congrArg (Fin.castAdd d) (ha h)
  · exact congrArg (Fin.natAdd n) h

theorem extendLabels_range_ne {n p : ℕ} {α : Type*} (a : Fin n → α) (b : Fin p → α)
    (d : ℕ) (hab : Set.range a≠Set.range b) :
    Set.range (extendLabels a d)≠Set.range (extendLabels b d) := by
  intro he
  apply hab
  ext x
  have hh : ∀ {n : ℕ} (a : Fin n → α), Sum.inl x∈Set.range (extendLabels a d) ↔ x∈Set.range a := by
    intro n a
    constructor
    · rintro ⟨i,hi⟩
      cases i using Fin.addCases with
      | left i => exact ⟨i,by simpa using hi⟩
      | right i => simp at hi
    · rintro ⟨i,rfl⟩; exact ⟨i.castAdd d,by simp⟩
  rw [←hh a,←hh b,he]

noncomputable def extraPairLabels {n p : ℕ} (r : Setoid (Fin (n+p))) (d : ℕ) :
    Fin ((n+d)+(p+d)) → ℕ ⊕ Fin d :=
  Fin.append (extendLabels (fun i : Fin n => numericPattern r (i.castAdd p)) d)
    (extendLabels (fun i : Fin p => numericPattern r (i.natAdd n)) d)

noncomputable def extraPairFamily {n p : ℕ} (r : Setoid (Fin (n+p))) (d : ℕ) :
    Finset (Finset (Fin ((n+d)+(p+d)))) := by
  classical
  exact fiberSubsetFamily (extraPairLabels r d) (Finset.univ.image (extraPairLabels r d))

theorem castAdd_ne_natAdd {n d : ℕ} (i : Fin n) (j : Fin d) : i.castAdd d≠j.natAdd n := by
  intro h
  have hh := congrArg Fin.val h
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hh
  have hi := i.isLt
  omega

theorem natAdd_ne_castAdd {n d : ℕ} (i : Fin d) (j : Fin n) : i.natAdd n≠j.castAdd d :=
  (castAdd_ne_natAdd j i).symm

theorem extraPairFamily_matched {n d : ℕ} (e : Equiv.Perm (Fin n)) :
    extraPairFamily (n:=n) (p:=n) (matchedPattern e) d=
      fiberSubsetFamily (permutedLabels (extendPerm e d)) Finset.univ := by
  classical
  have he := fiberSubsetFamily_image_eq_of_kernel (extraPairLabels (n:=n) (p:=n) (matchedPattern e) d)
    (permutedLabels (extendPerm e d))
  have hh : ∀ i j, extraPairLabels (n:=n) (p:=n) (matchedPattern e) d i=extraPairLabels (n:=n) (p:=n) (matchedPattern e) d j ↔
      permutedLabels (extendPerm e d) i=permutedLabels (extendPerm e d) j := by
    intro i j
    have hr (i j : Fin (n+n)) : numericPattern (matchedPattern e) i=numericPattern (matchedPattern e) j ↔
        permutedLabels e i=permutedLabels e j := by
      change (Setoid.ker (numericPattern (matchedPattern e))) i j ↔ _
      rw [numericPattern_ker]
      rfl
    cases i using Fin.addCases <;> cases j using Fin.addCases <;>
      simp only [extraPairLabels,Fin.append_left,Fin.append_right,permutedLabels] <;>
      rename_i i j <;> cases i using Fin.addCases <;> cases j using Fin.addCases <;>
      simp only [extendLabels_left,extendLabels_right,extendPerm_left,extendPerm_right,
        Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,Fin.castAdd_inj,Fin.natAdd_inj,
        hr,permutedLabels,Fin.append_left,Fin.append_right,Function.id_def,Equiv.apply_eq_iff_eq,
        castAdd_ne_natAdd,natAdd_ne_castAdd]
  have he' : extraPairFamily (matchedPattern e) d=
      fiberSubsetFamily (permutedLabels (extendPerm e d))
        (Finset.univ.image (permutedLabels (extendPerm e d))) := by
    ext S
    simpa only [extraPairFamily,mem_fiberSubsetFamily_image] using Finset.ext_iff.mp (he hh) S
  rw [he']
  congr 1
  ext i
  simp only [Finset.mem_image,Finset.mem_univ,true_and,iff_true]
  exact ⟨i.castAdd (n+d),by simp [permutedLabels]⟩

noncomputable def extraPairProfile {n p d : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin p → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ) :
    (Fin ((n+d)+(p+d)) → ℝ) → ℝ := tensorProfile (tensorProfile f w) (tensorProfile g w)

theorem extraPairProfile_compact {n p d : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin p → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) (hw : HasCompactSupport w) :
    HasCompactSupport (extraPairProfile f g w) :=
  tensorProfile_compact _ _ (tensorProfile_compact f w hf hw) (tensorProfile_compact g w hg hw)

theorem extraPairProfile_smooth {n p d : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin p → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (extraPairProfile f g w) :=
  tensorProfile_smooth _ _ (tensorProfile_smooth f w hf hw) (tensorProfile_smooth g w hg hw)

noncomputable def extraPairKernel {n p d : ℕ} (tau sigma : ℝ)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) (hw : HasCompactSupport w)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g) (hws : ContDiff ℝ ∞ w)
    (r : Setoid (Fin (n+p))) : ℂ :=
  kernelConstant (sourceFourier (fourierCoordinateSum (Fin ((n+d)+(p+d))))
    (fun v => (cumulativeProfile ((tau+sigma)+(tau+sigma)) (extraPairProfile f g w) v.ofLp:ℂ))
    (realEuclidean_compact _ (cumulativeProfile_compact _ _ (extraPairProfile_compact f g w hf hg hw)))
    (realEuclidean_smooth _ (cumulativeProfile_smooth _ _
      (extraPairProfile_compact f g w hf hg hw) (extraPairProfile_smooth f g w hfs hgs hws))))
      (extraPairFamily r d)

theorem extraPairKernel_unmatched {n p d : ℕ} {tau sigma : ℝ}
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) (hw : HasCompactSupport w)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g) (hws : ContDiff ℝ ∞ w)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau)
    (hsw : tsupport w⊆positiveSimplex d sigma)
    (r : Setoid (Fin (n+p)))
    (hl : Setoid.comap (Fin.castAdd p) r=⊥) (hr : Setoid.comap (Fin.natAdd n) r=⊥)
    (hne : Set.range (fun i : Fin n => numericPattern r (i.castAdd p))≠
      Set.range (fun i : Fin p => numericPattern r (i.natAdd n))) :
    extraPairKernel tau sigma f g w hf hg hw hfs hgs hws r=0 := by
  unfold extraPairKernel
  convert cumulative_tensor_unmatched_kernel_zero (tensorProfile f w) (tensorProfile g w)
    (tensorProfile_compact f w hf hw) (tensorProfile_compact g w hg hw)
    (tensorProfile_smooth f w hfs hws) (tensorProfile_smooth g w hgs hws)
    (tensorProfile_tsupport f w hsf hsw) (tensorProfile_tsupport g w hsg hsw)
    (extendLabels _ d) (extendLabels _ d)
    (extendLabels_injective _ d (numericPattern_left_injective r hl))
    (extendLabels_injective _ d (numericPattern_right_injective r hr))
    (extendLabels_range_ne _ _ d hne)
    (realEuclidean_compact _ (cumulativeProfile_compact _ _ (extraPairProfile_compact f g w hf hg hw)))
    (realEuclidean_smooth _ (cumulativeProfile_smooth _ _ (extraPairProfile_compact f g w hf hg hw)
      (extraPairProfile_smooth f g w hfs hgs hws))) using 1
  congr 2
  ext x
  simp only [extraPairFamily,extraPairLabels,mem_fiberSubsetFamily_image]

theorem extraPairKernel_matched {n d : ℕ} {tau sigma : ℝ}
    (f : (Fin n → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hw : HasCompactSupport w)
    (hfs : ContDiff ℝ ∞ f) (hws : ContDiff ℝ ∞ w)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsw : tsupport w⊆positiveSimplex d sigma)
    (hsym : SymmetricFunction f) (e : Equiv.Perm (Fin n)) :
    extraPairKernel tau sigma f f w hf hf hw hfs hfs hws (matchedPattern e)=
      (l2Mass f*l2Mass w:ℂ) := by
  unfold extraPairKernel
  rw [extraPairFamily_matched]
  have hh := cumulative_tensor_permuted_kernel_invariant (extendPerm e d) (tensorProfile f w)
    (tensorProfile_compact f w hf hw) (tensorProfile_smooth f w hfs hws)
    (tensorProfile_tsupport f w hsf hsw) (tensorProfile_extendPerm e f w (fun y => hsym e y))
    (realEuclidean_compact _ (cumulativeProfile_compact _ _ (extraPairProfile_compact f f w hf hf hw)))
    (realEuclidean_smooth _ (cumulativeProfile_smooth _ _ (extraPairProfile_compact f f w hf hf hw)
      (extraPairProfile_smooth f f w hfs hfs hws)))
  rw [l2Mass_tensor,Complex.ofReal_mul] at hh
  convert hh using 1
  rfl

noncomputable def splitOffsets (s d h : ℕ) : Fin (s+d) → ℕ :=
  Fin.append (fun _ => h+1) (fun _ => 1)

theorem splitBox_mem {s d h : ℕ} (u : Fin s → Fin h) (v : Fin d → Fin h) :
    Fin.append u v∈distinctBox (fun j => (splitOffsets s d h j:ℤ)) ↔
      u∈distinctBox (fun _ => ((h+1:ℕ):ℤ)) ∧ v∈distinctBox (fun _ => (1:ℤ)) := by
  classical
  simp only [distinctBox,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro hu
    constructor
    · intro i j hij
      have he : boxTuple (fun k => (splitOffsets s d h k:ℤ)) (Fin.append u v) (i.castAdd d)=
          boxTuple (fun k => (splitOffsets s d h k:ℤ)) (Fin.append u v) (j.castAdd d) := by
        simpa [boxTuple,splitOffsets] using hij
      exact Fin.castAdd_inj.mp (hu he)
    · intro i j hij
      have he : boxTuple (fun k => (splitOffsets s d h k:ℤ)) (Fin.append u v) (i.natAdd s)=
          boxTuple (fun k => (splitOffsets s d h k:ℤ)) (Fin.append u v) (j.natAdd s) := by
        simpa [boxTuple,splitOffsets] using hij
      have he' := congrArg Fin.val (hu he)
      simp only [Fin.val_natAdd] at he'
      exact Fin.ext (Nat.add_left_cancel he')
  · rintro ⟨hu,hv⟩ i j hij
    cases i using Fin.addCases with
    | left i =>
      cases j using Fin.addCases with
      | left j =>
        congr 1
        apply hu
        simpa [boxTuple,splitOffsets] using hij
      | right j =>
        have hi := (u i).isLt
        have hj := (v j).isLt
        simp only [boxTuple,splitOffsets,Fin.append_left,Fin.append_right,Nat.cast_add,Nat.cast_one] at hij
        omega
    | right i =>
      cases j using Fin.addCases with
      | left j =>
        have hi := (v i).isLt
        have hj := (u j).isLt
        simp only [boxTuple,splitOffsets,Fin.append_left,Fin.append_right,Nat.cast_add,Nat.cast_one] at hij
        omega
      | right j =>
        congr 1
        apply hv
        simpa [boxTuple,splitOffsets] using hij

noncomputable def splitBoxEquiv (s d h : ℕ) :
    ({u // u∈distinctBox (s:=s) (h:=h) (fun _ => ((h+1:ℕ):ℤ))} ×
      {v // v∈distinctBox (s:=d) (h:=h) (fun _ => (1:ℤ))}) ≃
    {u // u∈distinctBox (s:=s+d) (h:=h) (fun j => (splitOffsets s d h j:ℤ))} where
  toFun t := ⟨Fin.append t.1.1 t.2.1,(splitBox_mem t.1.1 t.2.1).mpr ⟨t.1.2,t.2.2⟩⟩
  invFun v := by
    let v1 := fun i : Fin s => v.1 (i.castAdd d)
    let v2 := fun i : Fin d => v.1 (i.natAdd s)
    have he : Fin.append v1 v2=v.1 := by
      funext i
      cases i using Fin.addCases <;> simp [v1,v2]
    have hv : v1∈distinctBox (fun _ => ((h+1:ℕ):ℤ)) ∧ v2∈distinctBox (fun _ => (1:ℤ)) :=
      (splitBox_mem v1 v2).mp (he.symm ▸ v.2)
    exact (⟨v1,hv.1⟩,⟨v2,hv.2⟩)
  left_inv t := by
    apply Prod.ext <;> apply Subtype.ext <;> funext i <;> simp
  right_inv v := by
    apply Subtype.ext
    funext i
    cases i using Fin.addCases <;> simp

theorem split_double_sum {s d h : ℕ} {K : Type*} [AddCommMonoid K]
    (F : (Fin (s+d) → Fin h) → K) :
    (∑ u∈distinctBox (s:=s) (h:=h) (fun _ => ((h+1:ℕ):ℤ)),
      ∑ v∈distinctBox (s:=d) (h:=h) (fun _ => (1:ℤ)),F (Fin.append u v))=
      ∑ w∈distinctBox (s:=s+d) (h:=h) (fun j => (splitOffsets s d h j:ℤ)),F w := by
  classical
  conv_lhs => rw [←Finset.sum_coe_sort]; arg 2; ext u; rw [←Finset.sum_coe_sort]
  conv_rhs => rw [←Finset.sum_coe_sort]
  calc
    _ = ∑ t : {u // u∈distinctBox (s:=s) (h:=h) (fun _ => ((h+1:ℕ):ℤ))} ×
      {v // v∈distinctBox (s:=d) (h:=h) (fun _ => (1:ℤ))},F (Fin.append t.1.val t.2.val) :=
        (Fintype.sum_prod_type _).symm
    _ = _ := Fintype.sum_equiv (splitBoxEquiv s d h) _ _ (fun _ => rfl)

theorem splitOffsets_eventually {lam : ℝ} (hlam : 0<lam) (s d : ℕ) :
    ∀ᶠ X : ℕ in atTop,∀ j,splitOffsets s d (blockLength lam X) j≤2*blockLength lam X := by
  filter_upwards [blockOffset_eventually hlam] with X hX j
  cases j using Fin.addCases with
  | left j => simpa only [splitOffsets,Fin.append_left] using hX
  | right j => simp only [splitOffsets,Fin.append_right]; omega

noncomputable def extraBoxLabels {n p : ℕ} (r : Setoid (Fin (n+p))) (d : ℕ) :
    Fin ((n+d)+(p+d)) → Fin (Fintype.card (Quotient r)+d) :=
  Fin.append
    (Fin.append (fun i : Fin n => (patternLabels r (i.castAdd p)).castAdd d) (Fin.natAdd _))
    (Fin.append (fun i : Fin p => (patternLabels r (i.natAdd n)).castAdd d) (Fin.natAdd _))

theorem extraBoxLabels_surjective {n p : ℕ} (r : Setoid (Fin (n+p))) (d : ℕ) :
    Function.Surjective (extraBoxLabels r d) := by
  intro i
  cases i using Fin.addCases with
  | left i =>
    obtain ⟨j,hj⟩ := patternLabels_surjective r i
    cases j using Fin.addCases with
    | left j => exact ⟨(j.castAdd d).castAdd (p+d),by simp [extraBoxLabels,hj]⟩
    | right j => exact ⟨(j.castAdd d).natAdd (n+d),by simp [extraBoxLabels,hj]⟩
  | right i => exact ⟨(i.natAdd n).castAdd (p+d),by simp [extraBoxLabels]⟩

noncomputable def extraShifts {n p d h : ℕ} (b : Fin (n+p) → Fin h) (c : Fin d → Fin h) :
    Fin ((n+d)+(p+d)) → ℕ :=
  Fin.append
    (Fin.append (fun i : Fin n => h+1+(b (i.castAdd p):ℕ)) (fun i => 1+(c i:ℕ)))
    (Fin.append (fun i : Fin p => h+1+(b (i.natAdd n):ℕ)) (fun i => 1+(c i:ℕ)))

theorem extraBoxShifts_eq {n p d h : ℕ} (r : Setoid (Fin (n+p)))
    (b : {b // b∈patternClass (α:=Fin h) r}) (c : Fin d → Fin h) :
    patternBoxShifts (extraBoxLabels r d) (splitOffsets _ d h)
      (Fin.append (patternTupleEquiv r h (h+1) b).val c)=extraShifts b.val c := by
  funext i
  have hb := patternTupleEquiv_labels r h (h+1) b
  cases i using Fin.addCases <;> rename_i i <;> cases i using Fin.addCases <;>
    simp only [extraBoxLabels,extraShifts,Fin.append_left,Fin.append_right,patternBoxShifts,
      splitOffsets,Fin.append_left,Fin.append_right]
  · exact congrFun hb _
  · exact congrFun hb _

theorem extra_pattern_sum_eq_box {n p d h X : ℕ} (r : Setoid (Fin (n+p)))
    (F : (Fin ((n+d)+(p+d)) → ℝ) → ℝ) :
    (∑ b∈patternClass (α:=Fin h) r,∑ c∈distinctBox (s:=d) (h:=h) (fun _ => (1:ℤ)),
      (average X (fun m => divisorSum X F m (extraShifts b c)):ℂ))=
    ∑ v∈distinctBox (s:=Fintype.card (Quotient r)+d) (h:=h)
      (fun j => (splitOffsets _ d h j:ℤ)),
      (average X (fun m => divisorSum X F m (patternBoxShifts (extraBoxLabels r d)
        (splitOffsets _ d h) v)):ℂ) := by
  classical
  rw [←split_double_sum]
  conv_lhs => rw [←Finset.sum_coe_sort]
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Fintype.sum_equiv (patternTupleEquiv r h ((h+1:ℕ):ℤ))
  intro b
  apply Finset.sum_congr rfl
  intro c _
  have he := extraBoxShifts_eq r b c
  convert congrArg (fun sh => (average X (fun m => divisorSum X F m sh):ℂ)) he.symm using 1
  norm_cast

theorem extra_square_pattern_sum {n d : ℕ} {tau sigma : ℝ} (lam : ℝ)
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsym : SymmetricFunction f)
    (w : (Fin d → ℝ) → ℝ) (hw : HasCompactSupport w) (hws : ContDiff ℝ ∞ w)
    (hsw : tsupport w⊆positiveSimplex d sigma) :
    (∑ r : Setoid (Fin (n+n)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient n) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*extraPairKernel tau sigma f f w hf hf hw hfs hfs hws r))=
      (alpha lam n*l2Mass f*l2Mass w:ℂ) := by
  classical
  let A := fun r : Setoid (Fin (n+n)) =>
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient n) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*extraPairKernel tau sigma f f w hf hf hw hfs hfs hws r)
  have hz : ∀ r,r∉Set.range (@matchedPattern n) → A r=0 := by
    intro r hr
    by_cases hl : Setoid.comap (Fin.castAdd n) r=⊥
    · by_cases hr' : Setoid.comap (Fin.natAdd n) r=⊥
      · have hne : Set.range (fun i : Fin n => numericPattern r (i.castAdd n))≠
            Set.range (fun i : Fin n => numericPattern r (i.natAdd n)) := by
          intro he
          obtain ⟨e,rfl⟩ := matching_pattern_eq r hl hr' he
          exact hr ⟨e,rfl⟩
        simp only [A,extraPairKernel_unmatched f f w hf hf hw hfs hfs hws hsf hsf hsw r hl hr' hne,mul_zero]
      · simp only [A,tensorCoefficient,subsetCoefficient,ite_eq_right hr',mul_zero,Complex.ofReal_zero,zero_mul]
    · simp only [A,tensorCoefficient,subsetCoefficient,ite_eq_right hl,zero_mul,Complex.ofReal_zero]
  have hv : ∀ e : Equiv.Perm (Fin n), A (matchedPattern e)=
      ((n.factorial:ℂ)⁻¹)^2*((lam:ℂ)^n*((l2Mass f:ℂ)*(l2Mass w:ℂ))) := by
    intro e
    simp only [A,tensorCoefficient,matchedPattern_left,matchedPattern_right,subsetCoefficient,
      ↓reduceIte,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_natCast,
      matchedPattern_quotient_card,extraPairKernel_matched f w hf hw hfs hws hsf hsw hsym e,Complex.ofReal_mul,pow_two]
  have hh := sum_matched_patterns _ A hz hv
  change (∑ r,A r)=_
  rw [hh]
  have hn : (n.factorial:ℂ)≠0 := by exact_mod_cast n.factorial_ne_zero
  simp only [alpha,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast]
  field_simp

theorem extra_cross_pattern_sum {m n d : ℕ} (hmn : m≠n) {tau sigma : ℝ} (lam : ℝ)
    (f : (Fin m → ℝ) → ℝ) (g : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex m tau) (hsg : tsupport g⊆positiveSimplex n tau)
    (w : (Fin d → ℝ) → ℝ) (hw : HasCompactSupport w) (hws : ContDiff ℝ ∞ w)
    (hsw : tsupport w⊆positiveSimplex d sigma) :
    (∑ r : Setoid (Fin (m+n)),
      (tensorCoefficient (subsetCoefficient m) (subsetCoefficient n) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*extraPairKernel tau sigma f g w hf hg hw hfs hgs hws r))=0 := by
  apply Finset.sum_eq_zero
  intro r _
  by_cases hl : Setoid.comap (Fin.castAdd n) r=⊥
  · by_cases hr : Setoid.comap (Fin.natAdd m) r=⊥
    · have hne : Set.range (fun i : Fin m => numericPattern r (i.castAdd n))≠
          Set.range (fun i : Fin n => numericPattern r (i.natAdd m)) := by
        intro he
        exact hmn (injective_ranges_card _ _ (numericPattern_left_injective r hl)
          (numericPattern_right_injective r hr) he)
      rw [extraPairKernel_unmatched f g w hf hg hw hfs hgs hws hsf hsg hsw r hl hr hne,mul_zero,mul_zero]
    · simp only [tensorCoefficient,subsetCoefficient,ite_eq_right hr,mul_zero,Complex.ofReal_zero,zero_mul]
  · simp only [tensorCoefficient,subsetCoefficient,ite_eq_right hl,zero_mul,Complex.ofReal_zero]

theorem extraBoxLabels_family {n p : ℕ} (r : Setoid (Fin (n+p))) (d : ℕ) :
    shiftFamily (fun i => ((extraBoxLabels r d i).val:ℤ))=extraPairFamily r d := by
  classical
  have he : ∀ i j, (extraBoxLabels r d i).val=(extraBoxLabels r d j).val ↔
      extraPairLabels r d i=extraPairLabels r d j := by
    intro i j
    rw [Fin.val_inj]
    cases i using Fin.addCases <;> cases j using Fin.addCases <;>
      simp only [extraPairLabels,extraBoxLabels,Fin.append_left,Fin.append_right] <;>
      rename_i i j <;> cases i using Fin.addCases <;> cases j using Fin.addCases <;>
      simp only [Fin.append_left,Fin.append_right,extendLabels_left,extendLabels_right,
        Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,Fin.castAdd_inj,Fin.natAdd_inj,
        castAdd_ne_natAdd,natAdd_ne_castAdd,numericPattern,patternLabels,Fin.val_inj]
  ext S
  simp only [shiftFamily,extraPairFamily,mem_fiberSubsetFamily_image,Int.natCast_inj,he]

theorem extra_pattern_limit {n p d : ℕ} {lam : ℝ} (hlam : 0<lam)
    (r : Setoid (Fin (n+p)))
    (F : (Fin ((n+(d+1))+(p+(d+1))) → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin ((n+(d+1))+(p+(d+1)))) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin ((n+(d+1))+(p+(d+1)))) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M) :
    Tendsto (fun X : ℕ => ∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
      ∑ c∈distinctBox (s:=d+1) (h:=blockLength lam X) (fun _ => (1:ℤ)),
        (average X (fun m => divisorSum X F m (extraShifts b c)):ℂ)) atTop
      (𝓝 ((lam:ℂ)^(Fintype.card (Quotient r)+(d+1))*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin ((n+(d+1))+(p+(d+1)))))
          (fun v => (F v.ofLp:ℂ)) hF hFs) (extraPairFamily r (d+1)))) := by
  have hh := unmarked_box_pattern_limit hlam (extraBoxLabels r (d+1))
    (extraBoxLabels_surjective r (d+1)) (fun X => splitOffsets _ (d+1) (blockLength lam X))
    (splitOffsets_eventually hlam _ (d+1)) F rho hrho hrho1 hbudget hF hFs M hM hbound
  convert hh using 1
  · funext X
    exact extra_pattern_sum_eq_box r F
  · congr 3
    exact (extraBoxLabels_family (n:=n) (p:=p) r (d+1)).symm

noncomputable def extraAverage {d : ℕ} (X h : ℕ) (H : ℕ → ℝ)
    (W : (Fin d → ℝ) → ℝ) : ℝ :=
  average X (fun m => ∑ c∈distinctBox (s:=d) (h:=h) (fun _ => (1:ℤ)),
    H m * divisorSum X W m (fun i => 1+(c i:ℕ))^2)

theorem extraAverage_finset_sum {d : ℕ} {α : Type*} (X h : ℕ) (S : Finset α)
    (H : α → ℕ → ℝ) (W : (Fin d → ℝ) → ℝ) :
    extraAverage X h (fun m => ∑ i∈S,H i m) W=∑ i∈S,extraAverage X h (H i) W := by
  unfold extraAverage
  simp only [Finset.sum_mul,average_finset_sum]
  rw [Finset.sum_comm]

theorem extra_divisor_product {n p d X h : ℕ} {tau sigma : ℝ} (hX : 2≤X)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau)
    (hsw : tsupport w⊆positiveSimplex d sigma)
    (M : ℕ) (b : Fin (n+p) → Fin h) (c : Fin d → Fin h) :
    divisorSum X (cumulativeProfile ((tau+sigma)+(tau+sigma)) (extraPairProfile f g w)) M (extraShifts b c)=
      divisorSum X (cumulativeProfile tau f) M (fun i => h+1+(b (i.castAdd p):ℕ))*
      divisorSum X (cumulativeProfile tau g) M (fun i => h+1+(b (i.natAdd n):ℕ))*
      divisorSum X (cumulativeProfile sigma w) M (fun i => 1+(c i:ℕ))^2 := by
  unfold extraPairProfile extraShifts
  rw [divisorSum_cumulative_tensor _ _ (tensorProfile_tsupport f w hsf hsw)
    (tensorProfile_tsupport g w hsg hsw) hX,
    divisorSum_cumulative_tensor f w hsf hsw hX,
    divisorSum_cumulative_tensor g w hsg hsw hX]
  ring

theorem extra_block_expansion {n p d X : ℕ} {tau sigma : ℝ} (hX : 2≤X) (h : ℕ)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau)
    (hsw : tsupport w⊆positiveSimplex d sigma)
    (k : Setoid (Fin n) → ℝ) (l : Setoid (Fin p) → ℝ) :
    (extraAverage X h (fun m => weightedBlock X h (h+1) (cumulativeProfile tau f) k m*
      weightedBlock X h (h+1) (cumulativeProfile tau g) l m) (cumulativeProfile sigma w):ℂ)=
      ∑ b : Fin (n+p) → Fin h,(tensorCoefficient k l (Setoid.ker b):ℂ)*
        ∑ c∈distinctBox (s:=d) (h:=h) (fun _ => (1:ℤ)),
        (average X (fun m => divisorSum X (cumulativeProfile ((tau+sigma)+(tau+sigma))
          (extraPairProfile f g w)) m (extraShifts b c)):ℂ) := by
  have he (m : ℕ) (c : Fin d → Fin h) :
      weightedBlock X h (h+1) (cumulativeProfile tau f) k m*
      weightedBlock X h (h+1) (cumulativeProfile tau g) l m*
      divisorSum X (cumulativeProfile sigma w) m (fun i => 1+(c i:ℕ))^2=
      ∑ b : Fin (n+p) → Fin h,tensorCoefficient k l (Setoid.ker b)*
        divisorSum X (cumulativeProfile ((tau+sigma)+(tau+sigma)) (extraPairProfile f g w)) m (extraShifts b c) := by
    simp only [weightedBlock,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm,←Finset.sum_product']
    apply Finset.sum_equiv (Fin.appendEquiv n p)
    · intro bc; simp
    intro bc _
    rw [show (Fin.appendEquiv n p) bc=Fin.append bc.1 bc.2 from rfl,
      extra_divisor_product hX f g w hsf hsg hsw]
    simp only [tensorCoefficient,append_ker_left,append_ker_right,Fin.append_left,Fin.append_right]
    ring
  unfold extraAverage
  simp only [he,average_finset_sum,average_const_mul,Complex.ofReal_sum,Complex.ofReal_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]

theorem extra_labeled_limit {n p d : ℕ} {lam : ℝ} (hlam : 0<lam)
    (F : (Fin ((n+(d+1))+(p+(d+1))) → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin ((n+(d+1))+(p+(d+1)))) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin ((n+(d+1))+(p+(d+1)))) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M)
    (k : Setoid (Fin (n+p)) → ℝ) :
    Tendsto (fun X : ℕ => ∑ b : Fin (n+p) → Fin (blockLength lam X),(k (Setoid.ker b):ℂ)*
      ∑ c∈distinctBox (s:=d+1) (h:=blockLength lam X) (fun _ => (1:ℤ)),
        (average X (fun m => divisorSum X F m (extraShifts b c)):ℂ)) atTop
      (𝓝 (∑ r : Setoid (Fin (n+p)),(k r:ℂ)*((lam:ℂ)^(Fintype.card (Quotient r)+(d+1))*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin ((n+(d+1))+(p+(d+1)))))
          (fun v => (F v.ofLp:ℂ)) hF hFs) (extraPairFamily r (d+1))))) := by
  have hh := tendsto_finsetSum Finset.univ (fun r _ =>
    (extra_pattern_limit hlam r F rho hrho hrho1 hbudget hF hFs M hM hbound).const_mul (k r:ℂ))
  apply hh.congr'
  exact Eventually.of_forall fun X => by
    dsimp only
    calc
      (∑ r : Setoid (Fin (n+p)),(k r:ℂ)*∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
        ∑ c∈distinctBox (s:=d+1) (h:=blockLength lam X) (fun _ => (1:ℤ)),
          (average X (fun m => divisorSum X F m (extraShifts b c)):ℂ)) =
        ∑ r : Setoid (Fin (n+p)),∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
          (k (Setoid.ker b):ℂ)*∑ c∈distinctBox (s:=d+1) (h:=blockLength lam X) (fun _ => (1:ℤ)),
          (average X (fun m => divisorSum X F m (extraShifts b c)):ℂ) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        rw [(mem_patternClass r b).mp hb]
      _ = _ := sum_patterns _
    apply Finset.sum_congr (by ext b; simp)
    intro b _
    rfl

end LargePrimeGaps

end OAI
