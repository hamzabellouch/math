import OAI.NumberTheory.PowerFree.IntegerPatches

namespace OAI

universe u

open scoped BigOperators
open Matrix
open scoped BigOperators

namespace QuarticPowerFree
open MvPolynomial

def kernelDegreeBudget (D : ℕ) : ℕ → ℕ → ℕ
  | 0, e => e
  | h+1, e => max e (kernelDegreeBudget D h (D*e))

def kernelCountBudget (D : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | h+1, e => 1+(D*e)*kernelCountBudget D h (D*e)

theorem le_kernelDegreeBudget (D h e : ℕ) : e ≤ kernelDegreeBudget D h e := by
  cases h with
  | zero => exact le_rfl
  | succ h => exact Nat.le_max_left _ _

theorem one_le_kernelCountBudget (D h e : ℕ) : 1 ≤ kernelCountBudget D h e := by
  cases h <;> simp only [kernelCountBudget] <;> omega

theorem bounded_kernel_components {n D : ℕ} {K : Type u} [Field K]
    (F : Set (MvPolynomial (Fin n) K))
    (hF : ∀ p ∈ F, p.totalDegree ≤ D) (h e : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hd : affineDimension I ≤ h) (he : affineDegree I ≤ e) :
    ∃ L : List (Ideal (MvPolynomial (Fin n) K)),
      L.length ≤ kernelCountBudget D h e ∧
      (∀ J ∈ L, J.IsPrime ∧ I ≤ J ∧ affineDimension J ≤ affineDimension I ∧
        affineDegree J ≤ kernelDegreeBudget D h e ∧ F ⊆ J ∧
        (¬ F ⊆ I → affineDimension J < affineDimension I)) ∧
      (∀ z : Fin n → K, (∀ p ∈ I, eval z p = 0) →
        (∀ p ∈ F, eval z p = 0) → ∃ J ∈ L, ∀ p ∈ J, eval z p = 0) := by
  classical
  induction h generalizing e I with
  | zero =>
    by_cases hFI : F ⊆ I
    · refine ⟨[I],le_rfl,?_,?_⟩
      · intro J hJ
        have hj : J = I := by simpa using hJ
        subst J
        exact ⟨inferInstance,le_rfl,le_rfl,he,hFI,fun hn => (hn hFI).elim⟩
      · intro z hz _
        exact ⟨I,by simp,hz⟩
    · refine ⟨[],by simp [kernelCountBudget],by simp,?_⟩
      intro z hz hFz
      exfalso
      apply hFI
      rw [zeroDim_eq_point I (Nat.eq_zero_of_le_zero hd) z hz]
      exact hFz
  | succ h ih =>
    by_cases hFI : F ⊆ I
    · refine ⟨[I],one_le_kernelCountBudget D (h+1) e,?_,?_⟩
      · intro J hJ
        have hj : J = I := by simpa using hJ
        subst J
        refine ⟨inferInstance,le_rfl,le_rfl,?_,hFI,fun hn => (hn hFI).elim⟩
        exact he.trans (by exact_mod_cast le_kernelDegreeBudget D (h+1) e)
      · intro z hz _
        exact ⟨I,by simp,hz⟩
    by_cases hd0 : affineDimension I = 0
    · refine ⟨[],by simp,by simp,?_⟩
      intro z hz hFz
      exfalso
      apply hFI
      rw [zeroDim_eq_point I hd0 z hz]
      exact hFz
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hd0
    have hkh : k ≤ h := by omega
    obtain ⟨p,hpF,hpI⟩ : ∃ p ∈ F, p ∉ I := by
      exact Set.not_subset.mp hFI
    obtain ⟨Q,hQcard,hQ,hQcov⟩ := bounded_cut_components I he p hpI (hF p hpF) hk
    have hc : ∀ q : Q, ∃ L : List (Ideal (MvPolynomial (Fin n) K)),
        L.length ≤ kernelCountBudget D h (D*e) ∧
        (∀ J ∈ L, J.IsPrime ∧ q.val ≤ J ∧ affineDimension J ≤ affineDimension q.val ∧
          affineDegree J ≤ kernelDegreeBudget D h (D*e) ∧ F ⊆ J ∧
          (¬ F ⊆ q.val → affineDimension J < affineDimension q.val)) ∧
        (∀ z : Fin n → K, (∀ p ∈ q.val, eval z p = 0) →
          (∀ p ∈ F, eval z p = 0) → ∃ J ∈ L, ∀ p ∈ J, eval z p = 0) := by
      intro q
      obtain ⟨hprime,_,hdq,heq⟩ := hQ q.val q.property
      let := hprime
      exact ih (D*e) q.val (hdq.le.trans hkh) (by simpa only [Nat.cast_mul] using heq)
    choose L hlen hgood hcover using hc
    let R := Q.attach.toList.flatMap L
    refine ⟨R,?_,?_,?_⟩
    · have hh : R.length ≤ Q.card * kernelCountBudget D h (D*e) := by
        simpa only [R,Finset.length_toList,Finset.card_attach] using
          list_flatMap_length_le Q.attach.toList L (kernelCountBudget D h (D*e))
            (fun q _ => hlen q)
      exact (hh.trans (Nat.mul_le_mul_right _ hQcard)).trans
        (Nat.le_add_left _ _)
    · intro J hJ
      obtain ⟨q,_,hJL⟩ := List.mem_flatMap.mp hJ
      obtain ⟨hpJ,hqJ,hdJ,heJ,hFJ,_⟩ := hgood q J hJL
      have hend : affineDimension J < affineDimension I := by
        have hdq := (hQ q.val q.property).2.2.1
        omega
      refine ⟨hpJ,(hQ q.val q.property).2.1.trans hqJ,hend.le,?_,hFJ,fun _ => hend⟩
      exact heJ.trans (by exact_mod_cast Nat.le_max_right e (kernelDegreeBudget D h (D*e)))
    · intro z hz hFz
      obtain ⟨q,hq,hzq⟩ := hQcov z hz (hFz p hpF)
      obtain ⟨J,hJL,hzJ⟩ := hcover ⟨q,hq⟩ z hzq hFz
      exact ⟨J,List.mem_flatMap.mpr ⟨⟨q,hq⟩,by simp,hJL⟩,hzJ⟩

theorem affineDimension_antitone {n : ℕ} {K : Type u} [Field K]
    (I J : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] [J.IsPrime]
    (hIJ : I ≤ J) : affineDimension J ≤ affineDimension I := by
  have ht := trdeg_le_of_surjective (Ideal.Quotient.factorₐ K hIJ)
    (Ideal.Quotient.factor_surjective hIJ)
  rw [← hilbert_natDegree_eq_trdeg I (coordinateHilbert I) (coordinateHilbert_eventually I),
    ← hilbert_natDegree_eq_trdeg J (coordinateHilbert J) (coordinateHilbert_eventually J)] at ht
  exact_mod_cast ht

theorem bounded_kernel_patch_cover {n D A h e : ℕ} {K : Type u} [Field K] [CharZero K]
    (F : Set (MvPolynomial (Fin n) K)) (hF : ∀ p ∈ F, p.totalDegree ≤ D)
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hd : affineDimension I ≤ h) (he : affineDegree I ≤ e)
    (S : Finset (Fin n → ℤ)) (H : ℝ) (hH : 1 ≤ H)
    (hz : ∀ z ∈ S, ∀ l, |(z l : ℝ)| ≤ H) :
    ∃ L : List (Ideal (MvPolynomial (Fin n) K) × IntegerPatch n),
      L.length ≤ kernelCountBudget D h e * patchCountBudget n A h (kernelDegreeBudget D h e) ∧
      (∀ C ∈ L,
        GoodPatchPiece I S A h (patchDegreeBudget n A h (kernelDegreeBudget D h e)) H C ∧
        F ⊆ C.1 ∧ affineDimension C.1 ≤ affineDimension I ∧
        (¬ F ⊆ I → affineDimension C.1 < affineDimension I)) ∧
      ∀ z ∈ S, PointOn I z → (∀ p ∈ F, eval (fun l => (z l : K)) p = 0) →
        ∃ C ∈ L, PatchPieceCovers C z := by
  classical
  obtain ⟨Q,hQlen,hQ,hQcov⟩ := bounded_kernel_components F hF h e I hd he
  let S' := fun q : {q // q ∈ Q} => S.filter (PointOn q.val)
  have hc : ∀ q : {q // q ∈ Q}, ∃ L : List (Ideal (MvPolynomial (Fin n) K) × IntegerPatch n),
      L.length ≤ patchCountBudget n A h (kernelDegreeBudget D h e) ∧
      (∀ C ∈ L, GoodPatchPiece q.val (S' q) A h
        (patchDegreeBudget n A h (kernelDegreeBudget D h e)) H C) ∧
      ∀ z ∈ S' q, ∃ C ∈ L, PatchPieceCovers C z := by
    intro q
    obtain ⟨hprime,_,hdq,heq,_⟩ := hQ q.val q.property
    let := hprime
    apply bounded_integer_patch_cover A h (kernelDegreeBudget D h e) q.val (hdq.trans hd) heq
      (S' q)
    · intro z hz; exact (Finset.mem_filter.mp hz).2
    · exact hH
    · intro z hzs; exact hz z (Finset.mem_filter.mp hzs).1
  choose L hlen hgood hcover using hc
  let R := Q.attach.flatMap L
  refine ⟨R,?_,?_,?_⟩
  · have hh : R.length ≤ Q.length * patchCountBudget n A h (kernelDegreeBudget D h e) := by
      simpa only [R,List.length_attach] using list_flatMap_length_le Q.attach L
        (patchCountBudget n A h (kernelDegreeBudget D h e)) (fun q _ => hlen q)
    exact hh.trans (Nat.mul_le_mul_right _ hQlen)
  · intro C hC
    obtain ⟨q,_,hCL⟩ := List.mem_flatMap.mp hC
    obtain ⟨hpq,hIq,hdq,heq,hFq,hstrict⟩ := hQ q.val q.property
    obtain ⟨hpC,hqC,hdC,heC,hOn,hBound,hLock⟩ := hgood q C hCL
    let := hpq
    let := hpC
    have hdim := affineDimension_antitone q.val C.1 hqC
    refine ⟨⟨hpC,hIq.trans hqC,hdC,heC,hOn,hBound,hLock.of_filter hqC S⟩,
      hFq.trans hqC,hdim.trans hdq,?_⟩
    exact fun hn => hdim.trans_lt (hstrict hn)
  · intro z hz hIz hFz
    obtain ⟨q,hq,hzq⟩ := hQcov (fun l => (z l : K)) hIz hFz
    obtain ⟨C,hCL,hCz⟩ := hcover ⟨q,hq⟩ z (Finset.mem_filter.mpr ⟨hz,hzq⟩)
    refine ⟨C,List.mem_flatMap.mpr ⟨⟨q,hq⟩,?_,hCL⟩,hCz⟩
    exact List.mem_attach Q ⟨q,hq⟩

noncomputable def stagedEvaluationSpace {n : ℕ} (S : Finset (Fin n → ℤ)) (d E : ℕ) :
    Submodule ℂ (totalSpace (σ := Fin n) (K := ℂ) E) :=
  (totalSpace d).comap (totalSpace E).subtype ⊓ evaluationSpace S E

def stagedKernelPolynomials {n : ℕ} (d E : ℕ)
    (W : Submodule ℂ (totalSpace (σ := Fin n) (K := ℂ) E)) :
    Set (MvPolynomial (Fin n) ℂ) :=
  {p | ∃ v ∈ W, (v : MvPolynomial (Fin n) ℂ) = p ∧ p.totalDegree ≤ d}

theorem stagedKernelPolynomials_degree {n d E : ℕ}
    (W : Submodule ℂ (totalSpace (σ := Fin n) (K := ℂ) E))
    (p : MvPolynomial (Fin n) ℂ) (hp : p ∈ stagedKernelPolynomials d E W) :
    p.totalDegree ≤ d := hp.choose_spec.2.2

theorem stagedEvaluationSpace_mono {n d E : ℕ} {S T : Finset (Fin n → ℤ)}
    (hST : S ⊆ T) : stagedEvaluationSpace T d E ≤ stagedEvaluationSpace S d E :=
  inf_le_inf le_rfl (evaluationSpace_antitone hST)

theorem mem_stagedKernelPolynomials {n d E : ℕ} (hdE : d ≤ E)
    (S : Finset (Fin n → ℤ)) (p : MvPolynomial (Fin n) ℂ) :
    p ∈ stagedKernelPolynomials d E (stagedEvaluationSpace S d E) ↔
      p.totalDegree ≤ d ∧ ∀ z ∈ S, eval (fun l => (z l : ℂ)) p = 0 := by
  constructor
  · rintro ⟨v,hv,rfl,hdeg⟩
    exact ⟨hdeg,hv.2⟩
  · rintro ⟨hdeg,hz⟩
    refine ⟨⟨p,mem_totalSpace.mpr (hdeg.trans hdE)⟩,?_,rfl,hdeg⟩
    exact ⟨mem_totalSpace.mpr hdeg,hz⟩

structure KernelGeometry (n : ℕ) where
  points : Finset (Fin n → ℤ)
  height : ℝ
  one_le_height : 1 ≤ height
  bounded : ∀ z ∈ points, ∀ l, |(z l : ℝ)| ≤ height

def KernelParent {n : ℕ} (h e : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) : Prop :=
  I.IsPrime ∧ affineDimension I ≤ h ∧ affineDegree I ≤ e

noncomputable def kernelChildList {n E : ℕ} (G : KernelGeometry n) (d A h e : ℕ)
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    (W : Submodule ℂ (totalSpace (σ := Fin n) (K := ℂ) E)) :
    List (Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n) := by
  classical
  exact if hi : KernelParent h e I then
    letI := hi.1
    (bounded_kernel_patch_cover (A := A) (stagedKernelPolynomials d E W)
      (stagedKernelPolynomials_degree W) I hi.2.1 hi.2.2 G.points G.height
      G.one_le_height G.bounded).choose
  else []

theorem kernelChildList_spec {n E : ℕ} (G : KernelGeometry n) (d A h e : ℕ)
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    (W : Submodule ℂ (totalSpace (σ := Fin n) (K := ℂ) E))
    (hi : KernelParent h e I) :
    (kernelChildList G d A h e I W).length ≤
      kernelCountBudget d h e * patchCountBudget n A h (kernelDegreeBudget d h e) ∧
    (∀ C ∈ kernelChildList G d A h e I W,
      GoodPatchPiece I G.points A h (patchDegreeBudget n A h (kernelDegreeBudget d h e)) G.height C ∧
      stagedKernelPolynomials d E W ⊆ C.1 ∧ affineDimension C.1 ≤ affineDimension I ∧
      (¬ stagedKernelPolynomials d E W ⊆ I → affineDimension C.1 < affineDimension I)) ∧
    ∀ z ∈ G.points, PointOn I z →
      (∀ p ∈ stagedKernelPolynomials d E W, eval (fun l => (z l : ℂ)) p = 0) →
      ∃ C ∈ kernelChildList G d A h e I W, PatchPieceCovers C z := by
  classical
  let := hi.1
  simpa only [kernelChildList,dite_eq_left hi] using
    (bounded_kernel_patch_cover (A := A) (stagedKernelPolynomials d E W)
      (stagedKernelPolynomials_degree W) I hi.2.1 hi.2.2 G.points G.height
      G.one_le_height G.bounded).choose_spec

noncomputable def firstCoveringChild {n : ℕ} (z : Fin n → ℤ)
    (s : Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (L : List (Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)) :
    Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n := by
  classical
  exact (L.find? (fun C => decide (PatchPieceCovers C z))).getD s

theorem firstCoveringChild_spec {n : ℕ} (z : Fin n → ℤ)
    (s : Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (L : List (Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n))
    (hL : ∃ C ∈ L, PatchPieceCovers C z) :
    firstCoveringChild z s L ∈ L ∧ PatchPieceCovers (firstCoveringChild z s L) z := by
  classical
  simp only [firstCoveringChild]
  cases hh : L.find? (fun C => decide (PatchPieceCovers C z)) with
  | none =>
    obtain ⟨C,hC,hcov⟩ := hL
    have hc := List.find?_eq_none.mp hh C hC
    simp [hcov] at hc
  | some C =>
    simp only [Option.getD_some]
    have hc : decide (PatchPieceCovers C z) = true :=
      List.find?_some (p := fun C => decide (PatchPieceCovers C z)) hh
    exact ⟨List.mem_of_find?_eq_some hh,of_decide_eq_true hc⟩

open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def kernelHeightConstant (m : ℕ) : ℝ :=
  (1+(m:ℝ)^2) * m.factorial * (1+(m:ℝ))^m

theorem kernel_height_pow_bound (m d : ℕ) (H : ℝ) (hH : 1 ≤ H) :
    integralKernelHeight m (H^d) ≤ kernelHeightConstant m * H^(2*d*(m+1)) := by
  have hpow : 1 ≤ (H^d)^2 := one_le_pow₀ (one_le_pow₀ hH)
  have ha : 1+(m:ℝ)^2*(H^d)^2 ≤ (1+(m:ℝ)^2)*(H^d)^2 := by nlinarith
  have hb : 1+(m:ℝ)*(H^d)^2 ≤ (1+(m:ℝ))*(H^d)^2 := by nlinarith
  unfold integralKernelHeight
  calc
    (1+(m:ℝ)^2*(H^d)^2) * m.factorial * (1+(m:ℝ)*(H^d)^2)^m ≤
        ((1+(m:ℝ)^2)*(H^d)^2) * m.factorial * (((1+(m:ℝ))*(H^d)^2)^m) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _)
      · exact pow_le_pow_left₀ (by positivity) hb _
      · positivity
      · positivity
    _ = kernelHeightConstant m * H^(2*d*(m+1)) := by
      rw [kernelHeightConstant,show 2*d*(m+1) = d*2*(m+1) by ring]
      simp only [pow_mul,mul_pow,pow_succ]
      ring

def minorSizeConstant (n d m : ℕ) : ℝ :=
  m.factorial * ((((d+n).choose n : ℝ)*(d:ℝ)*kernelHeightConstant ((d+n).choose n))^m)

def minorSizeExponent (n d m : ℕ) : ℕ :=
  (2*d*((d+n).choose n+1)+d)*m

theorem minorSizeConstant_nonneg (n d m : ℕ) : 0 ≤ minorSizeConstant n d m := by
  unfold minorSizeConstant kernelHeightConstant
  positivity

theorem bounded_minor_height {n d : ℕ} {P : IntegerPatch n}
    (hdeg : ∀ i, (P.equations i).totalDegree ≤ d) (H : ℝ) (hH : 1 ≤ H)
    (hc : ∀ i a, |(((P.equations i).coeff a : ℤ) : ℝ)| ≤
      integralKernelHeight ((d+n).choose n) (H^d))
    (z : Fin n → ℤ) (hz : ∀ l, |(z l : ℝ)| ≤ H) :
    |((eval z P.minor : ℤ) : ℝ)| ≤
      minorSizeConstant n d (Fintype.card ↥(P.freeᶜ)) *
        H^(minorSizeExponent n d (Fintype.card ↥(P.freeᶜ))) := by
  let M := (d+n).choose n
  let m := Fintype.card ↥(P.freeᶜ)
  have hC : 0 ≤ integralKernelHeight M (H^d) := by unfold integralKernelHeight; positivity
  have hb := eval_jacobian_minor_abs_le P.equations Subtype.val d hdeg
    (integralKernelHeight M (H^d)) H hC hH hc z hz
  have hi : (M:ℝ)*((d:ℝ)*integralKernelHeight M (H^d))*H^d ≤
      ((M:ℝ)*(d:ℝ)*kernelHeightConstant M)*H^(2*d*(M+1)+d) := by
    calc
      _ ≤ (M:ℝ)*((d:ℝ)*(kernelHeightConstant M * H^(2*d*(M+1))))*H^d := by
        gcongr
        exact kernel_height_pow_bound M d H hH
      _ = _ := by rw [pow_add]; ring
  calc
    |((eval z P.minor : ℤ) : ℝ)| ≤ (m.factorial:ℝ)*
        ((M:ℝ)*((d:ℝ)*integralKernelHeight M (H^d))*H^d)^m := by
      simpa only [IntegerPatch.minor, m, M, Fintype.card_fin] using hb
    _ ≤ (m.factorial:ℝ)*(((M:ℝ)*(d:ℝ)*kernelHeightConstant M)*H^(2*d*(M+1)+d))^m := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply pow_le_pow_left₀ _ hi
      positivity
    _ = _ := by
      simp only [minorSizeConstant,minorSizeExponent,mul_pow,pow_mul,M,m]
      ring

theorem uniform_patch_minor_height (n D : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ B : ℕ, ∀ (P : IntegerPatch n) (H : ℝ),
      1 ≤ H → P.Bounded D H → ∀ z : Fin n → ℤ,
        (∀ l, |(z l : ℝ)| ≤ H) → |((eval z P.minor : ℤ) : ℝ)| ≤ C*H^B := by
  classical
  let C : ℝ := 1 + ∑ d ∈ Finset.range (D+1), ∑ m ∈ Finset.range (n+1), minorSizeConstant n d m
  let B : ℕ := ∑ d ∈ Finset.range (D+1), ∑ m ∈ Finset.range (n+1), minorSizeExponent n d m
  have hnonneg : ∀ d, 0 ≤ ∑ m ∈ Finset.range (n+1), minorSizeConstant n d m := fun d =>
    Finset.sum_nonneg (fun m _ => minorSizeConstant_nonneg n d m)
  have hsum : 0 ≤ ∑ d ∈ Finset.range (D+1), ∑ m ∈ Finset.range (n+1),
      minorSizeConstant n d m := Finset.sum_nonneg (fun d _ => hnonneg d)
  refine ⟨C, by dsimp [C]; linarith, B, ?_⟩
  intro P H hH hP z hz
  obtain ⟨d,hd,hdeg,hcoeff⟩ := hP
  let m := Fintype.card ↥(P.freeᶜ)
  have hm : m ≤ n := by
    simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun x : Fin n => x ∈ P.freeᶜ)
  have hdmem : d ∈ Finset.range (D+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hd)
  have hmmem : m ∈ Finset.range (n+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
  have hCs : minorSizeConstant n d m ≤ C := by
    have h₁ := Finset.single_le_sum (fun j _ => minorSizeConstant_nonneg n d j) hmmem
    have h₂ := Finset.single_le_sum (fun j _ => hnonneg j) hdmem
    dsimp [C]
    linarith
  have hBs : minorSizeExponent n d m ≤ B :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le (minorSizeExponent n d j)) hmmem).trans
      (Finset.single_le_sum (fun j _ => Nat.zero_le
        (∑ x ∈ Finset.range (n+1), minorSizeExponent n j x)) hdmem)
  exact (bounded_minor_height hdeg H hH hcoeff z hz).trans
    (mul_le_mul hCs (pow_le_pow_right₀ hH hBs) (by positivity) (by
      exact (minorSizeConstant_nonneg n d m).trans hCs))

end QuarticPowerFree

end OAI
