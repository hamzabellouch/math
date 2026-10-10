import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.ExtendPolynomial
import OAI.Combinatorics.Chromatic.Shuffle.TaylorSCoeffHomogeneous

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

def interaction (a : I → I → ℕ) (d e : I → ℕ) : ℤ :=
  ∑ i,∑ j,(a i j:ℤ)*d i*e j

omit [DecidableEq I] in
lemma interaction_nonnegative (a : I → I → ℕ) (d e : I → ℕ) : 0 ≤ interaction a d e := by
  exact Finset.sum_nonneg (fun i _=>Finset.sum_nonneg (fun j _=>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)))

omit [DecidableEq I] in
lemma interaction_add (a : I → I → ℕ) (d e : I → ℕ) :
    interaction a (d+e) (d+e) = interaction a d d + interaction a d e +
      interaction a e d + interaction a e e := by
  simp only [interaction,Pi.add_apply,Nat.cast_add,mul_add,add_mul,Finset.sum_add_distrib]
  ring

omit [DecidableEq I] in
lemma eulerForm_lower (a : I → I → ℕ) (d : I → ℕ) : -interaction a d d≤eulerForm a d d := by
  have h : 0≤∑ i,(d i:ℤ)*d i := Finset.sum_nonneg (fun i _=>mul_self_nonneg _)
  change -interaction a d d≤(∑ i,(d i:ℤ)*d i)-interaction a d d
  omega

omit [DecidableEq I] in
lemma SplitTree.doubleShift_lower (a : I → I → ℕ) (T : SplitTree I) :
    -interaction a T.dim T.dim ≤ T.doubleShift a := by
  induction T with
  | leaf d => exact eulerForm_lower a d
  | node l r ihl ihr =>
    change -interaction a (l.dim+r.dim) (l.dim+r.dim)≤l.doubleShift a+r.doubleShift a
    rw [interaction_add]
    have h1 := interaction_nonnegative a l.dim r.dim
    have h2 := interaction_nonnegative a r.dim l.dim
    omega

noncomputable def dimensionEquivB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e : I → ℕ} (h : d=e) : B a μ d ≃ₐ[ℚ] B a μ e := by
  subst e
  exact AlgEquiv.refl

noncomputable def restrictionTest (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) {d : I → ℕ} (T : SplitTree I) (hs : T.OnSlope c η θ) (hd : T.dim=d)
    (k : T.Degrees) (z : T.Centers →₀ ℕ) :
    B a (SlopeArithmetic.slope c η) d →ₗ[ℚ]
      SplitTree.tensor (SplitTree.quotientFamily a (SlopeArithmetic.slope c η)) T :=
  (SplitTree.componentTensor a (SlopeArithmetic.slope c η) T k).comp
    (((MvPolynomial.lcoeff _ z).restrictScalars ℚ).comp
      ((SplitTree.centeredRestrictionB a c η hc θ T hs).toLinearMap.comp
        (dimensionEquivB a (SlopeArithmetic.slope c η) hd.symm).toLinearMap))

noncomputable def sourceFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) : Submodule ℚ (B a (SlopeArithmetic.slope c η) d) where
  carrier := {f | ∀ (T : SplitTree I), T.IsOrderedList → ∀ (hs : T.OnSlope c η θ)
    (hd : T.dim=d) (k : T.Degrees) (z : T.Centers →₀ ℕ),
    2*T.totalDegree k+T.doubleShift a<W → restrictionTest a c η hc θ T hs hd k z f=0}
  zero_mem' := by
    intro T hT hs hd k z hw
    exact (restrictionTest a c η hc θ T hs hd k z).map_zero
  add_mem' := by
    intro f g hf hg T hT hs hd k z hw
    rw [map_add,hf T hT hs hd k z hw,hg T hT hs hd k z hw,add_zero]
  smul_mem' := by
    intro r f hf T hT hs hd k z hw
    rw [map_smul,hf T hT hs hd k z hw,smul_zero]

lemma sourceFiltration_antitone (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) : Antitone (sourceFiltration a c η hc θ d) := by
  intro W V h f hf T hT hs hd k z hw
  exact hf T hT hs hd k z (lt_of_lt_of_le hw h)

theorem sourceFiltration_lower (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) :
    sourceFiltration a c η hc θ d (-interaction a d d)=⊤ := by
  classical
  apply top_unique
  intro f hf T hT hs hd k z hw
  have hn : ¬T.NonnegativeDegree k := by
    intro hh
    have ht := T.totalDegree_nonnegative k hh
    have hl := T.doubleShift_lower a
    rw [hd] at hl
    omega
  unfold restrictionTest
  rw [SplitTree.componentTensor_negative a _ T k hn]
  rfl

lemma coeff_zero_toMvPolynomial {R α : Type*} [CommRing R] (i : α) (p : Polynomial R) :
    (Polynomial.toMvPolynomial i p).coeff 0=p.coeff 0 := by
  change MvPolynomial.constantCoeff (Polynomial.toMvPolynomial i p)=p.coeff 0
  rw [← MvPolynomial.eval_zero']
  have h := RingHom.congr_fun (MvPolynomial.eval_comp_toMvPolynomial (fun _ : α=> (0:R)) i) p
  simpa [Polynomial.coeff_zero_eq_eval_zero] using h

lemma restrictionTest_leaf_zero (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (hs : (SplitTree.leaf d).OnSlope c η θ)
    (k : ℤ) (f : B a (SlopeArithmetic.slope c η) d) :
    restrictionTest a c η hc θ (.leaf d) hs rfl k 0 f = componentB a (SlopeArithmetic.slope c η) d k f := by
  change componentB a (SlopeArithmetic.slope c η) d k
    ((Polynomial.toMvPolynomial () (taylorB a (SlopeArithmetic.slope c η) d f)).coeff 0) = _
  rw [coeff_zero_toMvPolynomial,taylorB_coeff_zero]

theorem sourceFiltration_upper (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (hd : d≠0) (hθ : SlopeArithmetic.slope c η d=θ)
    (k W : ℤ) (hw : 2*k+eulerForm a d d<W) :
    gradeB a (SlopeArithmetic.slope c η) d k ⊓ sourceFiltration a c η hc θ d W=⊥ := by
  apply bot_unique
  intro f hf
  obtain ⟨hf,hg⟩ := hf
  have h := hg (.leaf d) trivial ⟨hd,hθ⟩ rfl k 0 hw
  rw [restrictionTest_leaf_zero,(mem_gradeB_iff a _ d k f).mp hf] at h
  exact h

theorem leading_restrictions_detect (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (f : B a (SlopeArithmetic.slope c η) d)
    (hf : f∈sourceFiltration a c η hc θ d W)
    (h : ∀ (T : SplitTree I), T.IsOrderedList → ∀ (hs : T.OnSlope c η θ)
      (hd : T.dim=d) (k : T.Degrees) (z : T.Centers →₀ ℕ),
      2*T.totalDegree k+T.doubleShift a=W → restrictionTest a c η hc θ T hs hd k z f=0) :
    f∈sourceFiltration a c η hc θ d (W+1) := by
  intro T hT hs hd k z hw
  by_cases he : 2*T.totalDegree k+T.doubleShift a=W
  · exact h T hT hs hd k z he
  · exact hf T hT hs hd k z (by omega)

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.Homogeneity ElementaryPositivity.SeparatedSymmetry ElementaryPositivity.ShufflePolynomiality
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma reynoldsS_homogeneous (d : I → ℕ) (p : MvPolynomial (Σi,Fin (d i)) ℚ)
    (k : ℤ) (hp : p.IsWeightedHomogeneous (fun _=>(1:ℤ)) k) :
    (reynoldsS d p).val.IsWeightedHomogeneous (fun _=>(1:ℤ)) k := by
  change (average (packAction (fun i=>Fin (d i))) p).IsWeightedHomogeneous _ _
  rw [average_apply]
  apply (weightedHomogeneousSubmodule ℚ (fun _=>(1:ℤ)) k).smul_mem
  exact IsWeightedHomogeneous.sum _ _ _ (fun σ _=>constantWeight_rename _ _ hp)

lemma separateTensor_product_any (d e : I → ℕ)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (g : MvPolynomial (Σi,Fin (e i)) ℚ) :
    separateTensor d e (rename Sum.inl f * rename Sum.inr g) = reynoldsS d f ⊗ₜ[ℚ] reynoldsS e g := by
  rw [← tensorEquivSum_tmul]
  simp [separateTensor]

lemma monomial_sumElim {α β : Type*} (x : α →₀ ℕ) (y : β →₀ ℕ) (c : ℚ) :
    monomial (x.sumElim y) c = rename Sum.inl (monomial x c) * rename Sum.inr (monomial y (1:ℚ)) := by
  rw [rename_monomial,rename_monomial,monomial_mul_monomial,mul_one,Finsupp.sumElim_eq_add]

lemma totalWeight_sumElim {α β : Type*} (x : α →₀ ℕ) (y : β →₀ ℕ) :
    Finsupp.weight (fun _=>(1:ℤ)) (x.sumElim y) =
      Finsupp.weight (fun _=>(1:ℤ)) x + Finsupp.weight (fun _=>(1:ℤ)) y := by
  simp only [Finsupp.weight_apply,Finsupp.sum_sumElim,Function.comp_def]

lemma component_separateTensor_homogeneous (d e : I → ℕ)
    (f : MvPolynomial ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i))) ℚ) (k : ℤ)
    (hf : f.IsWeightedHomogeneous (fun _=>(1:ℤ)) k) (m n : ℤ) (h : m+n≠k) :
    TensorProduct.map (componentS d m) (componentS e n) (separateTensor d e f)=0 := by
  classical
  rw [← f.support_sum_monomial_coeff,map_sum,map_sum]
  apply Finset.sum_eq_zero
  intro u hu
  let x := Finsupp.comapDomain Sum.inl u (Set.injOn_of_injective Sum.inl_injective)
  let y := Finsupp.comapDomain Sum.inr u (Set.injOn_of_injective Sum.inr_injective)
  have hxy : x.sumElim y=u := Finsupp.comapDomain_sumElim_comapDomain u
  have hw : Finsupp.weight (fun _=>(1:ℤ)) x + Finsupp.weight (fun _=>(1:ℤ)) y=k := by
    rw [← totalWeight_sumElim,hxy]
    exact hf (mem_support_iff.mp hu)
  rw [← hxy,monomial_sumElim,separateTensor_product_any,TensorProduct.map_tmul,
    componentS_of_homogeneous _ _ (reynoldsS_homogeneous _ _ _ (isWeightedHomogeneous_monomial _ _ _ rfl)),
    componentS_of_homogeneous _ _ (reynoldsS_homogeneous _ _ _ (isWeightedHomogeneous_monomial _ _ _ rfl))]
  split_ifs with hm hn <;> simp_all

lemma component_restrictTensor_homogeneous {d e : I → ℕ} (A : Cut d e)
    (f : S (d+e)) (k : ℤ) (hf : f.val.IsWeightedHomogeneous (fun _=>(1:ℤ)) k)
    (m n : ℤ) (h : m+n≠k) :
    TensorProduct.map (componentS d m) (componentS e n) (restrictTensor A f)=0 := by
  exact component_separateTensor_homogeneous d e _ k (constantWeight_rename _ _ hf) m n h

lemma component_quotientTensor (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d e : I → ℕ) (m n : ℤ) (f : S d ⊗[ℚ] S e) :
    TensorProduct.map (componentB a μ d m) (componentB a μ e n) (quotientTensor a μ d e f)=
      quotientTensor a μ d e (TensorProduct.map (componentS d m) (componentS e n) f) := by
  induction f using TensorProduct.inductionOn with
  | tmul f g => rfl
  | add f g hf hg => simp [hf,hg]

theorem restrictionB_graded (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (A : Cut d e) (f : B a (SlopeArithmetic.slope c η) (d+e))
    (k : ℤ) (hf : f∈gradeB a (SlopeArithmetic.slope c η) (d+e) k)
    (m n : ℤ) (h : m+n≠k) :
    TensorProduct.map (componentB a (SlopeArithmetic.slope c η) d m)
      (componentB a (SlopeArithmetic.slope c η) e n) (restrictionB a c η hc hs A f)=0 := by
  obtain ⟨g,hg,rfl⟩ := gradeB_homogeneous_representative a _ (d+e) k f hf
  change TensorProduct.map _ _ (restrictionB a c η hc hs A (quotientAlg a _ (d+e) g))=0
  rw [restrictionB_mk,component_quotientTensor,component_restrictTensor_homogeneous A g k hg m n h,map_zero]

end ElementaryPositivity.RawShuffle

end

end OAI
