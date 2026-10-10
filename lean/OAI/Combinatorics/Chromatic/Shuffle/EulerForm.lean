import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.SymmetricSpace
import OAI.Combinatorics.Chromatic.GradedAlgebra.DegreeSet

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.Homogeneity
variable {I : Type*} [Fintype I] [DecidableEq I]

def eulerForm (a : I → I → ℕ) (d e : I → ℕ) : ℤ :=
  (∑ i,(d i:ℤ)*e i) - ∑ i, ∑ j,(a i j:ℤ)*d i*e j

lemma diagonal_homogeneous {σ : Type*} (i j : σ) :
    (diagonal i j : MvPolynomial σ ℚ).IsWeightedHomogeneous (fun _=>(1:ℤ)) 1 :=
  (isWeightedHomogeneous_X ℚ (fun _=>(1:ℤ)) j).sub
    (isWeightedHomogeneous_X ℚ (fun _=>(1:ℤ)) i)

omit [Fintype I] [DecidableEq I] in
lemma cutFactor_homogeneous {d e : I → ℕ} (A : Cut d e) (i j : I) (k : ℕ) :
    (cutFactor A i j k).IsWeightedHomogeneous (fun _=>(1:ℤ)) ((d i:ℤ)*e j*k) := by
  classical
  unfold cutFactor
  have h := IsWeightedHomogeneous.prod (A i).val _ _ (fun x _=>
    IsWeightedHomogeneous.prod (A j).valᶜ _ _
      (fun y _=> (diagonal_homogeneous (⟨i,x⟩ : Σi,Fin (d i+e i)) ⟨j,y⟩).pow k))
  convert h using 1
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,(A i).property,right_card]
  ring

omit [DecidableEq I] in
lemma cutDenominator_homogeneous {d e : I → ℕ} (A : Cut d e) :
    (cutDenominator A).IsWeightedHomogeneous (fun _=>(1:ℤ)) (∑ i,(d i:ℤ)*e i) := by
  unfold cutDenominator
  simpa only [Nat.cast_one,mul_one] using IsWeightedHomogeneous.prod Finset.univ _ _
    (fun i _=> cutFactor_homogeneous A i i 1)

omit [DecidableEq I] in
lemma cutNumerator_homogeneous (a : I → I → ℕ) {d e : I → ℕ} (A : Cut d e)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (g : MvPolynomial (Σi,Fin (e i)) ℚ)
    {m n : ℤ} (hf : f.IsWeightedHomogeneous (fun _=>(1:ℤ)) m)
    (hg : g.IsWeightedHomogeneous (fun _=>(1:ℤ)) n) :
    (cutNumerator a A f g).IsWeightedHomogeneous (fun _=>(1:ℤ))
      (m+n+ ∑ i, ∑ j,(a i j:ℤ)*d i*e j) := by
  unfold cutNumerator
  have h := (constantWeight_rename (leftInput A) f hf).mul
    (constantWeight_rename (rightInput A) g hg)
  have hk := IsWeightedHomogeneous.prod Finset.univ _ _ (fun i _=>
    IsWeightedHomogeneous.prod Finset.univ _ _
      (fun j _=> cutFactor_homogeneous A i j (a i j)))
  have heq : (∑ i, ∑ j,(d i:ℤ)*e j*a i j) =
      ∑ i, ∑ j,(a i j:ℤ)*d i*e j := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq] at hk
  exact h.mul hk

omit [DecidableEq I] in
lemma naturalVandermonde_homogeneous (d : I → ℕ) :
    (naturalVandermonde d (fun _=>True)).IsWeightedHomogeneous (fun _=>(1:ℤ))
      (naturalPairs d (fun _=>True)).card := by
  classical
  rw [naturalVandermonde_product]
  simpa using IsWeightedHomogeneous.prod (naturalPairs d (fun _=>True)) _ _
    (fun p _=> diagonal_homogeneous (finPackPair d p).1 (finPackPair d p).2)

theorem shufflePolynomial_homogeneous (a : I → I → ℕ) {d e : I → ℕ}
    (f : S d) (g : S e) {m n : ℤ}
    (hf : f.val.IsWeightedHomogeneous (fun _=>(1:ℤ)) m)
    (hg : g.val.IsWeightedHomogeneous (fun _=>(1:ℤ)) n) :
    (shufflePolynomial a f g).val.IsWeightedHomogeneous (fun _=>(1:ℤ))
      (m+n-eulerForm a d e) := by
  classical
  let V := naturalVandermonde (d+e) (fun _=>True)
  let v : ℤ := (naturalPairs (d+e) (fun _=>True)).card
  have hV : V.IsWeightedHomogeneous (fun _=>(1:ℤ)) v := naturalVandermonde_homogeneous _
  have hV0 : V≠0 := naturalVandermonde_ne_zero _ _
  have hb : ∀ A : Cut d e, ∃ b, V = cutDenominator A * b := fun A=> cutDenominator_dvd A
  choose b hb using hb
  have hbhome (A : Cut d e) : (b A).IsWeightedHomogeneous (fun _=>(1:ℤ))
      (v- ∑ i,(d i:ℤ)*e i) :=
    Homogeneity.of_mul (cutDenominator A) (b A) (cutDenominator_homogeneous A)
      (cutDenominator_ne_zero A) (by rw [← hb]; exact hV)
  have hclear : V*(shufflePolynomial a f g).val = ∑ A : Cut d e,b A*cutNumerator a A f.val g.val := by
    apply IsFractionRing.injective _ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))
    rw [map_mul,shufflePolynomial_eq,rawShuffle,Finset.mul_sum,map_sum]
    apply Finset.sum_congr rfl
    intro A hA
    rw [hb A,map_mul,map_mul]
    have hden : algebraMap _ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))
        (cutDenominator A) ≠ 0 :=
      by
        intro hz
        apply cutDenominator_ne_zero A
        exact (IsFractionRing.injective (MvPolynomial (Σi,Fin (d i+e i)) ℚ)
          (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))) (by simpa only [map_zero] using hz)
    let φ := algebraMap (MvPolynomial (Σi,Fin (d i+e i)) ℚ)
      (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))
    change (φ (cutDenominator A) * φ (b A)) *
      (φ (cutNumerator a A f.val g.val) / φ (cutDenominator A)) =
      φ (b A) * φ (cutNumerator a A f.val g.val)
    change φ (cutDenominator A) ≠ 0 at hden
    field_simp
  have hhom : (V*(shufflePolynomial a f g).val).IsWeightedHomogeneous
      (fun _=>(1:ℤ)) (v+(m+n-eulerForm a d e)) := by
    rw [hclear]
    apply IsWeightedHomogeneous.sum
    intro A hA
    convert (hbhome A).mul (cutNumerator_homogeneous a A f.val g.val hf hg) using 1
    simp only [eulerForm]
    ring
  have hh := Homogeneity.of_mul V (shufflePolynomial a f g).val hV hV0 hhom
  simpa only [add_sub_cancel_left] using hh

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.Homogeneity
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def componentS (d : I → ℕ) (k : ℤ) : S d →ₗ[ℚ] S d where
  toFun f := ⟨weightedHomogeneousComponent (fun _=>(1:ℤ)) k f.val, by
    intro σ
    rw [constantWeight_component_rename,f.property σ]⟩
  map_add' f g := Subtype.ext (map_add _ _ _)
  map_smul' r f := Subtype.ext (map_smul _ _ _)

omit [Fintype I] [DecidableEq I] in
@[simp] lemma componentS_val (d : I → ℕ) (k : ℤ) (f : S d) :
    (componentS d k f).val = weightedHomogeneousComponent (fun _=>(1:ℤ)) k f.val := rfl

omit [Fintype I] [DecidableEq I] in
lemma componentS_homogeneous (d : I → ℕ) (k : ℤ) (f : S d) :
    (componentS d k f).val.IsWeightedHomogeneous (fun _=>(1:ℤ)) k :=
  weightedHomogeneousComponent_isWeightedHomogeneous _ _

omit [Fintype I] [DecidableEq I] in
lemma sum_componentS (d : I → ℕ) (f : S d) :
    ∑ k ∈ degreeSet f.val,componentS d k f = f := by
  apply Subtype.ext
  change (symmetricSpace d).val (∑ k ∈ degreeSet f.val,componentS d k f) = f.val
  rw [map_sum]
  exact sum_components f.val

omit [Fintype I] [DecidableEq I] in
lemma componentS_of_homogeneous (d : I → ℕ) (f : S d) {m : ℤ}
    (hf : f.val.IsWeightedHomogeneous (fun _=>(1:ℤ)) m) (k : ℤ) :
    componentS d k f = if k=m then f else 0 := by
  classical
  apply Subtype.ext
  change weightedHomogeneousComponent (fun _=>(1:ℤ)) k f.val = _
  rw [weightedHomogeneousComponent_of_mem hf]
  split_ifs <;> rfl

omit [Fintype I] [DecidableEq I] in
lemma componentS_dimensionCast {d e : I → ℕ} (h : d=e) (k : ℤ) (f : S d) :
    componentS e k (dimensionCast h f) = dimensionCast h (componentS d k f) := by
  subst e
  rfl

omit [Fintype I] [DecidableEq I] in
lemma homogeneous_dimensionCast {d e : I → ℕ} (h : d=e) (f : S d) {k : ℤ}
    (hf : f.val.IsWeightedHomogeneous (fun _=>(1:ℤ)) k) :
    (dimensionCast h f).val.IsWeightedHomogeneous (fun _=>(1:ℤ)) k := by
  subst e
  exact hf

lemma shuffleLinear_apply (a : I → I → ℕ) (d e : I → ℕ) (f : S d) (g : S e) :
    shuffleLinear a d e f g = shufflePolynomial a f g := rfl

lemma shuffle_sum_components (a : I → I → ℕ) {d e : I → ℕ} (f : S d) (g : S e) :
    shufflePolynomial a f g =
    ∑ k ∈ degreeSet f.val, ∑ l ∈ degreeSet g.val,
      shufflePolynomial a (componentS d k f) (componentS e l g) := by
  change shuffleLinear a d e f g = _
  conv_lhs => rw [← sum_componentS d f,← sum_componentS e g]
  simp only [map_sum,LinearMap.sum_apply,shuffleLinear_apply]
  rw [Finset.sum_comm]

theorem componentS_destabilizing_mem (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (k : ℤ) (f : S d) (hf : f ∈ destabilizingSpace a μ d) :
    componentS d k f ∈ destabilizingSpace a μ d := by
  classical
  apply Submodule.span_induction (p:=fun x _=> componentS d k x ∈ destabilizingSpace a μ d)
    ?_ ?_ ?_ ?_ hf
  · intro F hF
    obtain ⟨u,v,h,f,g,hu,hv,hμ,rfl⟩ := hF
    rw [shuffle_sum_components a f g,map_sum,map_sum]
    apply Submodule.sum_mem
    intro i hi
    rw [map_sum,map_sum]
    apply Submodule.sum_mem
    intro j hj
    have hhom := homogeneous_dimensionCast h
      (shufflePolynomial a (componentS u i f) (componentS v j g))
      (shufflePolynomial_homogeneous a _ _ (componentS_homogeneous u i f)
        (componentS_homogeneous v j g))
    rw [componentS_of_homogeneous _ _ hhom]
    split_ifs
    · apply Submodule.subset_span
      exact ⟨u,v,h,componentS u i f,componentS v j g,hu,hv,hμ,rfl⟩
    · exact Submodule.zero_mem _
  · simp
  · intro x y hx hy hxc hyc
    simpa only [map_add] using (destabilizingSpace a μ d).add_mem hxc hyc
  · intro r x hx hxc
    simpa only [map_smul] using (destabilizingSpace a μ d).smul_mem r hxc

end ElementaryPositivity.RawShuffle

end

end OAI
