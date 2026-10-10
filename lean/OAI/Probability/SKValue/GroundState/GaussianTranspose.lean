import Mathlib
import OAI.Probability.SKValue.GroundState.QuadraticSK

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG

variable (κ ν : Type*) [Fintype κ] [Fintype ν]

def uncurryGaussian : (κ → ν → ℝ) ≃ᵐ ((κ×ν) → ℝ) where
  toFun f k := f k.1 k.2
  invFun f i j := f (i,j)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    change Measurable (fun f : κ → ν → ℝ ↦ fun k : κ×ν ↦ f k.1 k.2)
    fun_prop
  measurable_invFun := by
    change Measurable (fun f : (κ×ν) → ℝ ↦ fun i j ↦ f (i,j))
    fun_prop

lemma uncurryGaussian_preserving :
    MeasurePreserving (uncurryGaussian κ ν) (Measure.pi (fun _ : κ ↦ gaussianProduct ν))
      (gaussianProduct (κ×ν)) := by
  refine ⟨(uncurryGaussian κ ν).measurable,?_⟩
  apply Eq.symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (uncurryGaussian κ ν).measurable (MeasurableSet.univ_pi hs)]
  have he : (uncurryGaussian κ ν) ⁻¹' univ.pi s=
      univ.pi (fun i : κ ↦ univ.pi (fun j : ν ↦ s (i,j))) := by
    ext f
    simp only [mem_preimage,mem_univ_pi,uncurryGaussian,MeasurableEquiv.coe_mk]
    exact ⟨fun h i j ↦ h (i,j),fun h k ↦ h k.1 k.2⟩
  rw [he,Measure.pi_pi]
  simp only [gaussianProduct,Measure.pi_pi,Fintype.prod_prod_type]

def transposeGaussian : (κ → ν → ℝ) ≃ᵐ (ν → κ → ℝ) :=
  (uncurryGaussian κ ν).trans
    ((MeasurableEquiv.piCongrLeft (fun _ : ν×κ ↦ ℝ) (Equiv.prodComm κ ν)).trans
      (uncurryGaussian ν κ).symm)

omit [Fintype κ] [Fintype ν] in
lemma transposeGaussian_apply [Fintype κ] [Fintype ν] (f : κ → ν → ℝ) :
    transposeGaussian κ ν f=fun j i ↦ f i j := rfl

lemma transposeGaussian_preserving :
    MeasurePreserving (transposeGaussian κ ν) (Measure.pi (fun _ : κ ↦ gaussianProduct ν))
      (Measure.pi (fun _ : ν ↦ gaussianProduct κ)) := by
  exact (uncurryGaussian_preserving ν κ).symm.comp
    ((measurePreserving_piCongrLeft (fun _ : ν×κ ↦ standardGaussian) (Equiv.prodComm κ ν)).comp
      (uncurryGaussian_preserving κ ν))

lemma iid_gaussian_columns_law (K n : ℕ) :
    HasLaw (fun x : ℕ → (Fin K → ℝ) ↦ fun j : Fin K ↦ fun i : Fin n ↦ x i j)
      (columnHistoryLaw (Fin n) K)
      (Measure.infinitePi (fun _ : ℕ ↦ gaussianProduct (Fin K))) := by
  exact (transposeGaussian_preserving (Fin n) (Fin K)).hasLaw.comp
    (iid_prefix_law (gaussianProduct (Fin K)) n)

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG

lemma measurable_finite_eval {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (d : Ω → ι → ℝ) (hd : ∀ i,Measurable (fun x ↦ d x i)) (s : Ω → ι)
    (hs : Measurable s) : Measurable (fun x ↦ d x (s x)) := by
  classical
  have he : (fun x ↦ d x (s x))=fun x ↦ ∑ i : ι,if s x=i then d x i else 0 := by
    funext x
    simp
  rw [he]
  apply Finset.measurable_sum
  intro i hi
  exact (hd i).ite (hs (measurableSet_singleton i)) measurable_const

def rowSpin (K n : ℕ) (F : (Fin (K+1) → ℝ) → Bool)
    (h : ColumnHistory (Fin n) (K+1)) : Fin n → Bool :=
  fun i ↦ F (paddedRow K n h i)

lemma rowSpin_measurable (K n : ℕ) (F : (Fin (K+1) → ℝ) → Bool) (hF : Measurable F) :
    Measurable (rowSpin K n F) := by
  apply Measurable.of_eval
  intro i
  exact hF.comp (paddedRow_measurable K n (K+1) i)

lemma rowSpin_rows (K n : ℕ) (F : (Fin (K+1) → ℝ) → Bool)
    (x : ℕ → (Fin (K+1) → ℝ)) :
    rowSpin K n F (rowHistory K n (fun i ↦ x i) (K+1))=fun i : Fin n ↦ F (x i) := by
  funext i
  change F (paddedRow K n (rowHistory K n (fun i ↦ x i) (K+1)) i)=F (x i)
  apply congrArg F
  funext j
  simp [paddedRow,rowHistory,rowColumn,j.isLt]

lemma rowHistory_full (K n : ℕ) (x : ℕ → (Fin (K+1) → ℝ)) :
    rowHistory K n (fun i ↦ x i) (K+1)=fun j (i : Fin n) ↦ x i j := by
  funext j i
  simp [rowHistory,rowColumn,j.isLt]

theorem empirical_finite_spin_lower (K : ℕ)
    (f : ℕ → (Fin (K+1) → ℝ) → ℝ) (F : (Fin (K+1) → ℝ) → Bool)
    (hm : ∀ i,Measurable (f i))
    (ha : ∀ l x y,(∀ i : Fin (K+1),i.val≤l → x i=y i) → f l x=f l y)
    (hF : Measurable F) {n : ℕ} (hn : 0<n) :
    (∫ x,∑ j∈Finset.range K,empiricalColumnEnergy K n f x (fun y ↦ spin (F y)) j
      ∂Measure.infinitePi (fun _ : ℕ ↦ gaussianProduct (Fin (K+1))))≤groundStateSequence n := by
  let v := predictableDirection K n f
  let s := rowSpin K n F
  have hs : Measurable (fun h ↦ adaptiveOffset (spinVector n) v (K+1) h (s h)) :=
    measurable_finite_eval _
      (adaptiveOffset_measurable (spinVector n) v (predictableDirection_measurable K n f hm) (K+1))
      s (rowSpin_measurable K n F hF)
  have hb := finite_adaptive_SK_lower hn v (predictableDirection_measurable K n f hm)
    (predictableDirection_unitOrZero K n f) (K+1) s hs
  let d := fun h ↦ adaptiveOffset (spinVector n) v (K+1) h (s h)/
    ((n : ℝ)*Real.sqrt (n : ℝ))
  have hd : Measurable d := hs.div_const _
  have he := (iid_gaussian_columns_law (K+1) n).integral_comp hd.aestronglyMeasurable
  have heq : (fun x : ℕ → (Fin (K+1) → ℝ) ↦ d (fun j i ↦ x i j))=
      fun x ↦ ∑ j∈Finset.range K,empiricalColumnEnergy K n f x (fun y ↦ spin (F y)) j := by
    funext x
    dsimp [d,v,s]
    rw [←rowHistory_full K n x,rowSpin_rows K n F x]
    exact normalizedOffset_rows K n f ha x hn F
  dsimp only [Function.comp_def] at he
  rw [heq] at he
  rw [he]
  simpa only [d,integral_div] using hb

end SKValueG

end

end OAI
