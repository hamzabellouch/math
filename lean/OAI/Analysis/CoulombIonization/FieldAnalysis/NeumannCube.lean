import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.CubeTranslationAverage

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_NeumannCube_scope

open MeasureTheory Set Submodule
open scoped BigOperators unitInterval ComplexConjugate

lemma cosMode_natAbs (k : ℤ) (x : I) :
    cosMode k.natAbs x = Real.cos (Real.pi*(k:ℝ)*(x:ℝ)) := by
  have hk : (k.natAbs:ℝ) = |(k:ℝ)| := by
    rw [← Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
  dsimp [cosMode]
  rw [hk]
  have he : Real.pi*|(k:ℝ)| * (x:ℝ) = |Real.pi*(k:ℝ)*(x:ℝ)| := by
    rw [abs_mul,abs_mul,abs_of_nonneg Real.pi_pos.le,abs_of_nonneg x.2.1]
  rw [he,Real.cos_abs]

lemma cosMode_mul (m n : ℕ) (x : I) :
    cosMode m x*cosMode n x = (1/2:ℝ)*
      (cosMode (m+n) x + cosMode ((m:ℤ)-n).natAbs x) := by
  rw [cosMode_natAbs]
  dsimp [cosMode]
  push_cast
  rw [show Real.pi*((m:ℝ)+n)*(x:ℝ) = Real.pi*m*(x:ℝ)+Real.pi*n*(x:ℝ) by ring,
    show Real.pi*((m:ℝ)-n)*(x:ℝ) = Real.pi*m*(x:ℝ)-Real.pi*n*(x:ℝ) by ring]
  nlinarith [Real.two_mul_cos_mul_cos (Real.pi*m*(x:ℝ)) (Real.pi*n*(x:ℝ))]

variable {d : Type*} [Fintype d]

def cubeCosMode (n : d → ℕ) : C(d → I,ℂ) where
  toFun x := ∏ i, (cosMode (n i) (x i) : ℂ)
  continuous_toFun := by fun_prop

@[simp] lemma cubeCosMode_zero : cubeCosMode (fun _ : d => 0) = 1 := by
  ext x
  simp [cubeCosMode,cosMode]

lemma cubeCosMode_mul [DecidableEq d] (m n : d → ℕ) :
    cubeCosMode m*cubeCosMode n = (1/2:ℂ)^Fintype.card d •
      ∑ s : d → Bool, cubeCosMode (fun i => if s i then m i+n i else ((m i:ℤ)-n i).natAbs) := by
  classical
  ext x
  simp only [ContinuousMap.mul_apply,cubeCosMode,ContinuousMap.coe_mk,
    ContinuousMap.smul_apply,ContinuousMap.sum_apply,smul_eq_mul]
  rw [← Finset.prod_mul_distrib]
  simp_rw [← Complex.ofReal_mul,cosMode_mul,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_ofNat,Complex.ofReal_add]
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
  congr 1
  have he (i : d) : (cosMode (m i+n i) (x i):ℂ)+cosMode ((m i:ℤ)-n i).natAbs (x i) =
      ∑ s : Bool, (cosMode (if s then m i+n i else ((m i:ℤ)-n i).natAbs) (x i):ℂ) := by
    simp
  simp_rw [he]
  rw [Fintype.prod_sum]

def cosineSpan (d : Type*) [Fintype d] : Submodule ℂ C(d → I,ℂ) :=
  span ℂ (range (cubeCosMode (d := d)))

lemma cubeCosMode_mem (n : d → ℕ) : cubeCosMode n ∈ cosineSpan d :=
  subset_span ⟨n,rfl⟩

lemma cosineSpan_one : (1 : C(d → I,ℂ)) ∈ cosineSpan d := by
  rw [← cubeCosMode_zero]
  exact cubeCosMode_mem _

lemma cosineSpan_mul {f g : C(d → I,ℂ)} (hf : f ∈ cosineSpan d) (hg : g ∈ cosineSpan d) :
    f*g ∈ cosineSpan d := by
  classical
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨m,rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨n,rfl⟩ := hg
      rw [cubeCosMode_mul]
      exact (cosineSpan d).smul_mem _ ((cosineSpan d).sum_mem (fun s _ => cubeCosMode_mem _))
    | zero => simp only [mul_zero]; exact (cosineSpan d).zero_mem
    | add g h hg hh hge hhe => simpa only [mul_add] using (cosineSpan d).add_mem hge hhe
    | smul a g hg hge => simpa only [mul_smul_comm] using (cosineSpan d).smul_mem a hge
  | zero => simp only [zero_mul]; exact (cosineSpan d).zero_mem
  | add f h hf hh hfe hhe => simpa only [add_mul] using (cosineSpan d).add_mem hfe hhe
  | smul a f hf hfe => simpa only [smul_mul_assoc] using (cosineSpan d).smul_mem a hfe

lemma cubeCosMode_star (n : d → ℕ) : star (cubeCosMode n) = cubeCosMode n := by
  ext x
  simp [cubeCosMode]

lemma cosineSpan_star {f : C(d → I,ℂ)} (hf : f ∈ cosineSpan d) : star f ∈ cosineSpan d := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨n,rfl⟩ := hf
    rw [cubeCosMode_star]
    exact cubeCosMode_mem _
  | zero => simp only [star_zero]; exact (cosineSpan d).zero_mem
  | add f g hf hg hfe hge => simpa only [star_add] using (cosineSpan d).add_mem hfe hge
  | smul a f hf hfe => simpa only [star_smul] using (cosineSpan d).smul_mem (star a) hfe

def cosineAlgebra (d : Type*) [Fintype d] : StarSubalgebra ℂ C(d → I,ℂ) where
  carrier := cosineSpan d
  zero_mem' := (cosineSpan d).zero_mem
  add_mem' := (cosineSpan d).add_mem
  one_mem' := cosineSpan_one
  mul_mem' := cosineSpan_mul
  algebraMap_mem' a := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (cosineSpan d).smul_mem a cosineSpan_one
  star_mem' := cosineSpan_star

lemma cubeCosMode_single [DecidableEq d] (i : d) (x : d → I) :
    cubeCosMode (Pi.single i 1) x = (Real.cos (Real.pi*(x i:ℝ)) : ℂ) := by
  simp only [cubeCosMode,ContinuousMap.coe_mk]
  rw [Finset.prod_eq_single i]
  · simp only [Pi.single_eq_same,cosMode,ContinuousMap.coe_mk,Nat.cast_one,mul_one]
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji,cosMode]
  · simp

lemma cosineAlgebra_separatesPoints : (cosineAlgebra d).SeparatesPoints := by
  classical
  intro x y hxy
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hxy
  refine ⟨_,⟨cubeCosMode (Pi.single i 1),cubeCosMode_mem _,rfl⟩,?_⟩
  simp only [cubeCosMode_single,ne_eq,Complex.ofReal_inj]
  intro hh
  have hx : Real.pi*(x i:ℝ) ∈ Icc 0 Real.pi :=
    ⟨mul_nonneg Real.pi_pos.le (x i).2.1, (mul_le_mul_of_nonneg_left (x i).2.2 Real.pi_pos.le).trans_eq (mul_one _)⟩
  have hy : Real.pi*(y i:ℝ) ∈ Icc 0 Real.pi :=
    ⟨mul_nonneg Real.pi_pos.le (y i).2.1, (mul_le_mul_of_nonneg_left (y i).2.2 Real.pi_pos.le).trans_eq (mul_one _)⟩
  exact hi (Subtype.ext (mul_left_cancel₀ Real.pi_ne_zero (Real.injOn_cos hx hy hh)))

lemma cosineSpan_dense : (cosineSpan d).topologicalClosure = ⊤ := by
  have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (cosineAlgebra d) cosineAlgebra_separatesPoints
  exact congrArg (fun a : StarSubalgebra ℂ C(d → I,ℂ) => a.toSubalgebra.toSubmodule) h

end Work_NeumannCube_scope

open MeasureTheory Set Submodule
open scoped BigOperators unitInterval ComplexConjugate ENNReal

variable {d : Type*} [Fintype d]

def cubeNeumannMode (n : d → ℕ) : C(d → I,ℂ) where
  toFun x := ∏ i, neumannMode (n i) (x i)
  continuous_toFun := by fun_prop

lemma cosNormalization_pos (n : ℕ) : 0 < cosNormalization n := by
  unfold cosNormalization
  split_ifs <;> positivity

lemma cubeNeumannMode_eq (n : d → ℕ) :
    cubeNeumannMode n = (∏ i, (cosNormalization (n i):ℂ)) • cubeCosMode n := by
  ext x
  simp only [cubeNeumannMode,cubeCosMode,neumannMode,ContinuousMap.coe_mk,
    ContinuousMap.smul_apply,smul_eq_mul,Complex.ofReal_mul,Finset.prod_mul_distrib]

lemma cubeNeumannMode_span : span ℂ (range (cubeNeumannMode (d := d))) = cosineSpan d := by
  apply le_antisymm
  · refine span_le.mpr ?_
    rintro _ ⟨n,rfl⟩
    rw [cubeNeumannMode_eq]
    exact (cosineSpan d).smul_mem _ (cubeCosMode_mem _)
  · refine span_le.mpr ?_
    rintro _ ⟨n,rfl⟩
    have hnon : (∏ i, (cosNormalization (n i):ℂ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      exact_mod_cast (cosNormalization_pos (n i)).ne'
    have hi : cubeCosMode n = (∏ i, (cosNormalization (n i):ℂ))⁻¹ • cubeNeumannMode n := by
      rw [cubeNeumannMode_eq,smul_smul,inv_mul_cancel₀ hnon,one_smul]
    rw [hi]
    exact (span ℂ (range cubeNeumannMode)).smul_mem _ (subset_span ⟨n,rfl⟩)

lemma cubeNeumannMode_inner (m n : d → ℕ) :
    (∫ x : d → I, conj (cubeNeumannMode m x)*cubeNeumannMode n x) = if m=n then 1 else 0 := by
  classical
  simp only [cubeNeumannMode,ContinuousMap.coe_mk,map_prod,← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_volume_eq_prod (fun i (x : I) => conj (neumannMode (m i) x)*neumannMode (n i) x)]
  simp_rw [neumannMode_inner]
  by_cases h : m=n
  · simp [h]
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

abbrev neumannLp (n : d → ℕ) : Lp ℂ 2 (volume : Measure (d → I)) :=
  ContinuousMap.toLp 2 volume ℂ (cubeNeumannMode n)

lemma orthonormal_neumann : Orthonormal ℂ (neumannLp (d := d)) := by
  classical
  rw [orthonormal_iff_ite]
  intro m n
  rw [ContinuousMap.inner_toLp]
  simpa only [mul_comm] using cubeNeumannMode_inner m n

lemma neumannLp_span_dense : (span ℂ (range (neumannLp (d := d)))).topologicalClosure = ⊤ := by
  have hc : (span ℂ (range (cubeNeumannMode (d := d)))).topologicalClosure = ⊤ := by
    rw [cubeNeumannMode_span,cosineSpan_dense]
  simpa only [map_span,ContinuousLinearMap.coe_coe,← range_comp,Function.comp_def] using
    (ContinuousMap.toLp_denseRange ℂ (volume : Measure (d → I)) ℂ (by norm_num : (2:ENNReal) ≠ ⊤)).topologicalClosure_map_submodule hc

def neumannBasis : HilbertBasis (d → ℕ) ℂ (Lp ℂ 2 (volume : Measure (d → I))) :=
  HilbertBasis.mk orthonormal_neumann neumannLp_span_dense.ge

@[simp] lemma neumannBasis_apply (n : d → ℕ) : neumannBasis n = neumannLp n :=
  congrFun (HilbertBasis.coe_mk _ _) n

end CoulombNeumann

end

end OAI
