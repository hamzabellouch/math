import OAI.Combinatorics.HoneycombChords.MatrixPencils
import OAI.Combinatorics.HoneycombChords.ChebyshevSystems

namespace OAI

/-! Oblique comparison and noncoincidence for the strip jet pencils. -/

section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory
noncomputable def jetRectPencil {n m : ℕ} (b c : ℕ → ℝ) (z t : ℝ) : Matrix (Fin n) (Fin m) ℝ :=
  fun i j=>∫ p in Set.Ioi (0:ℝ),cosineKernelJet (nodalOrder b i) 0 (b i) (p^2)*
    cosineKernelJet (nodalOrder c j) 0 (c j) (p^2)*((p^2-t)*poleAdjustedDensity z p)
lemma jetRectPencil_square {n : ℕ} (b c : ℕ → ℝ) (z t : ℝ) :
    jetRectPencil (n:=n) (m:=n) b c z t=jetPencil (poleAdjustedDensity z) b c t := rfl
lemma jetRectPencil_transpose {n m : ℕ} (b c : ℕ → ℝ) (z t : ℝ) :
    (jetRectPencil (n:=n) (m:=m) b c z t).transpose=jetRectPencil c b z t := by
  ext i j
  dsimp [jetRectPencil]
  apply integral_congr_ae
  filter_upwards with p
  ring
lemma jetRectPencil_vecMul {n m : ℕ} (b c : ℕ → ℝ) (a : Fin n → ℝ)
    {z : ℝ} (hz : 0<z) (t : ℝ)
    (hb0 : ∀ i : Fin n,0 ≤ b i) (hc0 : ∀ i : Fin m,0 ≤ c i)
    (hb1 : ∀ i : Fin n,b i ≤ (3*angle/2)^2) (hc1 : ∀ i : Fin m,c i ≤ angle^2) (j : Fin m) :
    (a ᵥ* jetRectPencil b c z t) j=∫ p in Set.Ioi (0:ℝ),(p^2-t)*jetCombination b a (p^2)*
      cosineKernelJet (nodalOrder c j) 0 (c j) (p^2)*poleAdjustedDensity z p := by
  have hi (i : Fin n) := (pole_jet_pair_pencil_integrable (hb0 i) (hc0 j) (hb1 i) (hc1 j) hz
    (nodalOrder b i) (nodalOrder c j) t).const_mul (a i)
  simp only [Matrix.vecMul,dotProduct,jetRectPencil,←integral_const_mul]
  rw [←integral_finsetSum _ (fun i _=>hi i)]
  apply integral_congr_ae
  filter_upwards with p
  dsimp [jetCombination]
  rw [mul_sum,sum_mul,sum_mul]
  apply sum_congr rfl
  intro i _
  ring
lemma pole_jetRectPencil_vecMul_nonzero {n m : ℕ} (b c : ℕ → ℝ) (a : Fin n → ℝ)
    {z : ℝ} (hz : 0<z) (t : ℝ) (hnm : n < m)
    (hb : Monotone (fun i : Fin n=>b i)) (hc : Monotone (fun i : Fin m=>c i))
    (hb0 : ∀ i : Fin n,0 ≤ b i) (hc0 : ∀ i : Fin m,0 ≤ c i) (ha : a≠0)
    (hb1 : ∀ i : Fin n,b i ≤ (3*angle/2)^2) (hc1 : ∀ i : Fin m,c i ≤ angle^2) :
    a ᵥ* jetRectPencil (m:=m) b c z t≠0 := by
  obtain ⟨j,hj⟩ := pole_jet_linear_nonorthogonality b c a hz t hnm hb hc hb0 hc0 ha hb1 hc1
  intro he
  have hh := congrFun he j
  rw [jetRectPencil_vecMul b c a hz t hb0 hc0 hb1 hc1 j] at hh
  exact hj hh
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory
noncomputable def reorderedKnotPencil (N : ℕ) (s t z r : ℝ) : Matrix (Fin (2*N+1)) (Fin (2*N+1)) ℝ :=
  (jetPencil (poleAdjustedDensity z) (interiorKnotLabels N s) (interiorKnotLabels N t) r).submatrix
    (knotPermutation N) (knotPermutation N)
lemma reorderedKnotPencil_transpose (N : ℕ) (s t z r : ℝ) :
    (reorderedKnotPencil N s t z r).transpose=reorderedKnotPencil N t s z r := by
  rw [reorderedKnotPencil,Matrix.transpose_submatrix,←jetRectPencil_square,jetRectPencil_transpose,jetRectPencil_square]
  rfl
lemma reorderedKnotPencil_corner (N : ℕ) {s t : ℝ}
    (hs : 0<s) (hsL : s<angle) (ht : 0<t) (htL : t<angle) (z r : ℝ) :
    (reorderedKnotPencil N s t z r).submatrix Fin.castSucc Fin.castSucc=
      jetPencil (n:=2*N) (poleAdjustedDensity z) (twoKnotLabels N) (twoKnotLabels N) r := by
  ext i j
  simp only [reorderedKnotPencil,Matrix.submatrix_apply,knotPermutation_castSucc,jetPencil,jetGram]
  simp only [insertKnot_row N hs hsL,insertKnot_row N ht htL]
lemma reorderedKnotPencil_vecMul (N : ℕ) {s t : ℝ}
    (hs : 0<s) (hsL : s<angle) (z r : ℝ) (a : Fin (2*N) → ℝ) (j : Fin (2*N+1)) :
    ((Fin.lastCases 0 a) ᵥ* reorderedKnotPencil N s t z r) j=
      (a ᵥ* jetRectPencil (m:=2*N+1) (twoKnotLabels N) (interiorKnotLabels N t) z r) (knotPermutation N j) := by
  simp only [Matrix.vecMul,dotProduct]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.lastCases_castSucc,Fin.lastCases_last,zero_mul,add_zero]
  apply sum_congr rfl
  intro i _
  congr 1
  simp only [reorderedKnotPencil,Matrix.submatrix_apply,knotPermutation_castSucc,jetPencil,jetGram,jetRectPencil]
  simp only [insertKnot_row N hs hsL]
lemma reorderedKnotPencil_left_nonzero (N : ℕ) {s t z : ℝ}
    (hs : 0<s) (hsL : s<angle) (ht : 0<t) (htL : t<angle) (hz : 0<z) (r : ℝ)
    (a : Fin (2*N) → ℝ) (ha : a≠0) :
    (Fin.lastCases 0 a) ᵥ* reorderedKnotPencil N s t z r≠0 := by
  have hL : angle^2 ≤ (3*angle/2)^2 := by nlinarith [sq_nonneg angle]
  have hn:=pole_jetRectPencil_vecMul_nonzero (m:=2*N+1) (twoKnotLabels N) (interiorKnotLabels N t) a hz r (by omega)
    (fun i j hij=>twoKnot_monotone N hij) (fun i j hij=>interiorKnot_monotone N ht htL hij)
    (fun i=>twoKnot_nonneg N i) (fun i=>interiorKnot_nonneg N i t) ha
    (fun i=>(twoKnot_le N i).trans hL) (fun i=>interiorKnot_le N i ht htL)
  intro he
  apply hn
  ext j
  have hp := congrFun he ((knotPermutation N).symm j)
  rw [reorderedKnotPencil_vecMul N hs hsL] at hp
  simpa only [Equiv.apply_symm_apply,Pi.zero_apply] using hp

theorem pole_knotPencil_no_common_root (N : ℕ) {s t z : ℝ}
    (hs : 0<s) (hsL : s<angle) (ht : 0<t) (htL : t<angle) (hz : 0<z) (r : ℝ)
    (hM : (jetPencil (n:=2*N) (poleAdjustedDensity z) (twoKnotLabels N) (twoKnotLabels N) r).det=0) :
    (jetPencil (n:=2*N+1) (poleAdjustedDensity z) (interiorKnotLabels N s) (interiorKnotLabels N t) r).det≠0 := by
  have h:=bordered_det_nonzero (reorderedKnotPencil N s t z r)
    (reorderedKnotPencil_left_nonzero N hs hsL ht htL hz r) (by
      intro a ha he
      have hn:=reorderedKnotPencil_left_nonzero N ht htL hs hsL hz r a ha
      apply hn
      rw [←reorderedKnotPencil_transpose N s t z r,Matrix.vecMul_transpose]
      exact he)
    (by rw [reorderedKnotPencil_corner N hs hsL ht htL];exact hM)
  simpa only [reorderedKnotPencil,Matrix.det_submatrix_equiv_self] using h
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory Filter
lemma jetGram_isHermitian {n : ℕ} (w : ℝ → ℝ) (b : ℕ → ℝ) : (jetGram (n:=n) w b b).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  ext i j
  dsimp [jetGram,Matrix.transpose]
  apply integral_congr_ae
  filter_upwards with p
  ring
lemma jetGram_quadratic {n : ℕ} (w : ℝ → ℝ) (b : ℕ → ℝ) (a : Fin n → ℝ)
    (hi : ∀ i j : Fin n,IntegrableOn (fun p=>cosineKernelJet (nodalOrder b i) 0 (b i) (p^2)*
      cosineKernelJet (nodalOrder b j) 0 (b j) (p^2)*w p) (Set.Ioi 0)) :
    a ⬝ᵥ (jetGram w b b *ᵥ a)=∫ p in Set.Ioi (0:ℝ),jetCombination b a (p^2)^2*w p := by
  have hij (i j : Fin n) := ((hi i j).const_mul (a i)).mul_const (a j)
  have he p : jetCombination b a (p^2)^2*w p=
      ∑ i : Fin n,∑ j : Fin n,a i*(cosineKernelJet (nodalOrder b i) 0 (b i) (p^2)*
        cosineKernelJet (nodalOrder b j) 0 (b j) (p^2)*w p)*a j := by
    rw [pow_two]
    simp only [jetCombination,sum_mul,mul_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=>hij i j))]
  simp_rw [integral_finsetSum _ (fun j _=>hij _ j),integral_mul_const,integral_const_mul]
  simp [dotProduct,mulVec,jetGram,mul_sum,mul_assoc]
lemma jetGram_posDef {n : ℕ} (w : ℝ → ℝ) (b : ℕ → ℝ)
    (hb : Monotone (fun i : Fin n=>b i)) (hb0 : ∀ i : Fin n,0 ≤ b i)
    (hw : ∀ p,0<p → 0<w p)
    (hi : ∀ i j : Fin n,IntegrableOn (fun p=>cosineKernelJet (nodalOrder b i) 0 (b i) (p^2)*
      cosineKernelJet (nodalOrder b j) 0 (b j) (p^2)*w p) (Set.Ioi 0)) :
    (jetGram (n:=n) w b b).PosDef := by
  have hp : (jetGram (n:=n) w b b).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (jetGram_isHermitian w b)
    intro a
    rw [star_trivial,jetGram_quadratic w b a hi]
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    exact mul_nonneg (sq_nonneg _) (hw p hp).le
  exact hp.posDef_iff_det_ne_zero.mpr (jetGram_det_pos w b b hb hb hb0 hb0 hw hi).ne'
/-- The symmetric M pencil has only positive real roots. -/
theorem pole_symmetric_jet_pencil_factors {n : ℕ} (b : ℕ → ℝ) {z : ℝ} (hz : 0<z)
    (hb : Monotone (fun i : Fin n=>b i)) (hb0 : ∀ i : Fin n,0 ≤ b i)
    (hb1 : ∀ i : Fin n,b i ≤ angle^2) :
    ∃ e : Fin n → ℝ,(∀ i,0<e i) ∧ ∀ t : ℝ,
      (jetPencil (n:=n) (poleAdjustedDensity z) b b t).det=
        (jetGram (n:=n) (poleAdjustedDensity z) b b).det*∏ i,(e i-t) := by
  have hL : angle^2 ≤ (3*angle/2)^2 := by nlinarith [sq_nonneg angle]
  have hi i j := pole_adjusted_pair_moment_integrable (hb0 i) (hb0 j) ((hb1 i).trans hL) (hb1 j) hz
    (nodalOrder b i) (nodalOrder b j) 0
  have hi0 : ∀ i j : Fin n,IntegrableOn (fun p=>cosineKernelJet (nodalOrder b i) 0 (b i) (p^2)*
      cosineKernelJet (nodalOrder b j) 0 (b j) (p^2)*poleAdjustedDensity z p) (Set.Ioi 0) := by
    intro i j
    simpa only [pow_zero,one_mul] using hi i j
  have hi2 i j := pole_adjusted_pair_moment_integrable (hb0 i) (hb0 j) ((hb1 i).trans hL) (hb1 j) hz
    (nodalOrder b i) (nodalOrder b j) 2
  obtain ⟨e,he⟩ := positive_gram_pencil_real_factorization
    (jetPencil (n:=n) (poleAdjustedDensity z) b b 0) (jetGram (n:=n) (poleAdjustedDensity z) b b)
    (jetGram_isHermitian _ b) (jetGram_posDef _ b hb hb0 (fun _ hp=>poleAdjustedDensity_pos hz hp) hi0)
  have he' (t : ℝ) := he t
  simp_rw [←jetPencil_affine _ b b _ hi0 hi2] at he'
  refine ⟨e,?_,he'⟩
  intro i
  apply pole_jetPencil_real_root_positive b b hz hb hb hb0 hb0 (fun i=>(hb1 i).trans hL) hb1
  rw [he' (e i)]
  have hp : (∏ j : Fin n,(e j-e i))=0 := prod_eq_zero (mem_univ i) (sub_self _)
  rw [hp,mul_zero]
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory
lemma pole_jetPencil_affine {n : ℕ} (b c : ℕ → ℝ) {z : ℝ} (hz : 0<z) (t : ℝ)
    (hb0 : ∀ i : Fin n,0 ≤ b i) (hc0 : ∀ i : Fin n,0 ≤ c i)
    (hb1 : ∀ i : Fin n,b i ≤ (3*angle/2)^2) (hc1 : ∀ i : Fin n,c i ≤ angle^2) :
    jetPencil (n:=n) (poleAdjustedDensity z) b c t =
      jetPencil (poleAdjustedDensity z) b c 0-t • jetGram (poleAdjustedDensity z) b c := by
  apply jetPencil_affine
  · intro i j
    simpa only [pow_zero,one_mul] using pole_adjusted_pair_moment_integrable (hb0 i) (hc0 j) (hb1 i) (hc1 j) hz (nodalOrder b i) (nodalOrder c j) 0
  · intro i j
    exact pole_adjusted_pair_moment_integrable (hb0 i) (hc0 j) (hb1 i) (hc1 j) hz (nodalOrder b i) (nodalOrder c j) 2
lemma pole_jetGram_det_pos {n : ℕ} (b c : ℕ → ℝ) {z : ℝ} (hz : 0<z)
    (hb : Monotone (fun i : Fin n=>b i)) (hc : Monotone (fun i : Fin n=>c i))
    (hb0 : ∀ i : Fin n,0 ≤ b i) (hc0 : ∀ i : Fin n,0 ≤ c i)
    (hb1 : ∀ i : Fin n,b i ≤ (3*angle/2)^2) (hc1 : ∀ i : Fin n,c i ≤ angle^2) :
    0<(jetGram (n:=n) (poleAdjustedDensity z) b c).det := by
  apply jetGram_det_pos _ b c hb hc hb0 hc0 (fun _ hp=>poleAdjustedDensity_pos hz hp)
  intro i j
  simpa only [pow_zero,one_mul] using pole_adjusted_pair_moment_integrable (hb0 i) (hc0 j) (hb1 i) (hc1 j) hz (nodalOrder b i) (nodalOrder c j) 0
lemma pole_jetGram_posDef {n : ℕ} (b : ℕ → ℝ) {z : ℝ} (hz : 0<z)
    (hb : Monotone (fun i : Fin n=>b i)) (hb0 : ∀ i : Fin n,0 ≤ b i) (hb1 : ∀ i : Fin n,b i ≤ angle^2) :
    (jetGram (n:=n) (poleAdjustedDensity z) b b).PosDef := by
  have hL : angle^2 ≤ (3*angle/2)^2 := by nlinarith [sq_nonneg angle]
  apply jetGram_posDef _ b hb hb0 (fun _ hp=>poleAdjustedDensity_pos hz hp)
  intro i j
  simpa only [pow_zero,one_mul] using pole_adjusted_pair_moment_integrable (hb0 i) (hb0 j) ((hb1 i).trans hL) (hb1 j) hz (nodalOrder b i) (nodalOrder b j) 0
lemma pole_jetPencil_zero_posDef {n : ℕ} (b : ℕ → ℝ) {z : ℝ} (hz : 0<z)
    (hb : Monotone (fun i : Fin n=>b i)) (hb0 : ∀ i : Fin n,0 ≤ b i) (hb1 : ∀ i : Fin n,b i ≤ angle^2) :
    (jetPencil (n:=n) (poleAdjustedDensity z) b b 0).PosDef := by
  have hL : angle^2 ≤ (3*angle/2)^2 := by nlinarith [sq_nonneg angle]
  apply jetGram_posDef _ b hb hb0
  · intro p hp
    exact mul_pos (by simpa using sq_pos_of_pos hp) (poleAdjustedDensity_pos hz hp)
  · intro i j
    exact pole_jet_pair_pencil_integrable (hb0 i) (hb0 j) ((hb1 i).trans hL) (hb1 j) hz _ _ 0
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open MeasureTheory Filter Finset Matrix
lemma pole_cosh_moment_continuousOn {b z : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ (3*angle/2)^2)
    (hz : 0<z) (k : ℕ) (r : ℝ) :
    ContinuousOn (fun t : ℝ=>∫ p in Set.Ioi (0:ℝ),
      (p^2-r)*cosineKernelJet k 0 b (p^2)*Real.cosh (t*p)*poleAdjustedDensity z p)
      (Set.Icc 0 angle) := by
  let f : ℝ → ℝ := fun p=>cosineKernelJet k 0 b (p^2)*Real.cosh (angle*p)*poleAdjustedDensity z p
  have hf0 : IntegrableOn f (Set.Ioi 0) := by
    have h:=pole_adjusted_pair_moment_integrable hb (sq_nonneg angle) hb1 le_rfl hz k 0 0
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    simp only [pow_zero,one_mul,cosineKernelJet_zero_zero_cosh (sq_nonneg angle) (sq_nonneg p),Real.sqrt_sq strip_angle_pos.le,Real.sqrt_sq hp.le,f]
  have hf2 : IntegrableOn (fun p=>p^2*f p) (Set.Ioi 0) := by
    have h:=pole_adjusted_pair_moment_integrable hb (sq_nonneg angle) hb1 le_rfl hz k 0 2
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    simp only [cosineKernelJet_zero_zero_cosh (sq_nonneg angle) (sq_nonneg p),Real.sqrt_sq strip_angle_pos.le,Real.sqrt_sq hp.le,f]
    ring
  apply continuousOn_of_dominated (bound:=fun p=>(p^2+|r|)*f p)
  · intro t ht
    have hjet : Continuous (fun p : ℝ=>cosineKernelJet k 0 b (p^2)) :=
      (cosineKernelJet_contDiff_right k 0 b 0).continuous.comp (by fun_prop)
    exact (((by fun_prop : Continuous (fun p : ℝ=>p^2-r)).aestronglyMeasurable.mul hjet.aestronglyMeasurable).mul
      (by fun_prop : Continuous (fun p : ℝ=>Real.cosh (t*p))).aestronglyMeasurable).mul
      (by unfold poleAdjustedDensity stripDensity;fun_prop : Measurable (poleAdjustedDensity z)).aestronglyMeasurable
  · intro t ht
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    have hc : Real.cosh (t*p) ≤ Real.cosh (angle*p) := by
      apply Real.cosh_le_cosh.mpr
      rw [abs_of_nonneg (mul_nonneg ht.1 hp.le),abs_of_nonneg (mul_nonneg strip_angle_pos.le hp.le)]
      exact mul_le_mul_of_nonneg_right ht.2 hp.le
    have hq : |p^2-r| ≤ p^2+|r| := by
      exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (sq_nonneg p)])
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_mul,
      abs_of_nonneg (cosineKernelJet_nonneg hb (sq_nonneg p) k 0),
      abs_of_pos (Real.cosh_pos _),abs_of_pos (poleAdjustedDensity_pos hz hp)]
    dsimp [f]
    rw [←mul_assoc,←mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (mul_le_mul_of_nonneg_right hq (cosineKernelJet_nonneg hb (sq_nonneg p) k 0)) hc
        (Real.cosh_pos _).le (mul_nonneg (by positivity) (cosineKernelJet_nonneg hb (sq_nonneg p) k 0)))
      (poleAdjustedDensity_pos hz hp).le
  · apply (hf2.add (hf0.const_mul |r|)).congr
    filter_upwards with p
    dsimp [f]
    ring
  · filter_upwards with p
    exact (by fun_prop : Continuous (fun t : ℝ=>(p^2-r)*cosineKernelJet k 0 b (p^2)*Real.cosh (t*p)*poleAdjustedDensity z p)).continuousOn
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open MeasureTheory Matrix Finset Filter
noncomputable def knotPairing (N : ℕ) (z : ℝ) (a : Fin (2*N) → ℝ) (r t : ℝ) : ℝ :=
  ∑ i,a i*(∫ p in Set.Ioi (0:ℝ),(p^2-r)*
    cosineKernelJet (nodalOrder (twoKnotLabels N) i) 0 (twoKnotLabels N i) (p^2)*
    Real.cosh (t*p)*poleAdjustedDensity z p)
lemma knotPairing_continuousOn (N : ℕ) {z : ℝ} (hz : 0<z) (a : Fin (2*N) → ℝ) (r : ℝ) :
    ContinuousOn (knotPairing N z a r) (Set.Icc 0 angle) := by
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_const.mul
  exact pole_cosh_moment_continuousOn (twoKnot_nonneg N i)
    ((twoKnot_le N i).trans (by nlinarith [sq_nonneg angle])) hz _ r
lemma reorderedKnotPencil_vecMul_last (N : ℕ) {s t : ℝ}
    (hs : 0<s) (hsL : s<angle) (ht : 0<t) (htL : t<angle) (z r : ℝ) (a : Fin (2*N) → ℝ) :
    ((Fin.lastCases 0 a) ᵥ* reorderedKnotPencil N s t z r) (Fin.last (2*N))=knotPairing N z a r t := by
  rw [reorderedKnotPencil_vecMul N hs hsL,knotPermutation_last]
  simp only [Matrix.vecMul,dotProduct,knotPairing]
  apply sum_congr rfl
  intro i _
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  simp only [interiorKnot_nodalOrder N N ht htL,lt_self_iff_false,ite_false,ite_true,
    interiorKnotLabels,cosineKernelJet_zero_zero_cosh (sq_nonneg t) (sq_nonneg p),Real.sqrt_sq ht.le,Real.sqrt_sq hp.le]
  ring
lemma knotPairing_ne_zero (N : ℕ) {z : ℝ} (hz : 0<z) (a : Fin (2*N) → ℝ) (ha : a≠0) (r : ℝ)
    (har : a ᵥ* jetPencil (n:=2*N) (poleAdjustedDensity z) (twoKnotLabels N) (twoKnotLabels N) r=0)
    {t : ℝ} (ht : 0<t) (htL : t<angle) : knotPairing N z a r t≠0 := by
  have hs : 0<angle/2 := by linarith [strip_angle_pos]
  have hsL : angle/2<angle := by linarith [strip_angle_pos]
  have hn:=reorderedKnotPencil_left_nonzero N hs hsL ht htL hz r a ha
  intro he
  apply hn
  ext j
  refine Fin.lastCases ?_ (fun k=>?_) j
  · simpa only [Pi.zero_apply,reorderedKnotPencil_vecMul_last N hs hsL ht htL] using he
  · have hcorner:=reorderedKnotPencil_corner N hs hsL ht htL z r
    have h:=congrFun har k
    simp only [Matrix.vecMul,dotProduct] at h ⊢
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc,Fin.lastCases_last,zero_mul,add_zero,Pi.zero_apply]
    rw [←hcorner] at h
    exact h
lemma continuousOn_nonzero_mul_pos {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hn : ∀ x∈Set.Ioo a b,f x≠0)
    {s t : ℝ} (hs : s∈Set.Ioo a b) (ht : t∈Set.Ioo a b) : 0<f s*f t := by
  have hi : IsPreconnected (Set.Ioo a b) := isPreconnected_Ioo
  have hc : ContinuousOn f (Set.Ioo a b) := hf.mono Set.Ioo_subset_Icc_self
  have hsign : f s<0 ↔ f t<0 := by
    constructor <;> intro hneg
    · by_contra hh
      have hnon : 0 ≤ f t := le_of_not_gt hh
      obtain ⟨x,hx,hfx⟩ := hi.intermediate_value hs ht hc ⟨hneg.le,hnon⟩
      exact hn x hx hfx
    · by_contra hh
      have hnon : 0 ≤ f s := le_of_not_gt hh
      obtain ⟨x,hx,hfx⟩ := hi.intermediate_value ht hs hc ⟨hneg.le,hnon⟩
      exact hn x hx hfx
  rcases lt_or_gt_of_ne (hn s hs) with hneg|hpos
  · exact mul_pos_of_neg_of_neg hneg (hsign.mp hneg)
  · have htp : 0<f t := by
      rcases lt_or_gt_of_ne (hn t ht) with htneg|htpos
      · exact False.elim ((not_lt_of_gt hpos) (hsign.mpr htneg))
      · exact htpos
    exact mul_pos hpos htp
/-- The residues of the actual first-chain oblique Schur complement have the
symmetric sign. This avoids assuming complex-root reality or interlacing. -/
theorem knotPairing_product_pos (N : ℕ) {z : ℝ} (hz : 0<z) (a : Fin (2*N) → ℝ) (ha : a≠0) (r : ℝ)
    (har : a ᵥ* jetPencil (n:=2*N) (poleAdjustedDensity z) (twoKnotLabels N) (twoKnotLabels N) r=0)
    {s t : ℝ} (hs : 0<s) (hsL : s<angle) (ht : 0<t) (htL : t<angle) :
    0<knotPairing N z a r s*knotPairing N z a r t :=
  continuousOn_nonzero_mul_pos (knotPairing_continuousOn N hz a r)
    (fun _ h=>knotPairing_ne_zero N hz a ha r har h.1 h.2) ⟨hs,hsL⟩ ⟨ht,htL⟩
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory
noncomputable def reorderedKnotGram (N : ℕ) (s t z : ℝ) : Matrix (Fin (2*N+1)) (Fin (2*N+1)) ℝ :=
  (jetGram (poleAdjustedDensity z) (interiorKnotLabels N s) (interiorKnotLabels N t)).submatrix
    (knotPermutation N) (knotPermutation N)
lemma reorderedKnotGram_corner (N : ℕ) {s t : ℝ}
    (hs : 0<s) (hsL : s<angle) (ht : 0<t) (htL : t<angle) (z : ℝ) :
    (reorderedKnotGram N s t z).submatrix Fin.castSucc Fin.castSucc=
      jetGram (n:=2*N) (poleAdjustedDensity z) (twoKnotLabels N) (twoKnotLabels N) := by
  ext i j
  simp only [reorderedKnotGram,Matrix.submatrix_apply,knotPermutation_castSucc,jetGram]
  simp only [insertKnot_row N hs hsL,insertKnot_row N ht htL]
lemma reorderedKnotPencil_affine (N : ℕ) {s t z : ℝ}
    (hs : 0<s) (hsL : s<angle) (ht : 0<t) (htL : t<angle) (hz : 0<z) (r : ℝ) :
    reorderedKnotPencil N s t z r=reorderedKnotPencil N s t z 0-r • reorderedKnotGram N s t z := by
  have hL : angle^2 ≤ (3*angle/2)^2 := by nlinarith [sq_nonneg angle]
  have h:=pole_jetPencil_affine (n:=2*N+1) (interiorKnotLabels N s) (interiorKnotLabels N t) hz r
    (fun i=>interiorKnot_nonneg N i s) (fun i=>interiorKnot_nonneg N i t)
    (fun i=>(interiorKnot_le N i hs hsL).trans hL) (fun i=>interiorKnot_le N i ht htL)
  rw [reorderedKnotPencil,h]
  rfl
lemma reorderedKnotPencil_det_pos_nonpos (N : ℕ) {s t z r : ℝ}
    (hs : 0<s) (hsL : s<angle) (ht : 0<t) (htL : t<angle) (hz : 0<z) (hr : r ≤ 0) :
    0<(reorderedKnotPencil N s t z r).det := by
  have hL : angle^2 ≤ (3*angle/2)^2 := by nlinarith [sq_nonneg angle]
  rw [reorderedKnotPencil,Matrix.det_submatrix_equiv_self]
  exact pole_jetPencil_det_pos_nonpos _ _ hz hr
    (fun _ _ hij=>interiorKnot_monotone N hs hsL hij) (fun _ _ hij=>interiorKnot_monotone N ht htL hij)
    (fun i=>interiorKnot_nonneg N i s) (fun i=>interiorKnot_nonneg N i t)
    (fun i=>(interiorKnot_le N i hs hsL).trans hL) (fun i=>interiorKnot_le N i ht htL)
lemma reorderedKnotGram_det_pos (N : ℕ) {s t z : ℝ}
    (hs : 0<s) (hsL : s<angle) (ht : 0<t) (htL : t<angle) (hz : 0<z) :
    0<(reorderedKnotGram N s t z).det := by
  have hL : angle^2 ≤ (3*angle/2)^2 := by nlinarith [sq_nonneg angle]
  rw [reorderedKnotGram,Matrix.det_submatrix_equiv_self]
  exact pole_jetGram_det_pos _ _ hz
    (fun _ _ hij=>interiorKnot_monotone N hs hsL hij) (fun _ _ hij=>interiorKnot_monotone N ht htL hij)
    (fun i=>interiorKnot_nonneg N i s) (fun i=>interiorKnot_nonneg N i t)
    (fun i=>(interiorKnot_le N i hs hsL).trans hL) (fun i=>interiorKnot_le N i ht htL)
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset

theorem pole_knot_characteristic_comparison (N : ℕ) {s t y z : ℝ}
    (hs : 0<s) (hsL : s<angle) (ht : 0<t) (htL : t<angle) (hy : 0<y) (hyz : y<z) :
    let M:=twoKnotLabels N
    let F:=interiorKnotLabels N s
    let G:=interiorKnotLabels N t
    let S:=(jetPencil (n:=2*N) (poleAdjustedDensity z) M M (-(y^2))).det/
      (jetPencil (n:=2*N) (poleAdjustedDensity z) M M (-(z^2))).det
    let Q:=(jetPencil (n:=2*N+1) (poleAdjustedDensity z) F G (-(y^2))).det/
      (jetPencil (n:=2*N+1) (poleAdjustedDensity z) F G (-(z^2))).det
    (y^2/z^2)*S ≤ Q ∧ Q ≤ S := by
  dsimp only
  have hz : 0<z := hy.trans hyz
  let A:=reorderedKnotPencil N s t z 0
  let B:=reorderedKnotGram N s t z
  have hA : (A.submatrix Fin.castSucc Fin.castSucc).PosDef := by
    rw [show A=reorderedKnotPencil N s t z 0 from rfl,reorderedKnotPencil_corner N hs hsL ht htL]
    exact pole_jetPencil_zero_posDef _ hz (fun _ _ hij=>twoKnot_monotone N hij) (fun i=>twoKnot_nonneg N i) (fun i=>twoKnot_le N i)
  have hB : (B.submatrix Fin.castSucc Fin.castSucc).PosDef := by
    rw [show B=reorderedKnotGram N s t z from rfl,reorderedKnotGram_corner N hs hsL ht htL]
    exact pole_jetGram_posDef _ hz (fun _ _ hij=>twoKnot_monotone N hij) (fun i=>twoKnot_nonneg N i) (fun i=>twoKnot_le N i)
  have h0 : 0<A.det := reorderedKnotPencil_det_pos_nonpos N hs hsL ht htL hz le_rfl
  have h1 : 0<B.det := reorderedKnotGram_det_pos N hs hsL ht htL hz
  have hres (r : ℝ) (x : Fin (2*N) → ℝ) (hx : x≠0)
      (hk : x ᵥ* ((A-r • B).submatrix Fin.castSucc Fin.castSucc)=0) :
      0 ≤ lastPairing (A-r • B) x*lastPairing (A-r • B).transpose x := by
    dsimp only [A,B] at hk ⊢
    rw [←reorderedKnotPencil_affine N hs hsL ht htL hz r] at hk ⊢
    rw [reorderedKnotPencil_corner N hs hsL ht htL] at hk
    rw [reorderedKnotPencil_transpose]
    simp only [lastPairing,reorderedKnotPencil_vecMul_last N hs hsL ht htL,
      reorderedKnotPencil_vecMul_last N ht htL hs hsL]
    exact (knotPairing_product_pos N hz x hx r hk ht htL hs hsL).le
  have h:=fin_pencil_ratio A B hA hB h0 h1 hres (sq_pos_of_pos hy) (by nlinarith : y^2 ≤ z^2)
  have heq (u : ℝ) : A+u • B=reorderedKnotPencil N s t z (-u) := by
    rw [reorderedKnotPencil_affine N hs hsL ht htL hz]
    simp only [neg_smul,sub_neg_eq_add]
    rfl
  rw [heq (y^2),heq (z^2)] at h
  simp only [reorderedKnotPencil_corner N hs hsL ht htL] at h
  simpa only [reorderedKnotPencil,Matrix.det_submatrix_equiv_self] using h
/-- The previously open exact target, at its literal F_s with s=L/2. -/
theorem first_oblique_characteristic_comparison : FirstObliqueCharacteristicComparison := by
  intro N _ t ht htL y z hy hyz
  exact pole_knot_characteristic_comparison N (by linarith [strip_angle_pos])
    (by linarith [strip_angle_pos]) ht htL hy hyz
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix MeasureTheory
/-- Remove the constant row and subtract evaluation at zero from every
remaining complete jet. When b 0=0 these are an exact basis of ker(ev₀). -/
noncomputable def zeroJet (b : ℕ → ℝ) (i : ℕ) (x : ℝ) : ℝ :=
  cosineKernelJet (nodalOrder b (i+1)) 0 (b (i+1)) x -
  cosineKernelJet (nodalOrder b (i+1)) 0 (b (i+1)) 0

noncomputable def extendedKnotLabels (N : ℕ) (k : ℕ) : ℝ :=
  if k<2*N+1 then interiorKnotLabels N (angle/2) k else (3*angle/2)^2
noncomputable def zeroJetPencil {n : ℕ} (w : ℝ → ℝ) (b c : ℕ → ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ p in Set.Ioi (0:ℝ),(p^2-t)*zeroJet b i (p^2)*zeroJet c j (p^2)*w p
noncomputable def mixedZeroJetPencil {n : ℕ} (w : ℝ → ℝ) (b c : ℕ → ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ p in Set.Ioi (0:ℝ),(p^2-t)*zeroJet b i (p^2)*
    cosineKernelJet (nodalOrder c j) 0 (c j) (p^2)*w p

def SecondObliqueCharacteristicComparison : Prop :=
  ∀ (N : ℕ),0<N → ∀ t : ℝ,0<t → t<angle → ∀ y z : ℝ,0<y → y<z →
    let M := twoKnotLabels N
    let F := extendedKnotLabels N
    let G := interiorKnotLabels N t
    let S := (zeroJetPencil (n:=2*N-1) (poleAdjustedDensity z) M M (-(y^2))).det/
      (zeroJetPencil (n:=2*N-1) (poleAdjustedDensity z) M M (-(z^2))).det
    let Q := (mixedZeroJetPencil (n:=2*N+1) (poleAdjustedDensity z) F G (-(y^2))).det/
      (mixedZeroJetPencil (n:=2*N+1) (poleAdjustedDensity z) F G (-(z^2))).det
    (y^2/z^2)^2*S ≤ Q ∧ Q ≤ S
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset
noncomputable def zeroJetCombination {n : ℕ} (b : ℕ → ℝ) (a : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ i,a i*zeroJet b i x
lemma jet_first_constant (b : ℕ → ℝ) (hb : b 0 = 0) (x : ℝ) :
    cosineKernelJet (nodalOrder b 0) 0 (b 0) x=1 := by
  simp [nodalOrder,hb,cosineKernelJet_at_zero]
lemma jetCombination_eq_zeroCombination {n : ℕ} (b : ℕ → ℝ) (a : Fin (n+1) → ℝ)
    (hb : b 0 = 0) (ha : jetCombination b a 0 = 0) (x : ℝ) :
    jetCombination b a x=zeroJetCombination b (fun i=>a i.succ) x := by
  have h0 : a 0 + ∑ i : Fin n,a i.succ*cosineKernelJet (nodalOrder b (i.val+1)) 0 (b (i.val+1)) 0 = 0 := by
    simpa only [jetCombination,Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,jet_first_constant b hb,mul_one] using ha
  unfold jetCombination zeroJetCombination zeroJet
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,Fin.val_succ,jet_first_constant b hb,mul_one,mul_sub,sum_sub_distrib]
  linarith
lemma zeroJetCombination_smul {n : ℕ} (b : ℕ → ℝ) (a : Fin n → ℝ) (e x : ℝ) :
    zeroJetCombination b (fun i=>e*a i) x=e*zeroJetCombination b a x := by
  simp only [zeroJetCombination,mul_sum]
  apply sum_congr rfl
  intro i _
  ring
lemma jetTest_zero_at_zero {n : ℕ} (b : ℕ → ℝ) (v : Fin n → ℝ) :
    jetCombination b (jetTestCoeffs b (Fin.cons 0 v)) 0 = 0 := by
  rw [jetTest_eq_det]
  apply Matrix.det_zero_of_column_eq (i:=0) (j:=Fin.succ (0 : Fin (n+1)))
  · exact (Fin.succ_ne_zero _).symm
  · intro k
    simp [jetEvaluation]
/-- The zero-at-the-origin flag has a sign-matching test for each continuous
function with fewer positive zeros than its dimension. This is the exact
flag used in the second oblique chain, not an additional Chebyshev input. -/
theorem zero_jet_flag_sign_matching {m : ℕ} (b : ℕ → ℝ) (f : ℝ → ℝ)
    (hb : Monotone (fun i : Fin (m+1)=>b i)) (hb0 : ∀ i : Fin (m+1),0  ≤  b i)
    (hbfirst : b 0 = 0) (hf : Continuous f) (s : Finset ℝ) (hs : ∀ x  ∈  s,0 < x)
    (hz : ∀ x,0 < x → (f x=0  ↔  x ∈ s)) (hc : s.card < m) :
    ∃ k : ℕ,k+1 ≤ m ∧ ∃ a : Fin (k+1) → ℝ,
      (∀ x,0 < x → 0 ≤ f x*zeroJetCombination b a x) ∧
      (∀ x,0 < x → f x ≠ 0 → 0 < f x*zeroJetCombination b a x) := by
  classical
  obtain ⟨t,ht,e,he,hpos⟩ := finite_zero_sign_polynomial f hf s 0 hs hz
  let o := t.orderIsoOfFin rfl
  let v : Fin t.card → ℝ := fun i=>(o i).val
  have hv : StrictMono v := o.strictMono
  have hvpos i : 0 < v i := hs _ (ht (o i).property)
  let w : Fin (t.card+1) → ℝ := Fin.cons 0 v
  have hw : StrictMono w := by
    intro i j
    refine Fin.cases ?_ (fun i=>?_) i
    · refine Fin.cases (fun h=>False.elim (lt_irrefl _ h)) (fun j _=>hvpos j) j
    · refine Fin.cases (fun h=>False.elim (Fin.not_lt_zero _ h)) (fun j h=>hv (Fin.succ_lt_succ_iff.mp h)) j
  have hw0 (i : Fin (t.card+1)) : 0 ≤ w i := Fin.cases le_rfl (fun i=>(hvpos i).le) i
  have hdim : t.card+1 ≤ m := Nat.add_one_le_iff.mpr ((card_le_card ht).trans_lt hc)
  have hd : t.card+2 ≤ m+1 := by omega
  have hb' : Monotone (fun i : Fin (t.card+2)=>b i) := fun i j hij=>hb (show (i.castLE hd : Fin (m+1)) ≤ j.castLE hd from hij)
  have hb0' (i : Fin (t.card+2)) : 0 ≤ b i := hb0 (i.castLE hd)
  let A : Fin (t.card+2) → ℝ := fun i=>(e*(-1)^(t.card+1))*jetTestCoeffs b w i
  have hA0 : jetCombination b A 0 = 0 := by
    rw [show A=(fun i=>(e*(-1)^(t.card+1))*jetTestCoeffs b w i) from rfl,jetCombination_smul]
    rw [show w=Fin.cons 0 v from rfl,jetTest_zero_at_zero,mul_zero]
  let a : Fin (t.card+1) → ℝ := fun i=>A i.succ
  have hstrict : ∀ x,0 < x → f x ≠ 0 → 0 < f x*zeroJetCombination b a x := by
    intro x hx hfx
    have hxs : x∉s := fun h=>hfx ((hz x hx).mpr h)
    have hxv i : x ≠ v i := fun h=>hxs (h.symm ▸ ht (o i).property)
    have hxw i : x ≠ w i := Fin.cases (ne_of_gt hx) hxv i
    have hp:=hpos x hx hxs
    have hj:=jetTest_sign_product b w hb' hb0' hw hw0 hx.le hxw
    have hprod : (∏ i : Fin t.card,(x-v i))=∏ z ∈ t,(x-z) := by
      calc
        _ = ∏ z : t,(x-z.val) := Equiv.prod_comp o.toEquiv (fun z : t=>x-z.val)
        _ = _ := Finset.prod_attach _ _
    have hneg : (∏ i : Fin (t.card+1),(w i-x))=(-1:ℝ)^(t.card+1)*x*(∏ z ∈ t,(x-z)) := by
      rw [Fin.prod_univ_succ]
      simp only [w,Fin.cons_zero,Fin.cons_succ,zero_sub]
      simp_rw [show ∀ i : Fin t.card,v i-x=(-1:ℝ)*(x-v i) from fun i=>by ring]
      rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,hprod,pow_succ]
      ring
    rw [hneg] at hj
    have hpp:=mul_pos hp hj
    have heq : (f x*(e*∏ z ∈ t,(x-z)))*(jetCombination b (jetTestCoeffs b w) x*
        ((-1:ℝ)^(t.card+1)*x*∏ z ∈ t,(x-z)))=
        (f x*zeroJetCombination b a x)*(x*(∏ z ∈ t,(x-z))^2) := by
      rw [←jetCombination_eq_zeroCombination b A hbfirst hA0]
      dsimp only [A]
      rw [jetCombination_smul]
      ring
    rw [heq] at hpp
    exact pos_of_mul_pos_left hpp (mul_nonneg hx.le (sq_nonneg _))
  refine ⟨t.card,hdim,a,?_,hstrict⟩
  intro x hx
  by_cases hfx : f x=0
  · simp [hfx]
  · exact (hstrict x hx hfx).le
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
