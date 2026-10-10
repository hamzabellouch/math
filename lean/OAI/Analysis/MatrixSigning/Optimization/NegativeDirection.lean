import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.EliminationCompleteness
import OAI.Analysis.MatrixSigning.Optimization.SqSum

namespace OAI

open Matrix

namespace CurrentKS.RationalRoot

section
open Matrix
open scoped BigOperators

variable {N : ℕ}

def negativeDirection (M : Matrix (Fin N) (Fin N) ℚ) (β : ℚ) : Option (Fin N → ℚ) :=
  (KS.W17.rationalNegativeWitness N M).map (fun v => normalize v β)

lemma quadratic_scale (M : Matrix (Fin N) (Fin N) ℚ) (v : Fin N → ℚ) (c : ℚ) :
    (fun i => c*v i) ⬝ᵥ (M *ᵥ (fun i => c*v i)) = c^2*(v ⬝ᵥ (M *ᵥ v)) := by
  simp only [dotProduct,mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem negativeDirection_spec (M : Matrix (Fin N) (Fin N) ℚ) (hM : M.IsSymm)
    (β : ℚ) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    match negativeDirection M β with
    | none => (M.map (fun q : ℚ => (q:ℝ))).PosSemidef
    | some w => 1-(β:ℝ) ≤ ‖realVector w‖ ∧ ‖realVector w‖ ≤ 1 ∧ w ⬝ᵥ (M *ᵥ w) < 0 := by
  unfold negativeDirection
  cases he : KS.W17.rationalNegativeWitness N M with
  | none => exact KS.W17.rationalNegativeWitness_none_psd N M hM he
  | some v =>
    simp only [Option.map_some]
    have hv := KS.W17.rationalNegativeWitness_sound N M hM v he
    have hv0 : v ≠ 0 := by
      intro h
      simp only [h,Matrix.mulVec_zero,dotProduct_zero] at hv
      exact (lt_irrefl 0 hv)
    obtain ⟨hl,hu,c,hc,hwe⟩ := normalize_spec v hv0 β hβ hβ1
    refine ⟨hl,hu,?_⟩
    rw [hwe,quadratic_scale]
    exact mul_neg_of_pos_of_neg (sq_pos_of_pos hc) hv
end

open scoped BigOperators

variable {N : ℕ}

def nearest (t : ℚ) : ℤ :=
  if 0 ≤ t then ⌈t-1/2⌉ else -⌈-t-1/2⌉

def roundMesh (ρ : ℚ) (v : Fin N → ℚ) : Fin N → ℚ :=
  fun i => ρ*(nearest (v i/ρ):ℚ)

lemma nearest_error (t : ℚ) : |(nearest t:ℚ)-t| ≤ 1/2 := by
  unfold nearest
  split_ifs with ht
  · have hl := Int.le_ceil (t-1/2)
    have hu := Int.ceil_lt_add_one (t-1/2)
    rw [abs_le]
    constructor <;> linarith
  · have hl := Int.le_ceil (-t-1/2)
    have hu := Int.ceil_lt_add_one (-t-1/2)
    rw [Int.cast_neg,abs_le]
    constructor <;> linarith

lemma roundMesh_coord_error (ρ : ℚ) (hρ : 0 < ρ) (v : Fin N → ℚ) (i : Fin N) :
    |roundMesh ρ v i-v i| ≤ ρ/2 := by
  have he : roundMesh ρ v i-v i=ρ*((nearest (v i/ρ):ℚ)-v i/ρ) := by
    dsimp [roundMesh]
    field_simp
  rw [he,abs_mul,abs_of_pos hρ]
  exact (mul_le_mul_of_nonneg_left (nearest_error _) hρ.le).trans_eq (by ring)

lemma norm_le_sum_abs (v : EuclideanSpace ℝ (Fin N)) : ‖v‖ ≤ ∑ i,|v i| := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_iff.mpr
  refine ⟨Finset.sum_nonneg (fun _ _ => abs_nonneg _),?_⟩
  simpa only [Real.norm_eq_abs] using
    Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (fun i _ => abs_nonneg (v i))

lemma roundMesh_error (ρ : ℚ) (hρ : 0 < ρ) (v : Fin N → ℚ) :
    ‖realVector (roundMesh ρ v)-realVector v‖ ≤ N*(ρ:ℝ)/2 := by
  apply (norm_le_sum_abs _).trans
  calc
    (∑ i, |(realVector (roundMesh ρ v)-realVector v) i|) ≤ ∑ _ : Fin N,(ρ:ℝ)/2 := by
      apply Finset.sum_le_sum
      intro i _
      change |(roundMesh ρ v i:ℝ)-(v i:ℝ)| ≤ (ρ:ℝ)/2
      exact_mod_cast roundMesh_coord_error ρ hρ v i
    _ = N*(ρ:ℝ)/2 := by simp; ring

lemma realVector_scale (v : Fin N → ℚ) (c : ℚ) :
    realVector (fun i => c*v i)=(c:ℝ) • realVector v := by
  apply PiLp.ext
  intro i
  simp only [realVector,WithLp.ofLp_toLp,PiLp.smul_apply,smul_eq_mul,Rat.cast_mul]

theorem curvature_rounding (w : Fin N → ℚ) (s τ ρ : ℚ)
    (hs : 0 ≤ s) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hρ : 0 < ρ)
    (hmesh : (N:ℚ)*ρ/2 ≤ s*τ/8) (hw : ‖realVector w‖ ≤ 1) :
    let q := roundMesh ρ (fun i => s*(1-τ)*w i)
    ‖realVector q-((s:ℝ)*(1-(τ:ℝ))) • realVector w‖ ≤ (s:ℝ)*τ/8 ∧
    ‖realVector q‖ ≤ s ∧
    ‖realVector q-(s:ℝ) • realVector w‖ ≤ 9*(s:ℝ)*τ/8 := by
  let q := roundMesh ρ (fun i => s*(1-τ)*w i)
  have hs' : (0:ℝ) ≤ s := by exact_mod_cast hs
  have ht' : (0:ℝ) ≤ τ := by exact_mod_cast hτ
  have ht1' : (τ:ℝ) ≤ 1 := by exact_mod_cast hτ1
  have hm : (N:ℝ)*(ρ:ℝ)/2 ≤ (s:ℝ)*τ/8 := by exact_mod_cast hmesh
  have he := (roundMesh_error ρ hρ (fun i => s*(1-τ)*w i)).trans hm
  rw [realVector_scale] at he
  push_cast at he
  have ht : ‖((s:ℝ)*(1-(τ:ℝ))) • realVector w‖ ≤ (s:ℝ)*(1-(τ:ℝ)) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hs' (sub_nonneg.mpr ht1'))]
    exact mul_le_of_le_one_right (mul_nonneg hs' (sub_nonneg.mpr ht1')) hw
  have hqn : ‖realVector q‖ ≤ s := by
    have hb := norm_le_norm_sub_add (realVector q) (((s:ℝ)*(1-(τ:ℝ))) • realVector w)
    nlinarith [mul_nonneg hs' ht']
  refine ⟨he,hqn,?_⟩
  have hd : ‖((s:ℝ)*(1-(τ:ℝ))) • realVector w-(s:ℝ) • realVector w‖ ≤ (s:ℝ)*τ := by
    rw [← sub_smul,norm_smul,Real.norm_eq_abs]
    have hx : (s:ℝ)*(1-(τ:ℝ))-(s:ℝ) = -((s:ℝ)*τ) := by ring
    rw [hx,abs_neg,abs_of_nonneg (mul_nonneg hs' ht')]
    exact mul_le_of_le_one_right (mul_nonneg hs' ht') hw
  have hb := norm_sub_le_norm_sub_add_norm_sub (realVector q) (((s:ℝ)*(1-(τ:ℝ))) • realVector w) ((s:ℝ) • realVector w)
  linarith
end CurrentKS.RationalRoot

end OAI
