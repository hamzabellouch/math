import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

namespace OAI

/-! Coercivity, determinants, and positive matrix scaling maps. -/

section

noncomputable section
namespace Kaplansky

def scalingScalar (ε t : ℝ) : ℝ := 2*Real.log (1+ε*t) - (3/2)*Real.log t

/-- The endpoint lower bound which controls t approaching zero. -/
theorem scalingScalar_lower_small {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    -(3/2)*Real.log t ≤ scalingScalar ε t := by
  have h : 0 ≤ Real.log (1+ε*t) := Real.log_nonneg (by nlinarith [mul_pos hε ht])
  dsimp [scalingScalar]
  linarith

/-- The endpoint lower bound which controls t approaching infinity. -/
theorem scalingScalar_lower_large {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    2*Real.log ε + (1/2)*Real.log t ≤ scalingScalar ε t := by
  have h : Real.log (ε*t) ≤ Real.log (1+ε*t) :=
    Real.log_le_log (mul_pos hε ht) (by linarith)
  rw [Real.log_mul (ne_of_gt hε) (ne_of_gt ht)] at h
  dsimp [scalingScalar]
  linarith

/-- A uniform lower bound, without importing a minimizer assumption. -/
theorem scalingScalar_bounded_below {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    (3/2)*Real.log ε ≤ scalingScalar ε t := by
  have h1 := scalingScalar_lower_small hε ht
  have h2 := scalingScalar_lower_large hε ht
  linarith

theorem scalingScalar_sublevel {ε t C : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (hf : scalingScalar ε t ≤ C) :
    Real.exp (-2*C/3) ≤ t ∧ t ≤ Real.exp (2*C-4*Real.log ε) := by
  have h1 := scalingScalar_lower_small hε ht
  have h2 := scalingScalar_lower_large hε ht
  have hlo : -2*C/3 ≤ Real.log t := by linarith
  have hhi : Real.log t ≤ 2*C-4*Real.log ε := by linarith
  constructor
  · simpa only [Real.exp_log ht] using Real.exp_le_exp.mpr hlo
  · simpa only [Real.exp_log ht] using Real.exp_le_exp.mpr hhi

open scoped BigOperators

theorem scaling_eigenvalue_bounds {d : ℕ} {ε C : ℝ} (hε : 0 < ε)
    (eigs : Fin d → ℝ) (heigs : ∀ i, 0 < eigs i)
    (hsum : ∑ i, scalingScalar ε (eigs i) ≤ C) (i : Fin d) :
    let B := C - (d-1) * ((3/2)*Real.log ε)
    Real.exp (-2*B/3) ≤ eigs i ∧ eigs i ≤ Real.exp (2*B-4*Real.log ε) := by
  let b := (3/2)*Real.log ε
  have hb (j : Fin d) : b ≤ scalingScalar ε (eigs j) := scalingScalar_bounded_below hε (heigs j)
  have hi := Finset.single_le_sum (s := Finset.univ)
    (f := fun j => scalingScalar ε (eigs j) - b)
    (fun j _ => sub_nonneg.mpr (hb j)) (Finset.mem_univ i)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hi
  apply scalingScalar_sublevel hε (heigs i)
  change scalingScalar ε (eigs i) ≤ C - (d-1)*b
  linarith

end Kaplansky

end
end

section

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Kaplansky

/-- The ordered spectrum, with the matrix cardinality reduced to its size. -/
def decreasingEigenvalues {r : ℕ} {A : Matrix (Fin r) (Fin r) ℂ}
    (hA : A.IsHermitian) : Fin r → ℝ :=
  fun i => hA.eigenvalues₀ (Fin.cast (Fintype.card_fin r).symm i)

theorem decreasingEigenvalues_antitone {r : ℕ} {A : Matrix (Fin r) (Fin r) ℂ}
    (hA : A.IsHermitian) : Antitone (decreasingEigenvalues hA) := by
  intro i j hij
  exact hA.eigenvalues₀_antitone hij

theorem det_one_add_eq_prod {r : ℕ} {A : Matrix (Fin r) (Fin r) ℂ}
    (hA : A.IsHermitian) :
    (1 + A).det = ∏ i, ((1 + decreasingEigenvalues hA i : ℝ) : ℂ) := by
  have h : (1 + A).det = ∏ i, ((1 + hA.eigenvalues i : ℝ) : ℂ) := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [← map_one (Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary), ← map_add]
    rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul_comm, ← mul_assoc,
      Unitary.coe_star_mul_self, one_mul]
    simp only [← Matrix.diagonal_one,
      Matrix.diagonal_add, Matrix.det_diagonal, Function.comp_apply, Complex.ofReal_add, Complex.ofReal_one]
    rfl
  rw [h]
  let e : Fin (Fintype.card (Fin r)) ≃ Fin r :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let f := fun i => ((1 + hA.eigenvalues₀ i : ℝ) : ℂ)
  change (∏ i, f (e.symm i)) = ∏ i, f ((finCongr (Fintype.card_fin r).symm) i)
  exact (e.symm.prod_comp f).trans ((finCongr (Fintype.card_fin r).symm).prod_comp f).symm

theorem decreasingEigenvalues_nonneg {r : ℕ} {A : Matrix (Fin r) (Fin r) ℂ}
    (hA : A.PosSemidef) (i : Fin r) : 0 ≤ decreasingEigenvalues hA.1 i := by
  let e : Fin (Fintype.card (Fin r)) ≃ Fin r :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  change 0 ≤ hA.1.eigenvalues₀ (Fin.cast (Fintype.card_fin r).symm i)
  have h := hA.eigenvalues_nonneg (e (Fin.cast (Fintype.card_fin r).symm i))
  change 0 ≤ hA.1.eigenvalues₀ (e.symm (e (Fin.cast (Fintype.card_fin r).symm i))) at h
  simpa only [Equiv.symm_apply_apply] using h

/-- Real logarithm of the positive determinant, not the complex logarithm. -/
theorem log_det_one_add {r : ℕ} {A : Matrix (Fin r) (Fin r) ℂ}
    (hA : A.PosSemidef) :
    Real.log ((1 + A).det.re) = ∑ i, Real.log (1 + decreasingEigenvalues hA.1 i) := by
  rw [det_one_add_eq_prod hA.1, ← Complex.ofReal_prod, Complex.ofReal_re]
  exact Real.log_prod (fun i _ => ne_of_gt (by linarith [decreasingEigenvalues_nonneg hA i]))

theorem paired_log_sum {d r : ℕ} (hdr : 2*d ≤ r)
    (μ : Fin r → ℝ) (hμ : Antitone μ) (hμ0 : ∀ i, 0 ≤ μ i)
    (lam : Fin d → ℝ) (hlam : ∀ i, 0 < lam i) {ε : ℝ} (hε : 0 < ε)
    (hbound : ∀ s : Fin d, ε * lam s ≤ μ ⟨2*s.val+1, by omega⟩) :
    2 * ∑ s, Real.log (1+ε*lam s) ≤ ∑ j, Real.log (1+μ j) := by
  let f : Fin d × Fin 2 → Fin r := fun p => ⟨2*p.1.val+p.2.val, by omega⟩
  have hf : Function.Injective f := by
    intro ⟨i,a⟩ ⟨j,b⟩ h
    have hv := congrArg Fin.val h
    dsimp [f] at hv
    have hab : a = b := Fin.ext (by omega)
    have hij : i = j := Fin.ext (by omega)
    simp [hab, hij]
  have hpair : ∀ p : Fin d × Fin 2,
      Real.log (1+ε*lam p.1) ≤ Real.log (1+μ (f p)) := by
    intro p
    apply Real.log_le_log (by nlinarith [mul_pos hε (hlam p.1)])
    have hm := hμ (show f p ≤ ⟨2*p.1.val+1, by omega⟩ from by
      change 2*p.1.val+p.2.val ≤ 2*p.1.val+1; omega)
    linarith [hbound p.1]
  calc
    2 * ∑ s, Real.log (1+ε*lam s) =
        ∑ p : Fin d × Fin 2, Real.log (1+ε*lam p.1) := by
      simp [Fintype.sum_prod_type, ← Finset.sum_add_distrib, two_mul]
    _ ≤ ∑ p : Fin d × Fin 2, Real.log (1+μ (f p)) :=
      Finset.sum_le_sum (fun p _ => hpair p)
    _ ≤ ∑ j, Real.log (1+μ j) :=
      by
        have he := Finset.sum_image (f := fun j : Fin r => Real.log (1+μ j))
          (s := (Finset.univ : Finset (Fin d × Fin 2))) (g := f)
          (fun _ _ _ _ h => hf h)
        rw [← he]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => Real.log_nonneg (by linarith [hμ0 j]))

theorem scaling_log_det_of_spectral_bound {d r : ℕ} (hdr : 2*d ≤ r)
    {A : Matrix (Fin r) (Fin r) ℂ} (hA : A.PosSemidef)
    (lam : Fin d → ℝ) (hlam : ∀ i, 0 < lam i) {ε : ℝ} (hε : 0 < ε)
    (hbound : ∀ s : Fin d,
      ε * lam s ≤ decreasingEigenvalues hA.1 ⟨2*s.val+1, by omega⟩) :
    2 * ∑ s, Real.log (1+ε*lam s) ≤ Real.log ((1+A).det.re) := by
  rw [log_det_one_add hA]
  exact paired_log_sum hdr _ (decreasingEigenvalues_antitone hA.1)
    (decreasingEigenvalues_nonneg hA) lam hlam hε hbound

end Kaplansky

end
end

section

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Kaplansky
variable {n d r : ℕ}

def scalingMap (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  ∑ i, T i * P * (T i)ᴴ

theorem scalingMap_positive (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosSemidef) :
    (scalingMap T P).PosSemidef :=
  Matrix.posSemidef_sum _ (fun i _ => hP.mul_mul_conjTranspose_same (T i))

theorem scalingMap_sub (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (P Q : Matrix (Fin d) (Fin d) ℂ) :
    scalingMap T (P-Q) = scalingMap T P - scalingMap T Q := by
  simp [scalingMap, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

theorem scalingMap_smul (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ) (c : ℝ) :
    scalingMap T (c • P) = c • scalingMap T P := by
  simp [scalingMap, Finset.smul_sum]

theorem scalingMap_comparison (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    {P p : Matrix (Fin d) (Fin d) ℂ} (c : ℝ)
    (h : (P-c • p).PosSemidef) :
    (scalingMap T P - c • scalingMap T p).PosSemidef := by
  simpa only [scalingMap_sub, scalingMap_smul] using scalingMap_positive T h

/-- A sum of Gram matrices has exactly the common kernel. -/
theorem sum_gram_mulVec_zero_iff (B : Fin n → Matrix (Fin d) (Fin r) ℂ)
    (v : Fin r → ℂ) :
    (∑ i, (B i)ᴴ * B i) *ᵥ v = 0 ↔ ∀ i, B i *ᵥ v = 0 := by
  constructor
  · intro h
    have hq := congrArg (fun w => star v ⬝ᵥ w) h
    simp only [Matrix.sum_mulVec, dotProduct_sum, dotProduct_zero] at hq
    have he (i : Fin n) : star v ⬝ᵥ (((B i)ᴴ * B i) *ᵥ v) =
        star (B i *ᵥ v) ⬝ᵥ (B i *ᵥ v) := by
      rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star]
    simp_rw [he] at hq
    have hn (i : Fin n) : 0 ≤ star (B i *ᵥ v) ⬝ᵥ (B i *ᵥ v) :=
      Finset.sum_nonneg (fun j _ => star_mul_self_nonneg _)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn i)).mp hq
    exact fun i => dotProduct_star_self_eq_zero.mp (hz i (Finset.mem_univ i))
  · intro h
    simp [Matrix.sum_mulVec, ← mulVec_mulVec, h]

theorem scalingMap_projection_kernel (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    {p : Matrix (Fin d) (Fin d) ℂ} (hp : p.IsHermitian) (hpp : p*p = p)
    (v : Fin r → ℂ) :
    scalingMap T p *ᵥ v = 0 ↔ ∀ i, p *ᵥ ((T i)ᴴ *ᵥ v) = 0 := by
  have he : scalingMap T p = ∑ i, (p * (T i)ᴴ)ᴴ * (p * (T i)ᴴ) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hp.eq]
    simp only [← Matrix.mul_assoc, Matrix.mul_assoc (T i) p p, hpp]
  rw [he, sum_gram_mulVec_zero_iff]
  simp only [mulVec_mulVec]

theorem decreasingEigenvalues_pos_of_lt_rank {A : Matrix (Fin r) (Fin r) ℂ}
    (hA : A.PosSemidef) (k : Fin r) (hk : k.val < A.rank) :
    0 < decreasingEigenvalues hA.1 k := by
  let e : Fin (Fintype.card (Fin r)) ≃ Fin r :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let e' : Fin r ≃ Fin r := (finCongr (Fintype.card_fin r).symm).trans e
  have he (i : Fin r) : hA.1.eigenvalues (e' i) = decreasingEigenvalues hA.1 i := by
    change hA.1.eigenvalues₀ (e.symm (e (Fin.cast (Fintype.card_fin r).symm i))) = _
    simp only [Equiv.symm_apply_apply, decreasingEigenvalues]
  have hrank : A.rank = Fintype.card {i // decreasingEigenvalues hA.1 i ≠ 0} := by
    rw [hA.1.rank_eq_card_non_zero_eigs]
    exact (Fintype.card_congr (Equiv.subtypeEquiv e' (fun i => by rw [he]))).symm
  by_contra h
  have hk0 : decreasingEigenvalues hA.1 k = 0 :=
    le_antisymm (le_of_not_gt h) (decreasingEigenvalues_nonneg hA k)
  have hi : ∀ i, decreasingEigenvalues hA.1 i ≠ 0 → i.val < k.val := by
    intro i hne
    by_contra hlt
    have hm := decreasingEigenvalues_antitone hA.1 (show k ≤ i from Nat.le_of_not_gt hlt)
    exact hne (le_antisymm (hk0 ▸ hm) (decreasingEigenvalues_nonneg hA i))
  let f : {i // decreasingEigenvalues hA.1 i ≠ 0} → Fin k.val :=
    fun i => ⟨i.val.val, hi i.val i.property⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact Subtype.ext (Fin.ext (congrArg (fun z : Fin k.val => z.val) hij))
  have hc := Fintype.card_le_of_injective f hf
  rw [← hrank, Fintype.card_fin] at hc
  omega

end Kaplansky

end
end

section

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Kaplansky
variable {n d r : ℕ}

/-- Concatenation of all projected maps, whose range is their collective image. -/
def collectiveMatrix (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (p : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin r) (Fin n × Fin d) ℂ :=
  fun a j => (T j.1 * p) a j.2

theorem collectiveMatrix_mulVec (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (p : Matrix (Fin d) (Fin d) ℂ) (v : Fin n × Fin d → ℂ) :
    collectiveMatrix T p *ᵥ v = ∑ i, (T i * p) *ᵥ (fun b => v (i,b)) := by
  ext a
  simp [collectiveMatrix, mulVec, dotProduct, Fintype.sum_prod_type]

theorem collectiveMatrix_range (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (p : Matrix (Fin d) (Fin d) ℂ) :
    LinearMap.range (collectiveMatrix T p).mulVecLin =
      ⨆ i, LinearMap.range (T i * p).mulVecLin := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    change collectiveMatrix T p *ᵥ v ∈ _
    rw [collectiveMatrix_mulVec]
    apply Submodule.sum_mem
    intro i _
    exact (le_iSup (fun i => LinearMap.range (T i * p).mulVecLin) i)
      ⟨fun b => v (i,b), rfl⟩
  · apply iSup_le
    intro i v hv
    obtain ⟨w,rfl⟩ := hv
    refine ⟨fun j => if j.1 = i then w j.2 else 0, ?_⟩
    change collectiveMatrix T p *ᵥ _ = (T i * p) *ᵥ w
    rw [collectiveMatrix_mulVec]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      have hz : (fun b => if j=i then w b else 0) = (0 : Fin d → ℂ) := by
        funext b; simp [hji]
      rw [hz, Matrix.mulVec_zero]
    · simp

theorem scalingMap_eq_collective_gram (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    {p : Matrix (Fin d) (Fin d) ℂ} (hp : p.IsHermitian) (hpp : p*p=p) :
    scalingMap T p = collectiveMatrix T p * (collectiveMatrix T p)ᴴ := by
  have hi (i : Fin n) : T i * p * (T i)ᴴ = (T i * p) * (T i * p)ᴴ := by
    simp only [conjTranspose_mul, hp.eq]
    simp only [← Matrix.mul_assoc, Matrix.mul_assoc (T i) p p, hpp]
  ext a b
  simp only [scalingMap, Matrix.sum_apply, hi, Matrix.mul_apply,
    collectiveMatrix, conjTranspose_apply, Fintype.sum_prod_type]

theorem scalingMap_projection_rank (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (hexpand : ∀ S : Submodule ℂ (Fin d → ℂ),
      2 * Module.finrank ℂ S ≤ Module.finrank ℂ (⨆ i, S.map (T i).mulVecLin : Submodule ℂ (Fin r → ℂ)))
    {p : Matrix (Fin d) (Fin d) ℂ} (hp : p.IsHermitian) (hpp : p*p=p) :
    2*p.rank ≤ (scalingMap T p).rank := by
  rw [scalingMap_eq_collective_gram T hp hpp, Matrix.rank_self_mul_conjTranspose]
  change 2 * Module.finrank ℂ (LinearMap.range p.mulVecLin) ≤
    Module.finrank ℂ (LinearMap.range (collectiveMatrix T p).mulVecLin)
  rw [collectiveMatrix_range]
  have h := hexpand (LinearMap.range p.mulVecLin)
  have he (i : Fin n) : LinearMap.range (T i * p).mulVecLin =
      (LinearMap.range p.mulVecLin).map (T i).mulVecLin := by
    rw [Matrix.mulVecLin_mul, LinearMap.range_comp]
  rw [show (⨆ i, LinearMap.range (T i * p).mulVecLin) =
      (⨆ i, (LinearMap.range p.mulVecLin).map (T i).mulVecLin) from iSup_congr he]
  exact h

theorem scalingMap_projection_positive (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    {p : Matrix (Fin d) (Fin d) ℂ} (hp : p.IsHermitian) (hpp : p*p=p) :
    (scalingMap T p).PosSemidef := by
  rw [scalingMap_eq_collective_gram T hp hpp]
  exact posSemidef_self_mul_conjTranspose _

/-- Pointwise positivity of the 2s-th eigenvalue, with s=rank(p)>0.
The uniform positive minimum over the projection bundle is still separate. -/
theorem scalingMap_projection_eigenvalue_pos
    (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (hexpand : ∀ S : Submodule ℂ (Fin d → ℂ),
      2 * Module.finrank ℂ S ≤ Module.finrank ℂ (⨆ i, S.map (T i).mulVecLin : Submodule ℂ (Fin r → ℂ)))
    {p : Matrix (Fin d) (Fin d) ℂ} (hp : p.IsHermitian) (hpp : p*p=p)
    (hpos : 0 < p.rank) :
    ∃ k : Fin r, k.val+1 = 2*p.rank ∧
      0 < decreasingEigenvalues (scalingMap_projection_positive T hp hpp).1 k := by
  have hrank := scalingMap_projection_rank T hexpand hp hpp
  have hr := Matrix.rank_le_card_width (scalingMap T p)
  simp only [Fintype.card_fin] at hr
  let k : Fin r := ⟨2*p.rank-1, by omega⟩
  refine ⟨k, by dsimp [k]; omega, ?_⟩
  exact decreasingEigenvalues_pos_of_lt_rank (scalingMap_projection_positive T hp hpp) k
    (by dsimp [k]; omega)

end Kaplansky

end
end

end OAI
