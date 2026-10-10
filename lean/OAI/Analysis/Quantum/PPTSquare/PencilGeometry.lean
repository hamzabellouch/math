import OAI.Analysis.Quantum.PPTSquare.InfinityMinors
import OAI.Analysis.Quantum.PPTSquare.Evaluation
import OAI.Analysis.Quantum.PPTSquare.MatrixSelection

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open Matrix PencilAlgebra PencilEvaluation
namespace PencilGeometry

lemma rows_injective (r : Fin 15) : Function.Injective (rows r) := by
  have h : ∀ r : Fin 15, Function.Injective (rows r) := by decide
  exact h r
lemma row_sets : (Finset.univ : Finset (Fin 6)).powersetCard 4 =
    Finset.univ.image (fun r : Fin 15 => Finset.univ.image (rows r)) := by decide
lemma rows_cover (j : Fin 4 → Fin 6) (hj : Function.Injective j) :
    ∃ r : Fin 15, Set.range (rows r) = Set.range j := by
  classical
  have hc : (Finset.univ.image j).card = 4 := by rw [Finset.card_image_of_injective _ hj]; decide
  have hm : Finset.univ.image j ∈ (Finset.univ : Finset (Fin 6)).powersetCard 4 := by
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and, hc]
  rw [row_sets] at hm
  obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hm
  refine ⟨r, ?_⟩
  ext i
  have hi := congrArg (fun s : Finset (Fin 6) => i ∈ s) hr
  simpa using hi

variable {K : Type*} [Field K]
lemma rank_lt_iff (x : Fin 4 → K) : (pencil x).rank < 4 ↔ minors x = 0 := by
  classical
  constructor
  · intro h
    ext r
    change ((pencil x).submatrix (rows r) id).det = 0
    by_contra hn
    have hh : ((pencil x).submatrix (rows r) id).rank = 4 := by
      simpa using Matrix.rank_of_det_ne_zero hn
    have hl := Matrix.rank_submatrix_le (pencil x) (rows r) (id : Fin 4 → Fin 4)
    omega
  · intro h
    apply MatrixSelection.rank_lt_of_all_row_minors_zero
    intro j hj
    obtain ⟨r,hr⟩ := rows_cover j hj
    have hc : ∀ i : Fin 4, ∃ a, rows r a = j i := by
      intro i
      change j i ∈ Set.range (rows r)
      rw [hr]
      exact Set.mem_range_self i
    choose p hp using hc
    have hi : Function.Injective p := by
      intro i j hh
      apply hj
      rw [← hp i, ← hp j, hh]
    let e : Equiv.Perm (Fin 4) := Equiv.ofBijective p ⟨hi,Finite.surjective_of_injective hi⟩
    have he : (pencil x).submatrix j id = ((pencil x).submatrix (rows r) id).submatrix e id := by
      ext i a
      simp only [Matrix.submatrix_apply, id_eq]
      exact congrArg (fun z => pencil x z a) (hp i).symm
    rw [he, Matrix.det_permute]
    have hh := congrFun h r
    change ((pencil x).submatrix (rows r) id).det = 0 at hh
    rw [hh, mul_zero]

variable [CharZero K]
abbrev Hk : Matrix (Fin 15) (Fin 15) K := H.map (Int.castRingHom K)
abbrev Ck : Matrix (Fin 15) (Fin 20) K := CNum.map (Int.castRingHom K)
abbrev Dk : Matrix (Fin 15) (Fin 20) K := D.map (Int.castRingHom K)
omit [CharZero K] in
lemma H_product : Hk (K := K) * HinvNum.map (Int.castRingHom K) = (denominator : K) • 1 := by
  rw [← Matrix.map_mul, H_Hinv]
  ext i j
  change ((denominator * (1 : Matrix (Fin 15) (Fin 15) ℤ) i j : ℤ) : K) = (denominator : K) * (1 : Matrix (Fin 15) (Fin 15) K) i j
  simp [Matrix.one_apply]
omit [CharZero K] in
lemma HC_product : Hk (K := K) * Ck (K := K) = (-(denominator : K)) • Dk (K := K) := by
  rw [← Matrix.map_mul, H_C]
  ext i j
  change (((-denominator) * D i j : ℤ) : K) = (-(denominator : K)) * (D i j : K)
  simp
lemma H_unit : IsUnit (Hk (K := K)) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have hh := congrArg Matrix.det (H_product (K := K))
  rw [Matrix.det_mul, hz, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at hh
  exact pow_ne_zero 15 (denominator_ne (K := K)) hh.symm
omit [CharZero K] in
lemma HC_vec (z : Fin 20 → K) : Hk.mulVec (Ck.mulVec z) = (-(denominator : K)) • Dk.mulVec z := by
  rw [Matrix.mulVec_mulVec, HC_product, Matrix.smul_mulVec]
lemma minors_zero_iff (t : Fin 3 → K) : minors ![1,t 0,t 1,t 2] = 0 ↔
    Ck.mulVec (lowMon t) = (denominator : K) • highMon t := by
  have hi := Matrix.mulVec_injective_iff_isUnit.mpr (H_unit (K := K))
  have hmul := HC_vec (K := K) (lowMon t)
  have hm : minors ![1,t 0,t 1,t 2] = Dk.mulVec (lowMon t) + Hk.mulVec (highMon t) :=
    minors_affine t
  constructor
  · intro hz
    apply hi
    rw [Matrix.mulVec_smul]
    ext i
    have ha := congrFun (hm.symm.trans hz) i
    have hb := congrFun hmul i
    simp only [Pi.add_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at ha hb ⊢
    linear_combination hb - (denominator : K)*ha
  · intro hz
    ext i
    have hb := congrFun hmul i
    rw [hz, Matrix.mulVec_smul] at hb
    rw [hm]
    simp only [Pi.add_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at hb ⊢
    apply (mul_left_cancel₀ (denominator_ne (K := K)))
    linear_combination hb

lemma eigen_of_minors (t : Fin 3 → K) (h : minors ![1,t 0,t 1,t 2] = 0) (a : Fin 3) :
    lowMon t ᵥ* action a = ((denominator : K) * t a) • lowMon t := by
  have hh := (minors_zero_iff t).mp h
  ext j
  by_cases hj : (j : ℕ) < 10
  · let j' : Fin 10 := ⟨j,hj⟩
    have hje : j = j'.castLE (by decide) := Fin.ext rfl
    rw [hje, low_vecMul, low_step]
    change _ = ((denominator : K)*t a)*lowMon t _
    ring
  · let j' : Fin 10 := ⟨(j : ℕ)-10,by omega⟩
    have hje : j = j'.natAdd 10 := Fin.ext (by dsimp [j']; omega)
    rw [hje, high_vecMul, hh]
    simp only [Pi.smul_apply, smul_eq_mul, high_step]
    ring

lemma minors_of_eigen (t : Fin 3 → K)
    (h : ∀ a : Fin 3, lowMon t ᵥ* action a = ((denominator : K) * t a) • lowMon t) :
    minors ![1,t 0,t 1,t 2] = 0 := by
  apply (minors_zero_iff t).mpr
  ext i
  obtain ⟨⟨a,j⟩,hij⟩ := highNext_surjective i
  subst i
  have hh := congrFun (h a) (j.natAdd 10)
  rw [high_vecMul] at hh
  simp only [Pi.smul_apply, smul_eq_mul, high_step]
  simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc] using hh

lemma infinity_zero (t : Fin 3 → K) (h : minors ![0,t 0,t 1,t 2] = 0) : t = 0 := by
  have hz : highMon t = 0 := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr (H_unit (K := K))
    have hh := (minors_infinity t).symm.trans h
    have he : PencilAlgebra.w t = highMon t := rfl
    rw [he] at hh
    simpa only [Matrix.mulVec_zero] using hh
  have h0 := congrFun hz 14
  have h1 := congrFun hz 4
  have h2 := congrFun hz 0
  have hh0 : t 0 ^ 4 = 0 := by simpa [highMon, highExp, Fin.prod_univ_succ] using h0
  have hh1 : t 1 ^ 4 = 0 := by simpa [highMon, highExp, Fin.prod_univ_succ] using h1
  have hh2 : t 2 ^ 4 = 0 := by simpa [highMon, highExp, Fin.prod_univ_succ] using h2
  ext a
  fin_cases a
  · exact (pow_eq_zero_iff (by decide)).mp hh0
  · exact (pow_eq_zero_iff (by decide)).mp hh1
  · exact (pow_eq_zero_iff (by decide)).mp hh2
end PencilGeometry

end

end OAI
