import OAI.InformationTheory.Entanglement.FidelityTools

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {n : Type} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
lemma psd_diagonal_real {A : Mat n} (hA : A.PosSemidef) (i : n) :
    0≤(A i i).re := (Complex.nonneg_iff.mp (hA.diag_nonneg (i := i))).1

lemma powers_stormer_diagonal {A B : Mat n} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (z : n → ℝ) (hz : A-B=Matrix.diagonal (fun i => (z i : ℂ))) :
    ∑ i, (z i)^2 ≤ traceNorm (A*A-B*B) := by
  let ε : n → ℝ := fun i => if z i<0 then -1 else 1
  have hε (i : n) : ε i * z i=|z i| := by
    dsimp [ε]
    split_ifs with hi
    · rw [abs_of_neg hi]; ring
    · rw [abs_of_nonneg (le_of_not_gt hi)]; ring
  have hεsq (i : n) : ε i*ε i=1 := by dsimp [ε]; split_ifs <;> norm_num
  let S : Mat n := Matrix.diagonal (fun i => (ε i : ℂ))
  have hS : Sᴴ*S=1 := by
    simp only [S,Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i=j
    · subst j
      simp only [Matrix.diagonal_apply_eq,Matrix.one_apply_eq,Pi.star_apply,Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul,hεsq,
        Complex.ofReal_one]
    · simp [Matrix.diagonal_apply_ne _ h,Matrix.one_apply_ne h]
  have he : A*A-B*B=(A-B)*A+B*(A-B) := by noncomm_ring
  have ht : (Matrix.trace (S*(A*A-B*B))).re =
      ∑ i, |z i| *((A i i).re+(B i i).re) := by
    rw [he,hz]
    change (∑ i, (S*((diagonal (fun j => (z j : ℂ)))*A+B*diagonal (fun j => (z j : ℂ)))) i i).re = _
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [S,Matrix.add_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,
      Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,
      sub_zero]
    calc
      ε i * (z i*(A i i).re+(B i i).re*z i)=
          (ε i*z i)*((A i i).re+(B i i).re) := by ring
      _ = _ := by rw [hε]
  have hdiag (i : n) : (A i i).re-(B i i).re=z i := by
    have h := congrArg (fun M : Mat n => (M i i).re) hz
    simpa only [Matrix.sub_apply,Complex.sub_re,Matrix.diagonal_apply_eq,Complex.ofReal_re] using h
  have hi (i : n) : (z i)^2 ≤ |z i| *((A i i).re+(B i i).re) := by
    have habs : |z i| ≤ (A i i).re+(B i i).re := abs_le.mpr ⟨by
      linarith [hdiag i,psd_diagonal_real hA i,psd_diagonal_real hB i],by
      linarith [hdiag i,psd_diagonal_real hA i,psd_diagonal_real hB i]⟩
    have h := mul_le_mul_of_nonneg_left habs (abs_nonneg (z i))
    nlinarith [sq_abs (z i)]
  calc
    ∑ i, (z i)^2 ≤ ∑ i, |z i| *((A i i).re+(B i i).re) :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = (Matrix.trace (S*(A*A-B*B))).re := ht.symm
    _ ≤ ‖Matrix.trace (S*(A*A-B*B))‖ := Complex.re_le_norm _
    _ ≤ traceNorm (A*A-B*B) := trace_unitary_norm_le _ hS

lemma powers_stormer {A B : Mat n} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.trace ((A-B)*(A-B))).re ≤ traceNorm (A*A-B*B) := by
  let Z := A-B
  have hZ : Z.IsHermitian := hA.isHermitian.sub hB.isHermitian
  obtain ⟨U,hU,hdiag⟩ := unitary_spectral hZ
  let a := Uᴴ*A*U
  let b := Uᴴ*B*U
  have ha : a.PosSemidef := hA.conjTranspose_mul_mul_same U
  have hb : b.PosSemidef := hB.conjTranspose_mul_mul_same U
  have hab : a-b=diagonal (fun i => (hZ.eigenvalues i : ℂ)) := by
    rw [← hdiag]
    simp only [a,b,Z,Matrix.mul_sub,Matrix.sub_mul]
  have h := powers_stormer_diagonal ha hb hZ.eigenvalues hab
  have he : a*a-b*b=Uᴴ*(A*A-B*B)*U := by
    dsimp only [a,b]
    rw [unitary_conj_mul hU,unitary_conj_mul hU,Matrix.mul_sub,Matrix.sub_mul]
  rw [he,unitary_traceNorm_conj hU] at h
  have ht : (Matrix.trace ((A-B)*(A-B))).re=∑ i, (hZ.eigenvalues i)^2 := by
    rw [← unitary_trace_conj hU ((A-B)*(A-B)),← unitary_conj_mul hU]
    change (Matrix.trace ((Uᴴ*Z*U)*(Uᴴ*Z*U))).re=_
    rw [hdiag,Matrix.diagonal_mul_diagonal,Matrix.trace_diagonal,Complex.re_sum]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,pow_two]
  rwa [ht]

lemma fidelity_lower {H J : Mat n} (hH : H.PosSemidef) (hJ : J.PosSemidef) :
    ((Matrix.trace H).re+(Matrix.trace J).re-traceNorm (H-J))/2 ≤ fidelity H J := by
  have h := powers_stormer (sqrt_psd H) (sqrt_psd J)
  rw [CFC.sqrt_mul_sqrt_self H hH.nonneg,CFC.sqrt_mul_sqrt_self J hJ.nonneg] at h
  have he : (Matrix.trace ((CFC.sqrt H-CFC.sqrt J)*(CFC.sqrt H-CFC.sqrt J))).re =
      (Matrix.trace H).re+(Matrix.trace J).re-2*(Matrix.trace (CFC.sqrt H*CFC.sqrt J)).re := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.trace_sub,Complex.sub_re,
      CFC.sqrt_mul_sqrt_self H hH.nonneg,CFC.sqrt_mul_sqrt_self J hJ.nonneg]
    rw [Matrix.trace_mul_comm (CFC.sqrt J)]
    ring
  rw [he] at h
  have hf := trace_re_le_traceNorm (CFC.sqrt H*CFC.sqrt J)
  dsimp [fidelity]
  linarith
end SecretKey

end

end OAI
