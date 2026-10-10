import OAI.InformationTheory.AmplitudeDamping.TypicalProjectors

namespace OAI

universe u_1

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

def finiteProjectors {M : ℕ} (Q : Fin M → Matrix ι ι ℂ) (k : ℕ) : Matrix ι ι ℂ :=
  if h : k<M then Q ⟨k,h⟩ else 0

omit [DecidableEq ι] in
theorem finiteProjectors_projection {M : ℕ} (Q : Fin M → Matrix ι ι ℂ)
    (hQ : ∀ m, IsProjection (Q m)) (k : ℕ) : IsProjection (finiteProjectors Q k) := by
  dsimp [finiteProjectors]
  split_ifs with h
  · exact hQ _
  · exact ⟨Matrix.isHermitian_zero, Matrix.zero_mul _⟩

omit [Fintype ι] [DecidableEq ι] in
theorem finiteProjectors_apply {M : ℕ} (Q : Fin M → Matrix ι ι ℂ) (m : Fin M) :
    finiteProjectors Q m=Q m := by simp [finiteProjectors,m.isLt]

def sequentialMeasurement {M : ℕ} (P : Matrix ι ι ℂ) (Q : Fin M → Matrix ι ι ℂ)
    (m : Fin M) : Matrix ι ι ℂ :=
  (rejectProduct (finiteProjectors Q) m*P)ᴴ*Q m*(rejectProduct (finiteProjectors Q) m*P)

theorem sequentialMeasurement_pos {M : ℕ} (P : Matrix ι ι ℂ) (Q : Fin M → Matrix ι ι ℂ)
    (hQ : ∀ m, IsProjection (Q m)) (m : Fin M) : (sequentialMeasurement P Q m).PosSemidef :=
  (hQ m).posSemidef.conjTranspose_mul_mul_same _

theorem sequentialMeasurement_sum {M : ℕ} (P : Matrix ι ι ℂ) (hP : IsProjection P)
    (Q : Fin M → Matrix ι ι ℂ) (hQ : ∀ m, IsProjection (Q m)) :
    (∑ m, sequentialMeasurement P Q m)=
      P-P*(rejectProduct (finiteProjectors Q) M)ᴴ*rejectProduct (finiteProjectors Q) M*P := by
  let R := rejectProduct (finiteProjectors Q)
  have he : (∑ m, sequentialMeasurement P Q m)=
      P*(∑ m : Fin M, (R m)ᴴ*finiteProjectors Q m*R m)*P := by
    simp only [Matrix.mul_sum,Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    rw [finiteProjectors_apply,sequentialMeasurement,Matrix.conjTranspose_mul,hP.1.eq]
    simp only [Matrix.mul_assoc,R]
  rw [he,Fin.sum_univ_eq_sum_range (fun k ↦ (R k)ᴴ*finiteProjectors Q k*R k) M]
  have ht := rejectProduct_sum (finiteProjectors Q) (finiteProjectors_projection Q hQ) M
  dsimp only [R]
  rw [ht,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,hP.2]
  simp only [Matrix.mul_assoc]

theorem sequentialMeasurement_remainder {M : ℕ} (P : Matrix ι ι ℂ) (hP : IsProjection P)
    (Q : Fin M → Matrix ι ι ℂ) (hQ : ∀ m, IsProjection (Q m)) :
    (1-∑ m, sequentialMeasurement P Q m).PosSemidef := by
  rw [sequentialMeasurement_sum P hP Q hQ]
  have he : 1-(P-P*(rejectProduct (finiteProjectors Q) M)ᴴ*rejectProduct (finiteProjectors Q) M*P)=
      (1-P)+(rejectProduct (finiteProjectors Q) M*P)ᴴ*(rejectProduct (finiteProjectors Q) M*P) := by
    rw [Matrix.conjTranspose_mul,hP.1.eq]
    simp only [← Matrix.mul_assoc]
    abel
  rw [he]
  exact hP.complement.posSemidef.add (Matrix.posSemidef_conjTranspose_mul_self _)

omit [Fintype ι] in
theorem complete_submeasurement {M : ℕ} (hM : 0 < M) (D : Fin M → Matrix ι ι ℂ)
    (hD : ∀ m, (D m).PosSemidef) (hR : (1-∑ m, D m).PosSemidef) :
    ∃ E : Fin M → Matrix ι ι ℂ, (∀ m, (E m).PosSemidef) ∧ (∑ m, E m=1) ∧
      (∀ m, (E m-D m).PosSemidef) := by
  let m0 : Fin M := ⟨0,hM⟩
  let R := 1-∑ m, D m
  let E := fun m ↦ D m+if m=m0 then R else 0
  refine ⟨E,?_,?_,?_⟩
  · intro m
    dsimp [E]
    split_ifs
    · exact (hD m).add hR
    · simpa only [add_zero] using hD m
  · dsimp [E]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    dsimp [R]
    abel
  · intro m
    dsimp [E]
    split_ifs
    · convert hR using 1; dsimp [R]; abel
    · simp only [add_zero,sub_self]; exact Matrix.PosSemidef.zero

theorem sequentialMeasurement_success {M : ℕ} (P : Matrix ι ι ℂ) (Q : Fin M → Matrix ι ι ℂ)
    (hQ : ∀ m, IsProjection (Q m)) (F : Matrix ι ι ℂ) (m : Fin M) :
    (sequentialMeasurement P Q m*gram F).trace.re=
      mass (Q m*rejectProduct (finiteProjectors Q) m*P*F) := by
  have he : Q m*rejectProduct (finiteProjectors Q) m*P*F=
      Q m*((rejectProduct (finiteProjectors Q) m*P)*F) := by simp only [Matrix.mul_assoc]
  rw [he,← projection_inner (hQ m),frobVector_inner]
  have ht := Matrix.trace_mul_cycle
    ((rejectProduct (finiteProjectors Q) m*P)ᴴ*Q m*(rejectProduct (finiteProjectors Q) m*P)) F Fᴴ
  simpa only [sequentialMeasurement,gram,Matrix.conjTranspose_mul,Matrix.mul_assoc] using congrArg Complex.re ht

/-- Sequential decoding preceded by a global typical-subspace test. -/
theorem sequential_decoder_bound {M : ℕ} (hM : 0 < M) (P : Matrix ι ι ℂ) (hP : IsProjection P)
    (Q A : Fin M → Matrix ι ι ℂ) (hQ : ∀ m, IsProjection (Q m)) (hA : ∀ m, IsState (A m)) :
    ∃ D : Fin M → Matrix ι ι ℂ, (∀ m, (D m).PosSemidef) ∧ (∑ m, D m=1) ∧
      ∀ m, 1-(D m*A m).trace.re ≤
        9*(1-(P*A m).trace.re)+8*(1-(Q m*A m).trace.re)+
          4*∑ j : Fin M, if j=m then 0 else (Q j*(P*A m*P)).trace.re := by
  obtain ⟨D,hD,hDs,hDb⟩ := complete_submeasurement hM (sequentialMeasurement P Q)
    (sequentialMeasurement_pos P Q hQ) (sequentialMeasurement_remainder P hP Q hQ)
  refine ⟨D,hD,hDs,fun m ↦ ?_⟩
  let F := spectralFactor (hA m).1
  have hF : gram F=A m := spectralFactor_gram (hA m).1
  have hmF : mass F=1 := by dsimp [mass]; rw [hF,(hA m).2]; rfl
  have hb := sequential_projector_success (finiteProjectors Q) (finiteProjectors_projection Q hQ) (P*F) m
  rw [finiteProjectors_apply] at hb
  have hself := projected_self_failure (P := P) (hQ m) F
  have hfailP := projection_mass_decomposition hP F
  have hfailQ := projection_mass_decomposition (hQ m) F
  rw [projection_gram_mass hP F,hF] at hfailP
  rw [projection_gram_mass (hQ m) F,hF] at hfailQ
  have hcross : (∑ j ∈ Finset.range (m:ℕ), mass (finiteProjectors Q j*(P*F))) ≤
      ∑ j : Fin M, if j=m then 0 else (Q j*(P*A m*P)).trace.re := by
    have hgp : gram (P*F)=P*A m*P := by
      dsimp only [gram]
      rw [Matrix.conjTranspose_mul,hP.1.eq,← Matrix.mul_assoc,Matrix.mul_assoc P F Fᴴ]
      change P*gram F*P=P*A m*P
      rw [hF]
    calc
      _ = ∑ j ∈ Finset.range (m:ℕ), if j=(m:ℕ) then 0 else mass (finiteProjectors Q j*(P*F)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [ite_eq_right (by have := Finset.mem_range.mp hj; omega)]
      _ ≤ ∑ j ∈ Finset.range M, if j=(m:ℕ) then 0 else mass (finiteProjectors Q j*(P*F)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono m.isLt.le)
        intro j _ _
        split_ifs
        · exact le_rfl
        · exact mass_nonneg _
      _ = _ := by
        rw [← Fin.sum_univ_eq_sum_range (fun j ↦ if j=(m:ℕ) then 0 else mass (finiteProjectors Q j*(P*F))) M]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j=m
        · subst j; simp
        · have hjv : (j:ℕ) ≠ (m:ℕ) := by intro h; exact hj (Fin.ext h)
          rw [ite_eq_right hjv,ite_eq_right hj,finiteProjectors_apply,projection_gram_mass (hQ j),hgp]

  have hsucc := sequentialMeasurement_success P Q hQ F m
  rw [hF] at hsucc
  have hmono := trace_product_mono (hA m).1 (hDb m)
  rw [Matrix.trace_mul_comm (A m) (sequentialMeasurement P Q m),Matrix.trace_mul_comm (A m) (D m)] at hmono
  rw [hsucc] at hmono
  have hpm : mass (P*F)=(P*A m).trace.re := by rw [projection_gram_mass hP,hF]
  rw [hmF] at hfailP hfailQ
  rw [← Matrix.mul_assoc (Q m*rejectProduct (finiteProjectors Q) m) P F] at hb
  linarith

end GAD

end

end OAI
