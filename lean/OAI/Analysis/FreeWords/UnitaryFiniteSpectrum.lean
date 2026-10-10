import Mathlib
import OAI.Analysis.FreeWords.NormalFiniteSpectrum
import OAI.Analysis.FreeWords.PartitionHom

namespace OAI

noncomputable section

namespace KKProjectionSupport

noncomputable section

open scoped BigOperators

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Ring A] [Algebra ℂ A]

variable [StarRing A] [StarModule ℂ A]

end

end KKProjectionSupport

namespace KKSpectralSupport

open KKTraceTransfer KKProjectionSupport

noncomputable section

def complexPhase (z : ℂ) : ℂ := if z=0 then 1 else (‖z‖:ℂ)⁻¹*z

theorem complexPhase_norm (z : ℂ) : ‖complexPhase z‖=1 := by
  by_cases hz : z=0
  · simp [complexPhase,hz]
  · rw [complexPhase,ite_eq_right hz,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]

theorem complexPhase_dist (z : ℂ) : ‖z-complexPhase z‖=|‖z‖-1| := by
  by_cases hz : z=0
  · simp [complexPhase,hz]
  · have hzn : ‖z‖≠0 := norm_ne_zero_iff.mpr hz
    have he : z-complexPhase z=((‖z‖-1:ℝ):ℂ)*complexPhase z := by
      rw [complexPhase,ite_eq_right hz]
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hzn]
    rw [he,norm_mul,complexPhase_norm,mul_one,Complex.norm_real,Real.norm_eq_abs]

theorem projection_norm_one {A : Type*} [CStarAlgebra A] {p : A}
    (hp : IsStarProjection p) (hp0 : p≠0) : ‖p‖=1 := by
  have h := CStarRing.norm_star_mul_self (x := p)
  rw [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq] at h
  have hpos := norm_pos_iff.mpr hp0
  nlinarith

theorem partition_weight_mul {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [CStarAlgebra A] (p : ι → A) (hp : ∀ i, IsStarProjection (p i))
    (hort : ∀ i j, i≠j → p i*p j=0) (c : ι → ℂ) (j : ι) :
    (∑ i, c i • p i)*p j=c j • p j := by
  rw [Finset.sum_mul]
  rw [Finset.sum_eq_single j]
  · rw [smul_mul_assoc,(hp j).isIdempotentElem.eq]
  · intro i hi hij; rw [smul_mul_assoc,hort i j hij,smul_zero]
  · simp

theorem phase_partition_unitary {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [CStarAlgebra A] (p : ι → A) (hp : ∀ i, IsStarProjection (p i))
    (hort : ∀ i j, i≠j → p i*p j=0) (h1 : ∑ i, p i=1)
    (c : ι → ℂ) (hc : ∀ i, ‖c i‖=1) : ∑ i, c i • p i ∈ unitary A := by
  change partitionHom p hp hort h1 c ∈ unitary A
  apply Unitary.map_mem (partitionHom p hp hort h1)
  rw [Unitary.mem_iff]
  constructor <;> ext i
  · change star (c i)*c i=1
    rw [Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,hc]
    norm_num
  · change c i*star (c i)=1
    rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,hc]
    norm_num

theorem partition_phase_error {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [CStarAlgebra A] (p : ι → A) (hp : ∀ i, IsStarProjection (p i))
    (hort : ∀ i j, i≠j → p i*p j=0) (h1 : ∑ i, p i=1)
    (c : ι → ℂ) (u : unitary A) :
    ‖(∑ i, c i • p i)-(∑ i, complexPhase (c i) • p i)‖ ≤
      ‖u.val-∑ i, c i • p i‖ := by
  classical
  let D := ‖u.val-∑ i, c i • p i‖
  have hbound (i : ι) (hi : p i≠0) : ‖c i-complexPhase (c i)‖ ≤ D := by
    rw [complexPhase_dist]
    have hp1 := projection_norm_one (hp i) hi
    have hnorm := abs_norm_sub_norm_le ((c i) • p i) (u.val*p i)
    rw [norm_smul,hp1,mul_one,CStarRing.norm_coe_unitary_mul,hp1] at hnorm
    refine hnorm.trans ?_
    rw [norm_sub_rev]
    have he : u.val*p i-c i • p i=(u.val-∑ j, c j • p j)*p i := by
      rw [sub_mul,partition_weight_mul p hp hort]
    rw [he]
    exact (norm_mul_le _ _).trans (by rw [hp1,mul_one])
  let d : ι → ℂ := fun i => if p i=0 then 0 else c i-complexPhase (c i)
  have he : (∑ i, c i • p i)-(∑ i, complexPhase (c i) • p i)=partitionHom p hp hort h1 d := by
    rw [← Finset.sum_sub_distrib,partitionHom_apply]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [d]
    split_ifs with hz
    · simp [hz]
    · rw [sub_smul]
  rw [he]
  refine (NonUnitalStarAlgHom.norm_apply_le (partitionHom p hp hort h1) d).trans ?_
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  dsimp only [d]
  split_ifs with hz
  · rw [norm_zero]; exact norm_nonneg _
  · exact hbound i hz

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem unitary_finite_spectrum_approximation (M : VonNeumannAlgebra H)
    (u : unitary (ConcreteAlgebra M)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (m n : ℕ) (p : Fin m × Fin n → ConcreteAlgebra M)
      (c : Fin m × Fin n → ℂ),
      (∀ i, IsStarProjection (p i)) ∧ (∀ i j, i≠j → p i*p j=0) ∧
      (∑ i, p i=1) ∧ (∀ i, ‖c i‖=1) ∧ ‖u.val-∑ i, c i • p i‖ < ε := by
  classical
  have hun : IsStarNormal u.val := ⟨by
    change star u.val*u.val=u.val*star u.val
    rw [Unitary.star_mul_self_of_mem u.property,Unitary.mul_star_self_of_mem u.property]⟩
  obtain ⟨m,n,p,c,hp,ho,h1,hc,he⟩ := normal_finite_spectrum_approximation M u.val hun
    (ε/2) (half_pos hε)
  refine ⟨m,n,p,fun i => complexPhase (c i),hp,ho,h1,fun i => complexPhase_norm (c i),?_⟩
  have hb := partition_phase_error p hp ho h1 c u
  have ht := norm_add_le (u.val-(∑ i, c i • p i))
    ((∑ i, c i • p i)-(∑ i, complexPhase (c i) • p i))
  rw [sub_add_sub_cancel] at ht
  linarith

end

end KKSpectralSupport
end

end OAI
