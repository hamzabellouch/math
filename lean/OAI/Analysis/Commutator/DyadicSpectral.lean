import Mathlib
import OAI.Analysis.Commutator.SpectralCutoff

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology BigOperators

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def binaryRemainder (T : H →L[ℂ] H) : H →L[ℂ] H := T+T-halfCut T

lemma binaryRemainder_nonneg {T : H →L[ℂ] H} (hT : 0≤T) : 0≤binaryRemainder T := by
  let p := halfCut T
  have hp := isProjection_halfCut T
  have hc := halfCut_commute (IsSelfAdjoint.of_nonneg hT)
  have he : binaryRemainder T=(T+T-1)⁺+(1-p)*(T+T) := by
    rw [←halfCut_mul_shift (IsSelfAdjoint.of_nonneg hT)]
    change T+T-p=p*(T+T-1)+(1-p)*(T+T)
    noncomm_ring
  rw [he]
  exact add_nonneg (CFC.posPart_nonneg _) (Commute.mul_nonneg
    (sub_nonneg.mpr hp.le_one) (add_nonneg hT hT)
    (((Commute.one_left T).sub_left hc).add_right ((Commute.one_left T).sub_left hc)))

lemma binaryRemainder_le_one {T : H →L[ℂ] H} (hT : 0≤T) (hT1 : T≤1) :
    binaryRemainder T≤1 := by
  let b := T+T-1
  let p := halfCut T
  have hb : IsSelfAdjoint b := ((IsSelfAdjoint.of_nonneg hT).add
    (IsSelfAdjoint.of_nonneg hT)).sub (IsSelfAdjoint.one _)
  have hp := isProjection_halfCut T
  have hc := halfCut_commute (IsSelfAdjoint.of_nonneg hT)
  have hnb : b⁻=p*b-b := by
    rw [show p*b=b⁺ from halfCut_mul_shift (IsSelfAdjoint.of_nonneg hT)]
    calc
      b⁻=b⁺-(b⁺-b⁻) := by abel
      _=b⁺-b := by rw [CFC.posPart_sub_negPart b hb]
  have he : 1-binaryRemainder T=p*((1-T)+(1-T))+b⁻ := by
    rw [hnb]
    change 1-(T+T-p)=p*((1-T)+(1-T))+(p*(T+T-1)-(T+T-1))
    noncomm_ring
  apply sub_nonneg.mp
  rw [he]
  exact add_nonneg (Commute.mul_nonneg hp.nonneg (add_nonneg (sub_nonneg.mpr hT1)
    (sub_nonneg.mpr hT1)) ((Commute.one_right p).sub_right hc |>.add_right
      ((Commute.one_right p).sub_right hc))) (CFC.negPart_nonneg b)

lemma halfCut_commutes {T A : H →L[ℂ] H} (hTA : Commute T A) (hTAstar : Commute T (star A)) :
    Commute (halfCut T) A := by
  let b := T+T-1
  have hb : Commute b A := (hTA.add_left hTA).sub_left (Commute.one_left A)
  have hbs : Commute b (star A) := (hTAstar.add_left hTAstar).sub_left (Commute.one_left (star A))
  change Commute (rightSupport b⁺) A
  simpa only [partialIsometry_of_nonneg (CFC.posPart_nonneg b)] using
    partialIsometry_commutes b⁺ A (hb.cfcₙ_real (·⁺)) (hbs.cfcₙ_real (·⁺))

def dyadicRemainder (T : H →L[ℂ] H) : ℕ → H →L[ℂ] H
  | 0 => T
  | n+1 => binaryRemainder (dyadicRemainder T n)

lemma dyadicRemainder_bounds {T : H →L[ℂ] H} (hT : 0≤T) (hT1 : T≤1) (n : ℕ) :
    0≤dyadicRemainder T n ∧ dyadicRemainder T n≤1 := by
  induction n with
  | zero => exact ⟨hT,hT1⟩
  | succ n ih => exact ⟨binaryRemainder_nonneg ih.1,binaryRemainder_le_one ih.1 ih.2⟩

lemma dyadicRemainder_mem (M : VonNeumannAlgebra H) {T : H →L[ℂ] H} (hT : T∈M) (n : ℕ) :
    dyadicRemainder T n∈M := by
  induction n with
  | zero => exact hT
  | succ n ih => exact M.toStarSubalgebra.sub_mem (M.add_mem ih ih) (halfCut_mem M ih)

def dyadicStep (T : H →L[ℂ] H) (n : ℕ) : H →L[ℂ] H :=
  ∑ i∈Finset.range n, ((2:ℝ)⁻¹^(i+1)) • halfCut (dyadicRemainder T i)

lemma dyadicStep_remainder (T : H →L[ℂ] H) (n : ℕ) :
    T-dyadicStep T n=((2:ℝ)⁻¹^n) • dyadicRemainder T n := by
  induction n with
  | zero => simp [dyadicStep,dyadicRemainder]
  | succ n ih =>
    rw [dyadicStep,Finset.sum_range_succ]
    rw [←dyadicStep]
    change T-(dyadicStep T n+_)=_
    rw [sub_add_eq_sub_sub,ih]
    simp only [dyadicRemainder,binaryRemainder,smul_sub,smul_add,pow_succ]
    module

lemma dyadicStep_norm_error {T : H →L[ℂ] H} (hT : 0≤T) (hT1 : T≤1) (n : ℕ) :
    ‖T-dyadicStep T n‖≤(2:ℝ)⁻¹^n := by
  rw [dyadicStep_remainder,norm_smul,Real.norm_of_nonneg (by positivity)]
  have hb := dyadicRemainder_bounds hT hT1 n
  exact mul_le_of_le_one_right (by positivity) ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hb.1).mpr hb.2)

lemma dyadicRemainder_commutes {T A : H →L[ℂ] H} (hA : IsSelfAdjoint A)
    (hTA : Commute T A) (n : ℕ) : Commute (dyadicRemainder T n) A := by
  induction n with
  | zero => exact hTA
  | succ n ih =>
    exact (ih.add_left ih).sub_left (halfCut_commutes ih (by simpa only [hA.star_eq] using ih))

lemma dyadicCut_commutes_original {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (n : ℕ) :
    Commute (halfCut (dyadicRemainder T n)) T := by
  have hc := dyadicRemainder_commutes hT (Commute.refl T) n
  exact halfCut_commutes hc (by simpa only [hT.star_eq] using hc)

lemma dyadicCuts_commute {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (n m : ℕ) :
    Commute (halfCut (dyadicRemainder T n)) (halfCut (dyadicRemainder T m)) := by
  have hp : IsSelfAdjoint (halfCut (dyadicRemainder T m)) :=
    (isProjection_halfCut _).isSelfAdjoint
  have hc := dyadicRemainder_commutes hp (dyadicCut_commutes_original hT m).symm n
  exact halfCut_commutes hc (by simpa only [hp.star_eq] using hc)

theorem exists_positive_spectral_sum (M : VonNeumannAlgebra H)
    {T : H →L[ℂ] H} (hTM : T∈M) (hT : 0≤T) (hT1 : T≤1) {ε : ℝ} (hε : 0<ε) :
    ∃ n : ℕ, ∃ p : Fin n → H →L[ℂ] H, ∃ c : Fin n → ℝ,
      (∀ i,p i∈M ∧ IsStarProjection (p i)) ∧
      (∀ i j,Commute (p i) (p j)) ∧ ‖T-∑ i,c i • p i‖<ε := by
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2:ℝ)⁻¹<1)
  refine ⟨n,fun i => halfCut (dyadicRemainder T i.val),fun i => (2:ℝ)⁻¹^(i.val+1),
    fun i => ⟨halfCut_mem M (dyadicRemainder_mem M hTM i.val),isProjection_halfCut _⟩,
    fun i j => dyadicCuts_commute (IsSelfAdjoint.of_nonneg hT) i.val j.val,?_⟩
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    (2:ℝ)⁻¹^(i+1) • halfCut (dyadicRemainder T i))]
  exact (dyadicStep_norm_error hT hT1 n).trans_lt hn

end Kadison.Polar

end

end
end

end OAI
