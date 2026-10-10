import Mathlib
import OAI.Analysis.MatrixSigning.Potential.ValueFeasible

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

def ParameterCube (θ : Coordinates N) : Prop := ∀ i, 0 ≤ θ i ∧ θ i ≤ 1

def etaTheta (c : ℝ) (A : Fin N → H d) (θ : Coordinates N) : H d →L[ℝ] H d :=
  ∑ i, (c*θ i) • sandwichCLM (A i)

lemma etaTheta_apply (c : ℝ) (A : Fin N → H d) (θ : Coordinates N) (Z : H d) :
    etaTheta c A θ Z = ∑ i,(c*θ i) • sandwich (A i) Z := by
  exact sum_apply Finset.univ (fun i => (c*θ i) • sandwichCLM (A i)) Z

lemma etaTheta_psi (c : ℝ) (A : Fin N → H d) (x : Coordinates N) :
    etaTheta c A (fun i => psi (x i)) = eta c A x := rfl

lemma parameterCube_psi {x : Coordinates N} (hx : Cube x) : ParameterCube (fun i => psi (x i)) :=
  fun i => psi_bounds (hx i)

lemma etaTheta_positive {c : ℝ} (hc : 0 ≤ c) (A : Fin N → H d) {θ : Coordinates N}
    (hθ : ParameterCube θ) : ∀ Z ∈ psdCone d, etaTheta c A θ Z ∈ psdCone d := by
  intro Z hZ
  rw [etaTheta_apply]
  exact psd_sum _ _ fun i _ => psd_smul (sandwich_psd _ _ hZ) (mul_nonneg hc (hθ i).1)

lemma etaTheta_one_bound {c ν : ℝ} (hc : 0 ≤ c) (A : Fin N → H d)
    (hν : (∑ i,sandwich (A i) (Hermitian.one : H d)) ≤ ν • (Hermitian.one : H d))
    {θ : Coordinates N} (hθ : ParameterCube θ) :
    etaTheta c A θ (Hermitian.one : H d) ≤ (c*ν) • (Hermitian.one : H d) := by
  rw [etaTheta_apply,SemigroupAction.mul_smul]
  apply le_trans _ (smul_order hν hc)
  rw [Finset.smul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact scalar_mono_psd (sandwich_psd _ _ one_mem_psdCone)
    (mul_le_of_le_one_right hc (hθ i).2)

lemma sandwich_mono_order (A : H d) {U V : H d} (hUV : U ≤ V) : sandwich A U ≤ sandwich A V := by
  apply sub_nonneg.mp
  rw [← sandwich_sub]
  exact psd_nonneg (sandwich_psd A (V-U) ((mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr hUV)))

lemma etaTheta_difference_le {c ν δ R : ℝ} (hc : 0 ≤ c) (hδ : 0 ≤ δ) (hR : 0 ≤ R)
    (A : Fin N → H d)
    (hν : (∑ i,sandwich (A i) (Hermitian.one : H d)) ≤ ν • (Hermitian.one : H d))
    (θ φ : Coordinates N) (hdiff : ∀ i, θ i-φ i ≤ δ)
    (Z : H d) (hZ : Z ∈ psdCone d) (hZR : Z ≤ R • (Hermitian.one : H d)) :
    etaTheta c A θ Z-etaTheta c A φ Z ≤ (c*δ*R*ν) • (Hermitian.one : H d) := by
  have hsum : (∑ i,sandwich (A i) Z) ≤ (R*ν) • (Hermitian.one : H d) := by
    calc
      _ ≤ ∑ i,sandwich (A i) (R • (Hermitian.one : H d)) :=
        Finset.sum_le_sum fun i _ => sandwich_mono_order (A i) hZR
      _ = R • (∑ i,sandwich (A i) (Hermitian.one : H d)) := by
        simp only [sandwich_smul,Finset.smul_sum]
      _ ≤ R • (ν • (Hermitian.one : H d)) := smul_order hν hR
      _ = _ := by rw [smul_smul]
  calc
    _ = ∑ i,(c*(θ i-φ i)) • sandwich (A i) Z := by
      simp only [etaTheta_apply,← Finset.sum_sub_distrib,mul_sub]
      apply Finset.sum_congr rfl
      intro i _
      exact (sub_smul (c*θ i) (c*φ i) (sandwich (A i) Z)).symm
    _ ≤ ∑ i,(c*δ) • sandwich (A i) Z := by
      apply Finset.sum_le_sum
      intro i _
      exact scalar_mono_psd (sandwich_psd _ _ hZ) (mul_le_mul_of_nonneg_left (hdiff i) hc)
    _ = (c*δ) • (∑ i,sandwich (A i) Z) := by rw [Finset.smul_sum]
    _ ≤ (c*δ) • ((R*ν) • (Hermitian.one : H d)) := smul_order hsum (mul_nonneg hc hδ)
    _ = _ := by rw [smul_smul]; congr 1; ring

lemma etaTheta_shift_feasible {c ν δ R : ℝ} (hc : 0 ≤ c) (hδ : 0 ≤ δ) (hR : 0 ≤ R)
    (A : Fin N → H d)
    (hν : (∑ i,sandwich (A i) (Hermitian.one : H d)) ≤ ν • (Hermitian.one : H d))
    (θ φ : Coordinates N) (hdiff : ∀ i, φ i-θ i ≤ δ) (S : H d)
    (z : Point d) (hz : z ∈ feasible S (etaTheta c A θ))
    (hX : z.2.1 ≤ R • (Hermitian.one : H d)) (hY : z.2.2 ≤ R • (Hermitian.one : H d)) :
    (z.1+c*δ*R*ν,z.2) ∈ feasible S (etaTheta c A φ) := by
  obtain ⟨hpX,hpY,h₁,h₂⟩ := (feasible_iff _ _ _).mp hz
  refine (feasible_iff _ _ _).mpr ⟨hpX,hpY,?_,?_⟩
  · have hh := etaTheta_difference_le hc hδ hR A hν φ θ hdiff z.2.2 hpY.posSemidef hY
    have hb := add_le_add h₁ hh
    convert hb using 1 <;> first | rfl | module
  · have hh := etaTheta_difference_le hc hδ hR A hν φ θ hdiff z.2.1 hpX.posSemidef hX
    have hb := add_le_add h₂ hh
    convert hb using 1 <;> first | rfl | module

lemma objective_shift (ε t : ℝ) (z : Point d) :
    objective ε (z.1+t,z.2) = objective ε z+t := by simp only [objective]; ring

lemma etaTheta_minimizer [NeZero d] (A : Fin N → H d)
    (hA : ∀ i,A i ∈ psdCone d) (htr : ∑ i,Hermitian.realTrace (A i) = 1)
    {ν : ℝ} (hν : 0 < ν) (hν₁ : ν ≤ 1)
    (hvar : (∑ i,sandwich (A i) (Hermitian.one : H d)) ≤ ν • (Hermitian.one : H d))
    (x θ : Coordinates N) (hx : Cube x) (hθ : ParameterCube θ) :
    ∃ z ∈ feasible (S A x) (etaTheta 384 A θ), objective (ν/d) z ≤ 100 ∧
      ∀ w ∈ feasible (S A x) (etaTheta 384 A θ), objective (ν/d) z ≤ objective (ν/d) w := by
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hε : 0 < ν/(d : ℝ) := div_pos hν hd
  have hb := S_bounds A hA htr hx
  have hz := scalar_feasible (S A x) (etaTheta 384 A θ)
    (show -(1 : ℝ) • (Hermitian.one : H d) ≤ S A x by simpa only [neg_one_smul ℝ (Hermitian.one : H d)] using hb.1)
    (show S A x ≤ (1 : ℝ) • (Hermitian.one : H d) by simpa using hb.2)
    (etaTheta_one_bound (by norm_num) A hvar hθ) (show (0 : ℝ)<1/20 by norm_num)
  have hf : objective (ν/(d : ℝ)) (1+(1/20 : ℝ)⁻¹+(384*ν)*(1/20),(1/20 : ℝ) • (Hermitian.one : H d),
      (1/20 : ℝ) • (Hermitian.one : H d)) ≤ 100 := by
    rw [scalar_objective]
    have he : (d : ℝ)*(ν/d) = ν := mul_div_cancel₀ ν (ne_of_gt hd)
    norm_num
    nlinarith
  apply exists_minimizer (S A x) (etaTheta 384 A θ) (etaTheta_positive (by norm_num) A hθ) hε
    (show (0 : ℝ)<100 by norm_num) _ _ _ hz hf
  · exact (show -(100 : ℝ) • (Hermitian.one : H d) ≤ -(Hermitian.one : H d) by
      convert scalar_one_mono (d := d) (show (-100 : ℝ) ≤ -1 by norm_num) using 1; first | rfl | module).trans hb.1
  · exact hb.2.trans (show (Hermitian.one : H d) ≤ (100 : ℝ) • Hermitian.one by
      simpa only [one_smul] using scalar_one_mono (show (1 : ℝ)≤100 by norm_num))

lemma etaTheta_value_le [NeZero d] (A : Fin N → H d)
    (hA : ∀ i,A i ∈ psdCone d) (htr : ∑ i,Hermitian.realTrace (A i) = 1)
    {ν δ : ℝ} (hν : 0 < ν) (hν₁ : ν ≤ 1) (hδ : 0 ≤ δ)
    (hvar : (∑ i,sandwich (A i) (Hermitian.one : H d)) ≤ ν • (Hermitian.one : H d))
    (x θ φ : Coordinates N) (hx : Cube x) (hθ : ParameterCube θ) (hφ : ParameterCube φ)
    (hdiff : ∀ i,θ i-φ i ≤ δ) :
    value (ν/d) (S A x) (etaTheta 384 A θ) ≤
      value (ν/d) (S A x) (etaTheta 384 A φ)+38400*(d : ℝ)*δ := by
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hε : 0 < ν/(d : ℝ) := div_pos hν hd
  obtain ⟨z,hz,hz100,hzmin⟩ := etaTheta_minimizer A hA htr hν hν₁ hvar x φ hx hφ
  have hb := S_bounds A hA htr hx
  have hl : -(100 : ℝ) • (Hermitian.one : H d) ≤ S A x :=
    (show -(100 : ℝ) • (Hermitian.one : H d) ≤ -(Hermitian.one : H d) by
      simpa only [neg_one_smul ℝ (Hermitian.one : H d)] using
        scalar_one_mono (d := d) (show (-100 : ℝ) ≤ -1 by norm_num)).trans hb.1
  have hu : S A x ≤ (100 : ℝ) • (Hermitian.one : H d) := hb.2.trans (by
    simpa only [one_smul] using scalar_one_mono (d := d) (show (1 : ℝ) ≤ 100 by norm_num))
  have hbox := sublevel_box (S A x) (etaTheta 384 A φ)
    (etaTheta_positive (by norm_num) A hφ) hε (show (0 : ℝ)<100 by norm_num) hl hu hz hz100
  have hshift := etaTheta_shift_feasible (show (0 : ℝ)≤384 by norm_num) hδ
    (show 0 ≤ 100/(ν/(d : ℝ)) by positivity) A hvar φ θ hdiff (S A x) z hz hbox.2.1.2 hbox.2.2.2
  have hmin := value_eq_of_min (ν/d) (S A x) (etaTheta 384 A φ) z hz hzmin
  calc
    _ ≤ objective (ν/d) (z.1+384*δ*(100/(ν/(d : ℝ)))*ν,z.2) :=
      value_le_feasible _ hε.le _ _ (etaTheta_positive (by norm_num) A hθ) _ hshift
    _ = objective (ν/d) z+384*δ*(100/(ν/(d : ℝ)))*ν := objective_shift _ _ _
    _ = _ := by rw [hmin]; congr 1; field_simp; ring

lemma sum_parameter_difference_le {θ φ : Coordinates N} {δ : ℝ}
    (h : ∀ i,θ i-φ i ≤ δ) : (∑ i,θ i)-(∑ i,φ i) ≤ (N : ℝ)*δ := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ _ : Fin N,δ := Finset.sum_le_sum fun i _ => h i
    _ = _ := by simp

lemma etaTheta_value_perturbation [NeZero d] (A : Fin N → H d)
    (hA : ∀ i,A i ∈ psdCone d) (htr : ∑ i,Hermitian.realTrace (A i) = 1)
    {ν δ lam : ℝ} (hν : 0 < ν) (hν₁ : ν ≤ 1) (hδ : 0 ≤ δ) (hlam : 0 ≤ lam)
    (hvar : (∑ i,sandwich (A i) (Hermitian.one : H d)) ≤ ν • (Hermitian.one : H d))
    (x θ φ : Coordinates N) (hx : Cube x) (hθ : ParameterCube θ) (hφ : ParameterCube φ)
    (hdiff : ∀ i,|θ i-φ i| ≤ δ) :
    |(value (ν/d) (S A x) (etaTheta 384 A θ)+lam*∑ i,θ i)-
      (value (ν/d) (S A x) (etaTheta 384 A φ)+lam*∑ i,φ i)| ≤
      (38400*(d : ℝ)+lam*N)*δ := by
  have h₁ : ∀ i,θ i-φ i ≤ δ := fun i => (abs_le.mp (hdiff i)).2
  have h₂ : ∀ i,φ i-θ i ≤ δ := fun i => by have h := (abs_le.mp (hdiff i)).1; linarith
  have hv₁ := etaTheta_value_le A hA htr hν hν₁ hδ hvar x θ φ hx hθ hφ h₁
  have hv₂ := etaTheta_value_le A hA htr hν hν₁ hδ hvar x φ θ hx hφ hθ h₂
  have hs₁ := mul_le_mul_of_nonneg_left (sum_parameter_difference_le h₁) hlam
  have hs₂ := mul_le_mul_of_nonneg_left (sum_parameter_difference_le h₂) hlam
  apply abs_le.mpr
  constructor <;> nlinarith

end
end CurrentKS.State

end OAI
