import Mathlib
import OAI.MathematicalPhysics.BFSS.FrequencyComparison
import OAI.MathematicalPhysics.BFSS.FrequencyOperators

namespace OAI

/-! CAR eigenmodes, actual ground vectors and lowering operators. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix Finset
open scoped ComplexConjugate
variable {N : ℕ} (M : AlgebraData N)

def thetaMode (v : FrequencyIndex N → ℂ) : Fermion N →L[ℂ] Fermion N :=
  ∑ r, v r • M.thetaPair r

lemma thetaMode_smul (c : ℂ) (v : FrequencyIndex N → ℂ) :
    M.thetaMode (c • v) = c • M.thetaMode v := by
  simp only [thetaMode,Pi.smul_apply,smul_eq_mul,Finset.smul_sum,smul_smul]

theorem thetaMode_CAR (v w : FrequencyIndex N → ℂ) :
    M.thetaMode v*M.thetaMode w+M.thetaMode w*M.thetaMode v =
      (∑ r, v r*w r) • (1 : Fermion N →L[ℂ] Fermion N) := by
  have hh (r s : FrequencyIndex N) :
      (v r • M.thetaPair r)*(w s • M.thetaPair s)+
        (w s • M.thetaPair s)*(v r • M.thetaPair r) =
      (v r*w s) • (if r = s then (1 : Fermion N →L[ℂ] Fermion N) else 0) := by
    rw [smul_mul_smul,smul_mul_smul,mul_comm (w s)]
    rw [←(smul_add (v r*w s) (M.thetaPair r*M.thetaPair s)
      (M.thetaPair s*M.thetaPair r)),M.thetaPair_CAR]
  unfold thetaMode
  simp only [Finset.sum_mul,Finset.mul_sum]
  conv_lhs =>
    arg 2
    rw [Finset.sum_comm]
  rw [←Finset.sum_add_distrib]
  simp_rw [←Finset.sum_add_distrib,hh]
  have hs (r : FrequencyIndex N) :
      (∑ s : FrequencyIndex N, (v r*w s) •
        (if r = s then (1 : Fermion N →L[ℂ] Fermion N) else 0)) =
      (v r*w r) • (1 : Fermion N →L[ℂ] Fermion N) := by
    rw [Finset.sum_eq_single r]
    · simp
    · intro s _ hsr
      rw [ite_eq_right (Ne.symm hsr)]
      exact (@smul_zero ℂ (Fermion N →L[ℂ] Fermion N) _ _ (v r*w s))
    · intro hr
      exact (hr (Finset.mem_univ r)).elim
  rw [Finset.sum_comm]
  calc
    _ = ∑ r : FrequencyIndex N, (v r*w r) • (1 : Fermion N →L[ℂ] Fermion N) :=
      Finset.sum_congr rfl (fun r _ => hs r)
    _ = _ := (@Finset.sum_smul (FrequencyIndex N) ℂ (Fermion N →L[ℂ] Fermion N)
      _ _ _ (fun r => v r*w r) Finset.univ 1).symm

lemma thetaMode_star (v : FrequencyIndex N → ℂ) :
    star (M.thetaMode v) = M.thetaMode (fun r => conj (v r)) := by
  have hs (f : FrequencyIndex N → (Fermion N →L[ℂ] Fermion N)) :
      star (∑ r, f r) = ∑ r, star (f r) := star_sum Finset.univ f
  have hc (c : ℂ) (A : Fermion N →L[ℂ] Fermion N) :
      star (c • A) = conj c • star A := star_smul c A
  simp only [thetaMode,hs,hc,M.thetaPair_star]

theorem thetaMode_commutator (K : FrequencyMatrix N) (hK : K.transpose = -K)
    (v : FrequencyIndex N → ℂ) :
    M.quantizeFrequency K*M.thetaMode v-M.thetaMode v*M.quantizeFrequency K =
      M.thetaMode (fun r => Complex.I*∑ s, (K r s : ℂ)*v s) := by
  have hd (c : ℂ) (A B : Fermion N →L[ℂ] Fermion N) :
      A*(c • B)-(c • B)*A = c • (A*B-B*A) := by
    rw [mul_smul_comm,smul_mul_assoc,smul_sub]
  unfold thetaMode
  simp only [Finset.mul_sum,Finset.sum_mul,←Finset.sum_sub_distrib,hd,
    M.quantizeFrequency_commutator K hK,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  calc
    _ = (∑ s : FrequencyIndex N, v s*(Complex.I*(K r s : ℂ))) • M.thetaPair r :=
      (@Finset.sum_smul (FrequencyIndex N) ℂ (Fermion N →L[ℂ] Fermion N)
        _ _ _ (fun s => v s*(Complex.I*(K r s : ℂ))) Finset.univ (M.thetaPair r)).symm
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      ring

end
end BFSSQuantum.AlgebraData

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix Finset
variable {N : ℕ} (M : AlgebraData N)

theorem quantizeFrequency_ground_exists (K : FrequencyMatrix N) (hK : K.transpose = -K) :
    ∃ (E : ℝ) (u : Fermion N), u ≠ 0 ∧ M.quantizeFrequency K u = (E : ℂ) • u ∧
      ∀ (e : ℝ) (v : Fermion N), v ≠ 0 →
        M.quantizeFrequency K v = (e : ℂ) • v → E ≤ e := by
  classical
  let T : Fermion N →ₗ[ℂ] Fermion N := (M.quantizeFrequency K).toLinearMap
  have hs : T.IsSymmetric := (M.quantizeFrequency_selfAdjoint K hK).isSymmetric
  let d := Module.finrank ℂ (Fermion N)
  have hd : 0 < d := Module.finrank_pos
  let i₀ : Fin d := ⟨0,hd⟩
  obtain ⟨i,hi,hm⟩ := Finset.exists_min_image Finset.univ (hs.eigenvalues rfl)
    (show (Finset.univ : Finset (Fin d)).Nonempty from ⟨i₀,Finset.mem_univ i₀⟩)
  refine ⟨hs.eigenvalues rfl i,hs.eigenvectorBasis rfl i,
    (hs.hasEigenvector_eigenvectorBasis rfl i).2, hs.apply_eigenvectorBasis rfl i,?_⟩
  intro e v hv he
  have hev : Module.End.HasEigenvalue T (e : ℂ) :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr he,hv⟩
  obtain ⟨j,hj⟩ := hs.exists_eigenvalues_eq rfl hev
  have heq : hs.eigenvalues rfl j = e := Complex.ofReal_injective hj
  rw [←heq]
  exact hm j (Finset.mem_univ j)

theorem quantizeFrequency_ground_killed (K : FrequencyMatrix N) (hK : K.transpose = -K)
    (E : ℝ) (u : Fermion N) (hu : M.quantizeFrequency K u = (E : ℂ) • u)
    (hmin : ∀ (e : ℝ) (w : Fermion N), w ≠ 0 →
      M.quantizeFrequency K w = (e : ℂ) • w → E ≤ e)
    (v : FrequencyIndex N → ℂ) (ω : ℝ) (hω : ω < 0)
    (hv : ∀ r, Complex.I*(∑ s, (K r s : ℂ)*v s) = (ω : ℂ)*v r) :
    M.thetaMode v u = 0 := by
  have he : (fun r => Complex.I*(∑ s, (K r s : ℂ)*v s)) = (ω : ℂ) • v := by
    funext r
    exact hv r
  have hc := M.thetaMode_commutator K hK v
  rw [he,M.thetaMode_smul] at hc
  have hc' := congrArg (fun A : Fermion N →L[ℂ] Fermion N => A u) hc
  change M.quantizeFrequency K (M.thetaMode v u) -
    M.thetaMode v (M.quantizeFrequency K u) = (ω : ℂ) • M.thetaMode v u at hc'
  rw [hu,map_smul] at hc'
  have hE : M.quantizeFrequency K (M.thetaMode v u) =
      ((E+ω : ℝ) : ℂ) • M.thetaMode v u := by
    rw [Complex.ofReal_add,add_smul]
    exact eq_add_of_sub_eq' hc'
  by_contra hn
  have h := hmin (E+ω) (M.thetaMode v u) hn hE
  linarith

theorem normal_fermion_ground_lowering (q : Boson N)
    (_hq : M.deformedBosonicPotential 1 1 q = 0) :
    ∃ (E : ℝ) (u : Fermion N), u ≠ 0 ∧
      M.quantizeFrequency (M.normalFermionFrequency q) u = (E : ℂ) • u ∧
      ∀ (v : FrequencyIndex N → ℂ) (ω : ℝ), ω < 0 →
        (∀ r, Complex.I*(∑ s, (M.normalFermionFrequency q r s : ℂ)*v s) =
          (ω : ℂ)*v r) → M.thetaMode v u = 0 := by
  have hs := M.normalFermionFrequency_skew q
  obtain ⟨E,u,hu,he,hm⟩ := M.quantizeFrequency_ground_exists (M.normalFermionFrequency q) hs
  refine ⟨E,u,hu,he,?_⟩
  intro v ω hω hv
  exact M.quantizeFrequency_ground_killed (M.normalFermionFrequency q) hs E u he hm v ω hω hv

end
end BFSSQuantum.AlgebraData

end OAI
