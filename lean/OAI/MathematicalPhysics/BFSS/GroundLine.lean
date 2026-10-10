import Mathlib
import OAI.MathematicalPhysics.BFSS.FermionModes
import OAI.MathematicalPhysics.BFSS.FrequencySpectrum
import OAI.MathematicalPhysics.BFSS.Vacuum

namespace OAI

/-! Irreducibility of negative modes and the unique normal fermion ground line. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix Finset
open scoped ComplexConjugate
variable {N : ℕ} (M : AlgebraData N)

lemma thetaMode_zero : M.thetaMode (0 : FrequencyIndex N → ℂ) = 0 := by
  unfold thetaMode
  apply Finset.sum_eq_zero
  intro r _
  exact zero_smul ℂ (M.thetaPair r)

lemma thetaMode_add (v w : FrequencyIndex N → ℂ) :
    M.thetaMode (v+w) = M.thetaMode v+M.thetaMode w := by
  unfold thetaMode
  have ha (a b : ℂ) (T : Fermion N →L[ℂ] Fermion N) :
      (a+b) • T = a • T+b • T := add_smul a b T
  simp only [Pi.add_apply,ha,Finset.sum_add_distrib]

lemma thetaMode_single (r : FrequencyIndex N) :
    M.thetaMode (Pi.single r (1 : ℂ)) = M.thetaPair r := by
  classical
  unfold thetaMode
  rw [Finset.sum_eq_single r]
  · rw [Pi.single_eq_same]
    exact one_smul ℂ (M.thetaPair r)
  · intro s _ hsr
    rw [Pi.single_eq_of_ne hsr]
    exact zero_smul ℂ (M.thetaPair s)
  · simp

def NegativeFrequencyMode (K : FrequencyMatrix N) :=
  {v : FrequencyIndex N → ℂ // ∃ ω : ℝ, ω < 0 ∧
    ∀ r, Complex.I*(∑ s, (K r s : ℂ)*v s) = (ω : ℂ)*v r}

theorem normal_negative_modes_irreducible (q : Boson N)
    (hq : M.deformedBosonicPotential 1 1 q = 0) (W : Submodule ℂ (Fermion N))
    (ha : ∀ i : NegativeFrequencyMode (M.normalFermionFrequency q),
      ∀ x ∈ W, M.thetaMode i.1 x ∈ W)
    (hc : ∀ i : NegativeFrequencyMode (M.normalFermionFrequency q),
      ∀ x ∈ W, M.thetaMode (fun r => conj (i.1 r)) x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  classical
  let K := M.normalFermionFrequency q
  have hH := complexFrequency_hermitian K (M.normalFermionFrequency_skew q)
  let b := hH.eigenvectorBasis
  let V : Submodule ℂ (EuclideanSpace ℂ (FrequencyIndex N)) := {
    carrier := {v | ∀ x ∈ W, M.thetaMode v x ∈ W}
    zero_mem' := by
      intro x hx
      change M.thetaMode (0 : FrequencyIndex N → ℂ) x ∈ W
      rw [M.thetaMode_zero]
      exact W.zero_mem
    add_mem' := by
      intro v w hv hw x hx
      change M.thetaMode ((v : FrequencyIndex N → ℂ)+(w : FrequencyIndex N → ℂ)) x ∈ W
      rw [M.thetaMode_add]
      exact W.add_mem (hv x hx) (hw x hx)
    smul_mem' := by
      intro c v hv x hx
      change M.thetaMode (c • (v : FrequencyIndex N → ℂ)) x ∈ W
      rw [M.thetaMode_smul]
      exact W.smul_mem c (hv x hx)
  }
  have hb (j : FrequencyIndex N) : b j ∈ V := by
    have hm := complexFrequency_eigenmode K (M.normalFermionFrequency_skew q) j
    by_cases hj : hH.eigenvalues j < 0
    · exact ha ⟨b j,hH.eigenvalues j,hj,hm⟩
    · have hp : 0 < hH.eigenvalues j := lt_of_le_of_ne (not_lt.mp hj)
        (Ne.symm (M.normal_frequency_eigenvalues_ne_zero q hq j))
      let i : NegativeFrequencyMode K := ⟨fun r => conj (b j r),
        -hH.eigenvalues j,neg_neg_of_pos hp,complexFrequency_conjugate_mode K (b j)
          (hH.eigenvalues j) hm⟩
      have hi := hc i
      have he : (fun r => conj (i.1 r)) = (b j : FrequencyIndex N → ℂ) := by
        funext r
        exact star_star _
      rw [he] at hi
      exact hi
  have hV : V = ⊤ := by
    apply top_unique
    rw [← b.toBasis.span_eq]
    apply Submodule.span_le.mpr
    rintro v ⟨j,rfl⟩
    exact hb j
  apply M.theta_irreducible W
  intro α A x hx
  have hv : WithLp.toLp 2 (Pi.single (α,A) (1 : ℂ)) ∈ V := by rw [hV]; trivial
  have h := hv x hx
  change M.thetaMode (Pi.single (α,A) (1 : ℂ)) x ∈ W at h
  rw [M.thetaMode_single] at h
  exact h

theorem normal_fermion_ground_line (q : Boson N)
    (hq : M.deformedBosonicPotential 1 1 q = 0) :
    ∃ (E : ℝ) (u : Fermion N), u ≠ 0 ∧
      M.quantizeFrequency (M.normalFermionFrequency q) u = (E : ℂ) • u ∧
      (∀ (e : ℝ) (w : Fermion N), w ≠ 0 →
        M.quantizeFrequency (M.normalFermionFrequency q) w = (e : ℂ) • w → E ≤ e) ∧
      ∀ z : Fermion N, M.quantizeFrequency (M.normalFermionFrequency q) z = (E : ℂ) • z ↔
        z ∈ Submodule.span ℂ {u} := by
  classical
  let K := M.normalFermionFrequency q
  have hs := M.normalFermionFrequency_skew q
  obtain ⟨E,u,hu,he,hm⟩ := M.quantizeFrequency_ground_exists K hs
  let a (i : NegativeFrequencyMode K) := (M.thetaMode i.1).toLinearMap
  let c (i : NegativeFrequencyMode K) := (M.thetaMode (fun r => conj (i.1 r))).toLinearMap
  let κ (i j : NegativeFrequencyMode K) : ℂ := ∑ r, i.1 r*conj (j.1 r)
  have hcar : ∀ i j x, a i (c j x)+c j (a i x) = κ i j • x := by
    intro i j x
    exact congrArg (fun T : Fermion N →L[ℂ] Fermion N => T x)
      (M.thetaMode_CAR i.1 (fun r => conj (j.1 r)))
  have hadj : ∀ i x y, inner ℂ x (c i y) = inner ℂ (a i x) y := by
    intro i x y
    change inner ℂ x (M.thetaMode (fun r => conj (i.1 r)) y) =
      inner ℂ (M.thetaMode i.1 x) y
    rw [←M.thetaMode_star]
    exact (M.thetaMode i.1).adjoint_inner_right x y
  have hirr : ∀ W : Submodule ℂ (Fermion N),
      (∀ i, ∀ x ∈ W, a i x ∈ W) → (∀ i, ∀ x ∈ W, c i x ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W ha hc
    exact M.normal_negative_modes_irreducible q hq W ha hc
  have killed (z : Fermion N) (hz : M.quantizeFrequency K z = (E : ℂ) • z) :
      ∀ i, a i z = 0 := by
    intro i
    obtain ⟨ω,hω,hv⟩ := i.2
    exact M.quantizeFrequency_ground_killed K hs E z hz hm i.1 ω hω hv
  have hline := BFSSScalarVacuum.vacuum_line_of_exists a c κ hcar hadj hirr u hu (killed u he)
  refine ⟨E,u,hu,he,hm,?_⟩
  intro z
  constructor
  · intro hz
    exact (hline z).mp (killed z hz)
  · intro hz
    obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [map_smul,he,smul_comm]

end
end BFSSQuantum.AlgebraData

end OAI
