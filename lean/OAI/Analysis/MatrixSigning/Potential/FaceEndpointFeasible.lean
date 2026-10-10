import Mathlib
import OAI.Analysis.MatrixSigning.Potential.FacePotential
import OAI.Analysis.MatrixSigning.Potential.LightPoint
import OAI.Analysis.MatrixSigning.Potential.Potential

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma face_endpoint_feasible {c : ℝ} (A : Fin N → H d) (S₀ : H d) (x : Coordinates N) (i : Fin N) {t : ℝ}
    (ht : |t| = 1) (hA : A i ∈ psdCone d) (hrank : (A i : Mat d).rank ≤ 1)
    (z : Point d) (hz : z ∈ feasible ((S₀+S A x)) (eta c A x))
    (hplus : t-x i ≤ c*psi (x i)*inner ℝ (A i) z.2.2)
    (hminus : x i-t ≤ c*psi (x i)*inner ℝ (A i) z.2.1) :
    z ∈ feasible ((S₀+S A (Function.update x i t))) (eta c A (Function.update x i t)) := by
  erw [feasible_iff] at hz ⊢
  refine ⟨hz.1,hz.2.1,?_,?_⟩
  · have he : invH z.2.1+(S₀+S A (Function.update x i t))+eta c A (Function.update x i t) z.2.2 =
        invH z.2.1+(S₀+S A x)+eta c A x z.2.2 +
          (t-x i-c*psi (x i)*inner ℝ (A i) z.2.2) • A i := by
      rw [S_update,eta_update,psi_endpoint ht,zero_sub,mul_neg,
        sandwich_rank_one (A i) z.2.2 hA hrank]
      module
    erw [he]
    have hs : (t-x i-c*psi (x i)*inner ℝ (A i) z.2.2) • A i ≤ 0 := by
      simpa only [zero_smul] using scalar_mono_psd hA (sub_nonpos.mpr hplus)
    calc
      _ ≤ invH z.2.1+(S₀+S A x)+eta c A x z.2.2 := by
        simpa only [add_zero] using add_le_add (le_refl (invH z.2.1+(S₀+S A x)+eta c A x z.2.2)) hs
      _ ≤ _ := hz.2.2.1
  · have he : invH z.2.2-(S₀+S A (Function.update x i t))+eta c A (Function.update x i t) z.2.1 =
        invH z.2.2-(S₀+S A x)+eta c A x z.2.1 +
          (x i-t-c*psi (x i)*inner ℝ (A i) z.2.1) • A i := by
      rw [S_update,eta_update,psi_endpoint ht,zero_sub,mul_neg,
        sandwich_rank_one (A i) z.2.1 hA hrank]
      module
    erw [he]
    have hs : (x i-t-c*psi (x i)*inner ℝ (A i) z.2.1) • A i ≤ 0 := by
      simpa only [zero_smul] using scalar_mono_psd hA (sub_nonpos.mpr hminus)
    calc
      _ ≤ invH z.2.2-(S₀+S A x)+eta c A x z.2.1 := by
        simpa only [add_zero] using add_le_add (le_refl (invH z.2.2-(S₀+S A x)+eta c A x z.2.1)) hs
      _ ≤ _ := hz.2.2.2

lemma face_endpoint_potential_le [NeZero d] {ε lam : ℝ} (hε : 0≤ε)
    (A : Fin N → H d) (S₀ : H d) (x : Coordinates N) (hx : Cube x) (i : Fin N) {t : ℝ}
    (ht : |t|=1) (hA : A i∈psdCone d) (hrank : (A i : Mat d).rank≤1)
    (z : Point d) (hz : z∈feasible (S₀+S A x) (eta 384 A x))
    (hmin : ∀ w∈feasible (S₀+S A x) (eta 384 A x),objective ε z≤objective ε w)
    (hplus : t-x i≤384*psi (x i)*inner ℝ (A i) z.2.2)
    (hminus : x i-t≤384*psi (x i)*inner ℝ (A i) z.2.1) :
    facePotential ε lam S₀ A (Function.update x i t)≤facePotential ε lam S₀ A x-lam*psi (x i) := by
  have hf := face_endpoint_feasible A S₀ x i ht hA hrank z hz hplus hminus
  have hv := value_le_feasible ε hε _ _ (eta_positive (by norm_num : (0:ℝ)≤384) A (Cube_update hx i ht.le)) z hf
  rw [←value_eq_of_min ε _ _ z hz hmin] at hv
  rw [facePotential,facePotential,penalty,penalty,
    sum_update_composite (fun (_ : Fin N) (r : ℝ) => psi r) x i t,psi_endpoint ht,add_zero]
  nlinarith

theorem endpoint_or_light [NeZero d] (A : Fin N → H d) (S₀ : H d) (x : Coordinates N)
    {ε lam : ℝ} (hε : 0<ε) (hε1 : ε≤1)
    (hA : ∀ i,A i∈psdCone d) (hA0 : ∀ i,A i≠0) (hrank : ∀ i,(A i : Mat d).rank≤1)
    (hx : ∀ i,|x i|<1)
    (hlo : -(100:ℝ) • (Hermitian.one : H d)≤S₀+S A x)
    (hhi : S₀+S A x≤(100:ℝ) • (Hermitian.one : H d))
    (z : Point d) (hz : z∈feasible (S₀+S A x) (eta 384 A x)) (hsub : objective ε z≤100)
    (hmin : ∀ w∈feasible (S₀+S A x) (eta 384 A x),objective ε z≤objective ε w) :
    (∃ (i : Fin N) (t : ℝ),|t|=1 ∧
      facePotential ε lam S₀ A (Function.update x i t)≤facePotential ε lam S₀ A x-lam*psi (x i)) ∨
    (∃ p : LightPoint d N,p.A=A ∧ p.x=x ∧ p.fixedPart=S₀ ∧ p.ε=ε ∧ p.primal=z) := by
  have hx1 : Cube x := fun i => (hx i).le
  have hxlo (i : Fin N) := (abs_lt.mp (hx i)).1
  have hxhi (i : Fin N) := (abs_lt.mp (hx i)).2
  have hposX (i : Fin N) : 0≤384*psi (x i)*inner ℝ (A i) z.2.1 :=
    mul_nonneg (mul_nonneg (by norm_num) (psi_pos (hx i)).le)
      (inner_nonneg_of_psd _ _ (hA i) hz.1.1.posSemidef)
  have hposY (i : Fin N) : 0≤384*psi (x i)*inner ℝ (A i) z.2.2 :=
    mul_nonneg (mul_nonneg (by norm_num) (psi_pos (hx i)).le)
      (inner_nonneg_of_psd _ _ (hA i) hz.1.2.posSemidef)
  by_cases hLA : ∀ i,384*psi (x i)*inner ℝ (A i) z.2.1<1+x i
  · by_cases hLB : ∀ i,384*psi (x i)*inner ℝ (A i) z.2.2<1-x i
    · exact Or.inr (lightPoint_of_optimizer A x S₀ hε hε1 hA hA0 hrank hx hlo hhi z hz hsub hmin hLA hLB)
    · push Not at hLB
      obtain ⟨i,hi⟩ := hLB
      refine Or.inl ⟨i,1,by norm_num,?_⟩
      exact face_endpoint_potential_le hε.le A S₀ x hx1 i (by norm_num) (hA i) (hrank i) z hz hmin hi (by linarith [hposX i,hxhi i])
  · push Not at hLA
    obtain ⟨i,hi⟩ := hLA
    refine Or.inl ⟨i,-1,by norm_num,?_⟩
    exact face_endpoint_potential_le hε.le A S₀ x hx1 i (by norm_num) (hA i) (hrank i) z hz hmin
      (by linarith [hposY i,hxlo i]) (by linarith)

lemma psi_ge_strip {x σ : ℝ} (hx : |x|<1) (hstrip : |x|≤1-σ) : σ≤psi x := by
  have hab := abs_nonneg x
  have hsq := sq_abs x
  have hb := psi_ge_base hx
  nlinarith [sq_nonneg (1-|x|)]

end
end CurrentKS.State

end OAI
