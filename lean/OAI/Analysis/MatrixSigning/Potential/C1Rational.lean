import Mathlib
import OAI.Analysis.MatrixSigning.Potential.StateIA
import OAI.Analysis.MatrixSigning.Potential.EndpointCandidates
import OAI.Analysis.MatrixSigning.Potential.FaceEndpointFeasible
import OAI.Analysis.MatrixSigning.Potential.MovementBudget

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State.LightPoint
open CurrentKS.Schedule

variable {d n : ℕ}

lemma C1_eq_rational (p : LightPoint d n) (ε : ℚ) (hε : p.ε=(ε:ℝ)) :
    p.C1=(movementBudget n ε:ℝ) := by
  simp only [C1,E0,J,s0,movementBudget,hε,Rat.cast_max,Rat.cast_mul,Rat.cast_add,
    Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_one]

lemma Psi_eq_facePotential (p : LightPoint d n) :
    p.Psi=fun lam => facePotential p.ε lam p.fixedPart p.A := rfl

end CurrentKS.State.LightPoint

namespace CurrentKS.Difference
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.State CurrentKS.Variational CurrentKS.Schedule
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius ContDiff

variable {d n : ℕ}

lemma pointCast_update (x : Fin n → ℚ) (i : Fin n) (t : ℚ) :
    pointCast (Function.update x i t)=Function.update (pointCast x) i (t:ℝ) := by
  funext j
  by_cases hj : j=i
  · subst j;simp [pointCast]
  · simp [pointCast,Function.update_of_ne hj]

theorem face_candidates_progress [NeZero d] [NeZero n]
    (A : Fin n → H d) (S₀ : H d) (x : Fin n → ℚ)
    (query : (Fin n → ℚ) → ℚ) (ε lam σ h a M s ρ : ℚ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hεd : ε*d ≤ 1) (hlam : 0 < lam)
    (hσ : 0 < σ) (hx : ∀ i,|x i| ≤ 1-σ)
    (hA : ∀ i,A i∈psdCone d) (hA0 : ∀ i,A i≠0) (hrank : ∀ i,(A i : Mat d).rank ≤ 1)
    (hlo : -(Hermitian.one : H d) ≤ S₀+S A (pointCast x))
    (hhi : S₀+S A (pointCast x) ≤ (Hermitian.one : H d))
    (hη : eta 384 A (pointCast x) (Hermitian.one : H d) ≤ (384:ℝ) • (Hermitian.one : H d))
    (haeq : a=threshold n ε lam) (ha : 0 < a) (ha1 : a ≤ 1) (hM1 : 1 ≤ M)
    (hs : 0 < s) (hs1 : s ≤ 1/4) (hsσ : s ≤ σ/4) (hstep : M*s ≤ a/4)
    (hh : 0 < h) (hh1 : h ≤ 1) (hhsmall : h ≤ a/(64*M*n))
    (hρ : 0 < ρ) (hmesh : (n:ℚ)*ρ/2 ≤ s*(a/(1024*M))/8)
    (hreg : ∀ y,‖y-pointCast x‖ ≤ (s:ℝ)+2*(h:ℝ) →
      ContDiffAt ℝ 3 (facePotential (ε:ℝ) (lam:ℝ) S₀ A) y)
    (hders : ∀ y,‖y-pointCast x‖ ≤ (s:ℝ)+2*(h:ℝ) → ∀ u,‖u‖ ≤ 1 →
      |iteratedDeriv 2 (fun t : ℝ => facePotential (ε:ℝ) (lam:ℝ) S₀ A (y+t • u)) 0| ≤ (M:ℝ) ∧
      |iteratedDeriv 3 (fun t : ℝ => facePotential (ε:ℝ) (lam:ℝ) S₀ A (y+t • u)) 0| ≤ (M:ℝ))
    (hquery : ∀ y,‖pointCast y-pointCast x‖ ≤ 2*(h:ℝ) →
      |(query y:ℝ)-facePotential (ε:ℝ) (lam:ℝ) S₀ A (pointCast y)| ≤
        (a:ℝ)*(h:ℝ)^2/(128*n)) :
    ∃ y∈allCandidates query x h a M s ρ,
      facePotential (ε:ℝ) (lam:ℝ) S₀ A (pointCast y) ≤
        facePotential (ε:ℝ) (lam:ℝ) S₀ A (pointCast x)-2*(a:ℝ)*(s:ℝ)^2 := by
  have hxr : ∀ i,|pointCast x i| < 1 := by
    intro i
    have hh : |(x i:ℝ)| ≤ 1-(σ:ℝ) := by exact_mod_cast hx i
    have hσr : (0:ℝ) < σ := by exact_mod_cast hσ
    change |(x i:ℝ)| < 1
    linarith
  obtain ⟨z,hz,hsub,hmin⟩ := normalized_minimizer (ε:=(ε:ℝ)) (S₀+S A (pointCast x))
    (eta 384 A (pointCast x)) (eta_positive (by norm_num : (0:ℝ) ≤ 384) A (fun i => (hxr i).le))
    (by exact_mod_cast hε) (by exact_mod_cast hεd) hlo hhi hη
  have h100 := scalar_hundred_bounds hlo hhi
  rcases endpoint_or_light (ε:=(ε:ℝ)) A S₀ (pointCast x) (by exact_mod_cast hε) (by exact_mod_cast hε1)
    hA hA0 hrank hxr h100.1 h100.2 z hz hsub hmin (lam:=(lam:ℝ)) with hend|hlight
  · obtain ⟨i,t,ht,hdec⟩ := hend
    obtain ⟨tq,htq,heq⟩ : ∃ tq : ℚ,|tq|=1 ∧ (tq:ℝ)=t := by
      by_cases hs : 0 ≤ t
      · rw [abs_of_nonneg hs] at ht
        exact ⟨1,by norm_num,by simpa using ht.symm⟩
      · rw [abs_of_neg (lt_of_not_ge hs)] at ht
        exact ⟨-1,by norm_num,by push_cast;linarith⟩
    have hp : (σ:ℝ) ≤ psi (pointCast x i) :=
      psi_ge_strip (hxr i) (show |(x i:ℝ)| ≤ 1-(σ:ℝ) by exact_mod_cast hx i)
    have hC := movementBudget_one_le n ε
    have he := threshold_relation n ε lam
    rw [←haeq] at he
    have hale : a ≤ lam := by nlinarith [sq_nonneg (movementBudget n ε-1)]
    have hdecq : 2*a*s^2 ≤ lam*σ := by
      have hm := mul_le_mul_of_nonneg_left hsσ hs.le
      have hm' := mul_le_mul_of_nonneg_left hs1 hσ.le
      have hass : 2*s^2 ≤ σ := by nlinarith
      have hscale := mul_le_mul_of_nonneg_left hass ha.le
      have hal := mul_le_mul_of_nonneg_right hale hσ.le
      nlinarith
    have hdecr : 2*(a:ℝ)*(s:ℝ)^2 ≤ (lam:ℝ)*(σ:ℝ) := by exact_mod_cast hdecq
    have hlamr : (0:ℝ) ≤ lam := by exact_mod_cast hlam.le
    refine ⟨Function.update x i tq,List.mem_append_left _ (endpoint_mem x i tq htq),?_⟩
    rw [pointCast_update,heq]
    linarith [mul_le_mul_of_nonneg_left hp hlamr]
  · obtain ⟨p,hpA,hpx,hpS,hpε,_⟩ := hlight
    have hfun : p.Psi (lam:ℝ)=facePotential (ε:ℝ) (lam:ℝ) S₀ A := by
      rw [p.Psi_eq_facePotential,hpA,hpS,hpε]
    have hrel : (lam:ℝ)=512*(a:ℝ)*p.C1^2 := by
      rw [p.C1_eq_rational ε hpε]
      exact_mod_cast (by simpa only [haeq] using threshold_relation n ε lam)
    have hh := p.computed_candidates_progress query x hpx (lam:ℝ) h a M s ρ
      ha ha1 hM1 hrel hs hs1 hstep ‹0 < h› hh1 hhsmall hρ hmesh
      (by simpa only [hfun] using hreg) (by simpa only [hfun] using hders)
      (by simpa only [hfun] using hquery)
    obtain ⟨y,hy,hd⟩ := hh
    exact ⟨y,List.mem_append_right _ hy,by simpa only [hfun,hpx] using hd⟩

end CurrentKS.Difference

end

end OAI
