import Mathlib
import OAI.Analysis.MatrixSigning.Potential.LightPoint
import OAI.Analysis.MatrixSigning.Potential.EuclideanForget
import OAI.Analysis.MatrixSigning.Potential.EnsembleForcesNegative

namespace OAI

open Matrix

namespace CurrentKS.State.LightPoint
noncomputable section
open CurrentKS.Difference CurrentKS.RationalRoot
open scoped ContDiff

variable {d N : ℕ} (p : LightPoint d N)

theorem computed_candidates_progress [NeZero d] [NeZero N]
    (query : (Fin N → ℚ) → ℚ) (x : Fin N → ℚ) (hpx : p.x=pointCast x)
    (lam : ℝ) (h a M s ρ : ℚ) (ha : 0<a) (ha1 : a≤1) (hM1 : 1≤M)
    (hrel : lam=512*(a:ℝ)*p.C1^2)
    (hs : 0<s) (hs1 : s≤1/4) (hstep : M*s≤a/4) (hh : 0<h) (hh1 : h≤1)
    (hhsmall : h≤a/(64*M*N)) (hρ : 0<ρ) (hmesh : (N:ℚ)*ρ/2 ≤ s *(a/(1024*M))/8)
    (hreg : ∀ y,‖y-pointCast x‖≤(s:ℝ)+2*(h:ℝ) → ContDiffAt ℝ 3 (p.Psi lam) y)
    (hders : ∀ y,‖y-pointCast x‖≤(s:ℝ)+2*(h:ℝ) → ∀ u,‖u‖≤1 →
      |iteratedDeriv 2 (fun t : ℝ => p.Psi lam (y+t • u)) 0|≤(M:ℝ) ∧
      |iteratedDeriv 3 (fun t : ℝ => p.Psi lam (y+t • u)) 0|≤(M:ℝ))
    (hquery : ∀ y,‖pointCast y-pointCast x‖≤2*(h:ℝ) →
      |(query y:ℝ)-p.Psi lam (pointCast y)|≤(a:ℝ)*(h:ℝ)^2/(128*N)) :
    ∃ y∈interiorCandidates query x h a M s ρ,
      p.Psi lam (pointCast y)≤p.Psi lam p.x-2*(a:ℝ)*(s:ℝ)^2 := by
  have har : (0:ℝ)<a := by exact_mod_cast ha
  have hsr : (0:ℝ)<s := by exact_mod_cast hs
  have hacc := computed_stencil_accuracy query (p.Psi lam) x har (by exact_mod_cast hM1)
    hh (by exact_mod_cast hh1) (by exact_mod_cast hhsmall)
    (fun y hy => hreg y (by linarith))
    (fun y hy u hu => (hders y (by linarith) u hu).2) hquery
  have hp : (∃ i,(a:ℝ)≤|fderiv ℝ (p.Psi lam) (pointCast x) (realBasis i)|) ∨
      ¬∀ u,0≤realQuadratic (stencilHessian query x h) u+7*(a:ℝ)*‖u‖^2 := by
    by_cases hg : ∃ i,(a:ℝ)≤|fderiv ℝ (p.Psi lam) (pointCast x) (realBasis i)|
    · exact Or.inl hg
    right
    have hgrad : ∀ i,|fderiv ℝ (p.Psi lam) p.x (Pi.single i (1:ℝ))|≤(a:ℝ) := by
      intro i
      rw [hpx]
      exact le_of_lt (lt_of_not_ge fun h => hg ⟨i,h⟩)
    let test : Coordinates N → ℝ := fun u =>
      realQuadratic (stencilHessian query x h) (WithLp.toLp 2 u)
    have herr : ∀ u,|test u-fderiv ℝ (fderiv ℝ (p.Psi lam)) p.x u u|≤
        (a:ℝ)/16*(∑ i,u i^2) := by
      intro u
      have he := stencil_quadratic_accuracy (stencilHessian query x h)
        (fderiv ℝ (fderiv ℝ (p.Psi lam)) (pointCast x)) har.le hacc.2 (WithLp.toLp 2 u)
      simpa only [test,hpx,realQuadratic,EuclideanSpace.real_norm_sq_eq,WithLp.ofLp_toLp] using he
    have hnot := p.shifted_hessian_not_psd har hrel test hgrad herr
    intro hpsd
    apply hnot
    intro u
    have hh := hpsd (WithLp.toLp 2 u)
    simpa only [test,EuclideanSpace.real_norm_sq_eq,WithLp.ofLp_toLp] using hh
  have ht := interiorCandidates_progress query (p.Psi lam) x h a M s ρ ha ha1 hM1 hs hs1
    hstep hh hh1 hhsmall hρ hmesh hreg hders hquery hp
  simpa only [hpx] using ht

end
end CurrentKS.State.LightPoint

namespace CurrentKS.RationalRoot
open Matrix

variable {N : ℕ}

lemma computedCurvature_norm (H : Matrix (Fin N) (Fin N) ℚ) (hH : H.IsSymm)
    (a M s ρ : ℚ) (ha : 0 < a) (ha1 : a ≤ 1) (hM : 1 ≤ M) (hs : 0 ≤ s) (hρ : 0 < ρ)
    (hmesh : (N:ℚ)*ρ/2 ≤ s*(a/(1024*M))/8) (q : Fin N → ℚ)
    (hq : computedCurvature H a M s ρ=some q) : ‖realVector q‖ ≤ (s:ℝ) := by
  have hpar := curvature_parameters ha ha1 hM
  have hd := negativeDirection_spec (shiftedHessian H a) (shiftedHessian_symm H hH a)
    (a/(4096*M)) hpar.1 hpar.2.1
  unfold computedCurvature at hq
  cases he : negativeDirection (shiftedHessian H a) (a/(4096*M)) with
  | none => simp [he] at hq
  | some w =>
    simp only [he] at hd
    simp only [he,Option.map_some,Option.some.injEq] at hq
    subst q
    exact (curvature_rounding w s (a/(1024*M)) ρ hs hpar.2.2.1 hpar.2.2.2 hρ hmesh hd.2.1).2.1

end CurrentKS.RationalRoot

namespace CurrentKS.Difference
open CurrentKS.RationalRoot

variable {N : ℕ}

lemma interiorCandidates_distance [NeZero N]
    (query : (Fin N → ℚ) → ℚ) (x : Fin N → ℚ) (h a M s ρ : ℚ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hM : 1 ≤ M) (hs : 0 ≤ s) (hρ : 0 < ρ)
    (hmesh : (N:ℚ)*ρ/2 ≤ s*(a/(1024*M))/8) :
    ∀ y∈interiorCandidates query x h a M s ρ,‖pointCast y-pointCast x‖ ≤ (s:ℝ) := by
  intro y hy
  simp only [interiorCandidates,List.mem_cons] at hy
  rcases hy with rfl|hy
  · rw [pointCast_gradient,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (show (0:ℝ) ≤ s by exact_mod_cast hs)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (gradientDirection_bound (stencilGradient query x h)) (show (0:ℝ) ≤ s by exact_mod_cast hs)
  · cases he : computedCurvature (stencilHessian query x h) a M s ρ with
    | none => simp [he] at hy
    | some q =>
      have hb := (euclideanForget_bound (realVector q)).trans
        (computedCurvature_norm _ (stencilHessian_symm query x h) a M s ρ ha ha1 hM hs hρ hmesh q he)
      change ‖pointCast q‖ ≤ (s:ℝ) at hb
      simp only [he,List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl|rfl
      · simpa only [pointCast_add,add_sub_cancel_left] using hb
      · simpa only [pointCast_sub,sub_sub_cancel_left,norm_neg] using hb

def endpointCandidates (x : Fin N → ℚ) : List (Fin N → ℚ) :=
  (List.finRange N).flatMap fun i => [Function.update x i (-1),Function.update x i 1]

def allCandidates [NeZero N] (query : (Fin N → ℚ) → ℚ) (x : Fin N → ℚ)
    (h a M s ρ : ℚ) : List (Fin N → ℚ) :=
  endpointCandidates x++interiorCandidates query x h a M s ρ

lemma endpoint_mem (x : Fin N → ℚ) (i : Fin N) (t : ℚ) (ht : |t|=1) :
    Function.update x i t ∈ endpointCandidates x := by
  have hh : t=(-1:ℚ) ∨ t=1 := by
    exact ((abs_eq (by norm_num : (0:ℚ) ≤ 1)).mp ht).symm
  apply List.mem_flatMap.mpr
  refine ⟨i,List.mem_finRange i,?_⟩
  rcases hh with rfl|rfl <;> simp

lemma endpointCandidates_cube (x : Fin N → ℚ) (hx : ∀ i,|x i| ≤ 1) :
    ∀ y∈endpointCandidates x,∀ i,|y i| ≤ 1 := by
  intro y hy j
  obtain ⟨i,_,hy⟩ := List.mem_flatMap.mp hy
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
  rcases hy with rfl|rfl
  all_goals
    by_cases hji : j=i
    · subst j;simp
    · simpa only [Function.update_of_ne hji] using hx j

lemma allCandidates_cube [NeZero N]
    (query : (Fin N → ℚ) → ℚ) (x : Fin N → ℚ) (h a M s ρ σ : ℚ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hM : 1 ≤ M) (hs : 0 ≤ s) (hρ : 0 < ρ)
    (hmesh : (N:ℚ)*ρ/2 ≤ s*(a/(1024*M))/8) (hsσ : s ≤ σ)
    (_hσ : 0 ≤ σ) (hx : ∀ i,|x i| ≤ 1-σ) :
    ∀ y∈allCandidates query x h a M s ρ,∀ i,|y i| ≤ 1 := by
  intro y hy
  rcases List.mem_append.mp hy with he|hi
  · exact endpointCandidates_cube x (fun i => (hx i).trans (by linarith)) y he
  · have hd := interiorCandidates_distance query x h a M s ρ ha ha1 hM hs hρ hmesh y hi
    intro i
    have hb := (pi_norm_le_iff_of_nonneg (show (0:ℝ) ≤ s by exact_mod_cast hs)).mp hd i
    change ‖(y i:ℝ)-(x i:ℝ)‖ ≤ (s:ℝ) at hb
    rw [Real.norm_eq_abs] at hb
    have hc : |(x i:ℝ)| ≤ 1-(σ:ℝ) := by exact_mod_cast hx i
    have hd' : (s:ℝ) ≤ (σ:ℝ) := by exact_mod_cast hsσ
    have htri : |(y i:ℝ)| ≤ |(y i:ℝ)-(x i:ℝ)|+|(x i:ℝ)| := by
      simpa only [sub_zero] using abs_sub_le (y i:ℝ) (x i:ℝ) 0
    have hh : |(y i:ℝ)| ≤ 1 := by linarith
    exact_mod_cast hh

end CurrentKS.Difference

end OAI
