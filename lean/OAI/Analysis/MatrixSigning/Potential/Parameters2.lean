import Mathlib
import OAI.Analysis.MatrixSigning.Potential.MovementBudget

namespace OAI

open Matrix

namespace CurrentKS.Schedule

structure Parameters where
  ε : ℚ
  σ : ℚ
  a : ℚ
  M : ℚ
  s : ℚ
  h : ℚ
  ρ : ℚ
  stencilError : ℚ
  selectionError : ℚ
  deriving DecidableEq

def parameters (d n : ℕ) (ν lam : ℚ) : Parameters :=
  let ε := ν/(d:ℚ)
  let σ := lam^2/ν
  let a := threshold n ε lam
  let M := curveBudget d n ε σ lam
  let s := stepSize a M σ
  let h := stencilSize n a M σ
  let ρ := meshSize n a M s
  ⟨ε,σ,a,M,s,h,ρ,a*h^2/(128*n),a*s^2/4⟩

lemma stencil_error_bounds {n : ℕ} (hn : 0 < n) {a h : ℚ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1) :
    0 < a*h^2/(128*n) ∧ a*h^2/(128*n) ≤ 1 := by
  have hn0 : (0:ℚ) < n := by exact_mod_cast hn
  have hn1 : (1:ℚ) ≤ n := by exact_mod_cast hn
  refine ⟨by positivity,(div_le_one (by positivity)).mpr ?_⟩
  have hh2 : h^2 ≤ 1 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right ha1 (sq_nonneg h)
  nlinarith

lemma selection_error_bounds {a s : ℚ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1/4) :
    0 < a*s^2/4 ∧ a*s^2/4 ≤ 1 := by
  refine ⟨by positivity,(div_le_one (by norm_num : (0:ℚ) < 4)).mpr ?_⟩
  have hs2 : s^2 ≤ 1 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right ha1 (sq_nonneg s)
  nlinarith

structure Parameters.Valid (p : Parameters) (n : ℕ) : Prop where
  epsilon_pos : 0 < p.ε
  epsilon_le : p.ε ≤ 1
  strip_pos : 0 < p.σ
  threshold_pos : 0 < p.a
  threshold_le : p.a ≤ 1
  bound_one : 1 ≤ p.M
  step_pos : 0 < p.s
  step_strip : p.s ≤ p.σ/4
  step_le : p.s ≤ 1/4
  step_curvature : p.M*p.s ≤ p.a/4
  stencil_pos : 0 < p.h
  stencil_strip : p.h ≤ p.σ/8
  stencil_le : p.h ≤ 1
  stencil_curvature : p.h ≤ p.a/(64*p.M*n)
  mesh_pos : 0 < p.ρ
  mesh_error : (n:ℚ)*p.ρ/2 ≤ p.s*(p.a/(1024*p.M))/8
  radius : p.s+2*p.h ≤ p.σ/2
  stencilError_pos : 0 < p.stencilError
  stencilError_le : p.stencilError ≤ 1
  selectionError_pos : 0 < p.selectionError
  selectionError_le : p.selectionError ≤ 1

lemma parameters_valid {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    {ν lam : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    (parameters d n ν lam).Valid n := by
  have hd0 : (0:ℚ) < d := by exact_mod_cast hd
  have hd1 : (1:ℚ) ≤ d := by exact_mod_cast hd
  have hep : 0 < ν/(d:ℚ) := div_pos hν hd0
  have hep1 : ν/(d:ℚ) ≤ 1 := (div_le_one hd0).mpr (hν1.trans hd1)
  have hσ : 0 < lam^2/ν := by positivity
  have ha := threshold_pos n (ν/(d:ℚ)) hlam
  have ha1 := threshold_le_one n (ν/(d:ℚ)) hlam1
  have hM := curveBudget_one_le d n hep hσ lam
  have hMp : 0 < curveBudget d n (ν/(d:ℚ)) (lam^2/ν) lam := lt_of_lt_of_le (by norm_num) hM
  have hs := stepSize_spec ha hMp hσ
  have hh := stencilSize_spec hn ha hMp hσ
  have hρ := meshSize_spec hn ha hMp hs.1
  have he := stencil_error_bounds hn ha ha1 hh.1 hh.2.2.1
  have hg := selection_error_bounds ha ha1 hs.1 hs.2.2.1
  exact ⟨hep,hep1,hσ,ha,ha1,hM,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,
    hh.1,hh.2.1,hh.2.2.1,hh.2.2.2,hρ.1,hρ.2,schedule_radius hn ha hMp hσ,
    he.1,he.2,hg.1,hg.2⟩

end CurrentKS.Schedule

end OAI
