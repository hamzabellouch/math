import OAI.NumberTheory.Ostmann.QuadraticSieveSmallScaleBootstrap
import OAI.NumberTheory.Ostmann.QuadraticSieveWeightedSmoothingNorm

namespace OAI

namespace Ostmann.QuadraticSieve

theorem quadraticNorm_dyadic_small_scale_bootstrap {ξ : ℝ} (hξ1 : 1<ξ) (hξ2 : ξ≤2)
    (hξ : ExponentBound (fun M N => quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N)) ξ)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (η : ℝ) (M N : ℕ),
      0≤η → η≤ε/2 → 0<M → 0<N →
      (M:ℝ)≤4*(N:ℝ)*((M:ℝ)*N)^η →
      quadraticNorm (dyadicSquarefreeRows M) (oddSquarefreeUpTo N) ≤
        C*((M:ℝ)*N)^ε*((M:ℝ)+(M:ℝ)^(1-ξ)*(N:ℝ)^(2*ξ-1)) := by
  obtain ⟨C,hC,hbound⟩ := hξ (ε/2) (by positivity)
  refine ⟨8*C*(2:ℝ)^(ε/2),by positivity,?_⟩
  intro η M N hη hηε hM hN hscale
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hP1 : (1:ℝ)≤(M:ℝ)*N := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast hM) (by exact_mod_cast hN)
  have hs := small_scale_exponent_budget hMr hNr hP1 hη hξ1.le hξ2 hscale
  have hb := hbound (2*M) N (by omega) hN
  have hcast : ((2*M:ℕ):ℝ)=2*(M:ℝ) := by norm_cast
  rw [hcast,show 2*(M:ℝ)*N=2*((M:ℝ)*N) by ring,
    Real.mul_rpow (by norm_num : (0:ℝ)≤2) (by positivity)] at hb
  have hsum : 2*(M:ℝ)+(N:ℝ)^ξ≤8*((M:ℝ)*N)^η*
      ((M:ℝ)+(M:ℝ)^(1-ξ)*(N:ℝ)^(2*ξ-1)) := by nlinarith [Real.rpow_nonneg hNr.le ξ]
  have hp : ((M:ℝ)*N)^(ε/2)*((M:ℝ)*N)^η≤((M:ℝ)*N)^ε := by
    rw [← Real.rpow_add (by positivity : (0:ℝ)<(M:ℝ)*N)]
    exact Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
  calc
    _ ≤ quadraticNorm (oddSquarefreeUpTo (2*M)) (oddSquarefreeUpTo N) :=
      quadraticNorm_mono_rows (Finset.filter_subset _ _) _
    _ ≤ _ := hb
    _ ≤ C*((2:ℝ)^(ε/2)*((M:ℝ)*N)^(ε/2))*(8*((M:ℝ)*N)^η*
        ((M:ℝ)+(M:ℝ)^(1-ξ)*(N:ℝ)^(2*ξ-1))) := by gcongr
    _ = (8*C*(2:ℝ)^(ε/2))*(((M:ℝ)*N)^(ε/2)*((M:ℝ)*N)^η)*
        ((M:ℝ)+(M:ℝ)^(1-ξ)*(N:ℝ)^(2*ξ-1)) := by ring
    _ ≤ _ := by gcongr

end Ostmann.QuadraticSieve

end OAI
