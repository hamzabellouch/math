import OAI.NumberTheory.Ostmann.QuadraticSieveCutoffScales
import OAI.NumberTheory.Ostmann.QuadraticSieveSmoothingDescentOptimized
import OAI.NumberTheory.Ostmann.QuadraticSieveSmoothingDescentSmallScale

namespace OAI

namespace Ostmann.QuadraticSieve

theorem smoothingStepBound_dyadic_recursive {ξ : ℝ} (hξ1 : 1<ξ) (hξ2 : ξ≤2)
    (hξ : ExponentBound (fun M N => quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N)) ξ)
    (hstep : SmoothingStepBound ξ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (M N : ℕ), 0<M → 0<N →
      quadraticNorm (dyadicSquarefreeRows M) (oddSquarefreeUpTo N) ≤
        C*((M:ℝ)*N)^ε*((M:ℝ)+(M:ℝ)^(1-ξ)*(N:ℝ)^(2*ξ-1)) := by
  obtain ⟨η,hη,hηε,C,hC,hbound⟩ := hstep.optimized_smoothing ε hε
  obtain ⟨Cs,hCs,hsmall⟩ := quadraticNorm_dyadic_small_scale_bootstrap hξ1 hξ2 hξ ε hε
  refine ⟨34*C+Cs,by positivity,?_⟩
  intro M N hM hN
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hP1 : (1:ℝ)≤(M:ℝ)*N := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast hM) (by exact_mod_cast hN)
  have hRec0 : 0≤(M:ℝ)+(M:ℝ)^(1-ξ)*(N:ℝ)^(2*ξ-1) := by positivity
  by_cases hlarge : 4*(N:ℝ)*((M:ℝ)*N)^η≤M
  · have hT1 : 1≤((M:ℝ)*N)^η := Real.one_le_rpow hP1 hη.le
    have hNM : N≤M := by
      have : (N:ℝ)≤M := by nlinarith
      exact_mod_cast this
    obtain ⟨K,hKeq,hK,hKM,hcut,hKP,hscalar,hsqrt⟩ :=
      exists_smoothing_cutoff_scales hM hN hη hξ1 hξ2 hlarge
    have hb := hbound M K N hM hK hN hNM hKM hcut hsqrt
    have hQ := quadraticNorm_dyadic_le_smoothingNorm hM hKM (oddSquarefreeUpTo N)
      (fun n hn => (mem_oddSquarefreeUpTo.mp hn).2.2.1)
    have hP2 : 1≤((M:ℝ)*N)^(2*η) := Real.one_le_rpow hP1 (by positivity)
    have hMrec : (M:ℝ)≤(M:ℝ)+(M:ℝ)^(1-ξ)*(N:ℝ)^(2*ξ-1) :=
      le_add_of_nonneg_right (by positivity)
    have hMrec' : (M:ℝ)≤((M:ℝ)*N)^(2*η)*
        ((M:ℝ)+(M:ℝ)^(1-ξ)*(N:ℝ)^(2*ξ-1)) :=
      hMrec.trans (le_mul_of_one_le_left hRec0 hP2)
    have hcore : (M:ℝ)+Real.sqrt (M:ℝ)*(K:ℝ)^(ξ-1/2) ≤
        17*((M:ℝ)*N)^(2*η)*((M:ℝ)+(M:ℝ)^(1-ξ)*(N:ℝ)^(2*ξ-1)) := by
      nlinarith
    have hp : ((M:ℝ)*N)^(ε/2)*((M:ℝ)*N)^(2*η)≤((M:ℝ)*N)^ε := by
      rw [← Real.rpow_add (by positivity : (0:ℝ)<(M:ℝ)*N)]
      exact Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
    calc
      _ ≤ 2*smoothingNorm M K (oddSquarefreeUpTo N) := hQ
      _ ≤ 2*(C*((M:ℝ)*N)^(ε/2)*
          ((M:ℝ)+Real.sqrt (M:ℝ)*(K:ℝ)^(ξ-1/2))) := by gcongr
      _ ≤ 2*(C*((M:ℝ)*N)^(ε/2)*
          (17*((M:ℝ)*N)^(2*η)*((M:ℝ)+(M:ℝ)^(1-ξ)*(N:ℝ)^(2*ξ-1)))) := by
        gcongr
      _ = (34*C)*(((M:ℝ)*N)^(ε/2)*((M:ℝ)*N)^(2*η))*
          ((M:ℝ)+(M:ℝ)^(1-ξ)*(N:ℝ)^(2*ξ-1)) := by ring
      _ ≤ (34*C)*((M:ℝ)*N)^ε*((M:ℝ)+(M:ℝ)^(1-ξ)*(N:ℝ)^(2*ξ-1)) := by
        gcongr
      _ ≤ _ := by gcongr; linarith
  · have hs := hsmall η M N hη.le (by linarith) hM hN (le_of_lt (lt_of_not_ge hlarge))
    apply hs.trans
    gcongr
    linarith

end Ostmann.QuadraticSieve

end OAI
