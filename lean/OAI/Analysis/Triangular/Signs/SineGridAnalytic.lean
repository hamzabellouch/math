import OAI.Analysis.Triangular.Signs.SineGridDefs

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction

def realP (s : ℝ) : ℝ := ∏ a : Fin 15,(2*Real.sin (Real.pi*(s-residue a)/36))^2
lemma P_ofReal (s : ℝ) : P (s:ℂ)=(realP s:ℂ) := by
  unfold P realP sineFactor kappa
  push_cast
  congr 1
  funext a
  ring_nf
lemma realP_nonneg (s : ℝ) : 0≤realP s := Finset.prod_nonneg (fun _ _ => sq_nonneg _)
lemma realP_periodic : Function.Periodic realP 36 := by
  intro s
  unfold realP
  apply Finset.prod_congr rfl
  intro a _
  rw [show Real.pi*(s+36-residue a)/36=Real.pi*(s-residue a)/36+Real.pi by ring,Real.sin_add_pi]
  ring
lemma sin_abs_local (u : Fin 30) (j : Fin 15) (y : ℝ) :
    |Real.sin (Real.pi*((localCenter u:ℝ)+y-residue j)/36)|=
      |Real.sin (Real.pi*((localPhase u j:ℝ)+y)/36)| := by
  have he : (localCenter u:ℝ)-residue j=localPhase u j+36*(localShift u j:ℝ) := by
    exact_mod_cast (local_geometry u).2.2 j
  rw [show (localCenter u:ℝ)+y-residue j=(localPhase u j:ℝ)+y+36*(localShift u j:ℝ) by linarith,
    show Real.pi*((localPhase u j:ℝ)+y+36*(localShift u j:ℝ))/36=
      Real.pi*((localPhase u j:ℝ)+y)/36+(localShift u j:ℝ)*Real.pi by ring,
    Real.sin_add_int_mul_pi,abs_mul,abs_zpow]
  norm_num
lemma abs_cell_le (u : Fin 30) (k : Fin 100) {y : ℝ}
    (hy : y∈Icc (cellLo u k:ℝ) (cellHi u k:ℝ)) : |y|≤(cellMagnitude u k:ℝ) := by
  unfold cellMagnitude
  push_cast
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (cellLo u k:ℝ),le_max_left |(cellLo u k:ℝ)| |(cellHi u k:ℝ)|,hy.1]
  · exact hy.2.trans ((le_abs_self _).trans (le_max_right _ _))
lemma cell_factor_lower (u : Fin 30) (k : Fin 100)
    (hg : 0≤cellMagnitude u k ∧ cellMagnitude u k≤3 ∧
      (∀ j : Fin 15,j≠localPivot u → 0≤cellSeparation u k j ∧ cellSeparation u k j≤18))
    (j : Fin 15) {y : ℝ} (hy : y∈Icc (cellLo u k:ℝ) (cellHi u k:ℝ)) :
    (cellFactor u k j:ℝ)*(if j=localPivot u then |y| else 1)≤
      2*|Real.sin (Real.pi*((localCenter u:ℝ)+y-residue j)/36)| := by
  rw [sin_abs_local]
  by_cases hj : j=localPivot u
  · subst j
    simpa only [cellFactor,ite_true,(local_geometry u).2.1,Int.cast_zero,zero_add] using
      sine_vanishing_lower hg.1 hg.2.1 (abs_cell_le u k hy)
  · have hsep : (cellSeparation u k j:ℝ)=
        min ((localPhase u j:ℝ)+(cellLo u k:ℝ)) (36-((localPhase u j:ℝ)+(cellHi u k:ℝ))) := by
      unfold cellSeparation
      push_cast
      rfl
    have ht : (localPhase u j:ℝ)+y∈Icc (cellSeparation u k j:ℝ) (36-cellSeparation u k j) := by
      rw [hsep]
      constructor <;> linarith [min_le_left ((localPhase u j:ℝ)+(cellLo u k:ℝ))
        (36-((localPhase u j:ℝ)+(cellHi u k:ℝ))),
        min_le_right ((localPhase u j:ℝ)+(cellLo u k:ℝ))
        (36-((localPhase u j:ℝ)+(cellHi u k:ℝ))),hy.1,hy.2]
    simpa only [cellFactor,ite_eq_right hj,mul_one] using sine_arc_lower (hg.2.2 j hj).1 (hg.2.2 j hj).2 ht
lemma realP_cell_lower (u : Fin 30) (k : Fin 100)
    (hg : 0≤cellMagnitude u k ∧ cellMagnitude u k≤3 ∧
      (∀ j : Fin 15,j≠localPivot u → 0≤cellSeparation u k j ∧ cellSeparation u k j≤18))
    (hn : ∀ j : Fin 15,0≤cellFactor u k j)
    (hp : cellBarrier u < ∏ j : Fin 15,(cellFactor u k j)^2)
    {y : ℝ} (hy : y∈Icc (cellLo u k:ℝ) (cellHi u k:ℝ)) (hy0 : y≠0) :
    (cellBarrier u:ℝ)*y^2<realP ((localCenter u:ℝ)+y) := by
  have hc : (cellBarrier u:ℝ)<∏ j : Fin 15,(cellFactor u k j:ℝ)^2 := by
    exact_mod_cast hp
  calc
    _ < (∏ j : Fin 15,(cellFactor u k j:ℝ)^2)*y^2 := mul_lt_mul_of_pos_right hc (sq_pos_of_ne_zero hy0)
    _ = ∏ j : Fin 15,((cellFactor u k j:ℝ)*(if j=localPivot u then |y| else 1))^2 := by
      simp only [mul_pow]
      rw [Finset.prod_mul_distrib]
      simp only [ite_pow,one_pow,sq_abs]
      rw [Fintype.prod_ite_eq']
    _ ≤ ∏ j : Fin 15,(2*|Real.sin (Real.pi*((localCenter u:ℝ)+y-residue j)/36)|)^2 := by
      apply Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _)
      intro j _
      have hnon : 0≤(cellFactor u k j:ℝ) := by exact_mod_cast hn j
      apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
      exact cell_factor_lower u k hg j hy
    _ = _ := by simp [realP,mul_pow,sq_abs]
end AtomicTriangular.Construction
end

end OAI
