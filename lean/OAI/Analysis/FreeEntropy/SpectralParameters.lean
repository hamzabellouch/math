import OAI.Analysis.FreeEntropy.SpectralTestFunctions

namespace OAI

noncomputable section
open Finset Filter Set
open scoped Topology
namespace FiniteEntropySeparation
variable {p : ℕ}
 def spectralBasis (p : ℕ) (l : Fin p) : Polynomial ℝ := Lagrange.basis univ (equidiscreteAtom p) l
 def spectralAnnihilator (p : ℕ) : Polynomial ℝ := ∏l : Fin p,(Polynomial.X-Polynomial.C (equidiscreteAtom p l))
 def badFraction (p : ℕ) : ℝ := min (1/4096:ℝ) (1/(2*p))
 theorem badFraction_pos [NeZero p] : 0<badFraction p := by
  have hp : (0:ℝ)<p := by exact_mod_cast NeZero.pos p
  unfold badFraction
  positivity
 theorem spectralBasis_eval (hp : 2≤p) (l k : Fin p) :
    (spectralBasis p l).eval (equidiscreteAtom p k)=if l=k then 1 else 0 := by
  by_cases h : l=k
  · subst k; simp [spectralBasis,Lagrange.eval_basis_self (equidiscreteAtom_injective hp).injOn]
  · simp [spectralBasis,h,Lagrange.eval_basis_of_ne h]
 theorem spectralAnnihilator_eval (r : ℝ) :
    (spectralAnnihilator p).eval r=∏l : Fin p,(r-equidiscreteAtom p l) := by
  rw [spectralAnnihilator, Polynomial.eval_prod]
  simp
 theorem spectralAnnihilator_at (l : Fin p) : (spectralAnnihilator p).eval (equidiscreteAtom p l)=0 := by
  rw [spectralAnnihilator_eval]
  exact prod_eq_zero (mem_univ l) (sub_self _)
 theorem exists_spectral_parameters [NeZero p] (hp : 2≤p) : ∃δ Δ : ℝ,0<δ ∧ 0<Δ ∧ δ≤Δ/4 ∧
    (∀i j : Fin p,i≠j → Δ≤|equidiscreteAtom p i-equidiscreteAtom p j|) ∧
    (∀l : Fin p,∀r : ℝ,|r-equidiscreteAtom p l|≤δ → (3:ℝ)/4≤((spectralBasis p l).eval r)^2) := by
  classical
  let Δ : ℝ := univ.inf' univ_nonempty (fun ij : Fin p×Fin p => if ij.1=ij.2 then 1 else |equidiscreteAtom p ij.1-equidiscreteAtom p ij.2|)
  have hΔ : 0<Δ := by
    apply (lt_inf'_iff _).mpr
    rintro ⟨i,j⟩ _
    dsimp
    split_ifs with h
    · norm_num
    · exact abs_pos.mpr (sub_ne_zero.mpr (fun he => h (equidiscreteAtom_injective hp he)))
  have hsep (i j : Fin p) (h : i≠j) : Δ≤|equidiscreteAtom p i-equidiscreteAtom p j| := by
    have hh := inf'_le (s := (univ:Finset (Fin p×Fin p))) (f := fun ij : Fin p×Fin p => if ij.1=ij.2 then (1:ℝ) else |equidiscreteAtom p ij.1-equidiscreteAtom p ij.2|) (mem_univ (i,j))
    simpa only [ite_eq_right h] using hh
  have hev : ∀ᶠs : ℝ in 𝓝 0,∀l : Fin p,(3:ℝ)/4<((spectralBasis p l).eval (equidiscreteAtom p l+s))^2 := by
    rw [eventually_all]
    intro l
    have hc : Continuous (fun s : ℝ => ((spectralBasis p l).eval (equidiscreteAtom p l+s))^2) := by fun_prop
    have hh : (3:ℝ)/4<((spectralBasis p l).eval (equidiscreteAtom p l+0))^2 := by norm_num [spectralBasis_eval hp]
    exact (isOpen_lt continuous_const hc).mem_nhds hh
  obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp hev
  let δ := min (Δ/4) (ε/2)
  refine ⟨δ,Δ,lt_min (by positivity) (by positivity),hΔ,min_le_left _ _,hsep,?_⟩
  intro l r hr
  have hs : r-equidiscreteAtom p l ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero]
    exact hr.trans_lt (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  have hh := he hs l
  convert hh.le using 1 ; congr 2 ; ring
 def spectralGood (p : ℕ) (δ Δ : ℝ) (m : List (Fin (p+1)) → ℂ) : Prop :=
    (∀i : Fin p,(3:ℝ)/4<(m [i.castSucc,i.castSucc]).re ∧
      (m [i.castSucc,i.castSucc,i.castSucc,i.castSucc]).re<4 ∧
      commutatorMoment m i.castSucc (Fin.last p)<Δ^2/64) ∧
    (∀l : Fin p,univariateMoment m ((spectralBasis p l)^2) (Fin.last p)<9/(8*p)) ∧
    univariateMoment m ((spectralAnnihilator p)^2) (Fin.last p)<badFraction p*δ^(2*p)
 theorem spectralGood_isOpen (p : ℕ) (δ Δ : ℝ) : IsOpen {m | spectralGood p δ Δ m} := by
  unfold spectralGood
  simp only [ofPred_and,ofPred_forall]
  apply IsOpen.inter
  · apply isOpen_iInter_of_finite
    intro i
    exact (isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_apply _))).inter
      ((isOpen_lt (Complex.continuous_re.comp (continuous_apply _)) continuous_const).inter
      (isOpen_lt (commutatorMoment_continuous _ _) continuous_const))
  · exact (isOpen_iInter_of_finite (fun l => isOpen_lt (univariateMoment_continuous _ _) continuous_const)).inter
      (isOpen_lt (univariateMoment_continuous _ _) continuous_const)
 theorem spectralGood_C [NeZero p] (hp : 2≤p) {δ Δ : ℝ} (hδ : 0<δ) (hΔ : 0<Δ) :
    spectralGood p δ Δ (wordMoment (Model.τ p) (Model.C p)) := by
  refine ⟨?_,?_,?_⟩
  · intro i
    rw [Model.C_second,Model.C_fourth,Model.C_commutator]
    refine ⟨by norm_num,by norm_num,by positivity⟩
  · intro l
    rw [Model.C_univariateMoment]
    simp only [Polynomial.eval_pow,spectralBasis_eval hp]
    have he : (∑k : Fin p,(if l=k then (1:ℝ) else 0)^2)=1 := by simp [eq_comm]
    rw [he,mul_one]
    have hp' : (0:ℝ)<p := by exact_mod_cast NeZero.pos p
    apply (mul_lt_mul_iff_left₀ hp').mp
    field_simp
    norm_num
  · rw [Model.C_univariateMoment]
    simp only [Polynomial.eval_pow,spectralAnnihilator_at,zero_pow (by norm_num : 2≠0),sum_const_zero,mul_zero]
    exact mul_pos badFraction_pos (pow_pos hδ _)
 theorem exists_small_h_spectralGood [NeZero p] (hp : 2≤p) {δ Δ : ℝ} (hδ : 0<δ) (hΔ : 0<Δ) :
    ∃h : ℝ,0<h ∧ h<1 ∧ spectralGood p δ Δ (wordMoment (Model.τ p) (Model.X p h)) := by
  have hh : {h : ℝ | spectralGood p δ Δ (wordMoment (Model.τ p) (Model.X p h))} ∈ 𝓝 0 := by
    apply ((spectralGood_isOpen p δ Δ).preimage (Model.continuous_X_moments p)).mem_nhds
    simpa [Model.X_zero] using spectralGood_C hp hδ hΔ
  obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp hh
  let h := min (ε/2) (1/2)
  have hp' : 0<h := lt_min (by positivity) (by norm_num)
  refine ⟨h,hp',lt_of_le_of_lt (min_le_right _ _) (by norm_num),he ?_⟩
  rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hp']
  exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
end FiniteEntropySeparation

end

end OAI
