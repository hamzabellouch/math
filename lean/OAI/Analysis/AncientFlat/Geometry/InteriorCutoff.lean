import OAI.Analysis.AncientFlat.Regularity.CompactHolder

namespace OAI
noncomputable section
open Set Filter Metric Topology
open scoped ContDiff
namespace ParabolicLocalization
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
def baseBump (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] : ContDiffBump (0 : V) :=
  ⟨1,3/2,by norm_num,by norm_num⟩
def cutoff (t : ℝ) (x : V) : ℝ := baseBump ℝ t * baseBump V x
def cutoffTime (t : ℝ) (x : V) : ℝ := deriv (baseBump ℝ) t * baseBump V x
lemma cutoff_contDiff (t : ℝ) : ContDiff ℝ ∞ (cutoff t : V → ℝ) :=
  contDiff_const.mul ((baseBump V).contDiff (n := (⊤ : ℕ∞)))
lemma cutoff_hasDerivAt (t : ℝ) (x : V) :
    HasDerivAt (fun s => cutoff s x) (cutoffTime t x) t :=
  (((baseBump ℝ).contDiff (n := (⊤ : ℕ∞))).differentiable (by simp) t).hasDerivAt.mul_const _
lemma cutoff_nonneg (t : ℝ) (x : V) : 0≤cutoff t x :=
  mul_nonneg (baseBump ℝ).nonneg (baseBump V).nonneg
lemma cutoff_le_one (t : ℝ) (x : V) : cutoff t x≤1 := by
  exact (mul_le_mul (baseBump ℝ).le_one (baseBump V).le_one (baseBump V).nonneg zero_le_one).trans_eq (one_mul _)
lemma cutoff_eq_one {t : ℝ} {x : V} (ht : |t|≤1) (hx : ‖x‖≤1) : cutoff t x=1 := by
  unfold cutoff
  rw [(baseBump ℝ).one_of_mem_closedBall (by simpa [baseBump,Real.dist_eq] using ht),
    (baseBump V).one_of_mem_closedBall (by simpa [baseBump,dist_zero_right] using hx)]
  exact one_mul _
lemma cutoff_zero_time {t : ℝ} (ht : 3/2≤|t|) (x : V) : cutoff t x=0 := by
  unfold cutoff
  rw [(baseBump ℝ).zero_of_le_dist (by simpa [baseBump,Real.dist_eq] using ht),zero_mul]
lemma cutoff_compact (t : ℝ) : HasCompactSupport (cutoff t : V → ℝ) :=
  (baseBump V).hasCompactSupport.mul_left
lemma cutoff_zero_space (t : ℝ) {x : V} (hx : 3/2≤‖x‖) : cutoff t x=0 := by
  unfold cutoff
  rw [(baseBump V).zero_of_le_dist (by simpa [baseBump,dist_zero_right] using hx),mul_zero]
lemma cutoff_jet (n : ℕ) (t : ℝ) (x : V) :
    iteratedFDeriv ℝ n (cutoff t : V → ℝ) x =
      baseBump ℝ t • iteratedFDeriv ℝ n (baseBump V) x := by
  change iteratedFDeriv ℝ n (fun y => baseBump ℝ t • baseBump V y) x=_
  exact iteratedFDeriv_const_smul_apply' (baseBump V).contDiffAt
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
lemma compact_separated_smul (f : V → E) (g : ℝ → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    HasCompactSupport (fun p : V × ℝ => g p.2 • f p.1) := by
  apply HasCompactSupport.of_support_subset_isCompact (hf.isCompact.prod hg.isCompact)
  intro p hp
  have hne : g p.2 • f p.1≠0 := hp
  refine ⟨subset_tsupport f ?_,subset_tsupport g ?_⟩
  · intro he; exact hne (by rw [he,smul_zero])
  · intro he; exact hne (by rw [he,zero_smul])
lemma cutoff_jet_holder (α : ℝ) (hα : 0<α) (hα1 : α≤1) (n : ℕ) :
    ∃ C : ℝ, 0<C ∧ HolderBound α univ
      (fun p : V × ℝ => iteratedFDeriv ℝ n (cutoff p.2) p.1) C := by
  have hd : ContDiff ℝ 1 (iteratedFDeriv ℝ n (baseBump V)) :=
    ((baseBump V).contDiff (n := 1+n)).iteratedFDeriv_right (by push_cast; rfl)
  have hs := compact_separated_smul (iteratedFDeriv ℝ n (baseBump V)) (baseBump ℝ)
    ((baseBump V).hasCompactSupport.iteratedFDeriv n) (baseBump ℝ).hasCompactSupport
  have hc : ContDiff ℝ 1 (fun p : V × ℝ => baseBump ℝ p.2 • iteratedFDeriv ℝ n (baseBump V) p.1) :=
    ((baseBump ℝ).contDiff.comp contDiff_snd).smul (hd.comp contDiff_fst)
  simpa only [cutoff_jet] using compact_contDiff_holder α hα hα1 _ hc hs
lemma cutoff_time_holder (α : ℝ) (hα : 0<α) (hα1 : α≤1) :
    ∃ C : ℝ, 0<C ∧ HolderBound α univ (fun p : V × ℝ => cutoffTime p.2 p.1) C := by
  have hd : ContDiff ℝ 1 (deriv (baseBump ℝ)) :=
    ((baseBump ℝ).contDiff (n := 2)).deriv'
  have hs := compact_separated_smul (baseBump V) (deriv (baseBump ℝ))
    (baseBump V).hasCompactSupport (baseBump ℝ).hasCompactSupport.deriv
  exact compact_contDiff_holder α hα hα1 _
    ((hd.comp contDiff_snd).mul ((baseBump V).contDiff.comp contDiff_fst)) hs
end ParabolicLocalization

end

end OAI
