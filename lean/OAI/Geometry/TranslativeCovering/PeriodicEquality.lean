import OAI.Geometry.TranslativeCovering.SourceScale

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

universe u_1 u_2 u_3 u_4 u_5

namespace PeriodicEquality
open Set Filter MeasureTheory TranslativeCovering LatticeAveraging LocalizationWindow
open scoped ENNReal Topology BigOperators Classical
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

lemma volume_cube (n : ℕ) {R : ℝ} (hR : 0≤R) :
    volume (cube n R) = ENNReal.ofReal ((2*R)^n) := by
  have he : cube n R = WithLp.ofLp ⁻¹' (Set.univ.pi (fun _ : Fin n => Set.Icc (-R) R)) := by
    ext x
    simp only [cube,Set.mem_ofPred_eq,Set.mem_preimage,Set.mem_pi,Set.mem_univ,forall_true_left,Set.mem_Icc]
  rw [he,(PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    ((MeasurableSet.univ_pi (fun _ => measurableSet_Icc)).nullMeasurableSet),volume_pi,Measure.pi_pi]
  simp only [Real.volume_Icc,sub_neg_eq_add,← two_mul,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact (ENNReal.ofReal_pow (by positivity) n).symm

noncomputable def centers {n : ℕ} {I : Type u_1} (Λ : Submodule ℤ (Space n)) (p : I → Space n) : Set (Space n) :=
  {x | ∃ (i : I) (l : Λ),x=p i+l.val}

lemma locallyFinite {n : ℕ} {I : Type u_2} [Fintype I]
    (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ] (p : I → Space n) :
    LocallyFiniteCenters (centers Λ p) := by
  intro B hB
  apply ((finite_occurrences Λ p hB).image (fun q : I×Λ => p q.1+q.2.val)).subset
  rintro x ⟨⟨i,l,rfl⟩,hx⟩
  exact ⟨(i,l),hx,rfl⟩

lemma count_le_field {n : ℕ} {I : Type u_3} [Fintype I]
    (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ] (p : I → Space n)
    (z : Space n) (R : ℝ) :
    ((centers Λ p ∩ {x | x-z∈cube n R}).ncard:ℝ≥0∞) ≤
      field Λ p ((cube n R).indicator (fun _ => 1)) z := by
  let B : Set (Space n) := {x | x-z ∈ cube n R}
  have hB : Bornology.IsBounded B := by
    have he : B = (fun x : Space n => x+z) '' cube n R := by
      ext x; constructor
      · intro hx; exact ⟨x-z,hx,sub_add_cancel x z⟩
      · rintro ⟨x,hx,rfl⟩; simpa only [B,mem_ofPred_eq,add_sub_cancel_right] using hx
    rw [he]
    exact ((isCompact_cube n R).image (continuous_id.add continuous_const)).isBounded
  let S : Finset (I×Λ) := (finite_occurrences Λ p hB).toFinset
  have hcard : (centers Λ p ∩ B).ncard≤S.card := by
    have hs : centers Λ p ∩ B ⊆ (S.image (fun q => p q.1+q.2.val) : Set (Space n)) := by
      rintro x ⟨⟨i,l,rfl⟩,hx⟩
      exact Finset.mem_image.mpr ⟨(i,l),by simpa only [S,Set.Finite.mem_toFinset,mem_ofPred_eq] using hx,rfl⟩
    exact (Set.ncard_le_ncard hs).trans (by simpa only [Set.ncard_coe_finset] using Finset.card_image_le (s:=S) (f:=fun q => p q.1+q.2.val))
  have he : ∑ q ∈ S,(cube n R).indicator (fun _ => (1:ℝ≥0∞)) (z-p q.1-q.2.val) = (S.card:ℝ≥0∞) := by
    have hf (q : I×Λ) (hq : q∈S) : (cube n R).indicator (fun _ => (1:ℝ≥0∞)) (z-p q.1-q.2.val)=1 := by
      have hx : p q.1+q.2.val-z ∈ cube n R := by simpa only [S,Set.Finite.mem_toFinset,mem_ofPred_eq,B] using hq
      apply Set.indicator_of_mem
      intro i
      have hh := hx i
      change -R ≤ z i-p q.1 i-q.2.val i ∧ z i-p q.1 i-q.2.val i≤R
      change -R ≤ p q.1 i+q.2.val i-z i ∧ p q.1 i+q.2.val i-z i≤R at hh
      constructor <;> linarith only [hh.1,hh.2]
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using Finset.sum_congr rfl hf
  calc
    _ ≤ (S.card:ℝ≥0∞) := by exact_mod_cast hcard
    _ = ∑ q∈S,(cube n R).indicator (fun _ => (1:ℝ≥0∞)) (z-p q.1-q.2.val) := he.symm
    _ ≤ ∑' q : I×Λ,(cube n R).indicator (fun _ => (1:ℝ≥0∞)) (z-p q.1-q.2.val) := ENNReal.sum_le_tsum S
    _ = _ := by rw [ENNReal.tsum_prod',tsum_fintype]; rfl

lemma cubic_le_periodic_window {n : ℕ} {I : Type u_4} [Fintype I]
    (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (p : I → Space n) {F K : Set (Space n)}
    (hF : IsAddFundamentalDomain Λ F volume) (hF0 : volume F≠0) (hFtop : volume F≠∞)
    {r L : ℝ} (hL : 0<L) (hKr : K⊆cube n r) (hLr : 0≤L+r)
    (hc : ∀ y,∃ (i:I) (l:Λ),y-p i-l.val∈K) :
    cubicCenterInfimum K ≤ ((Fintype.card I:ℝ≥0∞)/volume F)*
      ENNReal.ofReal (((L+r)/L)^n) := by
  have hcover : Covers K (centers Λ p) := by
    intro y
    obtain ⟨i,l,hy⟩ := hc y
    refine ⟨p i+l.val,⟨i,l,rfl⟩,?_⟩
    simpa only [sub_add_eq_sub_sub] using hy
  let w : ℝ≥0∞ := ENNReal.ofReal ((2*L)^n)
  have hw0 : w≠0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hwtop : w≠∞ := ENNReal.ofReal_ne_top
  have hpoint (z : Space n) : cubicCenterInfimum K*w≤field Λ p ((cube n (L+r)).indicator (fun _ => 1)) z := by
    have hh := (cubicCenterInfimum_le_window hL hKr (locallyFinite Λ p) hcover z).trans
      (ENNReal.div_le_div_right (count_le_field Λ p z (L+r)) _)
    exact (ENNReal.le_div_iff_mul_le (Or.inl hw0) (Or.inl hwtop)).mp hh
  let := probability_window hF0 hFtop
  have hi := lintegral_mono (μ:=uniformWindow F) hpoint
  rw [lintegral_const,measure_univ,mul_one,normalized_averaging Λ hF p
    (measurable_const.indicator (isCompact_cube n (L+r)).measurableSet),
    lintegral_indicator (isCompact_cube n (L+r)).measurableSet,lintegral_const,
    Measure.restrict_apply_univ,one_mul,volume_cube n hLr] at hi
  have hh := (ENNReal.le_div_iff_mul_le (Or.inl hw0) (Or.inl hwtop)).mpr hi
  have he : ENNReal.ofReal ((2*(L+r))^n)/w = ENNReal.ofReal (((L+r)/L)^n) := by
    dsimp [w]
    rw [← ENNReal.ofReal_div_of_pos (by positivity),← div_pow]
    congr 2
    field_simp
  simpa only [mul_div_assoc,he] using hh

lemma cubic_le_periodic {n : ℕ} {I : Type u_5} [Fintype I]
    (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (p : I → Space n) {F K : Set (Space n)}
    (hF : IsAddFundamentalDomain Λ F volume) (hF0 : volume F≠0) (hFtop : volume F≠∞)
    (hK : IsCompact K) (hc : ∀ y,∃ (i:I) (l:Λ),y-p i-l.val∈K) :
    cubicCenterInfimum K ≤ (Fintype.card I:ℝ≥0∞)/volume F := by
  obtain ⟨r,hr,hKr⟩ := exists_cube_superset hK
  have heq (L : ℝ) (hL : 0<L) : (L+r)/L=1+r/L := by field_simp
  have ht : Tendsto (fun L : ℝ => ENNReal.ofReal (((L+r)/L)^n)) atTop (𝓝 1) := by
    have hrat := (tendsto_const_nhds (x:=(1:ℝ))).add (tendsto_id.const_div_atTop r)
    have hh := ENNReal.tendsto_ofReal (hrat.pow n)
    simp only [add_zero,one_pow,ENNReal.ofReal_one] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    simp only [id_eq,heq L hL]
  have ht' : Tendsto (fun L : ℝ => ((Fintype.card I:ℝ≥0∞)/volume F)*ENNReal.ofReal (((L+r)/L)^n)) atTop
      (𝓝 ((Fintype.card I:ℝ≥0∞)/volume F)) := by
    simpa only [mul_one] using (ENNReal.Tendsto.const_mul ht (Or.inr (ENNReal.div_ne_top (by finiteness) hF0)))
  apply ge_of_tendsto ht'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  exact cubic_le_periodic_window Λ p hF hF0 hFtop hL hKr (by linarith only [hL,hr]) hc
end PeriodicEquality

end OAI
