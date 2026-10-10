import OAI.Geometry.TranslativeCovering.PatternRounding

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2

namespace LocalizationComplete
open Set Metric MeasureTheory LatticeAveraging LocalizationWindow LocalizationGood
open PatternGeometry PatternRounding LocalizationRounding
open scoped ENNReal BigOperators Classical
abbrev Space (n : ℕ) := SphericalLaw.Space n

lemma window {n : ℕ} {I : Type u_1} [Fintype I] (Λ : Submodule ℤ (Space n))
    [DiscreteTopology Λ] (p : I → Space n) {F : Set (Space n)}
    (hF : IsAddFundamentalDomain Λ F volume) (hF0 : volume F ≠ 0) (hFtop : volume F ≠ ∞)
    {a r β C D L : ℝ} (hD : 0 < D) {N : ℕ} (hN : 0 < N)
    (hbad : uniformWindow F (good Λ p a r β (ENNReal.ofReal C))ᶜ ≤ 1/100)
    (hcount : ∫⁻ z,field Λ p (countFn (closedBall (0 : Space n) L)) z ∂uniformWindow F ≤ (N:ℝ≥0∞)/40) :
    ∃ z,field Λ p (countFn (closedBall (0 : Space n) L)) z ≤ (N:ℝ≥0∞) ∧
      volume (closedBall (0 : Space n) D) ≤ 2*volume
        {y | y ∈ closedBall (0 : Space n) D ∧ y+z ∈ good Λ p a r β (ENNReal.ofReal C)} := by
  let G := good Λ p a r β (ENNReal.ofReal C)
  have hG : MeasurableSet G := measurable_good Λ p a r β _
  let B := closedBall (0 : Space n) D
  let f : Space n → ℝ≥0∞ := Gᶜ.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hG.compl
  have hp (l : Λ) (y : Space n) : f (y+l.val) = f y := by
    simp only [f,G,Set.indicator_apply,Set.mem_compl_iff,periodic_good]
  let Z (z : Space n) : ℝ≥0∞ := ∫⁻ y in B,f (z+y)
  have hZ : Measurable Z := by
    apply Measurable.lintegral_prod_right
    exact hf.comp (measurable_fst.add measurable_snd)
  have hZint : ∫⁻ z,Z z ∂uniformWindow F ≤ volume B/100 := by
    rw [show (∫⁻ z,Z z ∂uniformWindow F) = volume B*∫⁻ z,f z ∂uniformWindow F from
      overlapping_windows Λ hF hF0 hFtop f hf hp]
    rw [lintegral_indicator hG.compl,lintegral_const,Measure.restrict_apply_univ,one_mul]

    calc
      _ ≤ volume B*(1/100) := by simpa only [mul_comm] using mul_le_mul_left hbad (volume B)
      _ = _ := by rw [mul_one_div]
  let := probability_window hF0 hFtop
  obtain ⟨z,hm,hz⟩ := slide (uniformWindow F)
    (field Λ p (countFn (closedBall (0 : Space n) L))) Z
    (measurable_field Λ p (measurable_const.indicator measurableSet_closedBall)) hZ
    (by exact_mod_cast hN.ne') (by finiteness) (measure_closedBall_pos volume (0 : Space n) hD).ne'
    (isCompact_closedBall (0 : Space n) D).measure_ne_top hcount hZint
  refine ⟨z,hm,?_⟩
  let Gz : Set (Space n) := {y | y+z ∈ G}
  have hGz : MeasurableSet Gz := hG.preimage (measurable_id.add_const z)
  have hzeq : Z z = volume (B \ Gz) := by
    have he : (fun y => f (z+y)) = Gzᶜ.indicator (fun _ => 1) := by
      funext y
      simp only [f,Gz,Set.indicator_apply,Set.mem_compl_iff,Set.mem_ofPred_eq,add_comm]
    change (∫⁻ y in B,f (z+y)) = _
    rw [he,lintegral_indicator hGz.compl,lintegral_const,Measure.restrict_restrict hGz.compl,
      Measure.restrict_apply_univ,one_mul,Set.inter_comm]
    rfl
  rw [hzeq] at hz
  have hsplit := measure_inter_add_sdiff (μ := (volume : Measure (Space n))) B hGz
  have hBfinite : volume B ≠ ∞ := (isCompact_closedBall (0 : Space n) D).measure_ne_top
  have hGoodf : volume (B∩Gz) ≠ ∞ := ne_top_of_le_ne_top hBfinite (measure_mono inter_subset_left)
  have hBadf : volume (B\Gz) ≠ ∞ := ne_top_of_le_ne_top hBfinite (measure_mono sdiff_subset)
  have hs := congrArg ENNReal.toReal hsplit
  rw [ENNReal.toReal_add hGoodf hBadf] at hs
  have hr := ENNReal.toReal_mono (by finiteness : volume B/2 ≠ ∞) hz
  rw [ENNReal.toReal_div] at hr
  norm_num only [ENNReal.toReal_ofNat] at hr
  apply (ENNReal.toReal_le_toReal hBfinite (by finiteness)).mp
  change (volume B).toReal ≤ (2*volume (B∩Gz)).toReal
  rw [ENNReal.toReal_mul]
  norm_num only [ENNReal.toReal_ofNat]
  linarith only [hs,hr]

theorem localize {n : ℕ} {I : Type u_2} [Fintype I] (Λ : Submodule ℤ (Space n))
    [DiscreteTopology Λ] (p : I → Space n) {F : Set (Space n)}
    (hF : IsAddFundamentalDomain Λ F volume) (hF0 : volume F ≠ 0) (hFtop : volume F ≠ ∞)
    {a r β C D L h b t u : ℝ} (ha : 0 < a) (hD : 0 < D) (hh : 0 < h) (hC : 0 ≤ C)
    (hL : D+b ≤ L) (hbuf : u+Real.sqrt n*h/2 ≤ β)
    (hlip : (2*(n:ℝ)/a)*(Real.sqrt n*h/2) ≤ 1) {N : ℕ} (hN : 0 < N)
    (hbad : uniformWindow F (good Λ p a r β (ENNReal.ofReal C))ᶜ ≤ 1/100)
    (hcount : ∫⁻ z,field Λ p (countFn (closedBall (0 : Space n) L)) z ∂uniformWindow F ≤ (N:ℝ≥0∞)/40)
    (U : PoissonConfig.Config (SphericalLaw.Sphere n))
    (hcover : ∀ y,∃ (i : I) (l : Λ),y-p i-l.val ∈ RandomBody.body b t U) :
    ∃ (S : Finset (I×Λ)) (q : S → Space n), S.card ≤ N ∧
      (∀ i,q i ∈ alphabet n h (L+Real.sqrt n*h/2)) ∧
      volume (closedBall (0 : Space n) D) ≤ 2*volume
        (roundedGood q a D (r-Real.sqrt n*h/2) u (2*C)) ∧
      ∀ y ∈ closedBall (0 : Space n) D,∃ i,y-q i ∈
        RandomBody.body (b+Real.sqrt n*h/2) (t+Real.sqrt n*h/2) U := by
  obtain ⟨z,hm,hgood⟩ := window Λ p hF hF0 hFtop hD hN hbad hcount
  let S : Finset (I×Λ) := (finite_occurrences Λ p (B := closedBall z L) isBounded_closedBall).toFinset
  have hSmem (j : I×Λ) : j ∈ S ↔ ‖p j.1+j.2.val-z‖ ≤ L := by
    simp only [S,Set.Finite.mem_toFinset,mem_ofPred_eq,mem_closedBall,dist_eq_norm]
  let c (j : S) : Space n := p j.val.1+j.val.2.val-z
  let q (j : S) := rounded h (c j)
  have hc (j : S) : ‖c j‖ ≤ L := (hSmem j).mp j.property
  have hcard : S.card ≤ N := by
    have hs := finite_sum_le_field Λ p (countFn (closedBall (0 : Space n) L)) z S
    have he : ∑ j ∈ S,countFn (closedBall (0 : Space n) L) (z-p j.1-j.2.val) = (S.card:ℝ≥0∞) := by
      have hf (j : I×Λ) (hj : j ∈ S) : countFn (closedBall (0 : Space n) L) (z-p j.1-j.2.val) = 1 := by
        have hn : ‖z-p j.1-j.2.val‖ ≤ L := by
          rw [show z-p j.1-j.2.val = -(p j.1+j.2.val-z) by abel,norm_neg]
          exact (hSmem j).mp hj
        simp only [countFn,Set.indicator_of_mem (mem_closedBall_zero_iff.mpr hn)]
      simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using Finset.sum_congr rfl hf
    rw [he] at hs
    exact_mod_cast hs.trans hm
  have hsub : {y | y ∈ closedBall (0 : Space n) D ∧ y+z ∈ good Λ p a r β (ENNReal.ofReal C)} ⊆
      roundedGood q a D (r-Real.sqrt n*h/2) u (2*C) := by
    intro y hy
    exact good_transfer Λ p S z y ha hh hC hbuf hlip hy.1 hy.2
  refine ⟨S,q,hcard,(fun j => rounded_mem_alphabet hh (c j) (by linarith only [hc j])),
    hgood.trans (by gcongr),?_⟩
  apply rounding_cover c hh U b t D
  intro y hy
  obtain ⟨i,l,hl⟩ := hcover (y+z)
  have hres : ‖y+z-p i-l.val‖ ≤ b := mem_closedBall_zero_iff.mp hl.1
  have hm : (i,l) ∈ S := by
    apply (hSmem (i,l)).mpr
    calc
      ‖p i+l.val-z‖ = ‖y-(y+z-p i-l.val)‖ := by congr 1 ; abel
      _ ≤ ‖y‖+‖y+z-p i-l.val‖ := norm_sub_le _ _
      _ ≤ D+b := add_le_add (mem_closedBall_zero_iff.mp hy) hres
      _ ≤ L := hL
  refine ⟨⟨(i,l),hm⟩,?_⟩
  change y-(p i+l.val-z) ∈ RandomBody.body b t U
  rw [show y-(p i+l.val-z)=y+z-p i-l.val by abel]
  exact hl
end LocalizationComplete

end OAI
