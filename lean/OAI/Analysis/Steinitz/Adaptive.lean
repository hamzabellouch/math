import OAI.Analysis.Steinitz.LiftedRearrangement

namespace OAI

/-! Energy-preserving sections and adaptive coordinate selection. -/

section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace ShiftedSections
open HeatL2 HeatL2.Diagonal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma section_crossing {K : Set (EuclideanSpace ℝ ι)} (hKm : MeasurableSet K)
    (hKc : Convex ℝ K) (hB : Bound K hKm (1/10000)) (j : ι) :
    ∃ r ∈ activeHeights K (EuclideanSpace.single j 1) (5/2),1 < r := by
  obtain ⟨f,hf,_,G,_,hG,hGs,hn,hH,hh,_⟩ := lifted_test hKm hKc hB j
    (η := 1/4) (ε := 1/10000) (by norm_num) le_rfl (by norm_num) le_rfl
  exact height_above_one _ _ hG hn hH (by linarith) hGs

omit [DecidableEq ι] in
lemma symbol_mul (t : ℝ≥0) (v : ι → ℝ≥0) :
    GaussianKernel.symbol (fun i => t*v i) = fun ξ => (t:ℝ)*GaussianKernel.symbol v ξ := by
  funext ξ
  simp only [GaussianKernel.symbol,NNReal.coe_mul]
  rw [← mul_div_assoc,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma section_rate_le {K : Set (EuclideanSpace ℝ ι)} (hKo : IsOpen K)
    (hKb : Bornology.IsBounded K) (hKc : Convex ℝ K)
    (hB : Bound K hKo.measurableSet (1/10000)) (j : ι)
    (v : ι → ℝ≥0) (hv : ∀ i,0 < v i) :
    sectionRate K hKo (EuclideanSpace.single j 1) (5/2) v 1 ≤
      ((1/10000:ℝ)/2)*∑ i,(v i:ℝ) := by
  let e := EuclideanSpace.single j (1:ℝ)
  let h := sectionRate K hKo e (5/2) v 1
  have hr := section_crossing hKo.measurableSet hKc hB j
  obtain ⟨h0,h1⟩ := activeHeights_contains_one hKc e (5/2) hr
  obtain ⟨a,ha,hline⟩ := EuclideanSteinitz.convex_supporting_line
    (sectionRate_convex hKo hKb hKc e (5/2) v (fun i => (hv i).ne'))
    (sectionRate_monotone hKo hKb hKc e (5/2) v) h0 h1 hr
  let L := h+a*(5/2)
  have hh : 0 ≤ h := sectionRate_nonneg hKo hKb e (5/2) v h1
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hstep : ∀ ε : ℝ, 0 < ε → ε ≤ 1/10000 →
      h ≤ (1+ε*L)*(((1/10000)+ε)/2)*(∑ i,(v i:ℝ)) := by
    intro ε hε hε1
    obtain ⟨η,hη,hη1,hηt⟩ := exists_coordinate_time v hv hε
    obtain ⟨f,hf,hE,G,hGm,hG,hGs,hn,hH,hheight,hcon⟩ :=
      lifted_test hKo.measurableSet hKc hB j hη hη1 hε hε1
    let εn : ℝ≥0 := ⟨ε,hε.le⟩
    let A := GaussianKernel.scaleMap (fun i => εn*v i)
    have hA : gaussianSymbol A = fun ξ => ε*GaussianKernel.symbol v ξ := by
      rw [GaussianKernel.symbol_eq,symbol_mul]
      rfl
    have hlow := integrated_section_rate hKo hKb e (by norm_num : (0:ℝ) ≤ 5/2)
      v hh ha hline hε (by linarith) A hA hGm hG hGs hn hH (by linarith)
    have hupp := integral_sliceEnergy_le hG hf A hcon
    rw [hA] at hupp
    have hweight := energy_weighted_density hf hη v hε.le hηt (fun i => (hE i).le)
    have hboth := hlow.trans (hupp.trans hweight)
    change ε/(1+ε*L)*h ≤ ε*((1/10000)+ε)/2*(∑ i,(v i:ℝ)) at hboth
    have hd : 0 < 1+ε*L := by positivity
    have hc : 0 < ε/(1+ε*L) := by positivity
    apply (mul_le_mul_iff_of_pos_left hc).mp
    calc
      ε/(1+ε*L)*h ≤ ε*((1/10000)+ε)/2*(∑ i,(v i:ℝ)) := hboth
      _ = ε/(1+ε*L)*((1+ε*L)*(((1/10000)+ε)/2)*(∑ i,(v i:ℝ))) := by field_simp
  have hcont : Continuous (fun ε : ℝ => (1+ε*L)*(((1/10000)+ε)/2)*(∑ i,(v i:ℝ))) := by fun_prop
  apply ge_of_tendsto ((hcont.tendsto' 0 _ (by ring)).mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds))
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1/10000 by norm_num)] with ε hε
  exact hstep ε hε.1 hε.2.le

lemma section_bound_positive {K : Set (EuclideanSpace ℝ ι)} (hKo : IsOpen K)
    (hKb : Bornology.IsBounded K) (hKc : Convex ℝ K)
    (hB : Bound K hKo.measurableSet (1/10000)) (j : ι)
    (v : ι → ℝ≥0) (hv : ∀ i,0 < v i) :
    Real.exp (-((1/10000:ℝ)/2)*∑ i,(v i:ℝ)) ≤
      sectionNorm K hKo (EuclideanSpace.single j 1) (5/2) 1 v := by
  have h1 := (activeHeights_contains_one hKc _ _ (section_crossing hKo.measurableSet hKc hB j)).2
  have hp := sectionNorm_pos hKo hKb (EuclideanSpace.single j 1) (5/2) v h1
  have hh := section_rate_le hKo hKb hKc hB j v hv
  rw [← Real.exp_log hp]
  apply Real.exp_le_exp.mpr
  change -Real.log (sectionNorm K hKo (EuclideanSpace.single j 1) (5/2) 1 v) ≤ _ at hh
  linarith

lemma section_bound {K : Set (EuclideanSpace ℝ ι)} (hKo : IsOpen K)
    (hKb : Bornology.IsBounded K) (hKc : Convex ℝ K)
    (hB : Bound K hKo.measurableSet (1/10000)) (j : ι) :
    Bound (sectionDomain K (EuclideanSpace.single j 1) (5/2) 1)
      (section_open hKo _ _ _).measurableSet (1/10000) := by
  intro v
  let e := EuclideanSpace.single j (1:ℝ)
  let D := sectionDomain K e (5/2) 1
  have hstep : ∀ δ : ℝ,0 < δ →
      Real.exp (-((1/10000:ℝ)/2)*(∑ i,((v i:ℝ)+δ))) ≤
        sectionNorm K hKo e (5/2) 1 v := by
    intro δ hδ
    let w : ι → ℝ≥0 := fun i => v i+⟨δ,hδ.le⟩
    have hw : ∀ i,0 < w i := by intro i; change 0 < (v i:ℝ)+δ; positivity
    have hb := section_bound_positive hKo hKb hKc hB j w hw
    have hm : ∀ ξ,GaussianKernel.symbol v ξ ≤ GaussianKernel.symbol w ξ := by
      intro ξ
      unfold GaussianKernel.symbol
      apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) ≤ 2)
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      change (v i:ℝ) ≤ (v i:ℝ)+δ
      linarith
    exact hb.trans (compressed_norm_mono_symbol D (section_open hKo e (5/2) 1).measurableSet
      _ _ (GaussianKernel.symbol_continuous v).aestronglyMeasurable
      (GaussianKernel.symbol_continuous w).aestronglyMeasurable
      (GaussianKernel.symbol_nonneg v) (GaussianKernel.symbol_nonneg w) hm)
  have hc : Continuous (fun δ : ℝ => Real.exp (-((1/10000:ℝ)/2)*(∑ i,((v i:ℝ)+δ)))) := by fun_prop
  apply le_of_tendsto ((hc.tendsto' 0 _ (by simp)).mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact hstep δ hδ

end ShiftedSections

end

section

open MeasureTheory Set
namespace ShiftedSections
open HeatL2.Diagonal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Coeff := EuclideanSpace ℝ ι

structure Good (K : Set (Coeff (ι := ι))) : Prop where
  nonempty : K.Nonempty
  isOpen : IsOpen K
  bounded : Bornology.IsBounded K
  convex : Convex ℝ K
  symmetric : ∀ x ∈ K,-x ∈ K
  bound : Bound K isOpen.measurableSet (1/10000)

omit [DecidableEq ι] in
lemma Good.zero_mem {K : Set (Coeff (ι := ι))} (hK : Good K) : (0:Coeff) ∈ K :=
  zero_mem_of_symmetric_convex hK.convex hK.symmetric hK.nonempty

lemma Good.section {K : Set (Coeff (ι := ι))} (hK : Good K) (j : ι) :
    Good (sectionDomain K (EuclideanSpace.single j 1) (5/2) 1) := by
  refine ⟨?_,section_open hK.isOpen _ _ _,section_bounded hK.bounded _ (by norm_num),
    section_convex hK.convex _ _ _,section_symmetric hK.symmetric _ _ _,
    section_bound hK.isOpen hK.bounded hK.convex hK.bound j⟩
  exact (activeHeights_contains_one hK.convex _ _
    (section_crossing hK.isOpen.measurableSet hK.convex hK.bound j)).2.2

noncomputable def backward : {n : ℕ} → (Fin n → ι) → Set (Coeff (ι := ι)) → Set (Coeff (ι := ι))
  | 0,_,K => K
  | _+1,j,K => sectionDomain (backward (fun i => j i.succ) K) (EuclideanSpace.single (j 0) 1) (5/2) 1

lemma backward_good {n : ℕ} (j : Fin n → ι) {K : Set (Coeff (ι := ι))} (hK : Good K) :
    Good (backward j K) := by
  induction n with
  | zero => exact hK
  | succ n ih => exact (ih (fun i => j i.succ)).section (j 0)

noncomputable def walk : {n : ℕ} → (Fin n → ι) → (Fin n → Coeff (ι := ι) → ℝ) →
    (Fin n → ℝ) → Coeff (ι := ι) → Coeff (ι := ι)
  | 0,_,_,_,x => x
  | _+1,j,q,ε,x => walk (fun i => j i.succ) (fun i => q i.succ) (fun i => ε i.succ)
      (x+(q 0 x+ε 0) • EuclideanSpace.single (j 0) 1)

lemma exists_walk {n : ℕ} (j : Fin n → ι) (q : Fin n → Coeff (ι := ι) → ℝ)
    (hq : ∀ i x,|q i x| ≤ 1/4) {K : Set (Coeff (ι := ι))} (hK : Good K)
    {x : Coeff (ι := ι)} (hx : x ∈ backward j K) :
    ∃ ε : Fin n → ℝ,(∀ i,ε i = -1 ∨ ε i=1) ∧ walk j q ε x ∈ K := by
  induction n generalizing x with
  | zero => exact ⟨Fin.elim0,fun i => i.elim0,hx⟩
  | succ n ih =>
    have htail := backward_good (fun i : Fin n => j i.succ) hK
    obtain ⟨e,he,hxe⟩ := shifted_step htail.convex (EuclideanSpace.single (j 0) 1) hx (hq 0 x)
    obtain ⟨ε,hε,hend⟩ := ih (fun i => j i.succ) (fun i => q i.succ)
      (fun i x => hq i.succ x) hxe
    refine ⟨Fin.cons e ε,?_,?_⟩
    · intro i
      refine Fin.cases he (fun i => ?_) i
      exact hε i
    · simpa only [walk,Fin.cons_zero,Fin.cons_succ] using hend

lemma adaptive_signs {n : ℕ} (j : Fin n → ι) (q : Fin n → Coeff (ι := ι) → ℝ)
    (hq : ∀ i x,|q i x| ≤ 1/4) {K : Set (Coeff (ι := ι))} (hK : Good K) :
    ∃ ε : Fin n → ℝ,(∀ i,ε i = -1 ∨ ε i=1) ∧ walk j q ε 0 ∈ K :=
  exists_walk j q hq hK (backward_good j hK).zero_mem

end ShiftedSections

end

end OAI
