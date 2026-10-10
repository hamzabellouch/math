import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.GaugeBounds

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal
namespace SLEExactGauge.PlanarGrid

 
def cell (r : ℝ) (p : ℤ×ℤ) : Set ℂ :=
  {z | (p.1:ℝ)*r ≤ z.re ∧ z.re ≤ ((p.1:ℝ)+1)*r ∧
    (p.2:ℝ)*r ≤ z.im ∧ z.im ≤ ((p.2:ℝ)+1)*r}

lemma cell_measurable (r : ℝ) (p : ℤ×ℤ) : MeasurableSet (cell r p) := by
  unfold cell
  measurability

 
lemma mem_floor_cell (r : ℝ) (hr : 0 < r) (z : ℂ) :
    z ∈ cell r (⌊z.re/r⌋,⌊z.im/r⌋) := by
  have lower (x : ℝ) : (⌊x/r⌋:ℝ)*r ≤ x := (le_div_iff₀ hr).mp (Int.floor_le _)
  have upper (x : ℝ) : x ≤ ((⌊x/r⌋:ℝ)+1)*r :=
    (div_le_iff₀ hr).mp (Int.lt_floor_add_one _).le
  exact ⟨lower _,upper _,lower _,upper _⟩

 

def nearby (r s : ℝ) (z : ℂ) : Finset (ℤ×ℤ) :=
  (Finset.Icc ⌊(z.re-s)/r⌋ ⌊(z.re+s)/r⌋).product
    (Finset.Icc ⌊(z.im-s)/r⌋ ⌊(z.im+s)/r⌋)

lemma floor_interval_card (r : ℝ) (hr : 0 < r) (x s : ℝ) (hs : 0 ≤ s) :
    ((Finset.Icc ⌊(x-s)/r⌋ ⌊(x+s)/r⌋).card:ℝ)  ≤  2*(s/r)+2 := by
  have hlo : (x-s)/r ≤ (x+s)/r := div_le_div_of_nonneg_right (by linarith) hr.le
  have hf : ⌊(x-s)/r⌋  ≤  ⌊(x+s)/r⌋ := Int.floor_mono hlo
  have hc := Int.card_Icc_of_le _ _ (Int.le_add_one hf)
  have hc' : ((Finset.Icc ⌊(x-s)/r⌋ ⌊(x+s)/r⌋).card:ℝ) =
      (⌊(x+s)/r⌋:ℝ)+1-(⌊(x-s)/r⌋:ℝ) := by exact_mod_cast hc
  rw [hc']
  have h1 := Int.floor_le ((x+s)/r)
  have h2 := Int.lt_floor_add_one ((x-s)/r)
  have he : (x+s)/r-(x-s)/r=2*(s/r) := by ring
  linarith

lemma nearby_card (r : ℝ) (hr : 0 < r) (s : ℝ) (hs : 0 ≤ s) (z : ℂ) :
    ((nearby r s z).card:ℝ)  ≤  16*max 1 ((s/r)^2) := by
  have h1 := floor_interval_card r hr z.re s hs
  have h2 := floor_interval_card r hr z.im s hs
  have hq : 0 ≤ s/r := div_nonneg hs hr.le
  have hprod : ((nearby r s z).card:ℝ) ≤ (2*(s/r)+2)^2 := by
    rw [nearby,Finset.product_eq_sprod,Finset.card_product,Nat.cast_mul,pow_two]
    exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)
  refine hprod.trans ?_
  by_cases hq1 : s/r ≤ 1
  · have hsq : (s/r)^2 ≤ 1 := by nlinarith
    rw [max_eq_left hsq]
    nlinarith
  · have hq1' : 1 ≤ s/r := (le_of_not_ge hq1)
    have hsq : 1 ≤ (s/r)^2 := by nlinarith
    rw [max_eq_right hsq]
    nlinarith [sq_nonneg (s/r-1)]

lemma subset_nearby (r : ℝ) (hr : 0 < r) (s : ℝ) (hs : 0 ≤ s)
    (U : Set ℂ) (hU : ediam U ≤ ENNReal.ofReal s) (z : ℂ) (hz : z ∈ U) :
    U ⊆ ⋃p ∈ nearby r s z,cell r p := by
  intro w hw
  have hd : dist w z ≤ s := by
    apply (ENNReal.ofReal_le_ofReal_iff hs).mp
    rw [←edist_dist]
    exact (edist_le_ediam_of_mem hw hz).trans hU
  rw [dist_eq_norm] at hd
  have hre : |w.re-z.re| ≤ s := (Complex.abs_re_le_norm (w-z)).trans hd
  have him : |w.im-z.im| ≤ s := (Complex.abs_im_le_norm (w-z)).trans hd
  rcases abs_le.mp hre with ⟨hre1,hre2⟩
  rcases abs_le.mp him with ⟨him1,him2⟩
  have hindex : (⌊w.re/r⌋,⌊w.im/r⌋) ∈ nearby r s z := by
    simp only [nearby,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc]
    constructor  <;> constructor  <;> apply Int.floor_mono  <;>
      apply div_le_div_of_nonneg_right _ hr.le  <;> linarith
  exact mem_iUnion.mpr ⟨_,mem_iUnion.mpr ⟨hindex,mem_floor_cell r hr w⟩⟩

 

theorem outerMass_le (ν : OuterMeasure ℂ) (r : ℝ) (hr : 0 < r)
    (B : ℝ) (hB : 0 ≤ B) (hcell : ∀p,ν (cell r p) ≤ ENNReal.ofReal B)
    (s : ℝ) (hs : 0 ≤ s) (U : Set ℂ) (hU : ediam U ≤ ENNReal.ofReal s) :
    ν U ≤ ENNReal.ofReal (16*B*max 1 ((s/r)^2)) := by
  classical
  by_cases hn : U.Nonempty
  · obtain ⟨z,hz⟩ := hn
    calc
      ν U ≤ ν (⋃p ∈ nearby r s z,cell r p) := ν.mono (subset_nearby r hr s hs U hU z hz)
      _ ≤ ∑p ∈ nearby r s z,ν (cell r p) := measure_biUnion_finset_le _ _
      _ ≤ ∑_p ∈ nearby r s z,ENNReal.ofReal B := Finset.sum_le_sum (fun p _=>hcell p)
      _=ENNReal.ofReal (((nearby r s z).card:ℝ)*B) := by
        simp only [Finset.sum_const,nsmul_eq_mul,ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by
        nlinarith [mul_le_mul_of_nonneg_right (nearby_card r hr s hs z) hB])
  · simp [Set.not_nonempty_iff_eq_empty.mp hn]

end SLEExactGauge.PlanarGrid
end
end
 

 
section
 

noncomputable section
open MeasureTheory Set Filter Metric
open scoped NNReal ENNReal Topology Classical
namespace SLEExactGauge.PlanarGrid

lemma cell_closed (r : ℝ) (p : ℤ×ℤ) : IsClosed (cell r p) := by
  exact (isClosed_le continuous_const Complex.continuous_re).inter
    ((isClosed_le Complex.continuous_re continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const)))

lemma cell_dist (r : ℝ) (_hr : 0≤r) (p : ℤ×ℤ) {z w : ℂ}
    (hz : z∈cell r p) (hw : w∈cell r p) : dist w z≤2*r := by
  have hre : |w.re-z.re|≤r := abs_le.mpr ⟨by linarith [hw.1,hz.2.1],by linarith [hz.1,hw.2.1]⟩
  have him : |w.im-z.im|≤r := abs_le.mpr ⟨by linarith [hw.2.2.1,hz.2.2.2],by linarith [hz.2.2.1,hw.2.2.2]⟩
  rw [dist_eq_norm]
  exact (Complex.norm_le_abs_re_add_abs_im (w-z)).trans (by simpa only [two_mul,Complex.sub_re,Complex.sub_im] using (add_le_add hre him))

 
lemma index_mem_pair (r : ℝ) (hr : 0<r) (x : ℝ) (p : ℤ)
    (hp : (p:ℝ)*r≤x) (hq : x≤((p:ℝ)+1)*r) :
    p∈({⌊x/r⌋,⌊x/r⌋-1} : Finset ℤ) := by
  have hl : p≤⌊x/r⌋ := Int.le_floor.mpr ((le_div_iff₀ hr).mpr hp)
  have hu : ⌊x/r⌋≤p+1 := by
    have hh := (div_le_iff₀ hr).mpr hq
    have hf := Int.floor_mono hh
    have he : ((p+1:ℤ):ℝ)=(p:ℝ)+1 := by norm_cast
    rw [←he,Int.floor_intCast] at hf
    exact hf
  simp only [Finset.mem_insert,Finset.mem_singleton]
  omega

def containingIndices (r : ℝ) (z : ℂ) : Finset (ℤ×ℤ) :=
  ({⌊z.re/r⌋,⌊z.re/r⌋-1} : Finset ℤ).product {⌊z.im/r⌋,⌊z.im/r⌋-1}

lemma mem_containingIndices (r : ℝ) (hr : 0<r) (z : ℂ) (p : ℤ×ℤ)
    (hp : z∈cell r p) : p∈containingIndices r z := by
  exact Finset.mem_product.mpr ⟨index_mem_pair r hr z.re p.1 hp.1 hp.2.1,
    index_mem_pair r hr z.im p.2 hp.2.2.1 hp.2.2.2⟩

lemma containingIndices_card (r : ℝ) (z : ℂ) : (containingIndices r z).card≤4 := by
  have h (i : ℤ) : ({i,i-1} : Finset ℤ).card≤2 := Finset.card_insert_le .. |>.trans (by simp)
  rw [containingIndices,Finset.product_eq_sprod,Finset.card_product]
  exact (Nat.mul_le_mul (h _) (h _)).trans (by norm_num)

 
lemma tsum_cell_mass (ν : Measure ℂ) (r : ℝ) (hr : 0<r) :
    (∑'p : ℤ×ℤ,ν (cell r p)) ≤ 4*ν univ := by
  have he (p : ℤ×ℤ) : ν (cell r p)=∫⁻z,(cell r p).indicator (fun _=>1) z∂ν :=
    (lintegral_indicator_one (cell_measurable _ _)).symm
  simp_rw [he]
  rw [←lintegral_tsum (fun p=>(measurable_const.indicator (cell_measurable r p)).aemeasurable)]
  calc
    _≤∫⁻z,(4:ℝ≥0∞)∂ν := by
      apply lintegral_mono
      intro z
      have ht : (∑'p : ℤ×ℤ,(cell r p).indicator (fun _=>(1:ℝ≥0∞)) z)=
          ∑p∈containingIndices r z,(cell r p).indicator (fun _=>(1:ℝ≥0∞)) z := by
        apply tsum_eq_sum
        intro p hp
        exact Set.indicator_of_notMem (fun h=>hp (mem_containingIndices r hr z p h)) _
      change (∑'p : ℤ×ℤ,(cell r p).indicator (fun _=>(1:ℝ≥0∞)) z)≤4
      rw [ht]
      calc
        _≤∑_p∈containingIndices r z,(1:ℝ≥0∞) := by
          apply Finset.sum_le_sum
          intro p _
          exact Set.indicator_le_self' (fun _ _=>zero_le) _
        _=((containingIndices r z).card:ℝ≥0∞) := by simp
        _≤4 := by exact_mod_cast containingIndices_card r z
    _=4*ν univ := lintegral_const _

end SLEExactGauge.PlanarGrid
end
end
 

 
section
 

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal NNReal
namespace SLEExactGauge.PlanarGrid

 
def maximalMass (ν : Measure ℂ) (s : ℝ) : ℝ :=
  sSup {v | ∃U : Set ℂ, ediam U ≤ ENNReal.ofReal s ∧ v=(ν U).toReal}

lemma maximalMass_nonempty (ν : Measure ℂ) (s : ℝ) :
    Set.Nonempty {v | ∃U : Set ℂ, ediam U ≤ ENNReal.ofReal s ∧ v=(ν U).toReal} :=
  ⟨0,∅,by simp,by simp⟩

lemma maximalMass_bdd (ν : Measure ℂ) [IsFiniteMeasure ν] (s : ℝ) :
    BddAbove {v | ∃U : Set ℂ, ediam U ≤ ENNReal.ofReal s ∧ v=(ν U).toReal} := by
  refine ⟨(ν univ).toReal,?_⟩
  rintro v ⟨U,hU,rfl⟩
  exact ENNReal.toReal_mono (measure_ne_top ν univ) (measure_mono (subset_univ _))

lemma maximalMass_bounds (ν : Measure ℂ) [IsFiniteMeasure ν] (s : ℝ) :
    0 ≤ maximalMass ν s ∧ maximalMass ν s ≤ (ν univ).toReal := by
  constructor
  · exact le_csSup (maximalMass_bdd ν s) ⟨∅,by simp,by simp⟩
  · apply csSup_le (maximalMass_nonempty ν s)
    rintro v ⟨U,hU,rfl⟩
    exact ENNReal.toReal_mono (measure_ne_top ν univ) (measure_mono (subset_univ _))

lemma mass_le_maximalMass (ν : Measure ℂ) [IsFiniteMeasure ν]
    (s : ℝ) (U : Set ℂ) (hU : ediam U ≤ ENNReal.ofReal s) :
    (ν U).toReal ≤ maximalMass ν s :=
  le_csSup (maximalMass_bdd ν s) ⟨U,hU,rfl⟩

lemma maximalMass_grid (ν : Measure ℂ) [IsFiniteMeasure ν] (r : ℝ) (hr : 0<r)
    (B : ℝ) (hB : 0 ≤ B) (hcell : ∀p,ν (cell r p) ≤ ENNReal.ofReal B)
    (s : ℝ) (hs : 0 ≤ s) :
    maximalMass ν s ≤ 16*B*max 1 ((s/r)^2) := by
  apply csSup_le (maximalMass_nonempty ν s)
  rintro v ⟨U,hU,rfl⟩
  exact ENNReal.toReal_le_of_le_ofReal (by positivity)
    (outerMass_le ν.toOuterMeasure r hr B hB hcell s hs U hU)

 

theorem full_density {ι : Type*} [Nonempty ι] (d : ℝ) (b ρ : ι→ℝ)
    (hb : ∀i,0<b i) (hρ : ∀i,0<ρ i) (E : Finset ι)
    (ν : Measure ℂ) [IsFiniteMeasure ν] [NullSingletonClass ν]
    (K : ℝ) (hK : 0 ≤ K)
    (hcell : ∀i,i∉E → ∀p,ν (cell (ρ i) p) ≤ ENNReal.ofReal (K*b i*(ρ i)^d)) :
    ∃C : ℝ, 0<C ∧ ∀U : Set ℂ, ediam U ≤ 1 →
      ν U ≤ ENNReal.ofReal C * Deterministic.diameterCost (QuadraticGauge.gauge d b ρ) (ediam U) := by
  obtain ⟨C,hC,hbound⟩ := QuadraticGauge.finite_exclusions d b ρ hb hρ E
    (maximalMass ν) (ν univ).toReal (16*K) (fun s _=>maximalMass_bounds ν s)
    (by
      intro i hi s hs
      have H := maximalMass_grid ν (ρ i) (hρ i) (K*b i*(ρ i)^d) (mul_nonneg (mul_nonneg hK (hb i).le) (Real.rpow_nonneg (hρ i).le _))
        (hcell i hi) s hs.le
      dsimp only [QuadraticGauge.entry]
      convert H using 1; ring)
  refine ⟨C,hC,?_⟩
  intro U hU
  have hfin : ediam U≠∞ := ne_top_of_le_ne_top (by norm_num) hU
  by_cases hz : ediam U=0
  · have he : ν U=0 := (ediam_eq_zero_iff.mp hz).measure_zero ν
    rw [he]
    exact bot_le
  · have hs : 0<(ediam U).toReal := ENNReal.toReal_pos hz hfin
    have hm := (mass_le_maximalMass ν (ediam U).toReal U (by
      rw [ENNReal.ofReal_toReal hfin])).trans (hbound _ hs)
    have he := ENNReal.ofReal_le_ofReal hm
    rw [ENNReal.ofReal_toReal (measure_ne_top ν U),ENNReal.ofReal_mul hC.le] at he
    simpa only [Deterministic.diameterCost,ite_eq_right hfin] using he

 

theorem hausdorff_pos_of_grid {ι : Type*} [Nonempty ι] (d : ℝ) (b ρ : ι→ℝ)
    (hb : ∀i,0<b i) (hρ : ∀i,0<ρ i) (E : Finset ι)
    (ν : Measure ℂ) [IsFiniteMeasure ν] [NullSingletonClass ν]
    (K : ℝ) (hK : 0 ≤ K)
    (hcell : ∀i,i∉E → ∀p,ν (cell (ρ i) p) ≤ ENNReal.ofReal (K*b i*(ρ i)^d))
    (A : Set ℂ) (hA : 0<ν A) : 0<Target.hausdorff (QuadraticGauge.gauge d b ρ) A := by
  obtain ⟨C,hC,hbound⟩ := full_density d b ρ hb hρ E ν K hK hcell
  exact Deterministic.hausdorff_pos_of_mass_bound (δ := 1) (ν := ν.toOuterMeasure)
    (by norm_num) (ENNReal.ofReal_pos.mpr hC).ne' ENNReal.ofReal_ne_top hbound hA

end SLEExactGauge.PlanarGrid
end
end
 

 
section
 

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Classical
namespace SLEExactGauge.PlanarGrid

 
def badRegion (μ : Measure ℂ) (r B : ℝ) : Set ℂ :=
  ⋃ (p : ℤ×ℤ) (_ : ENNReal.ofReal B<μ (cell r p)),cell r p

lemma badRegion_measurable (μ : Measure ℂ) (r B : ℝ) : MeasurableSet (badRegion μ r B) :=
  MeasurableSet.iUnion (fun p=>MeasurableSet.iUnion (fun _=>cell_measurable r p))

 
def retained {ι X : Type*} (bad : ι→Set X) (E : Finset ι) : Set X :=
  {z | ∀i,i∉E → z∉bad i}

lemma retained_measurable {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (bad : ι→Set X) (hbad : ∀i,MeasurableSet (bad i)) (E : Finset ι) :
    MeasurableSet (retained bad E) := by
  have he : retained bad E = ⋂i,⋂(_ : i∉E),(bad i)ᶜ := by ext z; simp [retained]
  rw [he]
  exact MeasurableSet.iInter (fun i=>MeasurableSet.iInter (fun _=>(hbad i).compl))

lemma exists_positive_retained {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (σ : Measure X) (bad : ι→Set X) (hfinite : ∀ᵐ z∂σ,{i | z∈bad i}.Finite)
    (A : Set X) (hA : 0<σ A) :
    ∃E : Finset ι,0<σ (A∩retained bad E) := by
  have hc : ∀ᵐ z∂σ,z∈⋃E : Finset ι,retained bad E := by
    filter_upwards [hfinite] with z hz
    refine mem_iUnion.mpr ⟨hz.toFinset,?_⟩
    intro i hi hmem
    exact hi (hz.mem_toFinset.mpr hmem)
  by_contra! hh
  have hzero : σ (A∩⋃E : Finset ι,retained bad E)=0 := by
    rw [Set.inter_iUnion]
    exact measure_iUnion_null_iff.mpr (fun E=>le_antisymm (hh E) bot_le)
  have he : (A : Set X)=ᵐ[σ] (A∩⋃E : Finset ι,retained bad E : Set X) := by
    filter_upwards [hc] with z hz
    simp only [mem_inter_iff,hz,and_true]
  exact hA.ne' ((measure_congr he).trans hzero)

lemma retained_cell_bound {ι : Type*} (μ σ : Measure ℂ) (hσ : σ≤μ)
    (ρ B : ι→ℝ) (E : Finset ι) (i : ι) (hi : i∉E) (p : ℤ×ℤ) :
    (σ.restrict (retained (fun i=>badRegion μ (ρ i) (B i)) E)) (cell (ρ i) p) ≤
      ENNReal.ofReal (B i) := by
  by_cases hbad : ENNReal.ofReal (B i)<μ (cell (ρ i) p)
  · rw [Measure.restrict_apply (cell_measurable _ _)]
    have he : cell (ρ i) p∩retained (fun i=>badRegion μ (ρ i) (B i)) E=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hz.2 i hi (mem_iUnion.mpr ⟨p,mem_iUnion.mpr ⟨hbad,hz.1⟩⟩)
    rw [he,measure_empty]
    exact bot_le
  · exact (Measure.restrict_le_self.trans hσ _).trans (le_of_not_gt hbad)

 

theorem hausdorff_pos_of_finitely_bad {ι : Type*} [Nonempty ι] [Countable ι]
    (d : ℝ) (b ρ : ι→ℝ) (hb : ∀i,0<b i) (hρ : ∀i,0<ρ i)
    (μ σ : Measure ℂ) (hσ : σ≤μ) [IsFiniteMeasure σ] [NullSingletonClass σ]
    (K : ℝ) (hK : 0 ≤ K)
    (hfinite : ∀ᵐ z∂σ,{i | z∈badRegion μ (ρ i) (K*b i*(ρ i)^d)}.Finite)
    (A : Set ℂ) (hA : 0<σ A) : 0<Target.hausdorff (QuadraticGauge.gauge d b ρ) A := by
  let bad := fun i=>badRegion μ (ρ i) (K*b i*(ρ i)^d)
  obtain ⟨E,hE⟩ := exists_positive_retained σ bad hfinite A hA
  let ν := σ.restrict (retained bad E)
  have hνA : 0<ν A := by
    dsimp only [ν]
    rw [Measure.restrict_apply' (retained_measurable bad (fun i=>badRegion_measurable _ _ _) E)]
    exact hE
  exact hausdorff_pos_of_grid d b ρ hb hρ E ν K hK
    (fun i hi p=>retained_cell_bound μ σ hσ ρ (fun j=>K*b j*(ρ j)^d) E i hi p) A hνA

 

theorem ae_ae_finite_bad {Ω X ι : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable ι] (P : Measure Ω) (μ : Ω→Measure X) (bad : ι→Ω→Set X)
    (hm : ∀i,AEMeasurable (fun ω=>μ ω (bad i ω)) P)
    (hsum : (∑'i,∫⁻ω,μ ω (bad i ω)∂P)≠∞) :
    ∀ᵐ ω∂P,∀ᵐ z∂μ ω,{i | z∈bad i ω}.Finite := by
  have h : (∫⁻ω,∑'i,μ ω (bad i ω)∂P)≠∞ := by rwa [lintegral_tsum hm]
  filter_upwards [ae_lt_top' (AEMeasurable.tsum hm) h] with ω hω
  exact ae_finite_setOfPred_mem hω.ne

end SLEExactGauge.PlanarGrid
end
end
 

 
section
 

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology Classical
namespace SLEExactGauge.PlanarGrid

 

def testedBadCell {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Ω→Measure ℂ) (ρ B : ι→ℝ) (good : Set ι)
    (j : ι×(ℤ×ℤ)) (ω : Ω) : Set ℂ :=
  if j.1∈good ∧ ENNReal.ofReal (B j.1) < μ ω (cell (ρ j.1) j.2)
    then cell (ρ j.1) j.2 else ∅

lemma testedBadCell_mass {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Ω→Measure ℂ) (ρ B : ι→ℝ) (good : Set ι)
    (j : ι×(ℤ×ℤ)) (ω : Ω) :
    μ ω (testedBadCell μ ρ B good j ω)=
      if j.1∈good then
        {ω | ENNReal.ofReal (B j.1) < μ ω (cell (ρ j.1) j.2)}.indicator
          (fun ω=>μ ω (cell (ρ j.1) j.2)) ω else 0 := by
  by_cases hg : j.1∈good <;>
    by_cases hb : ENNReal.ofReal (B j.1) < μ ω (cell (ρ j.1) j.2) <;>
    simp [testedBadCell,hg,hb]

 

theorem ae_finitely_bad_of_spatial_tails {Ω ι : Type*}
    [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) (μ : Ω→Measure ℂ) (ν : Measure ℂ) [IsFiniteMeasure ν]
    (ρ B : ι→ℝ) (hρ : ∀i,0 < ρ i)
    (hm : ∀i p,Measurable (fun ω=>μ ω (cell (ρ i) p)))
    (good : Set ι) (hgood : goodᶜ.Finite)
    (C : ℝ≥0∞) (hC : C≠∞) (tail : ι→ℝ≥0∞) (htail : (∑'i,tail i)≠∞)
    (hbound : ∀i∈good,∀p : ℤ×ℤ,
      (∫⁻ω,{ω | ENNReal.ofReal (B i) < μ ω (cell (ρ i) p)}.indicator
        (fun ω=>μ ω (cell (ρ i) p)) ω∂P) ≤ C*ν (cell (ρ i) p)*tail i) :
    ∀ᵐ ω∂P,∀ᵐ z∂μ ω,{i | z∈badRegion (μ ω) (ρ i) (B i)}.Finite := by
  let bad := testedBadCell μ ρ B good
  have hbad (j : ι×(ℤ×ℤ)) :
      Measurable (fun ω=>μ ω (bad j ω)) := by
    simp only [bad,testedBadCell_mass]
    by_cases hj : j.1∈good
    · simp only [ite_eq_left hj]
      exact (hm j.1 j.2).indicator (measurableSet_lt measurable_const (hm j.1 j.2))
    · simp only [ite_eq_right hj]
      exact measurable_const
  have hi (j : ι×(ℤ×ℤ)) : (∫⁻ω,μ ω (bad j ω)∂P) ≤
      C*ν (cell (ρ j.1) j.2)*tail j.1 := by
    simp only [bad,testedBadCell_mass]
    by_cases hj : j.1∈good
    · simp only [ite_eq_left hj]
      exact hbound j.1 hj j.2
    · simp only [ite_eq_right hj,lintegral_zero]
      exact bot_le
  have hsum : (∑'j : ι×(ℤ×ℤ),∫⁻ω,μ ω (bad j ω)∂P)≠∞ := by
    apply ne_top_of_le_ne_top (show (C*(4*ν univ))*(∑'i,tail i)≠∞ from by finiteness)
    calc
      _≤∑'j : ι×(ℤ×ℤ),C*ν (cell (ρ j.1) j.2)*tail j.1 := ENNReal.tsum_le_tsum hi
      _=∑'i,C*(∑'p : ℤ×ℤ,ν (cell (ρ i) p))*tail i := by
        rw [ENNReal.tsum_prod']
        simp_rw [ENNReal.tsum_mul_right,ENNReal.tsum_mul_left]
      _≤∑'i,C*(4*ν univ)*tail i := by
        apply ENNReal.tsum_le_tsum
        intro i
        gcongr
        exact tsum_cell_mass ν (ρ i) (hρ i)
      _=(C*(4*ν univ))*(∑'i,tail i) := ENNReal.tsum_mul_left
  filter_upwards [ae_ae_finite_bad P μ bad (fun j=>(hbad j).aemeasurable) hsum] with ω hω
  filter_upwards [hω] with z hz
  apply (hgood.union (hz.image Prod.fst)).subset
  intro i hi
  by_cases hg : i∈good
  · right
    obtain ⟨p,hp⟩ := mem_iUnion.mp hi
    obtain ⟨hbad,hcell⟩ := mem_iUnion.mp hp
    refine ⟨(i,p),?_,rfl⟩
    change z∈testedBadCell μ ρ B good (i,p) ω
    simp only [testedBadCell,ite_eq_left (And.intro hg hbad)]
    exact hcell
  · exact Or.inl hg

end SLEExactGauge.PlanarGrid
end
end

end OAI
