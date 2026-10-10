import Mathlib
import OAI.Analysis.PathSelection.SectorInduction

namespace OAI

/-! Filtered clock series, bounded expansions and finite decompositions. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex
attribute [local instance] Classical.propDecidable
namespace DegeneratingTrees.Clock

lemma negative_degree_cutoff {δ : ℝ} (hδ : 0<δ)
    {E : ℕ → Set ℝ} (hE : ∀ n β,β∈E n → β≤-δ*(n:ℝ)) (B : ℝ) :
    ∃ N : ℕ,∀ n≥N,∀ β∈E n,β<B := by
  obtain ⟨N,hN⟩ := exists_nat_gt (-B/δ)
  refine ⟨N,?_⟩
  intro n hn β hβ
  have hn' : (N:ℝ)≤n := Nat.cast_le.mpr hn
  have hh := (div_lt_iff₀ hδ).mp hN
  have h := hE n β hβ
  nlinarith

lemma negative_union_finite {δ : ℝ} (hδ : 0<δ)
    {E : ℕ → Set ℝ} (hE : ∀ n β,β∈E n → β≤-δ*(n:ℝ))
    (hfin : ∀ n B,(E n∩Ici B).Finite) (B : ℝ) :
    ((⋃ n,E n)∩Ici B).Finite := by
  obtain ⟨N,hN⟩ := negative_degree_cutoff hδ hE B
  apply ((Finset.range N).finite_toSet.biUnion (fun n _ => hfin n B)).subset
  rintro β ⟨hβ,hB⟩
  obtain ⟨n,hn⟩ := mem_iUnion.mp hβ
  have hnN : n<N := by
    by_contra h
    exact (not_lt_of_ge hB) (hN n (Nat.le_of_not_gt h) β hn)
  exact mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨Finset.mem_range.mpr hnN,⟨hn,hB⟩⟩⟩

lemma negative_fiber_finite {δ : ℝ} (hδ : 0<δ)
    {E : ℕ → Set ℝ} (hE : ∀ n β,β∈E n → β≤-δ*(n:ℝ)) (β : ℝ) :
    {n | β∈E n}.Finite := by
  obtain ⟨N,hN⟩ := negative_degree_cutoff hδ hE β
  apply (Finset.range N).finite_toSet.subset
  intro n hn
  apply Finset.mem_range.mpr
  by_contra h
  exact (lt_irrefl β) (hN n (Nat.le_of_not_gt h) β hn)

variable {δ : ℝ} (hδ : 0<δ) {E : ℕ → Set ℝ}
  (hE : ∀ n β,β∈E n → β≤-δ*(n:ℝ))
  (hfin : ∀ n B,(E n∩Ici B).Finite)

def degreeCoefficient (b : ℕ → ℝ → ℂ → ℂ) (β : ℝ) (z : ℂ) : ℂ :=
  ∑ n ∈ (negative_fiber_finite hδ hE β).toFinset,b n β z

lemma degreeCoefficient_cutoff (b : ℕ → ℝ → ℂ → ℂ) {B : ℝ} {N : ℕ}
    (hN : ∀ n≥N,∀ β∈E n,β<B) {β : ℝ} (hβ : B≤β) (z : ℂ) :
    degreeCoefficient hδ hE b β z =
      ∑ n ∈ Finset.range N,if β∈E n then b n β z else 0 := by
  classical
  let S := (negative_fiber_finite hδ hE β).toFinset
  have hs : S⊆Finset.range N := by
    intro n hn
    have hn' : β∈E n := (negative_fiber_finite hδ hE β).mem_toFinset.mp hn
    apply Finset.mem_range.mpr
    by_contra h
    exact (not_lt_of_ge hβ) (hN n (Nat.le_of_not_gt h) β hn')
  change (∑ n ∈ S,b n β z)=_
  calc
    _ = ∑ n ∈ S,if β∈E n then b n β z else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      have he : β∈E n := (negative_fiber_finite hδ hE β).mem_toFinset.mp hn
      rw [ite_eq_left he]
    _ = _ := Finset.sum_subset hs (fun n hn hns => by
      have hn' : β∉E n := by simpa only [S,Set.Finite.mem_toFinset,mem_ofPred_eq] using hns
      simp only [ite_eq_right hn'])

lemma degree_truncation (b : ℕ → ℝ → ℂ → ℂ) {B : ℝ} {N : ℕ}
    (hN : ∀ n≥N,∀ β∈E n,β<B) (z : ℂ) :
    (∑ β ∈ (negative_union_finite hδ hE hfin B).toFinset,
      Complex.exp ((β:ℂ)*z)*degreeCoefficient hδ hE b β z) =
    ∑ n ∈ Finset.range N,∑ β ∈ (hfin n B).toFinset,
      Complex.exp ((β:ℂ)*z)*b n β z := by
  classical
  let S := (negative_union_finite hδ hE hfin B).toFinset
  calc
    _ = ∑ β ∈ S,∑ n ∈ Finset.range N,
        if β∈E n then Complex.exp ((β:ℂ)*z)*b n β z else 0 := by
      apply Finset.sum_congr rfl
      intro β hβ
      rw [degreeCoefficient_cutoff hδ hE b hN
        ((negative_union_finite hδ hE hfin B).mem_toFinset.mp hβ).2 z,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      split_ifs <;> simp
    _ = ∑ n ∈ Finset.range N,∑ β ∈ S,
        if β∈E n then Complex.exp ((β:ℂ)*z)*b n β z else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      symm
      have hs : (hfin n B).toFinset ⊆ S := by
        intro β hβ
        have hh := (hfin n B).mem_toFinset.mp hβ
        exact (negative_union_finite hδ hE hfin B).mem_toFinset.mpr
          ⟨mem_iUnion.mpr ⟨n,hh.1⟩,hh.2⟩
      calc
        _ = ∑ β ∈ (hfin n B).toFinset,
            if β∈E n then Complex.exp ((β:ℂ)*z)*b n β z else 0 := by
          apply Finset.sum_congr rfl
          intro β hβ
          simp only [ite_eq_left ((hfin n B).mem_toFinset.mp hβ).1]
        _ = _ := Finset.sum_subset hs (fun β hβ hβn => by
          have hB := ((negative_union_finite hδ hE hfin B).mem_toFinset.mp hβ).2
          have he : β∉E n := by
            intro he
            exact hβn ((hfin n B).mem_toFinset.mpr ⟨he,hB⟩)
          simp only [ite_eq_right he])

 

theorem SectorExpansion.of_negative_degree_series {F : ℂ → ℂ}
    {f : ℕ → ℂ → ℂ} {b : ℕ → ℝ → ℂ → ℂ}
    (hf : ∀ n,SectorExpansion (f n) (E n) (b n))
    (ha : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ F z)
    (happrox : ∀ B : ℝ,∀ᶠ N : ℕ in atTop,
      ExpSmall B (fun z => F z-∑ n ∈ Finset.range N,f n z)) :
    SectorExpansion F (⋃ n,E n) (degreeCoefficient hδ hE b) := by
  classical
  have hfin : ∀ n B,(E n∩Ici B).Finite := fun n => (hf n).finite_above
  have hbdd : BddAbove (⋃ n,E n) := by
    refine ⟨0,?_⟩
    rintro β hβ
    obtain ⟨n,hn⟩ := mem_iUnion.mp hβ
    exact (hE n β hn).trans (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ.le) (Nat.cast_nonneg n))
  apply SectorExpansion.of_expSmall hbdd (negative_union_finite hδ hE hfin) ha
  intro B
  obtain ⟨N,hN⟩ := negative_degree_cutoff hδ hE B
  obtain ⟨M,hM,he⟩ := ((eventually_ge_atTop N).and (happrox B)).exists
  have hdeg : ∀ n≥M,∀ β∈E n,β<B := fun n hn => hN n (hM.trans hn)
  have hrem := ExpSmall.sum (Finset.range M) (fun n _ => (hf n).expSmall_remainder B)
  convert he.add hrem using 1
  funext z
  rw [Finset.sum_sub_distrib,degree_truncation hδ hE hfin b hdeg z]
  ring

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

def BoundedExpansionOver (K : Set (ℂ → ℂ)) (α : ℝ) (f : ℂ → ℂ) : Prop :=
  ∃ E : Set ℝ,∃ b : ℝ → ℂ → ℂ,SectorExpansion f E b ∧
    (∀ β∈E,b β∈K) ∧ ∀ β∈E,β≤α

namespace BoundedExpansionOver
variable {K : Set (ℂ → ℂ)} (hK : LowerSectorData K)
include hK

lemma lower {f : ℂ → ℂ} (hf : f∈K) : BoundedExpansionOver K 0 f := by
  refine ⟨{0},fun _ => f,?_,fun _ _ => hf,fun β hβ => le_of_eq (mem_singleton_iff.mp hβ)⟩
  simpa only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_mul] using
    SectorExpansion.single 0 (hK.analytic hf) (hK.slow hf)

omit hK in
lemma zero (α : ℝ) : BoundedExpansionOver K α (fun _ => 0) := by
  refine ⟨∅,fun _ _ => 0,?_,by simp,by simp⟩
  apply SectorExpansion.of_expSmall (by simp) (by simp)
    (Eventually.of_forall fun _ => analyticAt_const)
  intro B
  simpa using ExpSmall.zero B

lemma add {α : ℝ} {f g : ℂ → ℂ}
    (hf : BoundedExpansionOver K α f) (hg : BoundedExpansionOver K α g) :
    BoundedExpansionOver K α (fun z => f z+g z) := by
  classical
  obtain ⟨E,b,hf,hb,hE⟩ := hf
  obtain ⟨F,c,hg,hc,hF⟩ := hg
  refine ⟨E∪F,fun β z => (if β∈E then b β z else 0)+(if β∈F then c β z else 0),
    hf.add hg,?_,?_⟩
  · intro β hβ
    apply hK.add_mem
    · by_cases he : β∈E
      · simpa only [ite_eq_left he] using hb β he
      · simpa only [ite_eq_right he] using hK.const_mem 0
    · by_cases he : β∈F
      · simpa only [ite_eq_left he] using hc β he
      · simpa only [ite_eq_right he] using hK.const_mem 0
  · intro β hβ
    exact hβ.elim (hE β) (hF β)

lemma mul {α γ : ℝ} {f g : ℂ → ℂ}
    (hf : BoundedExpansionOver K α f) (hg : BoundedExpansionOver K γ g) :
    BoundedExpansionOver K (α+γ) (fun z => f z*g z) := by
  obtain ⟨E,b,hf,hb,hE⟩ := hf
  obtain ⟨F,c,hg,hc,hF⟩ := hg
  refine ⟨exponentSum E F,_,hf.mul hg (fun β hβ => hK.slow (hb β hβ))
    (fun γ hγ => hK.slow (hc γ hγ)),
    fun δ _ => hK.convolution_mem hf.bounded_above hg.bounded_above
      hf.finite_above hg.finite_above hb hc δ,?_⟩
  rintro β ⟨⟨b,c⟩,⟨hb,hc⟩,rfl⟩
  exact add_le_add (hE b hb) (hF c hc)

lemma sum {ι : Type*} (S : Finset ι) {α : ℝ} {f : ι → ℂ → ℂ}
    (hf : ∀ i∈S,BoundedExpansionOver K α (f i)) :
    BoundedExpansionOver K α (fun z => ∑ i∈S,f i z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using zero α
  | @insert i S hi ih =>
    simpa only [Finset.sum_insert hi] using add hK
      (hf i (Finset.mem_insert_self _ _)) (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma prod {ι : Type*} (S : Finset ι) {α : ι → ℝ} {f : ι → ℂ → ℂ}
    (hf : ∀ i∈S,BoundedExpansionOver K (α i) (f i)) :
    BoundedExpansionOver K (∑ i∈S,α i) (fun z => ∏ i∈S,f i z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty,Finset.prod_empty] using lower hK (hK.const_mem 1)
  | @insert i S hi ih =>
    simpa only [Finset.sum_insert hi,Finset.prod_insert hi] using mul hK
      (hf i (Finset.mem_insert_self _ _)) (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma negative_series {δ : ℝ} (hδ : 0<δ) {f : ℕ → ℂ → ℂ}
    (hf : ∀ n : ℕ,BoundedExpansionOver K (-δ*(n:ℝ)) (f n)) {F : ℂ → ℂ}
    (ha : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ F z)
    (happrox : ∀ B : ℝ,∀ᶠ N : ℕ in atTop,
      ExpSmall B (fun z => F z-∑ n∈Finset.range N,f n z)) : ExpansionOver K F := by
  classical
  choose E b he hb hE using hf
  refine ⟨⋃ n,E n,degreeCoefficient hδ hE b,
    SectorExpansion.of_negative_degree_series hδ hE he ha happrox,?_⟩
  intro β hβ
  apply hK.finset_sum_mem
  intro n hn
  exact hb n β ((negative_fiber_finite hδ hE β).mem_toFinset.mp hn)
end BoundedExpansionOver
end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

private lemma filtered_positive_coeff_zero {field : Set (ℂ → ℂ)}
    (hfield : LowerSectorData field) {func : ℂ → ℂ} {support : Set ℝ}
    {coeff : ℝ → ℂ → ℂ} (hexp : SectorExpansion func support coeff)
    (hcoeff : ∀ exponent∈support,coeff exponent∈field) {limit : ℂ}
    (hlim : Tendsto (fun time : ℝ => func (time:ℂ)) atTop (𝓝 limit))
    {exponent : ℝ} (hmem : exponent∈support) (hpos : 0<exponent) :
    ∀ᶠ time : ℝ in atTop,coeff exponent (time:ℂ)=0 := by
  by_contra hnonzero
  have htrim := hexp.trim_zero (fun degree hdegree => hfield.analytic (hcoeff degree hdegree))
  have hsupport : exponent∈nonzeroRaySupport support coeff := ⟨hmem,hnonzero⟩
  obtain ⟨degree,hdegree,hmax⟩ := exists_greatest_of_finite_above htrim.finite_above ⟨exponent,hsupport⟩
  have hdegreepos : 0<degree := hpos.trans_le (hmax exponent hsupport)
  have hne : ∀ᶠ point in sectorInfinity,coeff degree point≠0 := by
    rcases hfield.zero_or_ne (hcoeff degree hdegree.1) with hzero | hne
    · exact False.elim (hdegree.2 (tendsto_real_sectorInfinity.eventually hzero))
    · exact hne
  have hslow := hfield.slow (hfield.inv_mem (hcoeff degree hdegree.1))
  have hone := (htrim.uniform_leading_tendsto hdegree hmax hne hslow).comp tendsto_real_sectorInfinity
  have hexponential : ExpSmall 0 (fun point => Complex.exp (((-degree:ℝ):ℂ)*point)) :=
    ⟨-degree,by linarith,ExpBound.cexp (-degree)⟩
  have hzero := ((hexponential.mul_slow hslow).tendsto_zero.comp tendsto_real_sectorInfinity).mul hlim
  exact zero_ne_one (by simpa only [zero_mul] using tendsto_nhds_unique hzero hone)

private lemma filtered_first_clock_limit {func : ℝ → ℂ} (hfunc : Puiseux func)
    {clock : ℝ → ℝ} {scale : ℝ} (hscale : 0<scale)
    (hclock : clock =ᶠ[atTop] fun time => scale*time)
    {model : ℂ → ℂ} (hanalytic : ∀ᶠ point in sectorInfinity,AnalyticAt ℂ model point)
    (heq : func =ᶠ[atTop] fun time => model (clock time:ℂ)) {limit : ℂ}
    (hlim : Tendsto func atTop (𝓝 limit)) : Tendsto model sectorInfinity (𝓝 limit) := by
  have hrepresentative : ∃ (representative : ℂ → ℂ) (radius : ℝ),
      (∀ point : ℂ,radius<‖point‖ → 0<point.re → AnalyticAt ℂ representative point) ∧
      (func =ᶠ[atTop] fun time => representative (time:ℂ)) ∧
      Tendsto representative radialInfinity (𝓝 limit) := by
    by_cases hzero : func =ᶠ[atTop] fun _ => 0
    · have hlimit : limit=0 := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hzero.symm)
      subst limit
      exact ⟨fun _ => 0,0,fun _ _ _ => analyticAt_const,hzero,tendsto_const_nhds⟩
    obtain ⟨order,horder,power,coefficient,hcoefficient,hconstant,hform⟩ := hfunc.normalize hzero
    have hform' : func =ᶠ[atTop] fun time =>
        (rootCoord order time:ℂ)^power*coefficient (rootCoord order time) := by
      simpa only [Complex.real_smul,Complex.ofReal_zpow] using hform
    have hpower : 0≤power := by
      by_contra hnegative
      have hnegative : power<0 := lt_of_not_ge hnegative
      let degree : ℕ := (-power).toNat
      have hdegree : 0<degree := by omega
      have hcast : (degree:ℤ)=-power := Int.toNat_of_nonneg (neg_nonneg.mpr hnegative.le)
      have hzero : Tendsto (fun time => (rootCoord order time:ℂ)^degree*func time) atTop (𝓝 0) := by
        simpa only [zero_pow hdegree.ne',zero_mul] using
          ((rootCoord_complex_tendsto_zero horder).pow degree).mul hlim
      have hcancel : (fun time => (rootCoord order time:ℂ)^degree*func time) =ᶠ[atTop]
          fun time => coefficient (rootCoord order time) := by
        filter_upwards [hform',eventually_gt_atTop (0:ℝ)] with time hform htime
        have hroot : (rootCoord order time:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (rootCoord_pos htime).ne'
        rw [hform,←mul_assoc,←zpow_natCast,←zpow_add₀ hroot,hcast,neg_add_cancel,zpow_zero,one_mul]
      exact hconstant (tendsto_nhds_unique (hcoefficient.continuousAt.tendsto.comp
        (rootCoord_complex_tendsto_zero horder)) (hzero.congr' hcancel))
    let degree := power.toNat
    have hcast : (degree:ℤ)=power := Int.toNat_of_nonneg hpower
    let representative : ℂ → ℂ := fun point =>
      (complexRoot order point)^degree*coefficient (complexRoot order point)
    have heq' : func =ᶠ[atTop] fun time => representative (time:ℂ) := by
      filter_upwards [hform',eventually_gt_atTop (0:ℝ)] with time hform htime
      simpa only [representative,complexRoot_real htime.le,←zpow_natCast,hcast] using hform
    have hlimit : limit=(0:ℂ)^degree*coefficient 0 := by
      have htendsto := ((rootCoord_complex_tendsto_zero horder).pow degree).mul
        (hcoefficient.continuousAt.tendsto.comp (rootCoord_complex_tendsto_zero horder))
      apply tendsto_nhds_unique hlim
      apply htendsto.congr'
      filter_upwards [hform'] with time hform
      simpa only [Function.comp_apply,←zpow_natCast,hcast] using hform.symm
    obtain ⟨radius,hradius⟩ := radial_eventually
      ((complexRoot_tendsto_zero horder).eventually hcoefficient.eventually_analyticAt)
    refine ⟨representative,radius,?_,heq',?_⟩
    · intro point hnorm hre
      have hroot := complexRoot_analytic (n := order) hre
      exact (hroot.pow degree).mul ((hradius point hnorm).comp hroot)
    · rw [hlimit]
      exact ((complexRoot_tendsto_zero horder).pow degree).mul
        (hcoefficient.continuousAt.tendsto.comp (complexRoot_tendsto_zero horder))
  obtain ⟨representative,radius,hrep,heqrep,hreplimit⟩ := hrepresentative
  let inverse : ℂ → ℂ := fun point => point/(scale:ℂ)
  have hinverse : Tendsto inverse sectorInfinity radialInfinity := by
    rw [radialInfinity,tendsto_comap_iff]
    simpa only [inverse,Function.comp_def,norm_div,Complex.norm_of_nonneg hscale.le] using
      tendsto_norm_sectorInfinity.atTop_div_const hscale
  have hinverseanalytic : ∀ point : ℂ,AnalyticAt ℂ inverse point := fun _ => analyticAt_id.div_const
  have hcomposition : ∀ᶠ point in sectorInfinity,AnalyticAt ℂ (fun point => representative (inverse point)) point := by
    have hnorm : ∀ᶠ point in sectorInfinity,radius<‖inverse point‖ :=
      (tendsto_comap_iff.mp hinverse).eventually (eventually_gt_atTop radius)
    filter_upwards [hnorm,tendsto_re_sectorInfinity.eventually (eventually_gt_atTop (0:ℝ))]
      with point hnorm hre
    have hre' : 0<(inverse point).re := by
      simpa only [inverse,Complex.div_ofReal_re] using div_pos hre hscale
    exact (hrep (inverse point) hnorm hre').comp (hinverseanalytic point)
  have hline : (fun time : ℝ => model (time:ℂ)) =ᶠ[atTop]
      fun time => representative (inverse (time:ℂ)) := by
    have htendsto : Tendsto (fun time : ℝ => time/scale) atTop atTop := tendsto_id.atTop_div_const hscale
    filter_upwards [htendsto.eventually heq,htendsto.eventually heqrep,htendsto.eventually hclock]
      with time heq heqrep hclock
    change func (time/scale)=model (clock (time/scale):ℂ) at heq
    change func (time/scale)=representative (time/scale:ℝ) at heqrep
    have hclock' : clock (time/scale)=time := by rw [hclock]; field_simp
    rw [hclock'] at heq
    simpa only [inverse,←Complex.ofReal_div] using heq.symm.trans heqrep
  exact (hreplimit.comp hinverse).congr' (sector_analytic_eq_of_ray hanalytic hcomposition hline).symm

private lemma filtered_previous_chart {clocks : List (ℝ → ℝ)} {clock lower : ℝ → ℝ}
    (hvalid : ValidClocks (clock::lower::clocks)) :
    ∃ inverse : ℂ → ℂ,(∀ᶠ point in sectorInfinity,AnalyticAt ℂ inverse point) ∧
      Tendsto inverse sectorInfinity sectorInfinity ∧
      (∀ᶠ time : ℝ in atTop,inverse (clock time:ℂ)=(lower time:ℂ)) := by
  obtain ⟨field,hdata⟩ := hvalid.1.sectorData
  have hlowert := hvalid.1.2.2.1
  have hclockt := hvalid.2.2.1
  have hlowerc := (hvalid.1.2.1.real_eventually_analytic hvalid.1.1).mono (fun _ hanalytic => hanalytic.continuousAt)
  obtain ⟨model,hmodel,heq⟩ := hdata.expansion_iff.mp hvalid.2.1
  have hreal : ∀ᶠ time : ℝ in atTop,(model (time:ℂ)).im=0 ∧ 0<(model (time:ℂ)).re := by
    apply eventually_of_comp_clock hlowert hlowerc
    filter_upwards [heq,hclockt.eventually (eventually_gt_atTop 0)] with time heq htime
    rw [←heq]
    exact ⟨rfl,htime⟩
  have htendsto : Tendsto (fun time : ℝ => (model (time:ℂ)).re) atTop atTop := by
    rw [Filter.tendsto_def]
    intro bound hbound
    apply eventually_of_comp_clock hlowert hlowerc
    exact (hclockt.congr' (heq.mono fun _ heq => congrArg Complex.re heq)).eventually hbound
  have hfast : Asymptotics.IsLittleO atTop id (fun time : ℝ => (model (time:ℂ)).re) := by
    apply Asymptotics.IsLittleO.of_bound
    intro epsilon hepsilon
    apply eventually_of_comp_clock hlowert hlowerc
    filter_upwards [heq,hvalid.2.2.2.def hepsilon] with time heq hbound
    change ‖lower time‖≤epsilon*‖(model (lower time:ℂ)).re‖
    rwa [←heq]
  obtain ⟨inverse,realInverse,hinverse,hfamily⟩ := hdata.charts model hmodel hreal htendsto hfast
  refine ⟨inverse,hinverse.analytic_left.mono (fun _ hanalytic => hanalytic.1),hinverse.maps_sector,?_⟩
  filter_upwards [heq,hlowert.eventually hinverse.right] with time heq hinverse
  rwa [heq]

private lemma filtered_finite_decomposition {xs : List (ℝ → ℝ)} {X : ℝ → ℝ}
    {K : Set (ℂ → ℂ)} (hK : ClockSectorData xs X K)
    (hlower : ∀ a∈K,∀ d : ℂ,Tendsto (fun t : ℝ => a (t:ℂ)) atTop (𝓝 d) →
      Tendsto a sectorInfinity (𝓝 d))
    {F : ℂ → ℂ} (hF : ExpansionOver K F) {d : ℂ}
    (hlim : Tendsto (fun t : ℝ => F (t:ℂ)) atTop (𝓝 d)) :
    ∃ (a r : ℂ → ℂ) (δ : ℝ),0<δ ∧ a∈K ∧ Tendsto a sectorInfinity (𝓝 d) ∧
      BoundedExpansionOver K (-δ) r ∧ ExpBound (-δ/2) r ∧
      (∀ᶠ z in sectorInfinity,AnalyticAt ℂ r z) ∧ ∀ z,F z=a z+r z := by
  classical
  obtain ⟨E,b,hF,hb⟩ := hF
  let D := nonzeroRaySupport E b
  have htrim : SectorExpansion F D b := hF.trim_zero (fun β hβ => hK.lower.analytic (hb β hβ))
  have hDb : ∀ β∈D,b β∈K := fun β hβ => hb β hβ.1
  have hnonpos : ∀ β∈D,β≤0 := by
    intro β hβ
    by_contra h
    exact hβ.2 (filtered_positive_coeff_zero hK.lower hF hb hlim hβ.1 (lt_of_not_ge h))
  have hgo : ∀ (a r : ℂ → ℂ) (A : Set ℝ),a∈K → SectorExpansion r A b →
      (∀ β∈A,b β∈K) → (∀ β∈A,β<0) → (∀ z,F z=a z+r z) →
      ∃ δ : ℝ,0<δ ∧ Tendsto a sectorInfinity (𝓝 d) ∧
        BoundedExpansionOver K (-δ) r ∧ ExpBound (-δ/2) r := by
    intro a r A ham hr hc hneg heq
    obtain ⟨δ,hδ,hgap⟩ := strict_negative_support_gap hr.finite_above hneg
    have hdec := hr.negative_bound hδ hgap
    have hr0 := hdec.tendsto_zero (by linarith : -δ/2<0)
    have har : Tendsto (fun t : ℝ => a (t:ℂ)) atTop (𝓝 d) := by
      have h := hlim.sub (hr0.comp tendsto_real_sectorInfinity)
      simp only [sub_zero] at h
      convert h using 1
      funext t
      simp only [heq,Function.comp_apply,add_sub_cancel_right]
    exact ⟨δ,hδ,hlower a ham d har,⟨A,b,hr,hc,hgap⟩,hdec⟩
  by_cases h0 : (0:ℝ)∈D
  · have hr := htrim.erase h0 (hK.lower.analytic (hDb 0 h0)) (hK.lower.slow (hDb 0 h0))
    simp only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_mul] at hr
    have he : ∀ z,F z=b 0 z+(F z-b 0 z) := fun z => by ring
    obtain ⟨δ,hδ,ha,hbnd,hdec⟩ := hgo (b 0) (fun z => F z-b 0 z) (D\{0})
      (hDb 0 h0) hr (fun β hβ => hDb β hβ.1)
      (fun β hβ => lt_of_le_of_ne (hnonpos β hβ.1) hβ.2) he
    exact ⟨b 0,_,δ,hδ,hDb 0 h0,ha,hbnd,hdec,hr.eventually_analytic,he⟩
  · have he : ∀ z,F z=0+F z := fun z => (zero_add _).symm
    obtain ⟨δ,hδ,ha,hbnd,hdec⟩ := hgo (fun _ => 0) F D (hK.lower.const_mem 0)
      htrim hDb (fun β hβ => lt_of_le_of_ne (hnonpos β hβ) (fun h => h0 (h ▸ hβ))) he
    exact ⟨_,F,δ,hδ,hK.lower.const_mem 0,ha,hbnd,hdec,htrim.eventually_analytic,he⟩

private lemma filtered_model_limit {clocks : List (ℝ → ℝ)} {clock : ℝ → ℝ}
    (hvalid : ValidClocks (clock::clocks)) {func : ℝ → ℂ} (hfunc : ClockGerm clocks func)
    {model : ℂ → ℂ} (hanalytic : ∀ᶠ point in sectorInfinity,AnalyticAt ℂ model point)
    (heq : func =ᶠ[atTop] fun time => model (clock time:ℂ)) {limit : ℂ}
    (hlim : Tendsto func atTop (𝓝 limit)) : Tendsto model sectorInfinity (𝓝 limit) := by
  induction clocks generalizing clock func model limit with
  | nil =>
    obtain ⟨scale,hscale,hclock⟩ := hvalid.2.2.2
    exact filtered_first_clock_limit hfunc hscale hclock hanalytic heq hlim
  | cons lower clocks ih =>
    obtain ⟨representative,support,coeff,hexp,hcoeff,heqrep⟩ := hfunc
    obtain ⟨field,hdata⟩ := hvalid.1.sectorData
    have hlowerc := (hvalid.1.2.1.real_eventually_analytic hvalid.1.1).mono
      (fun _ hanalytic => hanalytic.continuousAt)
    have hreal : Tendsto (fun time : ℝ => representative (time:ℂ)) atTop (𝓝 limit) := by
      rw [Filter.tendsto_def]
      intro bound hbound
      exact eventually_of_comp_clock hvalid.1.2.2.1 hlowerc
        ((hlim.congr' heqrep).eventually hbound)
    have hmembers : ∀ exponent∈support,coeff exponent∈field :=
      fun exponent hmem => (hdata.membership _).mpr (hcoeff exponent hmem)
    obtain ⟨constant,remainder,gap,hgap,hconstant,hconstantlim,hbound,hdecay,hanalyticrep,hdecomp⟩ :=
      filtered_finite_decomposition hdata
        (fun coefficient hmember value hlimit => ih hvalid.1
          ((hdata.membership _).mp hmember).1 ((hdata.membership _).mp hmember).2
          EventuallyEq.rfl (hlimit.comp hvalid.1.2.2.1))
        ⟨support,coeff,hexp,hmembers⟩ hreal
    have hreplimit : Tendsto representative sectorInfinity (𝓝 limit) := by
      have hzero := hdecay.tendsto_zero (by linarith : -gap/2<0)
      have heq : representative = fun point => constant point + remainder point :=
        funext hdecomp
      simpa only [heq,add_zero] using hconstantlim.add hzero
    obtain ⟨inverse,hinverseanalytic,hinverse,heqinverse⟩ := filtered_previous_chart hvalid
    have hcomposition : ∀ᶠ point in sectorInfinity,
        AnalyticAt ℂ (fun point => representative (inverse point)) point := by
      filter_upwards [hinverseanalytic,hinverse.eventually hexp.eventually_analytic]
        with point hinverse hrep
      exact hrep.comp hinverse
    have hmodels : model =ᶠ[sectorInfinity] fun point => representative (inverse point) := by
      apply sector_analytic_eq_of_ray hanalytic hcomposition
      have hclockc := (hvalid.2.1.real_eventually_analytic hvalid.1).mono
        (fun _ hanalytic => hanalytic.continuousAt)
      apply eventually_of_comp_clock hvalid.2.2.1 hclockc
      filter_upwards [heq,heqrep,heqinverse] with time heq heqrep heinverse
      rw [heinverse,←heq,←heqrep]
    exact (hreplimit.comp hinverse).congr' hmodels.symm

lemma ClockSectorData.finite_decomposition {xs : List (ℝ → ℝ)} {X : ℝ → ℝ}
    (hvalid : ValidClocks (X::xs)) {K : Set (ℂ → ℂ)} (hK : ClockSectorData xs X K)
    {F : ℂ → ℂ} (hF : ExpansionOver K F) {d : ℂ}
    (hlim : Tendsto (fun t : ℝ => F (t:ℂ)) atTop (𝓝 d)) :
    ∃ (a r : ℂ → ℂ) (δ : ℝ),0<δ ∧ a∈K ∧ Tendsto a sectorInfinity (𝓝 d) ∧
      BoundedExpansionOver K (-δ) r ∧ ExpBound (-δ/2) r ∧
      (∀ᶠ z in sectorInfinity,AnalyticAt ℂ r z) ∧ ∀ z,F z=a z+r z := by
  apply filtered_finite_decomposition hK _ hF hlim
  intro coefficient hmember value hlimit
  have hlower := (hK.membership _).mp hmember
  exact filtered_model_limit hvalid hlower.1 hlower.2 EventuallyEq.rfl
    (hlimit.comp hvalid.2.2.1)

lemma finite_common_positive {ι : Type*} [Fintype ι] {δ : ι → ℝ}
    (hδ : ∀ i,0<δ i) : ∃ ε : ℝ,0<ε ∧ ∀ i,ε≤δ i := by
  classical
  have h : ∀ S : Finset ι,∃ ε : ℝ,0<ε ∧ ∀ i∈S,ε≤δ i := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,by simp⟩
    | @insert i S hi ih =>
      obtain ⟨ε,hε,hh⟩ := ih
      refine ⟨min ε (δ i),lt_min hε (hδ i),?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl|hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hh j hj)
  obtain ⟨ε,hε,hh⟩ := h Finset.univ
  exact ⟨ε,hε,fun i => hh i (Finset.mem_univ i)⟩

lemma BoundedExpansionOver.mono {K : Set (ℂ → ℂ)} {α β : ℝ} {f : ℂ → ℂ}
    (hf : BoundedExpansionOver K α f) (h : α≤β) : BoundedExpansionOver K β f := by
  obtain ⟨E,b,hf,hb,hE⟩ := hf
  exact ⟨E,b,hf,hb,fun γ hγ => (hE γ hγ).trans h⟩

end DegeneratingTrees.Clock
end

end OAI
