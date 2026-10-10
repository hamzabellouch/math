import OAI.NumberTheory.DirichletL.Eisenstein.SquarefreeCoefficients

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma source_period_of_three_supported
    (hs:∀h:Eis,¬(3:Eis)∣h→sourceResidualFourierCoefficient h=0)
    (a:Eis) (z:ℂ) (v:ℝ) (hv:0<v) :
    cubicSourceResidualFunction (upperPoint (z+eisEmbedding a) v hv)=
      cubicSourceResidualFunction (upperPoint z v hv) := by
  rw [cubicSourceResidualFunction_bessel,cubicSourceResidualFunction_bessel]
  apply congrArg (fun t:ℂ=>(3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ)+t)
  apply tsum_congr
  intro h
  by_cases hd:(3:Eis)∣h
  · obtain ⟨b,rfl⟩:=hd
    have hp:ShortDraftTrace.breveE (cuspFrequency (3*b)*eisEmbedding a)=1:=by
      have he:cuspFrequency (3*b)*eisEmbedding a=cuspFrequency b*(3*eisEmbedding a):=by
        unfold cuspFrequency
        rw [map_mul,map_ofNat]
        ring
      rw [he,cuspFrequency_period]
    rw [mul_add,AddChar.map_add_eq_mul,hp,mul_one]
  · rw [hs h hd]
    by_cases hh:h=0 <;> simp [hh]

theorem exists_source_coefficient_not_three :
    ∃h:Eis,¬(3:Eis)∣h ∧ sourceResidualFourierCoefficient h≠0 := by
  by_contra hn
  have hs:∀h:Eis,¬(3:Eis)∣h→sourceResidualFourierCoefficient h=0:=by
    intro h hh
    by_contra hne
    exact hn ⟨h,hh,hne⟩
  apply cubicSource_not_eisenstein_periodic
  intro a w
  obtain ⟨z,v,hv,rfl⟩:=upperPoint_surjective w
  rw [complexTranslation_action]
  exact source_period_of_three_supported hs a z v hv

theorem exists_sourceArithmeticResidue_not_three :
    ∃h:Eis,¬(3:Eis)∣h ∧ sourceArithmeticResidue h≠0 := by
  obtain ⟨h,hh,ht⟩:=exists_source_coefficient_not_three
  refine ⟨h,hh,?_⟩
  intro hz
  apply ht
  simp only [sourceResidualFourierCoefficient,hz,mul_zero]

end CubicEisenstein

namespace CompletedGauss

section
open Filter MeasureTheory
open scoped Classical BigOperators Topology FourierTransform SchwartzMap ContDiff

lemma compactMellin_vertical_integrable (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V) (σ : ℝ) :
    Complex.VerticalIntegrable (mellin V) σ := by
  have hc : HasCompactSupport (CubicReflectionKernel.mellinLogFamily V σ) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (CubicReflectionKernel.mellinLogFamily_support V a b ha hsupp σ)
  have hd : ContDiff ℝ ∞ (CubicReflectionKernel.mellinLogFamily V σ) :=
    (CubicReflectionKernel.mellinLogFamily_smooth V hV).comp (contDiff_const.prodMk contDiff_id)
  let f : 𝓢(ℝ,ℂ) := hc.toSchwartzMap hd
  have hf : Integrable (fun t : ℝ=>(𝓕 f) (t/(2*Real.pi))) := by
    simpa only [div_eq_mul_inv] using
      (𝓕 f).integrable.comp_mul_right' (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  change Integrable (fun t : ℝ=>mellin V ((σ:ℂ)+t*Complex.I))
  have hfcoe : (f:ℝ→ℂ)=CubicReflectionKernel.mellinLogFamily V σ := rfl
  simpa only [CubicReflectionKernel.mellin_eq_logFamily_fourier,
    SchwartzMap.fourier_coe,hfcoe] using hf

theorem compactMellin_inversion (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (σ x : ℝ) (hx : 0<x) :
    V x=(1/(2*Real.pi):ℂ)*∫t : ℝ,
      (x:ℂ)^(-((σ:ℂ)+t*Complex.I))*mellin V ((σ:ℂ)+t*Complex.I) := by
  have hm := mellinInv_mellin_eq σ V hx
    (CubicReflectionKernel.compact_source_mellin_convergent V a b ha hsupp hV σ)
    (compactMellin_vertical_integrable V a b ha hsupp hV σ) hV.continuous.continuousAt
  simpa only [mellinInv,smul_eq_mul,Complex.real_smul,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_ofNat] using hm.symm

end

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

lemma positive_cpow_vertical_norm (r σ t : ℝ) (hr : 0<r) :
    ‖(r:ℂ)^((σ:ℂ)+t*Complex.I)‖=r^σ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp

lemma positive_cpow_negative_vertical_norm (r σ t : ℝ) (hr : 0<r) :
    ‖(r:ℂ)^(-((σ:ℂ)+t*Complex.I))‖=r^(-σ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp

lemma positive_cpow_vertical_continuous (r σ : ℝ) (hr : 0<r) :
    Continuous (fun t : ℝ=>(r:ℂ)^((σ:ℂ)+t*Complex.I)) := by
  let : NeZero (r:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hr.ne'⟩
  exact (_root_.continuous_const_cpow (r:ℂ)).comp (by fun_prop)

lemma positive_cpow_negative_vertical_continuous (r σ : ℝ) (hr : 0<r) :
    Continuous (fun t : ℝ=>(r:ℂ)^(-((σ:ℂ)+t*Complex.I))) := by
  let : NeZero (r:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hr.ne'⟩
  exact (_root_.continuous_const_cpow (r:ℂ)).comp (by fun_prop)

lemma vertical_power_mul_integrable (M : ℝ→ℂ) (hM : Integrable M)
    (r σ : ℝ) (hr : 0<r) :
    Integrable (fun t : ℝ=>(r:ℂ)^((σ:ℂ)+t*Complex.I)*M t) := by
  apply (hM.norm.const_mul (r^σ)).mono'
    ((positive_cpow_vertical_continuous r σ hr).aestronglyMeasurable.mul hM.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun t=>by simp only [Pi.mul_apply,norm_mul,positive_cpow_vertical_norm r σ t hr,le_refl])

lemma weighted_vertical_power_integrable (M : ℝ→ℂ) (hM : Integrable M)
    (r σ : ℝ) (hr : 0<r) (c : ℂ) :
    Integrable (fun t : ℝ=>c*(r:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t) := by
  apply (hM.norm.const_mul (‖c‖*r^(-σ))).mono'
    ((continuous_const.mul (positive_cpow_negative_vertical_continuous r σ hr)).aestronglyMeasurable.mul hM.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun t=>by
    simp only [Pi.mul_apply,norm_mul,positive_cpow_negative_vertical_norm r σ t hr,le_refl])

lemma weighted_vertical_power_integral_norm (M : ℝ→ℂ) (r σ : ℝ) (hr : 0<r) (c : ℂ) :
    (∫t : ℝ,‖c*(r:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t‖)=
      (‖c‖*r^(-σ))*(∫t : ℝ,‖M t‖) := by
  simp only [norm_mul,positive_cpow_negative_vertical_norm r σ _ hr,integral_const_mul]

theorem weighted_vertical_sum_integral {α : Type*} [Countable α]
    (r : α→ℝ) (hr : ∀i,0<r i) (c : α→ℂ) (σ : ℝ)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ)))
    (M : ℝ→ℂ) (hM : Integrable M) :
    (∑' i,∫t : ℝ,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t)=
      ∫t : ℝ,(∑' i,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I)))*M t := by
  have hi (i : α) := weighted_vertical_power_integrable M hM (r i) σ (hr i) (c i)
  have hs : Summable (fun i=>∫t : ℝ,‖c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t‖) := by
    simp only [weighted_vertical_power_integral_norm M _ σ (hr _) _]
    exact hc.mul_right _
  rw [integral_tsum_of_summable_integral_norm hi hs]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t=>tsum_mul_right)

lemma positive_quotient_cpow_neg (r X : ℝ) (hr : 0<r) (hX : 0<X) (s : ℂ) :
    ((r/X:ℝ):ℂ)^(-s)=(r:ℂ)^(-s)*(X:ℂ)^s := by
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg hr.le hX.le,
    Complex.cpow_neg,Complex.cpow_neg,div_inv_eq_mul]

theorem weightedMellin_inversion {α : Type*} [Countable α]
    (r : α→ℝ) (hr : ∀i,0<r i) (c : α→ℂ) (σ : ℝ)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ)))
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) :
    (∑'i,c i*V (r i/X))=(1/(2*Real.pi):ℂ)*∫t : ℝ,
      mellin V ((σ:ℂ)+t*Complex.I)*(X:ℂ)^((σ:ℂ)+t*Complex.I)*
        (∑'i,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))) := by
  let M : ℝ→ℂ := fun t=>(X:ℂ)^((σ:ℂ)+t*Complex.I)*mellin V ((σ:ℂ)+t*Complex.I)
  have hM : Integrable M := vertical_power_mul_integrable _
    (compactMellin_vertical_integrable V a b ha hsupp hV σ) X σ hX
  have hi (i : α) : c i*V (r i/X)=(1/(2*Real.pi):ℂ)*
      ∫t : ℝ,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t := by
    rw [compactMellin_inversion V a b ha hsupp hV σ _ (div_pos (hr i) hX)]
    rw [←mul_assoc,mul_comm (c i),mul_assoc,←integral_const_mul]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t=>by
      dsimp only
      rw [positive_quotient_cpow_neg _ _ (hr i) hX]
      dsimp only [M]
      ring)
  simp_rw [hi]
  rw [tsum_mul_left,weighted_vertical_sum_integral r hr c σ hc M hM]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t=>by dsimp only [M];ring)

end CompletedGauss

open Filter MeasureTheory
open scoped Classical BigOperators Topology

namespace CompletedGauss

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma angularFactor_norm_le_one (a : ActualEisensteinCubic.O) : ‖FiniteGaussPhase.angularFactor a‖≤1 := by
  by_cases ha : a=0
  · subst a; simp [FiniteGaussPhase.angularFactor]
  · exact (FiniteGaussPhase.norm_angularFactor a ha).le

lemma cubicRow_norm_le_one (I : Ideal ActualEisensteinCubic.O) (hI : primaryGenerator I≠0) (x : ActualEisensteinCubic.O⧸I) :
    ‖cubicRow I hI x‖≤1 := by
  unfold cubicRow
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro i hi; exact norm_nonneg _
  · intro i hi
    exact FiniteRayExpansion.norm_char_le_one _ _

lemma gaussTwo_norm_le_sqrt (I : Ideal ActualEisensteinCubic.O) (hI : primaryGenerator I≠0) :
    ‖gaussTwo I hI‖≤Real.sqrt (Ideal.absNorm I:ℝ) := by
  let n := primaryGenerator I
  let : Finite (ActualEisensteinCubic.O⧸Ideal.span {n}) := finite_quotient_span hI
  let : Fintype (ActualEisensteinCubic.O⧸Ideal.span {n}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (primaryGenerator_spec I hI).1
  let ψ := eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates n hI
  have hN : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h=>primaryGenerator_ne_zero_ideal I hI (Ideal.absNorm_eq_zero_iff.mp h))
  have hn : ‖eisEmbedding n‖=Real.sqrt (Ideal.absNorm I:ℝ) := primaryGenerator_norm I hI
  have hsum : ‖∑x : ActualEisensteinCubic.O⧸Ideal.span {n},cubicRow I hI (e x)*ψ x‖≤(Ideal.absNorm I:ℝ) := by
    calc
      _≤∑x : ActualEisensteinCubic.O⧸Ideal.span {n},‖cubicRow I hI (e x)*ψ x‖ := norm_sum_le _ _
      _≤∑_x : ActualEisensteinCubic.O⧸Ideal.span {n},(1:ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [norm_mul,AddChar.norm_apply,mul_one]
        exact cubicRow_norm_le_one I hI (e x)
      _=(Ideal.absNorm I:ℝ) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
        congr 1
        rw [←Nat.card_eq_fintype_card,←Submodule.cardQuot_apply,←Ideal.absNorm_apply,
          (primaryGenerator_spec I hI).1]
  change ‖(∑x : ActualEisensteinCubic.O⧸Ideal.span {n},cubicRow I hI (e x)*ψ x)/(‖eisEmbedding n‖:ℂ)‖≤_
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),hn]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hN)).mpr
  simpa only [Real.mul_self_sqrt hN.le] using hsum

lemma columnWeight_div_sqrt_norm_le_one (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1) (I : Ideal ActualEisensteinCubic.O) :
    ‖columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I:ℝ):ℂ)‖≤1 := by
  by_cases hI : Squarefree I ∧ primaryGenerator I≠0
  · have hN : 0<(Ideal.absNorm I:ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h=>primaryGenerator_ne_zero_ideal I hI.2 (Ideal.absNorm_eq_zero_iff.mp h))
    rw [columnWeight_eq Ψ I hI.1 hI.2,norm_div,norm_mul,norm_mul,norm_star,
      FiniteGaussPhase.norm_angularFactor _ hI.2,one_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    apply (div_le_one (Real.sqrt_pos.mpr hN)).mpr
    exact (mul_le_of_le_one_right (norm_nonneg _) (hΨ _)).trans (gaussTwo_norm_le_sqrt I hI.2)
  · simp only [columnWeight,squarefreeGaussCoefficient,dite_eq_right hI,zero_mul,zero_div,norm_zero,zero_le_one]

lemma cubeWeight_norm_le_one (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1) (I : Ideal ActualEisensteinCubic.O) :
    ‖cubeWeight Ψ I‖≤1 := by
  by_cases hI : I=0
  · subst I; simp
  have hN : (1:ℝ)≤(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h=>hI (Ideal.absNorm_eq_zero_iff.mp h))
  have hn : 0<(Ideal.absNorm I:ℝ) := lt_of_lt_of_le zero_lt_one hN
  change ‖star (FiniteGaussPhase.angularFactor (primaryGenerator I))^3*
    Ψ (primaryGenerator I)^3/(Ideal.absNorm I:ℂ)‖≤1
  rw [norm_div,norm_mul,norm_pow,norm_star,norm_pow,Complex.norm_natCast]
  apply (div_le_one hn).mpr
  apply le_trans _ hN
  calc
    _≤(1:ℝ)*1 := mul_le_mul
      (pow_le_one₀ (norm_nonneg _) (angularFactor_norm_le_one _))
      (pow_le_one₀ (norm_nonneg _) (hΨ _)) (pow_nonneg (norm_nonneg _) _) zero_le_one
    _=1 := one_mul _

end

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

section
open ActualEisensteinCubic CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

abbrev CompletedMellinIndex := NonzeroIdeal×NonzeroIdeal

def completedMellinLength (p : CompletedMellinIndex) : ℝ :=
  (Ideal.absNorm p.1.1:ℝ)*(Ideal.absNorm p.2.1:ℝ)^3

def completedMellinCoefficient (Ψ : ActualEisensteinCubic.O→*ℂ) (p : CompletedMellinIndex) : ℂ :=
  columnWeight Ψ p.1.1/(Real.sqrt (Ideal.absNorm p.1.1:ℝ):ℂ)*cubeWeight Ψ p.2.1

lemma nonzeroIdeal_norm_pos (I : NonzeroIdeal) : 0<(Ideal.absNorm I.1:ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (fun h=>I.2 (Ideal.absNorm_eq_zero_iff.mp h))

lemma completedMellinLength_pos (p : CompletedMellinIndex) : 0<completedMellinLength p :=
  mul_pos (nonzeroIdeal_norm_pos p.1) (pow_pos (nonzeroIdeal_norm_pos p.2) 3)

lemma completedMellinCoefficient_norm_le_one (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1)
    (p : CompletedMellinIndex) : ‖completedMellinCoefficient Ψ p‖≤1 := by
  rw [completedMellinCoefficient,norm_mul]
  exact (mul_le_mul_of_nonneg_right (columnWeight_div_sqrt_norm_le_one Ψ hΨ p.1.1)
    (norm_nonneg _)).trans (by simpa only [one_mul] using cubeWeight_norm_le_one Ψ hΨ p.2.1)

lemma nonzeroIdeal_norm_rpow_summable (σ : ℝ) (hσ : 1<σ) :
    Summable (fun I : NonzeroIdeal=>(Ideal.absNorm I.1:ℝ)^(-σ)) := by
  have h := (fullIdealWeight_summable_norm (σ:ℂ) (by simpa using hσ)).subtype (fun I=>I≠0)
  apply h.congr
  intro I
  change ‖fullIdealWeight (σ:ℂ) I.1‖=(Ideal.absNorm I.1:ℝ)^(-σ)
  rw [fullIdealWeight,ite_eq_right I.2]
  simpa only [Complex.neg_re,Complex.ofReal_re,Complex.ofReal_natCast] using
    (Complex.norm_cpow_eq_rpow_re_of_pos (nonzeroIdeal_norm_pos I) (-(σ:ℂ)))

lemma completedMellinLength_rpow (p : CompletedMellinIndex) (σ : ℝ) :
    (completedMellinLength p)^(-σ)=
      (Ideal.absNorm p.1.1:ℝ)^(-σ)*(Ideal.absNorm p.2.1:ℝ)^(-(3*σ)) := by
  rw [completedMellinLength,Real.mul_rpow (nonzeroIdeal_norm_pos p.1).le
    (pow_nonneg (nonzeroIdeal_norm_pos p.2).le _),←Real.rpow_natCast_mul (nonzeroIdeal_norm_pos p.2).le]
  congr 1
  congr 1
  ring

theorem completedMellinCoefficient_summable (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1)
    (σ : ℝ) (hσ : 1<σ) :
    Summable (fun p=>‖completedMellinCoefficient Ψ p‖*(completedMellinLength p)^(-σ)) := by
  have hI := nonzeroIdeal_norm_rpow_summable σ hσ
  have hJ := nonzeroIdeal_norm_rpow_summable (3*σ) (by linarith)
  have hp := hI.mul_of_nonneg hJ (fun I=>Real.rpow_nonneg (nonzeroIdeal_norm_pos I).le _)
    (fun J=>Real.rpow_nonneg (nonzeroIdeal_norm_pos J).le _)
  apply hp.of_nonneg_of_le
  · intro p; exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (completedMellinLength_pos p).le _)
  · intro p
    rw [←completedMellinLength_rpow]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (completedMellinLength_pos p).le _)
      (completedMellinCoefficient_norm_le_one Ψ hΨ p)

def completedDirichletSeries (Ψ : ActualEisensteinCubic.O→*ℂ) (s : ℂ) : ℂ :=
  ∑'p : CompletedMellinIndex,completedMellinCoefficient Ψ p*
    (completedMellinLength p:ℂ)^(1/2-s)

theorem completedT_eq_mellin_index (Ψ : ActualEisensteinCubic.O→*ℂ) (W : ℝ→ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0<X) :
    completedT Ψ W X=∑'p : CompletedMellinIndex,
      completedMellinCoefficient Ψ p*Vstar W (completedMellinLength p/X) := by
  have hfull := completedT_summable Ψ W hW X hX
  have hinj : Function.Injective (fun p : CompletedMellinIndex=>(p.1.1,p.2.1)) := by
    intro p q h
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  have hsub := hfull.comp_injective hinj
  calc
    completedT Ψ W X=∑'I : NonzeroIdeal,∑'J : Ideal ActualEisensteinCubic.O,summand Ψ W X I.1 J := by
      symm
      unfold completedT
      apply tsum_subtype_eq_of_support_subset
        (s:={I:Ideal ActualEisensteinCubic.O|I≠0}) (f:=fun I:Ideal ActualEisensteinCubic.O=>∑'J:Ideal ActualEisensteinCubic.O,summand Ψ W X I J)
      intro I hI hz
      subst I
      exact hI (by simp only [summand_zero_left,tsum_zero])
    _=∑'I : NonzeroIdeal,∑'J : NonzeroIdeal,summand Ψ W X I.1 J.1 := by
      apply tsum_congr
      intro I
      symm
      apply tsum_subtype_eq_of_support_subset
        (s:={J:Ideal ActualEisensteinCubic.O|J≠0}) (f:=fun J:Ideal ActualEisensteinCubic.O=>summand Ψ W X I.1 J)
      intro J hJ hz
      subst J
      exact hJ (summand_zero_right Ψ W X I.1)
    _=∑'p : CompletedMellinIndex,summand Ψ W X p.1.1 p.2.1 := hsub.tsum_prod.symm
    _=_ := rfl

theorem completedT_initial_mellin (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0<X) :
    completedT Ψ W X=(1/(2*Real.pi):ℂ)*∫t : ℝ,
      mellin (Vstar W) ((3/2:ℂ)+t*Complex.I)*(X:ℂ)^((3/2:ℂ)+t*Complex.I)*
        completedDirichletSeries Ψ ((2:ℂ)+t*Complex.I) := by
  let : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let : Countable (Ideal ActualEisensteinCubic.O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
  have hWc : HasCompactSupport W :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  rw [completedT_eq_mellin_index Ψ W hWc X hX]
  have h := weightedMellin_inversion completedMellinLength completedMellinLength_pos
    (completedMellinCoefficient Ψ) (3/2)
    (completedMellinCoefficient_summable Ψ hΨ (3/2) (by norm_num))
    (Vstar W) a b ha (Vstar_support W a b hsupp) (Vstar_contDiff W a b ha hsupp hW) X hX
  have hd (t : ℝ) : completedDirichletSeries Ψ ((2:ℂ)+t*Complex.I)=
      ∑'p : CompletedMellinIndex,completedMellinCoefficient Ψ p*
        (completedMellinLength p:ℂ)^(-((3/2:ℂ)+t*Complex.I)) := by
    unfold completedDirichletSeries
    apply tsum_congr
    intro p
    congr 2
    ring
  simpa only [hd,Complex.ofReal_div,Complex.ofReal_ofNat] using h

end

section
open ActualEisensteinCubic CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma nat_sqrt_cpow_half (a : ℕ) :
    (Real.sqrt (a:ℝ):ℂ)=(a:ℂ)^(1/2:ℂ) := by
  simpa only [Real.sqrt_eq_rpow,Complex.ofReal_natCast,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_ofNat] using
    (Complex.ofReal_cpow (Nat.cast_nonneg a) (1/2:ℝ))

lemma nat_half_shift_product (a b : ℕ) (ha : a≠0) (hb : b≠0) (C D s : ℂ) :
    (C/(Real.sqrt (a:ℝ):ℂ)*(D/(b:ℂ)))*((a:ℂ)*(b:ℂ)^3)^(1/2-s)=
      C*D*(b:ℂ)^(1/2-3*s)*(a:ℂ)^(-s) := by
  have ha0 : (a:ℂ)≠0 := Nat.cast_ne_zero.mpr ha
  have hb0 : (b:ℂ)≠0 := Nat.cast_ne_zero.mpr hb
  have hhalf : (a:ℂ)^(1/2:ℂ)≠0 := (Complex.cpow_ne_zero_iff).mpr (Or.inl ha0)
  rw [nat_sqrt_cpow_half]
  have hmul : ((a:ℂ)*(b:ℂ)^3)^(1/2-s)=
      (a:ℂ)^(1/2-s)*(b:ℂ)^(3*(1/2-s)) := by
    rw [←Nat.cast_pow,Complex.natCast_mul_natCast_cpow,Nat.cast_pow,
      ←Complex.natCast_cpow_natCast_mul]
    norm_num
  rw [hmul]
  have hA : (a:ℂ)^(1/2-s)=(a:ℂ)^(1/2:ℂ)*(a:ℂ)^(-s) := by
    rw [sub_eq_add_neg,Complex.cpow_add _ _ ha0]
  have hB : (b:ℂ)^(3*(1/2-s))=(b:ℂ)*(b:ℂ)^(1/2-3*s) := by
    rw [show (3:ℂ)*(1/2-s)=1+(1/2-3*s) by ring,
      Complex.cpow_add _ _ hb0,Complex.cpow_one]
  rw [hA,hB]
  field_simp

lemma completedDirichletTerm_expanded (Ψ : ActualEisensteinCubic.O→*ℂ) (s : ℂ) (p : CompletedMellinIndex) :
    completedMellinCoefficient Ψ p*(completedMellinLength p:ℂ)^(1/2-s)=
      columnWeight Ψ p.1.1*star (FiniteGaussPhase.angularFactor (primaryGenerator p.2.1))^3*
      Ψ (primaryGenerator p.2.1)^3*(Ideal.absNorm p.2.1:ℂ)^(1/2-3*s)*
      (Ideal.absNorm p.1.1:ℂ)^(-s) := by
  have ha : Ideal.absNorm p.1.1≠0 := fun h=>p.1.2 (Ideal.absNorm_eq_zero_iff.mp h)
  have hb : Ideal.absNorm p.2.1≠0 := fun h=>p.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
  unfold completedMellinCoefficient completedMellinLength
  change (columnWeight Ψ p.1.1/(Real.sqrt (Ideal.absNorm p.1.1:ℝ):ℂ)*
    (star (FiniteGaussPhase.angularFactor (primaryGenerator p.2.1))^3*
      Ψ (primaryGenerator p.2.1)^3/(Ideal.absNorm p.2.1:ℂ)))*
    (((Ideal.absNorm p.1.1:ℝ)*(Ideal.absNorm p.2.1:ℝ)^3:ℝ):ℂ)^(1/2-s)=_
  rw [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast,Complex.ofReal_natCast]
  rw [nat_half_shift_product _ _ ha hb]
  ring

theorem completedDirichletSeries_expanded (Ψ : ActualEisensteinCubic.O→*ℂ) (s : ℂ) :
    completedDirichletSeries Ψ s=∑'p : CompletedMellinIndex,
      columnWeight Ψ p.1.1*star (FiniteGaussPhase.angularFactor (primaryGenerator p.2.1))^3*
      Ψ (primaryGenerator p.2.1)^3*(Ideal.absNorm p.2.1:ℂ)^(1/2-3*s)*
      (Ideal.absNorm p.1.1:ℂ)^(-s) := by
  unfold completedDirichletSeries
  exact tsum_congr (completedDirichletTerm_expanded Ψ s)

end

open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

lemma weighted_vertical_series_continuous {α : Type*}
    (r : α→ℝ) (hr : ∀i,0<r i) (c : α→ℂ) (σ : ℝ)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ))) :
    Continuous (fun t : ℝ=>∑'i,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))) := by
  apply continuous_tsum
    (fun i=>continuous_const.mul (positive_cpow_negative_vertical_continuous (r i) σ (hr i))) hc
  intro i t
  change ‖c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))‖≤‖c i‖*(r i)^(-σ)
  rw [norm_mul,positive_cpow_negative_vertical_norm _ _ _ (hr i)]

lemma weighted_vertical_series_norm {α : Type*}
    (r : α→ℝ) (hr : ∀i,0<r i) (c : α→ℂ) (σ : ℝ)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ))) (t : ℝ) :
    ‖∑'i,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))‖≤∑'i,‖c i‖*(r i)^(-σ) := by
  have he (i : α) : ‖c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))‖=‖c i‖*(r i)^(-σ) := by
    rw [norm_mul,positive_cpow_negative_vertical_norm _ _ _ (hr i)]
  simpa only [he] using norm_tsum_le_tsum_norm (hc.congr (fun i=>(he i).symm))

lemma completedDirichletSeries_initial (Ψ : ActualEisensteinCubic.O→*ℂ) (t : ℝ) :
    completedDirichletSeries Ψ ((2:ℂ)+t*Complex.I)=
      ∑'p : CompletedMellinIndex,completedMellinCoefficient Ψ p*
        (completedMellinLength p:ℂ)^(-((3/2:ℂ)+t*Complex.I)) := by
  unfold completedDirichletSeries
  apply tsum_congr
  intro p
  congr 2
  ring

theorem completedT_initial_mellin_integrable (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0<X) :
    Integrable (fun t : ℝ=>mellin (Vstar W) ((3/2:ℂ)+t*Complex.I)*
      (X:ℂ)^((3/2:ℂ)+t*Complex.I)*completedDirichletSeries Ψ ((2:ℂ)+t*Complex.I)) := by
  have hsum := completedMellinCoefficient_summable Ψ hΨ (3/2) (by norm_num)
  have hc := weighted_vertical_series_continuous completedMellinLength completedMellinLength_pos
    (completedMellinCoefficient Ψ) (3/2) hsum
  have hb := weighted_vertical_series_norm completedMellinLength completedMellinLength_pos
    (completedMellinCoefficient Ψ) (3/2) hsum
  have hmi : Integrable (fun t : ℝ=>mellin (Vstar W) ((3/2:ℂ)+t*Complex.I)) := by
    simpa only [Complex.VerticalIntegrable,Complex.ofReal_div,Complex.ofReal_ofNat] using
      (compactMellin_vertical_integrable (Vstar W) a b ha (Vstar_support W a b hsupp)
        (Vstar_contDiff W a b ha hsupp hW) (3/2))
  have hbase := vertical_power_mul_integrable _ hmi X (3/2) hX
  have hi := hbase.mul_bdd hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  simpa only [Complex.ofReal_div,Complex.ofReal_ofNat,completedDirichletSeries_initial,
    mul_comm (mellin (Vstar W) _)] using hi

end CompletedGauss

open scoped BigOperators Classical
open Finset AddChar MulChar EisensteinEmbedding

namespace CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def dualIdealDyad (j : ℕ) : Finset (Ideal Eis) :=
  (ConcretePrimeRowBridge.idealsUpTo (2^j)).filter
    (fun I => Nat.clog 2 (Ideal.absNorm I)=j)

lemma mem_dualIdealDyad (I : Ideal Eis) (j : ℕ) :
    I∈dualIdealDyad j ↔ I≠0 ∧ Nat.clog 2 (Ideal.absNorm I)=j := by
  simp only [dualIdealDyad,Finset.mem_filter,ConcretePrimeRowBridge.mem_idealsUpTo]
  constructor
  · rintro ⟨⟨hI,_⟩,hj⟩
    exact ⟨fun h => by simp [h] at hI, hj⟩
  · rintro ⟨hI,hj⟩
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI),?_⟩,hj⟩
    simpa only [hj] using Nat.le_pow_clog (by norm_num : 1<2) (Ideal.absNorm I)

lemma dualIdealDyad_bounds (j : ℕ) (I : Ideal Eis) (hI : I∈dualIdealDyad j) :
    I≠0 ∧ (2:ℝ)^j/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^j := by
  obtain ⟨hn,hj⟩:= (mem_dualIdealDyad I j).mp hI
  have hu:=Nat.le_pow_clog (by norm_num : 1<2) (Ideal.absNorm I)
  have hl:=two_pow_clog_le_double (Ideal.absNorm I)
    (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hn))
  rw [hj] at hu hl
  refine ⟨hn,?_,by exact_mod_cast hu⟩
  have he : (2:ℝ)^j≤2*(Ideal.absNorm I:ℝ):=by exact_mod_cast hl
  linarith

abbrev NonzeroDualIdeal := {I : Ideal Eis // I≠0}

def dualDyadicIndexEquiv :
    (ℕ×NonzeroDualIdeal×NonzeroDualIdeal) ≃
      (Σ i : ℕ×ℕ×ℕ, (dualIdealDyad i.2.2)×(dualIdealDyad i.2.1)) where
  toFun x := ⟨(x.1,Nat.clog 2 (Ideal.absNorm x.2.2.val),Nat.clog 2 (Ideal.absNorm x.2.1.val)),
    ⟨⟨x.2.1.val,(mem_dualIdealDyad _ _).mpr ⟨x.2.1.property,rfl⟩⟩,
      ⟨x.2.2.val,(mem_dualIdealDyad _ _).mpr ⟨x.2.2.property,rfl⟩⟩⟩⟩
  invFun x := ⟨x.1.1,⟨x.2.1.val,((mem_dualIdealDyad _ _).mp x.2.1.property).1⟩,
    ⟨x.2.2.val,((mem_dualIdealDyad _ _).mp x.2.2.property).1⟩⟩
  left_inv x := by cases x; rfl
  right_inv x := by
    rcases x with ⟨⟨m,j,k⟩,⟨⟨I,hI⟩,⟨J,hJ⟩⟩⟩
    have hi:=((mem_dualIdealDyad I k).mp hI).2
    have hj:=((mem_dualIdealDyad J j).mp hJ).2
    dsimp only
    subst k
    subst j
    rfl

theorem tsum_dualIdealDyads
    (f : ℕ×NonzeroDualIdeal×NonzeroDualIdeal → ℂ) (hf : Summable f) :
    (∑'x, f x) = ∑'i : ℕ×ℕ×ℕ,
      ∑n : dualIdealDyad i.2.2, ∑b : dualIdealDyad i.2.1,
        f (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
          ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩) := by
  let g := f ∘ dualDyadicIndexEquiv.symm
  have hg : Summable g := dualDyadicIndexEquiv.symm.summable_iff.mpr hf
  calc
    _ = ∑'x,g x := (dualDyadicIndexEquiv.symm.tsum_eq f).symm
    _ = ∑'i,∑'x,g ⟨i,x⟩ := Summable.tsum_sigma' (fun _=>hasSum_fintype _ |>.summable) hg
    _ = _ := by
      apply tsum_congr
      intro i
      rw [tsum_fintype,Fintype.sum_prod_type]
      rfl

end CompletedGauss

end

end OAI
