import OAI.NumberTheory.DirichletL.Energy.State
import OAI.NumberTheory.DirichletL.Moments.FirstSourceReduction
import OAI.NumberTheory.DirichletL.Moments.DetectorPlainSource
import OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyOriginalSource
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentEligibleEnergy CenteredMomentCommonRadialData
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleMask
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentHeckeExpansion CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open CenteredMomentHeckeHeight
open CenteredMomentDivisorRowEnergy CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceRectangleEnergy
open CenteredMomentPositiveSummability CenteredMomentPlainEnergy CenteredMomentRowNorm
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance energyOriginalSourceDecidableSum : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def completeInput (s : Data ι) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hν : ∀i I,‖s.ν i I‖≤1) (hW : ∀i x,‖s.W i x‖≤s.M i)
    (lo hi : ℝ) (hlo : 0<lo) (hl : ∀i,lo≤s.lo i) (hh : ∀i,s.hi i≤hi) : Input ι where
  toData := s
  plain₁ := plainSupportPool s.b₁ s.X₁ s.Y₁
  plain₂ := plainSupportPool s.b₂ s.X₂ s.Y₂
  plain₁_ne := by
    intro I hI
    rcases Finset.mem_union.mp hI with hI|hI
    · exact (CenteredMomentSourceMass.mem_idealBall _ _).mp hI |>.1
    · exact (CenteredMomentSourceMass.mem_idealBall _ _).mp hI |>.1
  plain₂_ne := by
    intro I hI
    rcases Finset.mem_union.mp hI with hI|hI
    · exact (CenteredMomentSourceMass.mem_idealBall _ _).mp hI |>.1
    · exact (CenteredMomentSourceMass.mem_idealBall _ _).mp hI |>.1
  coverage₁ := plainSupportPool_coverage s.W₁ s.b₁ s.X₁ s.Y₁ hz₁ s.support₁ s.X₁_pos s.Y₁_pos
  coverage₂ := plainSupportPool_coverage s.W₂ s.b₂ s.X₂ s.Y₂ hz₂ s.support₂ s.X₂_pos s.Y₂_pos
  ν_bound := hν
  W_bound := hW
  lower := lo
  upper := hi
  lower_pos := hlo
  lower_le := hl
  upper_ge := hh

omit [DecidableEq ι] in
lemma input_tuplePool (s : Input ι) :
    Fintype.piFinset s.pools=tuplePool s.slots s.plain₁ s.plain₂ := by
  ext v
  simp only [Fintype.mem_piFinset,tuplePool,tuplePools,Input.pools]

lemma input_polynomial_difference (s : Input ι) (R : Ideal O) (z : O) :
    (∑I∈finiteColumns (Fintype.piFinset s.pools),coefficient s R 1 I*
      rowWeight s.η fixedBadMask 1 z s.t I)=
    (rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.t s.X₁*
      rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₂ s.t s.X₂-
     rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.t s.Y₁*
      rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₂ s.t s.Y₂)*
        ∏i,rowSlot s.η (fixedBadMask*idealGenerator R) 1 z (s.slots i)
          (s.toData.coefficient i) s.t := by
  unfold coefficient
  rw [input_tuplePool]
  rw [source_polynomial_eq_maskedRectangle s.η fixedBadMask 1 z s.t
    (dvd_mul_right _ _) (dvd_mul_left _ _) s.slots s.plain₁ s.plain₂ R 1
    s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 s.coverage₁ s.coverage₂]
  simp only [map_one,Nat.cast_one,div_one,maskedRectangle,one_dvd,ite_true,one_mul]
  exact actual_slot_rectangle_sum s.η (fixedBadMask*idealGenerator R) 1 z s.slots
    s.toData.coefficient s.t s.W₁ s.W₂ s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂
    s.support₁ s.support₂ s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos

lemma normalized_input_difference (s : Input ι) (R : Ideal O) (z : O) :
    positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P s.t s.X₁ s.X₂-
    positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P s.t s.Y₁ s.Y₂=
    (Real.sqrt (CenteredMomentAmplificationChildInput.volume s):ℂ)⁻¹*
      ∑I∈finiteColumns (Fintype.piFinset s.pools),coefficient s R 1 I*
        rowWeight s.η fixedBadMask 1 z s.t I := by
  rw [input_polynomial_difference]
  unfold positiveSlotRow CenteredMomentAmplificationChildInput.volume
  rw [s.same_product]
  ring

omit [DecidableEq ι] in
lemma input_energy_hasSum (s : Input ι) (R : Ideal O) (Φ : 𝓢(ℝ,ℂ))
    (K : ℝ) (hK : 0<K) :
    HasSum (fun z : O=>
      ‖∑I∈finiteColumns (Fintype.piFinset s.pools),coefficient s R 1 I*
        rowWeight s.η fixedBadMask 1 z s.t I‖^2*
          (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
      (finiteHeckeEnergy s.η fixedBadMask 1 s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R 1) Φ K).re := by
  have hs := Complex.hasSum_re (rowEnergy_summable Finset.univ
    (sourceGenerator (finiteColumns (Fintype.piFinset s.pools))) (sourceGenerator_supported _)
    (fun I=>coefficient s R 1 I*rowWeight s.η fixedBadMask 1 1 s.t I) Φ K hK).hasSum
  change HasSum _ (rowEnergy _ _ _ Φ K).re at hs
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hs
  simpa only [finiteHeckeEnergy_eq s.η fixedBadMask 1 s.t (dvd_mul_right _ _) (dvd_mul_left _ _),
    finite_hecke_sum_eq_rowPolynomial s.η fixedBadMask 1 _ s.t (dvd_mul_right _ _) (dvd_mul_left _ _)] using hs

theorem kept_difference_energy (s : Input ι) (R : Ideal O)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑'z : O,if keep z then
      ‖positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
          s.toData.coefficient s.P s.t s.X₁ s.X₂-
        positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
          s.toData.coefficient s.P s.t s.Y₁ s.Y₂‖^2*
        (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)=
      CenteredMomentRestrictedSource.sourceRestrictedEnergy keep
        (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R 1)
        (CenteredMomentHeckeColumnWindow.heightCoeff s.η s.t) Φ K /
          CenteredMomentAmplificationChildInput.volume s := by
  unfold CenteredMomentRestrictedSource.sourceRestrictedEnergy
    CenteredMomentRestrictedEnergy.restrictedEnergy
  rw [←tsum_div_const]
  apply tsum_congr
  intro z
  rw [height_source_row]
  by_cases hk : keep z
  · rw [ite_eq_left hk,ite_eq_left hk,normalized_input_difference,
      CenteredMomentDivisorRawEnergy.normalized_norm_sq _
        (CenteredMomentAmplificationChildInput.volume_pos s)]
    ring
  · simp only [ite_eq_right hk,zero_div]

omit [DecidableEq ι] in
lemma input_positive_summable (s : Input ι) (R : Ideal O) (keep : O→Prop)
    (Φ : 𝓢(ℝ,ℂ)) (K X₁ X₂ : ℝ) (hK : 0<K) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    Summable (fun z : O=>if keep z then
      ‖positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
        s.toData.coefficient s.P s.t X₁ X₂‖^2*
          (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0) := by
  obtain ⟨B,hB⟩ := product_bounded s.η (fixedBadMask*idealGenerator R) 1 s.t
    (Real.sqrt (X₁*X₂*∏i,s.P i):ℂ)⁻¹ s.W₁ s.W₂ s.b₁ s.b₂ X₁ X₂
    s.support₁ s.support₂ hX₁ hX₂ s.slots s.toData.coefficient
  exact bounded_radial_summable _ B hB keep Φ K hK

theorem positive_energy_comparison (s : Input ι) (R : Ideal O)
    (r : CenteredMomentRadialEligibleEnergy.Radial) :
    CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
      s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.X₁ s.X₂ r.keep r.profile r.scale ≤
    2*‖finiteHeckeEnergy s.η fixedBadMask 1 s.t (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s R 1) r.profile r.scale‖ / CenteredMomentAmplificationChildInput.volume s+
    2*CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
      s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.Y₁ s.Y₂ r.keep r.profile r.scale := by
  let V := CenteredMomentAmplificationChildInput.volume s
  have hV : 0<V := CenteredMomentAmplificationChildInput.volume_pos s
  let f : O→ℝ := fun z=>
    (‖∑I∈finiteColumns (Fintype.piFinset s.pools),coefficient s R 1 I*
      rowWeight s.η fixedBadMask 1 z s.t I‖^2*
      (r.profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/r.scale)).re)/V
  let g : O→ℝ := fun z=>if r.keep z then
    ‖positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P s.t s.Y₁ s.Y₂‖^2*
      (r.profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/r.scale)).re else 0
  have hf := (input_energy_hasSum s R r.profile r.scale r.scale_pos).div_const V
  have hg := input_positive_summable s R r.keep r.profile r.scale s.Y₁ s.Y₂
    r.scale_pos s.Y₁_pos s.Y₂_pos
  have hfn (z : O) : 0≤f z := div_nonneg (mul_nonneg (sq_nonneg _) (r.nonneg z)) hV.le
  have hgn (z : O) : 0≤g z := by
    dsimp only [g]
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (r.nonneg z)
    · rfl
  unfold CenteredMomentInductionEnergy.energy
  apply Real.tsum_le_of_sum_le (fun z=>by
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (r.nonneg z)
    · rfl)
  intro rows
  have hp (z : O) :
      (if r.keep z then
        ‖positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
          s.toData.coefficient s.P s.t s.X₁ s.X₂‖^2*
          (r.profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/r.scale)).re else 0) ≤ 2*f z+2*g z := by
    by_cases hk : r.keep z
    · let x := positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
        s.toData.coefficient s.P s.t s.X₁ s.X₂
      let y := positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
        s.toData.coefficient s.P s.t s.Y₁ s.Y₂
      have hn : ‖x‖≤‖x-y‖+‖y‖ := by simpa only [sub_add_cancel] using norm_add_le (x-y) y
      have hsq : ‖x‖^2≤2*‖x-y‖^2+2*‖y‖^2 := by
        have hh := pow_le_pow_left₀ (norm_nonneg x) hn 2
        nlinarith [sq_nonneg (‖x-y‖-‖y‖)]
      dsimp only [x,y] at hsq
      rw [normalized_input_difference,CenteredMomentDivisorRawEnergy.normalized_norm_sq _ hV] at hsq
      have hh := mul_le_mul_of_nonneg_right hsq (r.nonneg z)
      dsimp only [f,g]
      rw [ite_eq_left hk,ite_eq_left hk]
      convert hh using 1 ; ring
    · rw [ite_eq_right hk]
      exact add_nonneg (mul_nonneg (by norm_num) (hfn z)) (mul_nonneg (by norm_num) (hgn z))
  have hb := Finset.sum_le_sum (fun z (_:z∈rows)=>hp z)
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum] at hb
  have hs := sum_le_hasSum rows (fun z _=>hfn z) hf
  have ht := sum_le_hasSum rows (fun z _=>hgn z) hg.hasSum
  have he := div_le_div_of_nonneg_right
    (Complex.re_le_norm (finiteHeckeEnergy s.η fixedBadMask 1 s.t
      (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R 1) r.profile r.scale)) hV.le
  change ∑z∈rows,f z≤_ at hs
  change ∑z∈rows,g z≤∑'z,g z at ht
  change _≤2*‖finiteHeckeEnergy s.η fixedBadMask 1 s.t
    (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R 1) r.profile r.scale‖/V+2*∑'z,g z
  rw [mul_div_assoc]
  linarith

section Natural
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
variable {Z Bmask bΦ a b : ℝ}
variable (state : NaturalState Z Bmask bΦ) (p : Profiles a b) (ha : 0<a)
variable (S : ι→Finset (Ideal O)) (hp : ∀i,∀I∈S i,Prime I)
variable (ν : ι→Character) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
variable (hP : ∀i,0<P i) (hM : ∀i,1≤M i)
variable (aslot bslot : ℝ) (haslot : 0<aslot)
variable (hsSlot : ∀i,Function.support (Wslot i)⊆Set.Icc aslot bslot)
variable (hWslot : ∀i x,‖Wslot i x‖≤M i)
variable (t X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
variable (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (hsame : Y₁*Y₂=X₁*X₂)

def naturalData : Data ι where
  η := state.character
  m := state.mask
  A := 1
  t := t
  slots := S
  prime := hp
  ν := fun i=>idealCoeff (ν i)
  W := Wslot
  lo := fun _=>aslot
  hi := fun _=>bslot
  P := P
  lo_pos := fun _=>haslot
  P_pos := hP
  support := hsSlot
  W₁ := p.profile 0
  W₂ := p.profile 1
  X₁ := X₁
  X₂ := X₂
  Y₁ := Y₁
  Y₂ := Y₂
  M := M
  M_ge_one := hM
  coefficient_bound := fun i I _=>by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (idealCoeff_norm_le_one (ν i) I) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hWslot i ((Ideal.absNorm I:ℝ)/P i))
  b₁ := b
  b₂ := b
  support₁ := fun x hx=>(p.support 0 hx).2
  support₂ := fun x hx=>(p.support 1 hx).2
  X₁_pos := hX₁
  X₂_pos := hX₂
  Y₁_pos := hY₁
  Y₂_pos := hY₂
  same_product := hsame
  rows := ∅
  weight := fun _=>0
  weight_nonneg := fun _ _=>le_refl _

def naturalInput : Input ι :=
  completeInput (naturalData state p S hp ν Wslot P M hP hM aslot bslot haslot hsSlot hWslot
    t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame)
    (CenteredMomentDetectorPlainSource.support_zero (p.profile 0) a b ha (p.support 0))
    (CenteredMomentDetectorPlainSource.support_zero (p.profile 1) a b ha (p.support 1))
    (fun i I=>idealCoeff_norm_le_one (ν i) I) hWslot aslot bslot haslot
    (fun _=>le_refl _) (fun _=>le_refl _)

theorem natural_energy_comparison :
    let inp := naturalInput state p ha S hp ν Wslot P M hP hM aslot bslot haslot hsSlot hWslot
      t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame
    CenteredMomentInductionEnergy.energy state.character state.mask 1 t
      (p.profile 0) (p.profile 1) S
      (fun i I=>idealCoeff (ν i) I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P X₁ X₂
      state.radial.keep state.radial.profile state.radial.scale ≤
    2*‖finiteHeckeEnergy state.character fixedBadMask 1 t
      (finiteColumns (Fintype.piFinset inp.pools)) (coefficient inp state.puncture 1)
      state.radial.profile state.radial.scale‖/(X₁*X₂*∏i,P i)+
    2*CenteredMomentInductionEnergy.energy state.character state.mask 1 t
      (p.profile 0) (p.profile 1) S
      (fun i I=>idealCoeff (ν i) I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P Y₁ Y₂
      state.radial.keep state.radial.profile state.radial.scale :=
  positive_energy_comparison
    (naturalInput state p ha S hp ν Wslot P M hP hM aslot bslot haslot hsSlot hWslot
      t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame) state.puncture state.radial

end Natural
end SevenEighths.CenteredMomentEnergyOriginalSource

end

end OAI
