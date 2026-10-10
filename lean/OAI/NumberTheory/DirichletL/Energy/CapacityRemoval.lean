import OAI.NumberTheory.DirichletL.Moments.RelativeCapacityRemoval
import OAI.NumberTheory.DirichletL.Energy.State
import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFiber

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyCapacityRemoval
open HeckeFamily ConcreteTraceCRT CenteredMomentRetainedEnergy
open CenteredMomentInductionEnergy CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot
open CenteredMomentSlotNormalization CenteredMomentRelativeCapacityRemoval
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentEnergyState
open CenteredExceptionalProfile CenteredMomentFixedRowMask
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem compact_radial_summable (f : O→ℂ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ))
    (K b : ℝ) (hK : 0<K) (hs : Function.support (Φ:ℝ→ℂ)⊆Set.Iic b) :
    Summable (fun z : O=>if keep z then ‖f z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  obtain ⟨N,hN⟩:=exists_nat_ge (b*K)
  apply summable_of_ne_finset_zero (s:=ShortDraftLatticeCount.rowNormBall N)
  intro z hz
  have hΦ : Φ (‖eisEmbedding z‖^2/K)=0 := by
    by_contra hn
    have hh : ‖eisEmbedding z‖^2≤(N:ℝ):=((div_le_iff₀ hK).mp (hs hn)).trans hN
    apply hz
    apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
    exact_mod_cast (show ((Ideal.span {z}).absNorm:ℝ)≤N by
      rwa [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span])
  simp [hΦ]

omit [DecidableEq ι] in

theorem energy_support (η : Character) (m A : O) (t : ℝ) (W₁ W₂ : ℝ→ℂ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K=
      energy η m A t W₁ W₂ S β P X₁ X₂
        (fun z=>keep z ∧ Φ (‖eisEmbedding z‖^2/K)≠0) Φ K := by
  unfold energy
  apply tsum_congr
  intro z
  by_cases hk : keep z <;> by_cases hp : Φ (‖eisEmbedding z‖^2/K)=0 <;> simp [hk,hp]

omit [Fintype ι] in

theorem selected_eq_positive (J : Finset ι) (η : Character) (m A z : O)
    (W₁ W₂ : ℝ→ℂ) (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ)
    (P : ι→ℝ) (t X₁ X₂ : ℝ) (hX : 0≤X₁*X₂) (hP : ∀i,0≤P i) :
    selectedProduct J η m A z W₁ W₂ S β P t X₁ X₂=
      positiveSlotRow η m A z W₁ W₂ (fun i:J=>S i) (fun i:J=>β i)
        (fun i:J=>P i) t X₁ X₂ := by
  have hh:=selectedProduct_univ η m A z W₁ W₂
    (fun i:J=>S i) (fun i:J=>β i) (fun i:J=>P i) t X₁ X₂ hX (fun i=>hP i)
  have hp : (∏i:J,normalizedSlot η m A z (S i) (β i) t (P i))=
      ∏i∈J,normalizedSlot η m A z (S i) (β i) t (P i) :=
    Finset.prod_coe_sort J (fun i=>normalizedSlot η m A z (S i) (β i) t (P i))
  unfold selectedProduct at hh ⊢
  rw [hp] at hh
  exact hh

theorem unit_puncture_energy (η : Character) (t : ℝ) (W₁ W₂ : ℝ→ℂ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (X₁ X₂ : ℝ)
    (keep : O→Prop) (hz : ∀z,keep z→z≠0) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    energy η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 t W₁ W₂ S β P X₁ X₂ keep Φ K=
      energy η fixedBadMask 1 t W₁ W₂ S β P X₁ X₂ keep Φ K := by
  unfold energy
  apply tsum_congr
  intro z
  by_cases hk : keep z
  · simp only [ite_eq_left hk]
    rw [natural_unit_mask_positive (naturalRow η z (hz z hk))]
  · simp only [ite_eq_right hk]

theorem eventual_state_conductor (bΦ Mcap : ℝ) (hb : 0≤bΦ) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Bmask:ℝ,∀s:NaturalState Z Bmask bΦ,
      s.width≤Mcap → ∀z:O,∀hz:z≠0,
      s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale)≠0 →
      ((naturalRow s.character z hz).character.modulus.absNorm:ℝ)≤Z^(Mcap+1) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_ge_atTop ((fixedConductorFactor:ℝ)*bΦ)] with Z hZ hF
  refine ⟨hZ,?_⟩
  intro Bmask s hwidth z hz hΦ
  have hn : ((Ideal.span {z}).absNorm:ℝ)≤bΦ*Z^s.rowWidth := by
    rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,←s.scale_eq]
    exact (div_le_iff₀ s.radial.scale_pos).mp (s.radial_support hΦ)
  have he:=(naturalRow s.character z hz).modulus_power_bound Z s.characterWidth s.rowWidth bΦ
    (zero_lt_one.trans hZ) hb s.modulus_bound hn
  have hm:Z^(s.characterWidth+s.rowWidth)≤Z^Mcap:=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by simpa [NaturalState.width,add_comm] using hwidth)
  apply he.trans
  calc
    _≤Z*Z^Mcap:=mul_le_mul hF hm (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
      (zero_lt_one.trans hZ).le
    _=Z^(Mcap+1):=by rw [Real.rpow_add (zero_lt_one.trans hZ),Real.rpow_one];ring

theorem eventual_row_conductor (bΦ Mrow : ℝ) (hb : 0≤bΦ) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Bmask:ℝ,∀s:NaturalState Z Bmask bΦ,
      s.rowWidth≤Mrow → ∀q:ℝ,(s.character.modulus.absNorm:ℝ)≤Z^q →
      ∀z:O,∀hz:z≠0,s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale)≠0 →
      ((naturalRow s.character z hz).character.modulus.absNorm:ℝ)≤Z^(Mrow+q+1) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_ge_atTop ((fixedConductorFactor:ℝ)*bΦ)] with Z hZ hF
  refine ⟨hZ,?_⟩
  intro Bmask s hrow q hq z hz hΦ
  have hn : ((Ideal.span {z}).absNorm:ℝ)≤bΦ*Z^s.rowWidth := by
    rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,←s.scale_eq]
    exact (div_le_iff₀ s.radial.scale_pos).mp (s.radial_support hΦ)
  have he:=(naturalRow s.character z hz).modulus_power_bound Z q s.rowWidth bΦ
    (zero_lt_one.trans hZ) hb hq hn
  have hm:Z^(q+s.rowWidth)≤Z^(Mrow+q):=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  apply he.trans
  calc
    _≤Z*Z^(Mrow+q):=mul_le_mul hF hm (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
      (zero_lt_one.trans hZ).le
    _=Z^(Mrow+q+1):=by
      conv_rhs => rw [Real.rpow_add (zero_lt_one.trans hZ),Real.rpow_one]
      ring

lemma state_unit_nonexceptional {Z Bmask bΦ : ℝ} (s : NaturalState Z Bmask bΦ)
    (hpuncture : s.puncture=1) (Q : Ideal O) (hQ : s.fixedModulus=Q)
    (z : O) (hk : s.radial.keep z) : ¬FixedInducingRow s.character Q fixedBadMask 1 z := by
  intro hh
  apply s.nonexceptional z hk
  rw [hQ,hpuncture]
  exact (fixedInducingRow_mul_mask_iff s.character Q fixedBadMask
    (ConcretePrimeRowBridge.idealGenerator 1) 1 z fixedBadMask_ne_zero
    (ConcretePrimeRowBridge.idealGenerator_ne_zero 1 one_ne_zero) one_ne_zero (s.row_ne_zero z hk)
    (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr hh

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
include hH

theorem actual_state_capacity_removal
    (W : ι→ℝ→ℂ) (a b : ι→ℝ) (ha : ∀i,0<a i)
    (hWs : ∀i,Function.support (W i)⊆Set.Icc (a i) (b i))
    (hW : ∀i,ContDiff ℝ ∞ (W i))
    (Mrow bΦ Lmod Lslot ε lo hi κ : ℝ) (hbΦ : 0≤bΦ)
    (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hε : 0<ε)
    (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ) :
    ∃degree:ℕ,∃C:ℝ,0<C ∧ ∀ν:ι→Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀(J:Finset ι)(w:ι→ℝ)(n₁ n₂ width mesh:ℝ),0≤mesh →
      (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    ∃R:Finset ι,R⊆J ∧ (R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤width) ∧
      κ*(∑i∈R,w i)≤CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh ∧
    ∀Z:ℝ,Z₀≤Z → ∀Bmask:ℝ,∀s:NaturalState Z Bmask bΦ,
      s.puncture=1 → s.rowWidth≤Mrow → ∀q:ℝ,
      (s.character.modulus.absNorm:ℝ)≤Z^q → Mrow+q+1≤Lmod →
    ∀Q:Ideal O,s.fixedModulus=Q → Q≤M → (∀i,Q≤(ν i).modulus) →
    ∀(σ freq:ι→ℝ)(t V:ℝ),(∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤V → (∀i,|freq i|≤V) →
    ∀(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ),0<X₁ → 0<X₂ →
      let P:=fun i=>Z^(w i)
      let S:=fun i=>primePool M H (b i) (P i)
      let coeff:=fun i I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (W i) (P i) (σ i) (freq i) I
      energy s.character s.mask 1 t W₁ W₂ (fun i:J=>S i) (fun i:J=>coeff i)
        (fun i:J=>P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
        C*(1+|t|+V)^degree*Z^(ε+CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh)*
          energy s.character s.mask 1 t W₁ W₂ (fun i:↥(J\R)=>S i) (fun i:↥(J\R)=>coeff i)
            (fun i:↥(J\R)=>P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale := by
  obtain ⟨degree,C,hC,hbound⟩:=actual_relative_capacity_removal M H hH W a b ha hWs hW
    Lmod Lslot ε lo hi κ hLm hLs hε hbeta hκ
  obtain ⟨Zsupport,hsupport⟩:=eventually_atTop.mp (eventual_row_conductor bΦ Mrow hbΦ)
  refine ⟨degree,C,hC,?_⟩
  intro ν
  obtain ⟨Zbase,hZbase,hbound⟩:=hbound ν
  refine ⟨max Zbase Zsupport,lt_of_lt_of_le hZbase (le_max_left _ _),?_⟩
  intro J w n₁ n₂ width mesh hmesh hw hwm hwcap
  obtain ⟨R,hR,hcapacity,hcost,hpoint⟩:=hbound J w n₁ n₂ width mesh hmesh hw hwm hwcap
  refine ⟨R,hR,hcapacity,hcost,?_⟩
  intro Z hZ Bmask s hpuncture hrow q hmod hLmod Q hQ hQM hQν σ freq t V hσ hσhi hV hfreq W₁ W₂ X₁ X₂ hX₁ hX₂
  dsimp only
  have hZbase' : Zbase≤Z:=(le_max_left _ _).trans hZ
  have hs:=(hsupport Z ((le_max_right _ _).trans hZ))
  have hZpos:0<Z:=zero_lt_one.trans hs.1
  have hscale (i:ι) : 0≤Z^(w i):=Real.rpow_nonneg hZpos.le _
  let P:=fun i=>Z^(w i)
  let S:=fun i=>primePool M H (b i) (P i)
  let coeff:=fun i I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (W i) (P i) (σ i) (freq i) I
  let cost:=C*(1+|t|+V)^degree*Z^(ε+CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh)
  have hmask:s.mask=fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1:=by rw [NaturalState.mask,hpuncture]
  rw [hmask,unit_puncture_energy _ _ _ _ _ _ _ _ _ _ s.row_ne_zero,
    unit_puncture_energy _ _ _ _ _ _ _ _ _ _ s.row_ne_zero]
  change energy s.character fixedBadMask 1 t W₁ W₂ (fun i:J=>S i) (fun i:J=>coeff i)
    (fun i:J=>P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
    cost*energy s.character fixedBadMask 1 t W₁ W₂ (fun i:↥(J\R)=>S i) (fun i:↥(J\R)=>coeff i)
    (fun i:↥(J\R)=>P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale
  have hsum (T:Finset ι):=compact_radial_summable
    (fun z=>positiveSlotRow s.character fixedBadMask 1 z W₁ W₂ (fun i:T=>S i)
      (fun i:T=>coeff i) (fun i:T=>P i) t X₁ X₂)
    s.radial.keep s.radial.profile s.radial.scale bΦ s.radial.scale_pos s.radial_support
  unfold energy
  rw [←tsum_mul_left]
  apply (hsum J).tsum_le_tsum _ ((hsum (J\R)).mul_left cost)
  intro z
  by_cases hk:s.radial.keep z
  · simp only [ite_eq_left hk]
    by_cases hp:s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale)=0
    · simp [hp]
    · have hz:=s.row_ne_zero z hk
      have hc:((naturalRow s.character z hz).character.modulus.absNorm:ℝ)≤Z^Lmod:=
        (hs.2 Bmask s hrow q hmod z hz hp).trans
          (Real.rpow_le_rpow_of_exponent_le hs.1.le hLmod)
      have hh:=hpoint Z hZbase' s.character z hz (naturalRow s.character z hz) hc
        Q hQM hQν (state_unit_nonexceptional s hpuncture Q hQ z hk)
        σ freq t V hσ hσhi hV hfreq W₁ W₂ X₁ X₂
      dsimp only at hh
      rw [selected_eq_positive J s.character fixedBadMask 1 z W₁ W₂ S coeff P t X₁ X₂ (mul_pos hX₁ hX₂).le hscale,
        selected_eq_positive (J\R) s.character fixedBadMask 1 z W₁ W₂ S coeff P t X₁ X₂ (mul_pos hX₁ hX₂).le hscale] at hh
      exact (mul_le_mul_of_nonneg_right hh (s.radial.nonneg z)).trans_eq (by dsimp only [cost];ring)
  · simp only [ite_eq_right hk,mul_zero,le_refl]

theorem actual_relative_state_capacity_removal
    (W : ι→ℝ→ℂ) (a b : ι→ℝ) (ha : ∀i,0<a i)
    (hWs : ∀i,Function.support (W i)⊆Set.Icc (a i) (b i))
    (hW : ∀i,ContDiff ℝ ∞ (W i))
    (Mrow bΦ Lmod Lslot ε lo hi κ : ℝ) (hbΦ : 0≤bΦ)
    (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hε : 0<ε)
    (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ) :
    ∃degree:ℕ,∃C:ℝ,0<C ∧ ∀η₀:Character,∀θ:ι→RayQuotient.Characters M H,
    let ν:=fun i=>relativeCharacter M H hH η₀ (θ i);
    ∃Z₀:ℝ,1<Z₀ ∧
    ∀(J:Finset ι)(w:ι→ℝ)(n₁ n₂ width mesh:ℝ),0≤mesh →
      (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    ∃R:Finset ι,R⊆J ∧ (R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤width) ∧
      κ*(∑i∈R,w i)≤CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh ∧
    ∀Z:ℝ,Z₀≤Z → ∀Bmask:ℝ,∀s:NaturalState Z Bmask bΦ,
      s.puncture=1 → s.rowWidth≤Mrow → ∀q:ℝ,
      (s.character.modulus.absNorm:ℝ)≤Z^q → Mrow+q+1≤Lmod →
    ∀Q:Ideal O,s.fixedModulus=internalQ Q η₀ → Q≤M →
    ∀(σ freq:ι→ℝ)(t V:ℝ),(∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤V → (∀i,|freq i|≤V) →
    ∀(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ),0<X₁ → 0<X₂ →
      let P:=fun i=>Z^(w i)
      let S:=fun i=>primePool M H (b i) (P i)
      let coeff:=fun i I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (W i) (P i) (σ i) (freq i) I
      energy s.character s.mask 1 t W₁ W₂ (fun i:J=>S i) (fun i:J=>coeff i)
        (fun i:J=>P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
        C*(1+|t|+V)^degree*Z^(ε+CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh)*
          energy s.character s.mask 1 t W₁ W₂ (fun i:↥(J\R)=>S i) (fun i:↥(J\R)=>coeff i)
            (fun i:↥(J\R)=>P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale := by
  obtain ⟨degree,C,hC,hbound⟩:=actual_state_capacity_removal M H hH W a b ha hWs hW
    Mrow bΦ Lmod Lslot ε lo hi κ hbΦ hLm hLs hε hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro η₀ θ
  dsimp only
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound (fun i=>relativeCharacter M H hH η₀ (θ i))
  refine ⟨Z₀,hZ₀,?_⟩
  intro J w n₁ n₂ width mesh hmesh hw hwm hwcap
  obtain ⟨R,hR,hcapacity,hcost,henergy⟩:=hbound J w n₁ n₂ width mesh hmesh hw hwm hwcap
  refine ⟨R,hR,hcapacity,hcost,?_⟩
  intro Z hZ Bmask s hpuncture hrow q hmod hLmod Q hQ hQM
  exact henergy Z hZ Bmask s hpuncture hrow q hmod hLmod (internalQ Q η₀) hQ
    (inf_le_left.trans hQM)
    (fun i=>relativeCharacter_fixedQ M H hH η₀ (θ i) (internalQ Q η₀)
      (inf_le_left.trans hQM) inf_le_right)

end SevenEighths.CenteredMomentEnergyCapacityRemoval

end

end OAI
