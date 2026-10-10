import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourcePrimeBound

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeRowClosure HeckePrimeRay HeckeZeroSupremum
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open CenteredMomentFixedRayInducingTransport CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

lemma natural_relative_twists {η : Character} {z : O} (F : NaturalRow η z) (hz : z≠0)
    (η₀ : Character) (Q : Ideal O) (hQM : Q≤M)
    (hex : ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z) :
    ∀θ : RayQuotient.Characters M H,
      (twistedFamily M H hH (F.character.product η₀.inverse) θ).residue≠1 := by
  have hn : ¬FixedInducingRow (η.product η₀.inverse) (internalQ Q η₀) fixedBadMask 1 z :=
    (not_fixedInducingRow_product_iff η η₀.inverse _ fixedBadMask 1 z inf_le_right
      fixedBadMask_ne_zero one_ne_zero hz (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr hex
  apply CenteredMomentRayNonprincipal.all_ray_twists_nonprincipal M H hH
    (η.product η₀.inverse) (F.character.product η₀.inverse) (internalQ Q η₀)
    fixedBadMask 1 z ?_ (inf_le_left.trans hQM) hn
  exact product_row_presentation η F.character η₀.inverse fixedBadMask 1 z
    (by simpa only [one_mul] using F.element)

include hH

theorem natural_relative_slot_bound (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
      ∀P : ℝ,1≤P → P≤Z^Lslot → ∀η : Character,∀z : O,z≠0 →
      ∀F : NaturalRow η z,(F.character.modulus.absNorm:ℝ)≤Z^Lmod →
      ∀Q : Ideal O,Q≤M → ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z →
      ∀σ t v : ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H b P)
        (fun I=>idealCoeff η₀.inverse I*HeckePrimeAnnular.annularWeight W P σ v I) t P‖^2≤
        C*(1+|t|+|v|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,hbound⟩:=CenteredMomentPrimeHeight.ray_prime_all_height_squared
    M H hH W a b ha hWs hW (Lmod+1) Lslot loss lo hi κ (by linarith) hLs hloss hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro η₀
  filter_upwards [eventually_ge_atTop Z₀,eventually_ge_atTop (η₀.modulus.absNorm:ℝ),
    eventually_gt_atTop (0:ℝ)] with Z hZ0 hη₀ hZ
  intro P hP hPcap η z hz F hcond Q hQM hex σ t v hσ hσhi
  have hc : ((F.character.product η₀.inverse).modulus.absNorm:ℝ)≤Z^(Lmod+1) := by
    have hb : ((F.character.product η₀.inverse).modulus.absNorm:ℝ)≤
        (F.character.modulus.absNorm:ℝ)*(η₀.modulus.absNorm:ℝ) := by
      exact_mod_cast HeckePrimeScale.product_modulus_bound F.character η₀.inverse
    apply hb.trans
    calc
      _≤Z^Lmod*Z := mul_le_mul hcond hη₀ (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)
      _=Z^(Lmod+1) := by rw [Real.rpow_add hZ,Real.rpow_one]
  have hb:=hbound Z P hZ0 hP hPcap (F.character.product η₀.inverse) hc
    (natural_relative_twists M H hH F hz η₀ Q hQM hex) σ (t+v) hσ hσhi
  rw [relative_normalizedSlot_eq_ray M H η F.character η₀.inverse fixedBadMask 1 z
    (by simpa only [one_mul] using F.element) W b P σ t v (zero_lt_one.trans_le hP),norm_mul,
    CenteredMomentTwist.norm_real_imaginary_power P t (zero_lt_one.trans_le hP),one_mul]
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hP) _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ.le _)
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact pow_le_pow_left₀ (by positivity) (by linarith [abs_add_le t v]) degree

theorem natural_character_slot_bound (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ν : Character,∀ᶠZ : ℝ in atTop,
      ∀P : ℝ,1≤P → P≤Z^Lslot → ∀η : Character,∀z : O,z≠0 →
      ∀F : NaturalRow η z,(F.character.modulus.absNorm:ℝ)≤Z^Lmod →
      ∀Q : Ideal O,Q≤M → Q≤ν.modulus → ¬FixedInducingRow η Q fixedBadMask 1 z →
      ∀σ t v : ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H b P)
        (fun I=>idealCoeff ν I*HeckePrimeAnnular.annularWeight W P σ v I) t P‖^2≤
        C*(1+|t|+|v|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,hC,hbound⟩:=natural_relative_slot_bound M H hH W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro ν
  filter_upwards [hbound ν.inverse] with Z hz
  intro P hP hPcap η z hz0 F hcond Q hQM hQν hex σ t v hσ hσhi
  have hQeq : internalQ Q ν.inverse=Q := inf_eq_left.mpr hQν
  have he:=hz P hP hPcap η z hz0 F hcond Q hQM (by simpa only [hQeq] using hex) σ t v hσ hσhi
  simpa only [idealCoeff_inverse_conj,starRingEnd_self_apply] using he

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
