import OAI.NumberTheory.DirichletL.Energy.CapacityRemoval
import OAI.NumberTheory.DirichletL.Energy.Bands

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyPaidBands
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentPrimeSlot CenteredMomentRetainedEnergy
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource QuadraticInitialBound
local notation "O" => HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

omit [Fintype α] in
lemma remaining_energy_bound
    (W:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C₀ C₁:ℝ)
    (hC₀:0≤C₀)(hC₁:0≤C₁)
    (hzero:ZeroAt (internalQ Q η₀) a b bΦ Bmask L Mcap ε Z degree S C₀)
    (hpositive:PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
      Mcap ε κ Z η₀ Q degree S C₁)
    (J R:Finset α)(θ:α→RayQuotient.Characters M H)(w σ v:α→ℝ)(t height:ℝ)
    (hw:∀i,0≤w i)(hwL:∀i,w i≤Lslot)(hσlo:∀i,lo≤σ i)(hσhi:∀i,σ i≤hi)
    (hheight:0≤height)(hv:∀i,|v i|≤height)
    (s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=internalQ Q η₀)(hs:s.width≤Mcap)
    (p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hc₁:X₁≤Z^L)(hc₂:X₂≤Z^L)
    (hcapacity:R=J ∨ length Z X₁+length Z X₂+6*κ*(∑i∈J\R,w i)≤s.width):
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:↥(J\R)=>primePool M H bslot (Z^(w i)))
      (fun (i:↥(J\R)) I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i:↥(J\R)=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      (C₀+C₁)*diagonalControl s.radial.profile*(p.control S)^2*
        (1+|t|+height)^degree*Z^(s.width+ε) := by
  have hd:=diagonalControl_nonneg s.radial.profile
  have hp:=sq_nonneg (p.control S)
  have hz:0≤Z^(s.width+ε):=Real.rpow_nonneg (zero_le_one.trans s.base_ge_one) _
  rcases hcapacity with hR|hcap
  · subst R
    let : IsEmpty ↥(J\J) := ⟨fun i=>by
      have hi:=Finset.mem_sdiff.mp i.property
      exact hi.2 hi.1⟩
    have he:=hzero s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
    have hid : energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i:↥(J\J)=>primePool M H bslot (Z^(w i)))
        (fun (i:↥(J\J)) I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i:↥(J\J)=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale =
        s.plainEnergy p t X₁ X₂ := by
      simp only [energy,positiveSlotRow,NaturalState.plainEnergy,
        Fintype.prod_empty,mul_one]
    rw [hid]
    apply he.trans
    simp only [Real.norm_eq_abs]
    have hpow:(1+|t|)^degree≤(1+|t|+height)^degree :=
      pow_le_pow_left₀ (by positivity) (by linarith) degree
    exact mul_le_mul_of_nonneg_right (mul_le_mul
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₁) hd) hp)
      hpow (by positivity) (mul_nonneg (mul_nonneg (add_nonneg hC₀ hC₁) hd) hp)) hz
  · have he:=hpositive (J\R) (fun i=>θ i) (fun i=>w i) (fun i=>σ i) (fun i=>v i)
      t height (fun i=>hw i) (fun i=>hwL i) (fun i=>hσlo i) (fun i=>hσhi i)
      hheight (fun i=>hv i) s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂
      (by simpa only [Finset.sum_coe_sort] using hcap)
    apply he.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₀) hd) hp)
        (pow_nonneg (by positivity) _)) hz

end SevenEighths.CenteredMomentEnergyPaidBands

end

end OAI
