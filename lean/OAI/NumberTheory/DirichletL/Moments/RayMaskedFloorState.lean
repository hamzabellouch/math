import OAI.NumberTheory.DirichletL.Moments.RayMaskedFloor
import OAI.NumberTheory.DirichletL.Energy.State

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeZeroSupremum QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentPrimeSlot CenteredMomentInductionEnergy
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem exists_positive_floor {α : Type*} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (a₀ b₀ bΦ Bmask ε Lslot lo hi κ : ℝ)
    (ha₀ : 0<a₀) (hb₀ : 0≤b₀) (hbΦ : 0<bΦ) (hmask : 0≤Bmask)
    (hε : 0<ε) (hLs : 0≤Lslot) (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤T → (∀i,|v i|≤T) →
    ∀(Q : Ideal O),Q≤M → ∀s : NaturalState Z Bmask bΦ,
      s.fixedModulus=internalQ Q η₀ → s.width≤ε/16 → 6*κ*(∑i,w i)≤s.width →
    ∀p : Profiles a₀ b₀,∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=>primePool M H b (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      C*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+T)^degree*Z^(s.width+ε) := by
  let e : ℝ := ε/(4*(Bmask+1))
  have he : 0<e := div_pos hε (by positivity)
  have hcost : Bmask*e≤ε/4 := by
    have hh := mul_le_mul_of_nonneg_left (show Bmask≤Bmask+1 by linarith) he.le
    have hid : e*(Bmask+1)=ε/4 := by dsimp [e]; field_simp
    rw [hid] at hh
    linarith
  obtain ⟨J,S,C,hC,hfloor⟩ := natural_masked_positive_floor (α:=α) M H hH W a b ha hWs hW
    a₀ b₀ e ha₀ hb₀ he (ε/16) Lslot (ε/4) lo hi κ bΦ (by positivity) hbΦ.le hLs
    (by positivity) hbeta hκ
  refine ⟨J,S,C*bΦ^4,mul_pos hC (pow_pos hbΦ _),?_⟩
  intro η₀
  filter_upwards [hfloor η₀] with Z hZ
  intro θ w σ v t T hw hwL hσlo hσhi hT hv Q hQM s hQ hs hslots p X₁ X₂ hX₁ hX₂
  have hZ1 := s.base_ge_one
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ1
  have hrad : (s.puncture.radical.absNorm:ℝ)^e≤Z^(Bmask*e) := by
    rw [Real.rpow_mul hZ0.le]
    exact Real.rpow_le_rpow (by positivity) s.radical_bound he.le
  have hex (z : O) (hz : s.radial.keep z) :
      ¬CenteredExceptionalProfile.FixedInducingRow s.character (internalQ Q η₀)
        (fixedBadMask*ConcretePrimeRowBridge.idealGenerator s.puncture) 1 z := by
    rw [←hQ]
    exact s.nonexceptional z hz
  have hh := hZ θ w σ v t T hw hwL hσlo hσhi hT hv s.character Q s.radial s.puncture
    s.puncture_ne_zero hQM s.row_ne_zero hex s.radial_support s.rowWidth s.characterWidth
    (ε/16) s.row_nonneg s.character_nonneg hs le_rfl s.scale_eq s.modulus_bound
    (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) X₁ X₂ hX₁ hX₂
  have hwidth : s.rowWidth≤s.width := by dsimp [NaturalState.width]; linarith [s.character_nonneg]
  have hbudget : Bmask*e+(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i))≤s.width+ε := by
    linarith
  have hpow : Z^(Bmask*e)*Z^(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i))≤Z^(s.width+ε) := by
    rw [←Real.rpow_add hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ1 hbudget
  have hd := diagonalControl_nonneg s.radial.profile
  have hc := p.control_nonneg S
  apply hh.trans
  change C*(s.puncture.radical.absNorm:ℝ)^e*diagonalControl s.radial.profile*bΦ^4*
    (p.control S)^2*(1+|t|+T)^J*Z^(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i))≤_
  calc
    _ ≤ C*Z^(Bmask*e)*diagonalControl s.radial.profile*bΦ^4*
      (p.control S)^2*(1+|t|+T)^J*Z^(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i)) := by gcongr
    _ = (C*bΦ^4*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+T)^J)*
      (Z^(Bmask*e)*Z^(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI
