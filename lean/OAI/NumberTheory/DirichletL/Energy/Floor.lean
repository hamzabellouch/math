import OAI.NumberTheory.DirichletL.Energy.State

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyState
open HeckeFamily CenteredMomentNaturalMaskedFloor
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound

theorem exists_zero_floor (a b bΦ Bmask ε:ℝ)(ha:0<a)(hb:0≤b)
    (hbΦ:0<bΦ)(hmask:0≤Bmask)(hε:0<ε):
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀Q:Ideal HeckeFamily.O,ZeroBound Q a b bΦ Bmask (ε/16) ε degree S C 1:=by
  let e:ℝ:=ε/(4*(Bmask+1))
  have he:0<e:=div_pos hε (by positivity)
  have hbudget:e*Bmask+4*(ε/16)≤ε:=by
    have hcost:e*Bmask≤ε/4:=by
      have hinc:Bmask≤Bmask+1:=by linarith
      have hh:=mul_le_mul_of_nonneg_left hinc he.le
      have hid:e*(Bmask+1)=ε/4:=by dsimp [e];field_simp
      rw [hid] at hh
      exact hh
    linarith
  obtain ⟨degree,S,C,hC,hfloor⟩:=natural_masked_floor a b e ha hb he
  refine ⟨degree,S,C*bΦ^4,mul_pos hC (pow_pos hbΦ _),?_⟩
  intro Q Z hZ₀ s hQ hs p t X₁ X₂ hX₁ hX₂
  have hZ:=s.base_ge_one
  have hZ0:0<Z:=zero_lt_one.trans_le hZ
  have hrad: (s.puncture.radical.absNorm:ℝ)^e≤Z^(Bmask*e):=by
    rw [Real.rpow_mul hZ0.le]
    exact Real.rpow_le_rpow (by positivity) s.radical_bound he.le
  have hp:Z^(Bmask*e)*Z^(s.width+4*(ε/16))≤Z^(s.width+ε):=by
    rw [←Real.rpow_add hZ0]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    linarith
  have hh:=hfloor (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
    s.character s.fixedModulus s.puncture s.radial bΦ s.puncture_ne_zero hbΦ.le
    s.radial_support s.row_ne_zero s.nonexceptional Z s.rowWidth s.characterWidth
    (ε/16) t X₁ X₂ hZ s.row_nonneg s.character_nonneg s.scale_eq hs hX₁ hX₂ s.modulus_bound
  rw [s.plainEnergy_eq_zero]
  change CenteredMomentCoreFloor.zeroEnergy _ _ _ _ _ _ _ _ _≤_
  apply hh.trans
  have hd:=diagonalControl_nonneg s.radial.profile
  have hc:=p.control_nonneg S
  change C*(s.puncture.radical.absNorm:ℝ)^e*bΦ^4*diagonalControl s.radial.profile*
    (p.control S)^2*(1+‖t‖)^degree*Z^(s.width+4*(ε/16))≤_
  calc
    _≤C*Z^(Bmask*e)*bΦ^4*diagonalControl s.radial.profile*
      (p.control S)^2*(1+‖t‖)^degree*Z^(s.width+4*(ε/16)):=by gcongr
    _=(C*bΦ^4*diagonalControl s.radial.profile*(p.control S)^2*(1+‖t‖)^degree)*
      (Z^(Bmask*e)*Z^(s.width+4*(ε/16))):=by ring
    _≤_:=mul_le_mul_of_nonneg_left hp (by positivity)

end SevenEighths.CenteredMomentEnergyState

end

end OAI
