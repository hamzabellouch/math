import OAI.NumberTheory.DirichletL.Energy.ZeroGrowth
import OAI.NumberTheory.DirichletL.Energy.ZeroGrowthReserve
import OAI.NumberTheory.DirichletL.Energy.ZeroGrowthOriginal

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthConclusion
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyZeroGrowth CenteredMomentFiniteProfileExceptional
open CenteredMomentInductionEnergy QuadraticInitialBound
local notation "O" => HeckeFamily.O

lemma profile_control_mono {a b:ℝ}(p:Profiles a b)
    {S T:Finset (ℕ×ℕ)}(hST:S⊆T):p.control S≤p.control T:=by
  unfold Profiles.control
  exact mul_le_mul
    (Seminorm.le_def.mp (Finset.sup_mono hST) (p.profile 0))
    (Seminorm.le_def.mp (Finset.sup_mono hST) (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

lemma zeroGrowth_mono (Q:Ideal O)(a b bΦ Bmask L L' M M' ε ε' Z:ℝ)
    (degree degree':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hL:L'≤L)(hM:M'≤M)(hε:ε≤ε')(hdegree:degree≤degree')
    (hST:S⊆T)(hC:0≤C)(hCC:C≤C')
    (h:ZeroGrowthAt Q a b bΦ Bmask L M ε Z degree S C):
    ZeroGrowthAt Q a b bΦ Bmask L' M' ε' Z degree' T C':=by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hscale:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le s.base_ge_one hL
  have hh:=h s hQ (hs.trans hM) p t X₁ X₂ hX₁ hX₂
    (hc₁.trans hscale) (hc₂.trans hscale)
  have hC' : 0≤C' := hC.trans hCC
  have hp:=profile_control_mono p hST
  have hpn:=p.control_nonneg S
  have hpt:=p.control_nonneg T
  have hd:=diagonalControl_nonneg s.radial.profile
  have hheight:(1+‖t‖)^degree≤(1+‖t‖)^degree':=
    pow_le_pow_right₀ (by linarith [norm_nonneg t]) hdegree
  have hpower:Z^(max s.width (length Z X₁+length Z X₂)+ε)≤
      Z^(max s.width (length Z X₁+length Z X₂)+ε'):=
    Real.rpow_le_rpow_of_exponent_le s.base_ge_one (by linarith)
  have hZ : 0≤Z := zero_le_one.trans s.base_ge_one
  have hfront:C*diagonalControl s.radial.profile*(p.control S)^2*(1+‖t‖)^degree≤
      C'*diagonalControl s.radial.profile*(p.control T)^2*(1+‖t‖)^degree':=by
    apply mul_le_mul _ hheight (by positivity) (by positivity)
    apply mul_le_mul _ ((sq_le_sq₀ hpn hpt).mpr hp) (sq_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_right hCC hd
  exact hh.trans (mul_le_mul hfront hpower (Real.rpow_nonneg hZ _) (by positivity))

lemma zeroAt_mono (Q:Ideal O)(a b bΦ Bmask L L' M M' ε ε' Z:ℝ)
    (degree degree':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hL:L'≤L)(hM:M'≤M)(hε:ε≤ε')(hdegree:degree≤degree')
    (hST:S⊆T)(hC:0≤C)(hCC:C≤C')
    (h:ZeroAt Q a b bΦ Bmask L M ε Z degree S C):
    ZeroAt Q a b bΦ Bmask L' M' ε' Z degree' T C':=by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hscale:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le s.base_ge_one hL
  have hh:=h s hQ (hs.trans hM) p t X₁ X₂ hX₁ hX₂
    (hc₁.trans hscale) (hc₂.trans hscale)
  have hC' : 0≤C' := hC.trans hCC
  have hp:=profile_control_mono p hST
  have hpn:=p.control_nonneg S
  have hpt:=p.control_nonneg T
  have hd:=diagonalControl_nonneg s.radial.profile
  have hheight:(1+‖t‖)^degree≤(1+‖t‖)^degree':=
    pow_le_pow_right₀ (by linarith [norm_nonneg t]) hdegree
  have hpower:Z^(s.width+ε)≤Z^(s.width+ε'):=
    Real.rpow_le_rpow_of_exponent_le s.base_ge_one (by linarith)
  have hZ : 0≤Z := zero_le_one.trans s.base_ge_one
  have hfront:C*diagonalControl s.radial.profile*(p.control S)^2*(1+‖t‖)^degree≤
      C'*diagonalControl s.radial.profile*(p.control T)^2*(1+‖t‖)^degree':=by
    apply mul_le_mul _ hheight (by positivity) (by positivity)
    apply mul_le_mul _ ((sq_le_sq₀ hpn hpt).mpr hp) (sq_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_right hCC hd
  exact hh.trans (mul_le_mul hfront hpower (Real.rpow_nonneg hZ _) (by positivity))

theorem zero_from_same_width_growth (a b bΦ ε Mcap Bmask Loriginal:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)
    (hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d L:ℝ,0<d ∧ 0<L ∧ Loriginal≤L ∧
      ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K→
        ZeroGrowthAt Q a b bΦ Bmask L Mcap d Z degree S K→
        ZeroAt Q a b bΦ Bmask Loriginal Mcap ε Z J U (C*(K+1)):=by
  obtain ⟨d,L,saving,Cledger,hd,hL,hsaving,hCledger,hLoriginal,hroom,hledger⟩:=
    CenteredMomentEnergyZeroGrowthReserve.exists_growth_reserve
      ε Mcap Bmask bΦ Loriginal hε hM hB
  refine ⟨d,L,hd,hL,hLoriginal,?_⟩
  intro S
  obtain ⟨J,U,Csource,hCsource,hsource⟩:=
    CenteredMomentEnergyZeroGrowthOriginal.original_from_growth
      a b bΦ d d d saving L ha hlo hhi hbΦ hd hd hd S
  refine ⟨J,U,Csource*Cledger,mul_pos hCsource hCledger,?_⟩
  filter_upwards [hsource] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Q degree K hK hgrowth s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hscale:Z^Loriginal≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ.1.le hLoriginal
  have hh:=hZ.2 Bmask L Mcap d Q degree K hK hgrowth hB hroom
    (by linarith) s hQ hs p t X₁ X₂ hX₁ hX₂ (hc₁.trans hscale) (hc₂.trans hscale)
  have hl:=hledger Z hZ.1.le s hs
  have hfront:0≤Csource*(K+1)*diagonalControl s.radial.profile*
      (p.control U)^2*(1+|t|)^J:=by
    have hd:=diagonalControl_nonneg s.radial.profile
    positivity
  calc
    _≤Csource*(K+1)*diagonalControl s.radial.profile*(p.control U)^2*(1+|t|)^J*
        (Cledger*Z^(s.width+ε)):=by
      apply hh.trans
      convert mul_le_mul_of_nonneg_left hl hfront using 1 ; ring
    _=_:=by rw [Real.norm_eq_abs];ring

end SevenEighths.CenteredMomentEnergyZeroGrowthConclusion

end

end OAI
