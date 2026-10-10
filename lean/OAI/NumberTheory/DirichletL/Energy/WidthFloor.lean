import OAI.NumberTheory.DirichletL.Energy.WidthSchedule
import OAI.NumberTheory.DirichletL.Energy.Bands

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyWidthFloor
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyWidthSchedule CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open QuadraticInitialBound
local notation "O"=>HeckeFamily.O

private lemma control_mono {a b:ℝ}(p:Profiles a b){S T:Finset (ℕ×ℕ)}(h:S⊆T):
    p.control S≤p.control T:=by
  unfold Profiles.control
  exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono h) (p.profile 0))
    (Seminorm.le_def.mp (Finset.sup_mono h) (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_joint_floor (Mcap B κ ε:ℝ)(hMcap:0≤Mcap)(hB:0≤B)
    (hκ0:0≤κ)(hε:0<ε)
    (W:ℝ→ℂ)(aslot bslot:ℝ)(haslot:0<aslot)
    (hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (a b bΦ Bmask L lo hi:ℝ)(ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hmask:0≤Bmask)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∃Czero Cpositive:ℝ,0<Czero ∧ 0<Cpositive ∧
      ∀η₀:Character,∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Q:Ideal O,Q≤M→
        ZeroAt (internalQ Q η₀) a b bΦ Bmask L (width Mcap B ε 0)
          (loss Mcap B ε 0) Z degree S Czero ∧
        PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L (mesh Mcap B κ ε) lo hi
          (width Mcap B ε 0) (loss Mcap B ε 0) κ Z η₀ Q degree S Cpositive:=by
  have hs:=bounds Mcap B κ ε hMcap hB hκ0 hε
  have hr:=hs.2.2.2.1
  have hm:=hs.2.2.2.2.1
  obtain ⟨Jzero,Szero,Czero,hCzero,hzero⟩:=exists_zero_floor
    a b bΦ Bmask (reserve Mcap B ε) ha hb hbΦ hmask hr
  obtain ⟨Jpositive,Spositive,Cpositive,hCpositive,hpositive⟩:=exists_positive_bottom (α:=α)
    M H hH W aslot bslot haslot hWs hW a b bΦ Bmask L (mesh Mcap B κ ε) lo hi
      (reserve Mcap B ε) κ ha hb hbΦ hmask hr hm.le hbeta hκ
  refine ⟨Jzero+Jpositive,Szero∪Spositive,Czero,Cpositive,hCzero,hCpositive,?_⟩
  intro η₀
  filter_upwards [hpositive η₀] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Q hQM
  rw [width_zero,loss_zero]
  constructor
  · intro s hQ hwidth p t X₁ X₂ hX₁ hX₂ _ _
    have hh:=hzero (internalQ Q η₀) Z hZ.1.le s hQ hwidth p t X₁ X₂ hX₁ hX₂
    have hp:=control_mono p (Finset.subset_union_left (s₁:=Szero) (s₂:=Spositive))
    have hpn:=p.control_nonneg Szero
    have hpU:=p.control_nonneg (Szero∪Spositive)
    have hd:=diagonalControl_nonneg s.radial.profile
    have ht:(1+‖t‖)^Jzero≤(1+‖t‖)^(Jzero+Jpositive):=
      pow_le_pow_right₀ (by linarith [norm_nonneg t]) (Nat.le_add_right _ _)
    apply hh.trans
    gcongr
    exact Real.rpow_nonneg (zero_le_one.trans hZ.1.le) _
  · intro T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hwidth
      p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap
    have hh:=hZ.2 Q hQM T θ w σ v t height hw hwL hσlo hσhi hheight hv
      s hQ hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap
    have hp:=control_mono p (Finset.subset_union_right (s₁:=Szero) (s₂:=Spositive))
    have hpn:=p.control_nonneg Spositive
    have hpU:=p.control_nonneg (Szero∪Spositive)
    have hd:=diagonalControl_nonneg s.radial.profile
    have ht:(1+|t|+height)^Jpositive≤(1+|t|+height)^(Jzero+Jpositive):=
      pow_le_pow_right₀ (by linarith [abs_nonneg t]) (Nat.le_add_left _ _)
    apply hh.trans
    gcongr
    exact Real.rpow_nonneg (zero_le_one.trans hZ.1.le) _

end SevenEighths.CenteredMomentEnergyWidthFloor

end

end OAI
