import OAI.NumberTheory.DirichletL.Descent.SecondCanonicalSplit
import OAI.NumberTheory.DirichletL.Descent.SecondSupportedEnergy

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def SecondPairCanonicalAt {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ) : Prop :=
∀ (F : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
      (A₁ A₂ : Finset ι), A₁ ⊆ x.cube.support∪x.firstCommon → A₂ ⊆ x.cube.support∪x.firstCommon →
      ∀ (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
      (ω₁ ω₂ : ℝ → ℂ) (G₀ E₀ V₀ K₀ X₀ : ℝ) (t : JointLogSeparation.Frequency × (Fin 6 → ℝ)),
      let h := profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2
      let data := actualMarkedSecondProfileData p x Ψ m z A₁ A₂
      secondSeparatedPair p hp hcop hg F data slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ t =
      secondOuterPhase h (secondRelativeLog (secondActualNorms p data ∅ ∅) G₀ E₀ V₀ K₀ X₀) *
        ∑ J₁ ∈ slots₁.powerset, ∑ J₂ ∈ slots₂.powerset,
          (star (primeMark J₁ lists₁ a₁ ((A₁∪x.second.sourceCommon)∪x.second.overlap)) *
            primeMark J₂ lists₂ a₂ ((A₂∪x.second.sourceCommon)∪x.second.overlap)) *
          star (secondCanonicalPolynomial p hp hcop hg F (fun _ => secondRayMinus Ψ z)
            (actualSecondPuncture m) (slots₁\J₁) lists₁ a₁ (fun _ => childLogTest ω₁ (-h 4)) X₀
            (actualSecondChild p u v x)) *
          secondCanonicalPolynomial p hp hcop hg F (fun _ => secondRayPlus Ψ z)
            (actualSecondPuncture m) (slots₂\J₂) lists₂ a₂ (fun _ => childLogTest ω₂ (h 5)) X₀
            (actualSecondChild p u v {x with second := {x.second with frequency := -x.second.frequency}})

theorem exists_second_uniform_sectors
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∃ sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ,
      ∀ x ∈ source, SecondPairCanonicalAt (σ:=σ) p hp hcop hg x (sector x).1 (sector x).2 := by
  have he (x : {x // x ∈ source}) :=
    actual_second_separated_pair_canonical p hp hcop hg hpr (σ:=σ) x.val
      (hs.common_disjoint x.val x.property) (hs.first_divisor x.val x.property)
      (hs.second_divisor x.val x.property)
  choose u v hu using he
  let sector := fun x => if hx : x ∈ source then (u ⟨x,hx⟩,v ⟨x,hx⟩) else (1,1)
  refine ⟨sector,?_⟩
  intro x hx
  simpa only [sector,dite_eq_left hx,SecondPairCanonicalAt] using hu ⟨x,hx⟩

def secondSourceSector {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (sector : MarkedSecondSource ι Jo Jn → Eisˣ × Eisˣ) (uv : Eisˣ × Eisˣ) :
    Finset (MarkedSecondSource ι Jo Jn) := source.filter (fun x => sector x = uv)

omit [DecidableEq ι] in
theorem secondSourceSector_partition {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn))
    (sector : MarkedSecondSource ι Jo Jn → Eisˣ × Eisˣ) (H : MarkedSecondSource ι Jo Jn → ℂ) :
    ∑ x ∈ source,H x = ∑ uv : Eisˣ × Eisˣ,∑ x ∈ secondSourceSector source sector uv,H x :=
  (Finset.sum_fiberwise source sector H).symm

theorem second_unit_sector_card : Fintype.card (Eisˣ × Eisˣ) = 36 := by
  have hc : Fintype.card Eisˣ = 6 := by
    simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six
  rw [Fintype.card_prod,hc]

end
end SevenEighths.InverseMoment

end OAI
