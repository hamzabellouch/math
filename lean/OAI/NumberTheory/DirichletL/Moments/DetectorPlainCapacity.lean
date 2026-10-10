import OAI.NumberTheory.DirichletL.Moments.RelativeCapacityRemoval
import OAI.NumberTheory.DirichletL.Moments.DetectorPlainSlotProfile

namespace OAI

noncomputable section

open scoped Classical BigOperators ContDiff ComplexConjugate
namespace SevenEighths.CenteredMomentDetectorPlainCapacity
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSlotProfile
local notation "O"=>HeckeFamily.O
variable {Δ:ℝ}{D:Parameters.HighData Δ}

theorem physical_annular_all (S:ProbeFinalAssembly.SourceData D)(η₀:Character)
    (P:ℝ)(hP:0<P)(ζ:ℂ)(I:Ideal O):
    physicalSlotCoefficient η₀ S.W P ζ I=
      idealCoeff η₀.inverse I*annularWeight (fun x=>conj (S.W x)) P (1-ζ.re) (-ζ.im) I := by
  by_cases hI:I=0
  · subst I
    have hw:S.W 0=0:=by
      by_contra hh
      have hs:=S.complex_support hh
      norm_num at hs
    simp [physicalSlotCoefficient,annularWeight,hw]
  · exact physicalSlotCoefficient_annular η₀ S.W P ζ I hI hP

theorem selected_physical_annular {ι:Type*}
    (S:ProbeFinalAssembly.SourceData D)(J:Finset ι)(η η₀:Character)(m A z:O)
    (W₁ W₂:ℝ→ℂ)(pools:ι→Finset (Ideal O))(P:ι→ℝ)(hP:∀i,0<P i)
    (ζ:ι→ℂ)(t X₁ X₂:ℝ):
    selectedProduct J η m A z W₁ W₂ pools
      (fun i=>physicalSlotCoefficient η₀ S.W (P i) (ζ i)) P t X₁ X₂=
    selectedProduct J η m A z W₁ W₂ pools
      (fun i I=>idealCoeff η₀.inverse I*
        annularWeight (fun x=>conj (S.W x)) (P i) (1-(ζ i).re) (-(ζ i).im) I) P t X₁ X₂ := by
  congr 1
  funext i I
  exact physical_annular_all S η₀ (P i) (hP i) (ζ i) I

variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
include hH

theorem physical_capacity_removal {ι:Type*}[Fintype ι][DecidableEq ι]
    (S:ProbeFinalAssembly.SourceData D)(Lmod Lslot ε κ:ℝ)
    (hLm:0≤Lmod)(hLs:0≤Lslot)(hε:0<ε)
    (hbeta:(51/100:ℝ)≤beta)(hκ:2*beta-1≤κ):
    ∃degree:ℕ,∃C:ℝ,0<C ∧ ∀η₀:Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀(J:Finset ι)(w:ι→ℝ)(n₁ n₂ width mesh:ℝ),0≤mesh →
      (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    ∃R:Finset ι,R⊆J ∧ (R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤width) ∧
      κ*(∑i∈R,w i)≤CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh ∧
    ∀Z:ℝ,Z₀≤Z → ∀η:Character,∀z:O,z≠0 → ∀F:NaturalRow η z,
      (F.character.modulus.absNorm:ℝ)≤Z^Lmod →
    ∀Q:Ideal O,Q≤M → Q≤η₀.modulus → ¬FixedInducingRow η Q fixedBadMask 1 z →
    ∀(ζ:ι→ℂ)(t V:ℝ),(∀i,(ζ i).re∈Set.Icc (0:ℝ) 1) → 0≤V → (∀i,|(ζ i).im|≤V) →
    ∀(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ),
      let P:=fun i=>Z^(w i)
      let pools:=fun i=>primePool M H 2 (P i)
      let coeff:=fun i=>physicalSlotCoefficient η₀ S.W (P i) (ζ i)
      ‖selectedProduct J η fixedBadMask 1 z W₁ W₂ pools coeff P t X₁ X₂‖^2≤
        C*(1+|t|+V)^degree*Z^(ε+CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh)*
          ‖selectedProduct (J\R) η fixedBadMask 1 z W₁ W₂ pools coeff P t X₁ X₂‖^2 := by
  obtain ⟨degree,C,hC,hbound⟩:=CenteredMomentRelativeCapacityRemoval.actual_relative_capacity_removal
    M H hH (ι:=ι) (fun _ x=>conj (S.W x)) (fun _=>1) (fun _=>2) (fun _=>by norm_num)
    (fun _=>conjugate_source_support S) (fun _=>Complex.conjCLE.contDiff.comp (S.W.smooth ⊤))
    Lmod Lslot ε 0 1 κ hLm hLs hε hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro η₀
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound (fun _=>η₀.inverse)
  refine ⟨Z₀,hZ₀,?_⟩
  intro J w n₁ n₂ width mesh hmesh hw hwm hwcap
  obtain ⟨R,hR,hremaining,hcost,henergy⟩:=hbound J w n₁ n₂ width mesh hmesh hw hwm hwcap
  refine ⟨R,hR,hremaining,hcost,?_⟩
  intro Z hZ η z hz F hcond Q hQM hQη hex ζ t V hζ hV him W₁ W₂ X₁ X₂
  dsimp only
  have hZp:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  have hP (i:ι):0<Z^(w i):=Real.rpow_pos_of_pos hZp _
  rw [selected_physical_annular S J η η₀ fixedBadMask 1 z W₁ W₂ _ _ hP ζ t X₁ X₂,
    selected_physical_annular S (J\R) η η₀ fixedBadMask 1 z W₁ W₂ _ _ hP ζ t X₁ X₂]
  exact henergy Z hZ η z hz F hcond Q hQM (fun _=>hQη) hex
    (fun i=>1-(ζ i).re) (fun i=>-(ζ i).im) t V
    (fun i=>by linarith [(hζ i).2]) (fun i=>by linarith [(hζ i).1]) hV
    (fun i=>by simpa only [abs_neg] using him i) W₁ W₂ X₁ X₂

end SevenEighths.CenteredMomentDetectorPlainCapacity

end

end OAI
