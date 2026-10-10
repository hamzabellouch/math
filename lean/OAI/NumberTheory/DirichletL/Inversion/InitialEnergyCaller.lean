import OAI.NumberTheory.DirichletL.Inversion.InitialQuotientGeometry
import OAI.NumberTheory.DirichletL.Inversion.InitialClippedColumns

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
open SevenEighths.InverseInitialQuotientGeometry SevenEighths.InverseInitialClippedColumns
namespace SevenEighths.InverseInitialEnergyCaller
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in

theorem actual_sector_energy {J : ℕ}
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (S : Finset (Source (ι:=ι) J)) (u : Eisˣ)
    (lists : Fin J → Finset ι) (a : Fin J → ι → ℂ)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common)
    (hterm : ∀ x ∈ S, assignedTerm lists a (x.common ∪ x.overlap) x.assigned ≠ 0)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ S,
      (initialChild (toTuple p (sectorSource u x))).2.1 ∈ labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2 ∈ rows)
    (F : InitialChild → ℂ) :
    (∑ x ∈ S, ‖F (initialChild (toTuple p (sectorSource u x)))‖^2) ≤
      ∑ t ∈ quotientSet p S, ((idealDivisors t).card : ℝ)^J *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ)^(J+1) *
          ∑ k ∈ rows, ‖F (t,f,k)‖^2 := by
  let T := S.image (fun x => toTuple p (sectorSource u x))
  have hvalid : ∀ y ∈ T, InitialSourceValid y := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact actual_source_valid p hp hpr (sectorSource u x) (hdiv x hx) lists a (hterm x hx)
  have hc : ∀ y ∈ T, (initialChild y).2.1 ∈ labels ∧ (initialChild y).2.2 ∈ rows := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact hchild x hx
  have he := initial_energy_projection T hvalid labels rows hlabels hc
    (fun _ => 1) (fun _ _ => le_rfl) F
  simp only [one_mul] at he
  rw [show initialQuotientSet T = quotientSet p S from
    quotientSet_eq_initial p hp S u hdiv] at he
  have hs : (∑ y ∈ T, ‖F (initialChild y)‖^2) =
      ∑ x ∈ S, ‖F (initialChild (toTuple p (sectorSource u x)))‖^2 := by
    exact Finset.sum_image (fun x _ y _ he => sectorSource_injective u (toTuple_injective p hinj he))
  rw [hs] at he
  exact he

include hp in

theorem actual_sector_signed_pair {J : ℕ}
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (S : Finset (Source (ι:=ι) J)) (u : Eisˣ)
    (lists : Fin J → Finset ι) (a : Fin J → ι → ℂ)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common)
    (hterm : ∀ x ∈ S, assignedTerm lists a (x.common ∪ x.overlap) x.assigned ≠ 0)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ S,
      (initialChild (toTuple p (sectorSource u x))).2.1 ∈ labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2 ∈ rows)
    (c : Source (ι:=ι) J → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hc : ∀ x ∈ S, ‖c x‖ ≤ A) (F G : InitialChild → ℂ) :
    ‖∑ x ∈ S, c x * star (F (initialChild (toTuple p (sectorSource u x)))) *
        G (initialChild (toTuple p (sectorSource u x)))‖ ≤
      A * (Real.sqrt (∑ t ∈ quotientSet p S, ((idealDivisors t).card : ℝ)^J *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ)^(J+1) * ∑ k ∈ rows, ‖F (t,f,k)‖^2) *
        Real.sqrt (∑ t ∈ quotientSet p S, ((idealDivisors t).card : ℝ)^J *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ)^(J+1) * ∑ k ∈ rows, ‖G (t,f,k)‖^2)) := by
  let child := fun x : Source (ι:=ι) J => initialChild (toTuple p (sectorSource u x))
  have hF := actual_sector_energy p hp hinj hpr S u lists a hdiv hterm labels rows hlabels hchild F
  have hG := actual_sector_energy p hp hinj hpr S u lists a hdiv hterm labels rows hlabels hchild G
  calc
    _ ≤ ∑ x ∈ S, ‖c x * star (F (child x)) * G (child x)‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ S, A * (‖F (child x)‖ * ‖G (child x)‖) := by
      apply Finset.sum_le_sum
      intro x hx
      simp only [norm_mul, norm_star]
      nlinarith [mul_le_mul_of_nonneg_right (hc x hx)
        (mul_nonneg (norm_nonneg (F (child x))) (norm_nonneg (G (child x))))]
    _ = A * ∑ x ∈ S, ‖F (child x)‖ * ‖G (child x)‖ := by rw [Finset.mul_sum]
    _ ≤ A * (Real.sqrt (∑ x ∈ S, ‖F (child x)‖^2) *
        Real.sqrt (∑ x ∈ S, ‖G (child x)‖^2)) :=
      mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt S _ _) hA
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul (Real.sqrt_le_sqrt hF) (Real.sqrt_le_sqrt hG)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hA

end SevenEighths.InverseInitialEnergyCaller

end

end OAI
