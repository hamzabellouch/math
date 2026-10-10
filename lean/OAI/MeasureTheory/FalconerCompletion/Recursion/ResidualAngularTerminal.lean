import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Angular.AngularHTrivialBound
import OAI.MeasureTheory.FalconerCompletion.Graphs.ResidualPairSourceSymbolEqScalarPair

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer _root_.OAI.GraphLiteralSupport.Attempt4FullFar
open scoped ContDiff ENNReal Topology
variable {n : ℕ}

theorem actual_residual_angular_terminal
    {Ψ : ℝ → ℝ} (hΨ : Integrable Ψ)
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (B total : ℕ) (hW : ∀ L∈W, L.length≤B)
    {sig : ℝ} (hsig : 0<sig) (Cq : ℝ) (hCq : 0≤Cq) :
    ∃ H : ℝ, 0≤H ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ],
      ∀ (A : ℕ → ℝ) (q a₀ t₀ a : ℕ), 0<q → 0<N → a≤N →
      ∀ (words₁ words₂ : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (m : ℝ → ℝ) (C : ℝ) (J i : ℕ)
        (f g : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
        (Q P : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
        (X Y : CellPath (n+1)) (v lam sρ sκ : ℝ) (Bρ Bκ : ℕ),
      RegularizedProfileData ρ N Bρ sρ lam m → RegularizedProfileData κ N Bκ sκ lam m →
      X.length=a → Y.length=a → v-a≤100*(q:ℝ) →
      Measurable f → Measurable g → (∀ x, ‖f x‖≤1) → (∀ x, ‖g x‖≤1) →
      (∀ b∈policyDescriptorList A N q a₀ t₀, words₁ b∈W) →
      (∀ b∈policyDescriptorList A N q a₀ t₀, words₂ b∈W) →
      (∑ b∈policyDescriptorList A N q a₀ t₀, (words₁ b).length≤total) →
      (∑ b∈policyDescriptorList A N q a₀ t₀, (words₂ b).length≤total) →
      (∀ w, ‖w‖=1 → ‖Q.1 w‖≤Cq) → (∀ w, ‖w‖=1 → ‖P.1 w‖≤Cq) →
      let b := fun x w => (actualResidualSourceSymbol A N q a₀ t₀ a words₁ ρ m sig C J i f Q x).1 w
      let c := fun x w => (actualResidualSourceSymbol A N q a₀ t₀ a words₂ κ m sig C J i g P x).1 w
      Attempt4Near.sourceAngularHND (n+1) (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))) a v Ψ
        (fun p => sourceAngularTransformND ρ (treeCell X) (((2:ℝ)^N)^(-m a)) b p.1 p.2)
        (fun p => sourceAngularTransformND κ (treeCell Y) (((2:ℝ)^N)^(-m a)) c p.1 p.2) ≤
      H*((2:ℝ)^N)^(100*(n+1:ℝ)*q/N+4*(n+2:ℝ)*lam) := by
  obtain ⟨E,hE,he⟩ := actual_residual_transform_uniform_package W B total hW hsig Cq hCq
  let μ := canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))
  let I : ℝ := ∫ r, |Ψ r|
  let H := I*E^4*(μ.real univ)^2
  have hI : 0≤I := integral_nonneg (fun _ => abs_nonneg _)
  refine ⟨H,by dsimp [H]; positivity,?_⟩
  filter_upwards [he] with N he
  intro ρ κ hρ hκ A q a₀ t₀ a hq hN ha words₁ words₂ m C J i f g Q P X Y v lam sρ sκ Bρ Bκ
    hdρ hdκ hX hY hv hfm hgm hfb hgb hw₁ hw₂ ht₁ ht₂ hQ hP
  let R : ℝ := (2:ℝ)^N
  let S : ℝ := R^((n+2:ℝ)*lam)
  have hS : 0≤S := by dsimp [S]; positivity
  have hu := (he ρ A q a₀ t₀ a hq words₁ m C J i f Q hfm hfb hw₁ ht₁ hQ).2.2 (treeCell X) (R^(-m a))
  have hw := (he κ A q a₀ t₀ a hq words₂ m C J i g P hgm hgb hw₂ ht₂ hP).2.2 (treeCell Y) (R^(-m a))
  have hmass₁ : |(R^(-m a))⁻¹| *(ρ (treeCell X)).toReal*E ≤ S*E := by
    rw [abs_of_pos (inv_pos.mpr (Real.rpow_pos_of_pos (by dsimp [R]; positivity) _))]
    apply mul_le_mul_of_nonneg_right _ hE
    rw [mul_comm,← div_eq_mul_inv]
    simpa only [R,S,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using hdρ.normalized_cell_mass_le ha hX
  have hmass₂ : |(R^(-m a))⁻¹| *(κ (treeCell Y)).toReal*E ≤ S*E := by
    rw [abs_of_pos (inv_pos.mpr (Real.rpow_pos_of_pos (by dsimp [R]; positivity) _))]
    apply mul_le_mul_of_nonneg_right _ hE
    rw [mul_comm,← div_eq_mul_inv]
    simpa only [R,S,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using hdκ.normalized_cell_mass_le ha hY
  have hb₁ r : ∀ᵐ w ∂μ, ‖sourceAngularTransformND ρ (treeCell X) (R^(-m a))
      (fun x w => (actualResidualSourceSymbol A N q a₀ t₀ a words₁ ρ m sig C J i f Q x).1 w) r w‖≤S*E :=
    (hu.2 r).mono (fun _ hw => hw.trans hmass₁)
  have hb₂ r : ∀ᵐ w ∂μ, ‖sourceAngularTransformND κ (treeCell Y) (R^(-m a))
      (fun x w => (actualResidualSourceSymbol A N q a₀ t₀ a words₂ κ m sig C J i g P x).1 w) r w‖≤S*E :=
    (hw.2 r).mono (fun _ hw => hw.trans hmass₂)
  have hh := Attempt4Near.sourceAngularHND_trivial_bound (n+1) μ a v hΨ hu.1 hw.1 hb₁ hb₂
  have hS4 : S^4=R^(4*(n+2:ℝ)*lam) := by
    rw [← Real.rpow_mul_natCast (by dsimp [R]; positivity : 0≤R)]
    congr 1
    norm_num
    ring
  have hcoeff : (2:ℝ)^((↑(n+1):ℝ)*(v-a))*I*((S*E)^2*μ.real univ)*((S*E)^2*μ.real univ) =
      H*((2:ℝ)^((n+1:ℝ)*(v-a))*R^(4*(n+2:ℝ)*lam)) := by
    rw [← hS4]
    dsimp [H]
    push_cast
    ring
  change _ ≤ _ at hh
  rw [hcoeff] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by dsimp [H]; positivity)
  have hexp : (2:ℝ)^((n+1:ℝ)*(v-a)) ≤ R^(100*(n+1:ℝ)*q/N) := by
    dsimp [R]
    rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    have hn : (N:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hN)
    have heq : (N:ℝ)*(100*(n+1:ℝ)*q/N)=100*(n+1:ℝ)*q := by field_simp
    rw [heq]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hv (show 0≤(n+1:ℝ) by positivity)]
  rw [Real.rpow_add (by dsimp [R]; positivity : 0<R)]
  exact mul_le_mul_of_nonneg_right hexp (by positivity)

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
