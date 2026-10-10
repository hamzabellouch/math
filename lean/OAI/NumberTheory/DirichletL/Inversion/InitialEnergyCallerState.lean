import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerWindowGeometry
import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerClipping

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerState
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialQuotientGeometry
local notation "Eis"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda
variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

omit [DecidableEq ι] in
theorem windowSource_subset_retained
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(Z D B v θ H:ℝ) :
    windowSource p S ψ Z D B v θ H ⊆ retained p S (fun _=>1) (ψ 0) (ψ 1) Z B θ := by
  intro x hx
  refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,?_⟩
  have hn := (Finset.mem_filter.mp hx).2
  have hh := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1
  change ψ 0 (((sourceIdeal p x.common).absNorm:ℝ)/Z^B)*
    ψ 1 (((sourceIdeal p x.divisor).absNorm:ℝ)/Z^θ)≠0 at hh
  simpa only [sourceWeight,one_mul] using hh

theorem window_quotient_subset_retained
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(Z D B v θ H:ℝ) :
    quotientSet p (windowSource p S ψ Z D B v θ H) ⊆
      quotientSet p (retained p S (fun _=>1) (ψ 0) (ψ 1) Z B θ) :=
  Finset.image_subset_image (windowSource_subset_retained p S ψ Z D B v θ H)

theorem initial_F_exact (r z G B θ v:ℝ) :
    max 0 (r+z-2*G-B-v)+(θ+v)=
      initialF r z G (B-θ) (max 0 (r+z-2*G-B-v)-(r+z-2*G-B-v)) := by
  unfold initialF
  ring

variable (hp:∀i,p i≠0)
include hp

theorem actual_window_initial_margins (S : Finset (Source (ι:=ι) 0))
    (ψ : Fin 4 → ℝ → ℂ) (D v H : ℝ)
    (aC bC ad bd Z B θ η : ℝ) (hZ : 1 < Z)
    (hC : Function.support (ψ 0) ⊆ Set.Icc aC bC)
    (hd : Function.support (ψ 1) ⊆ Set.Icc ad bd)
    (hCup : bC ≤ Z^η) (hdlo : Z^(-η) ≤ ad)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common) (hpr : ∀ i, λ₀^2 ∣ p i-1)
    {σ : Type*} [DecidableEq σ] (all assigned : Finset σ) (ha : assigned ⊆ all)
    (q : σ → Eis) (z a b : σ → ℝ) (W : σ → ℝ → ℂ)
    (hz : ∀ i ∈ all, 0 ≤ z i) (hq : ∀ i ∈ assigned, q i ≠ 0)
    (hW : ∀ i ∈ assigned, Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hret : ∀ i ∈ assigned, W i ((Ideal.absNorm (Ideal.span {q i}) : ℝ)/Z^(z i)) ≠ 0)
    (hthreshold : (∏ i ∈ assigned, b i) ≤ Z^η)
    {t : Ideal Eis} (ht : t ∈ quotientSet p (windowSource p S ψ Z D B v θ H))
    (m r δ τ c₁ c₂ : ℝ)
    (h₁ : r+2*assignedCenter all z ≤ m-c₁)
    (h₂ : 2*r+8*assignedCenter all z ≤ 3*m-c₂) :
    c₁+δ-9*η-τ ≤
      initialF r (assignedCenter all z) (assignedCenter assigned z) (B-θ) δ -
      initialM m r (assignedCenter all z) (assignedCenter assigned z) (B-θ) η τ -
      punctureLength Z t (assignedElement assigned q) - assignedCenter (all\assigned) z ∧
    c₂+4*δ-22*η-3*τ ≤
      4*initialF r (assignedCenter all z) (assignedCenter assigned z) (B-θ) δ -
      3*initialM m r (assignedCenter all z) (assignedCenter assigned z) (B-θ) η τ -
      6*assignedCenter (all\assigned) z := by
  exact retained_initial_margins p hp S (fun _=>1) (ψ 0) (ψ 1)
    aC bC ad bd Z B θ η hZ hC hd hCup hdlo hdiv hpr all assigned ha q z a b W
    hz hq hW hret hthreshold (window_quotient_subset_retained p S ψ Z D B v θ H ht)
    m r δ τ c₁ c₂ h₁ h₂

theorem actual_window_canonical_margins (S : Finset (Source (ι:=ι) 0))
    (ψ : Fin 4 → ℝ → ℂ) (D v H : ℝ)
    (aC bC ad bd Z B θ η : ℝ) (hZ : 1 < Z)
    (hC : Function.support (ψ 0) ⊆ Set.Icc aC bC)
    (hd : Function.support (ψ 1) ⊆ Set.Icc ad bd)
    (hCup : bC ≤ Z^η) (hdlo : Z^(-η) ≤ ad)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common) (hpr : ∀ i, λ₀^2 ∣ p i-1)
    {σ : Type*} [DecidableEq σ] (all assigned : Finset σ) (ha : assigned ⊆ all)
    (q : σ → Eis) (z a b : σ → ℝ) (W : σ → ℝ → ℂ)
    (hz : ∀ i ∈ all, 0 ≤ z i) (hq : ∀ i ∈ assigned, q i ≠ 0)
    (hW : ∀ i ∈ assigned, Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hret : ∀ i ∈ assigned, W i ((Ideal.absNorm (Ideal.span {q i}) : ℝ)/Z^(z i)) ≠ 0)
    (hthreshold : (∏ i ∈ assigned, b i) ≤ Z^η)
    {t : Ideal Eis} (ht : t ∈ quotientSet p (windowSource p S ψ Z D B v θ H))
    (m r τ c₁ c₂ : ℝ)
    (h₁ : r+2*assignedCenter all z ≤ m-c₁)
    (h₂ : 2*r+8*assignedCenter all z ≤ 3*m-c₂)
    (hc:0≤min c₁ c₂)(hη:η≤min c₁ c₂/100)(hτ:τ≤min c₁ c₂/100) :
    CanonicalMargins
      (max 0 (r+assignedCenter all z-2*assignedCenter assigned z-B-v)+(θ+v))
      (initialM m r (assignedCenter all z) (assignedCenter assigned z) (B-θ) η τ)
      (punctureLength Z t (assignedElement assigned q))
      (assignedCenter (all\assigned) z) (3*min c₁ c₂/4) := by
  let δ:=max 0 (r+assignedCenter all z-2*assignedCenter assigned z-B-v)-
    (r+assignedCenter all z-2*assignedCenter assigned z-B-v)
  have hδ:0≤δ:=sub_nonneg.mpr (le_max_right _ _)
  obtain ⟨h1,h2⟩ := actual_window_initial_margins p hp S ψ D v H
    aC bC ad bd Z B θ η hZ hC hd hCup hdlo hdiv hpr all assigned ha q z a b W
    hz hq hW hret hthreshold ht m r δ τ c₁ c₂ h₁ h₂
  rw [initial_F_exact]
  change CanonicalMargins (initialF r (assignedCenter all z) (assignedCenter assigned z) (B-θ) δ)
    _ _ _ _
  have hc1:=min_le_left c₁ c₂
  have hc2:=min_le_right c₁ c₂
  constructor <;> linarith

end SevenEighths.InverseInitialEnergyCallerState

end

end OAI
