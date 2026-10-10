import Mathlib
import OAI.Geometry.PrescribedPotential.FamilyBernsteinBootstrap
import OAI.Geometry.PrescribedPotential.JetEnergyEstimates
import OAI.Geometry.PrescribedPotential.UniformJetControls

namespace OAI

/-! Residual Family Bootstrap. -/

section

noncomputable section
open Set Filter Topology Finset Module
open scoped ContDiff
namespace HigherJet
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {ι α : Type*} [Fintype ι]

lemma residual_family_low_energy {U : Set E} (hU : IsOpen U)
    (e : OrthonormalBasis ι ℝ E) (u : α → E → F) (τ : α → E → E ≃L[ℝ] E)
    (hu : ∀ a, ContDiffOn ℝ ∞ (u a) U)
    (hframes : ∀ K, IsCompact K → K ⊆ U → ∃ B : ℝ, 0 ≤ B ∧ ∀ a x, x ∈ K →
      ‖(τ a x).toContinuousLinearMap‖ ≤ B ∧ ‖(τ a x).symm.toContinuousLinearMap‖ ≤ B)
    (hfirst : ∀ K, IsCompact K → K ⊆ U → ∃ R : ℝ, 0 ≤ R ∧ ∀ a x, x ∈ K → ‖iteratedFDeriv ℝ 1 (u a) x‖ ≤ R)
    (hlow : ∀ K, IsCompact K → K ⊆ U → ∃ R : ℝ, 0 ≤ R ∧ ∀ a x, x ∈ K →
      (∀ σ, ‖frameLaplace (fun i => τ a x (e i)) (jetFamily e 1 (u a) σ) x‖ ≤ R*(1+‖iteratedFDeriv ℝ 2 (u a) x‖)) ∧
      (∀ σ, ‖frameLaplace (fun i => τ a x (e i)) (jetFamily e 2 (u a) σ) x‖ ≤ R*(1+‖iteratedFDeriv ℝ 2 (u a) x‖^2+‖iteratedFDeriv ℝ 3 (u a) x‖)))
 :
    ∀ K, IsCompact K → K ⊆ U → ∃ R : ℝ, 0 ≤ R ∧ ∀ a x, x ∈ K →
      familyDissipation (fun i => τ a x (e i)) (jetFamily e 1 (u a)) x-R ≤ frameLaplace (fun i => τ a x (e i)) (jetEnergy e 1 (u a)) x ∧
      familyDissipation (fun i => τ a x (e i)) (jetFamily e 2 (u a)) x-R*(1+jetEnergy e 2 (u a) x*Real.sqrt (jetEnergy e 2 (u a) x)) ≤ frameLaplace (fun i => τ a x (e i)) (jetEnergy e 2 (u a)) x := by
  let S := fun m a x => jetEnergy e m (u a) x
  let D := fun m a x => familyDissipation (fun i => τ a x (e i)) (jetFamily e m (u a)) x
  have hf : ∀ K, IsCompact K → K ⊆ U → EnergyBound S 1 K := by
    intro K hK hKU
    obtain ⟨R,hR,hr⟩ := hfirst K hK hKU
    refine ⟨(Fintype.card (Fin 1 → ι) : ℝ)*R^2,by positivity,fun a x hx => ?_⟩
    exact (jetEnergy_le_norm hU (hu a) e 1 (hKU hx)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hr a x hx) 2) (by positivity))
  intro K hK hKU
  obtain ⟨B,hB,hτ⟩ := hframes K hK hKU
  obtain ⟨A1,hA1,hc1⟩ := uniform_jet_controls (F := F) e 1 hB
  obtain ⟨A2,hA2,hc2⟩ := uniform_jet_controls (F := F) e 2 hB
  obtain ⟨R0,hR0,hr0⟩ := hf K hK hKU
  obtain ⟨R,hR,hr⟩ := hlow K hK hKU
  let A := A1+A2+Real.sqrt R0
  have hAA : 1 ≤ A := by dsimp [A]; linarith [Real.sqrt_nonneg R0]
  have h1A : A1 ≤ A := by dsimp [A]; linarith [Real.sqrt_nonneg R0]
  have h2A : A2 ≤ A := by dsimp [A]; linarith [Real.sqrt_nonneg R0]
  let C1 := 2*(A+(Fintype.card (Fin 1 → ι)+1)*R*A)^2+(A+(Fintype.card (Fin 1 → ι)+1)*R*A)^4
  let C2 := 4*((Fintype.card (Fin 2 → ι)+1)*R*A^2)+2*((Fintype.card (Fin 2 → ι)+1)*R*A^2)^2
  have hC1 : 0 ≤ C1 := by dsimp [C1]; positivity
  have hC2 : 0 ≤ C2 := by dsimp [C2]; positivity
  refine ⟨C1+C2,add_nonneg hC1 hC2,fun a x hx => ?_⟩
  have hcx1 := hc1 U hU (u a) (hu a) x (hKU hx) (τ a x) (hτ a x hx).1 (hτ a x hx).2
  have hcx2 := hc2 U hU (u a) (hu a) x (hKU hx) (τ a x) (hτ a x hx).1 (hτ a x hx).2
  have hs : Real.sqrt (S 1 a x) ≤ A := (Real.sqrt_le_sqrt (hr0 a x hx)).trans (by dsimp [A]; linarith)
  have hh1 := energy_first_of_residual hU (hu a) e (hKU hx) (fun i => τ a x (e i)) hAA hR hs
    (hcx1.2.1.trans (mul_le_mul_of_nonneg_right h1A (Real.sqrt_nonneg _))) (hr a x hx).1
  have hh2 := energy_second_of_residual hU (hu a) e (hKU hx) (fun i => τ a x (e i)) hAA hR
    (hcx2.1.trans (mul_le_mul_of_nonneg_right h2A (Real.sqrt_nonneg _)))
    (hcx2.2.1.trans (mul_le_mul_of_nonneg_right h2A (Real.sqrt_nonneg _))) (hr a x hx).2
  change D 1 a x-C1 ≤ _ at hh1
  change D 2 a x-C2*(1+S 2 a x*Real.sqrt (S 2 a x)) ≤ _ at hh2
  constructor
  · exact (sub_le_sub_left (le_add_of_nonneg_right hC2) _).trans hh1
  · have hq : 0 ≤ 1+S 2 a x*Real.sqrt (S 2 a x) := by have := jetEnergy_nonneg e 2 (u a) x; positivity
    exact (sub_le_sub_left (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC1) hq) _).trans hh2

lemma residual_family_high_energy {U : Set E} (hU : IsOpen U)
    (e : OrthonormalBasis ι ℝ E) (u : α → E → F) (τ : α → E → E ≃L[ℝ] E)
    (hu : ∀ a, ContDiffOn ℝ ∞ (u a) U)
    (hframes : ∀ K, IsCompact K → K ⊆ U → ∃ B : ℝ, 0 ≤ B ∧ ∀ a x, x ∈ K →
      ‖(τ a x).toContinuousLinearMap‖ ≤ B ∧ ‖(τ a x).symm.toContinuousLinearMap‖ ≤ B)
    (_hfirst : ∀ K, IsCompact K → K ⊆ U → ∃ R : ℝ, 0 ≤ R ∧ ∀ a x, x ∈ K → ‖iteratedFDeriv ℝ 1 (u a) x‖ ≤ R)
    (_hlow : ∀ K, IsCompact K → K ⊆ U → ∃ R : ℝ, 0 ≤ R ∧ ∀ a x, x ∈ K →
      (∀ σ, ‖frameLaplace (fun i => τ a x (e i)) (jetFamily e 1 (u a) σ) x‖ ≤ R*(1+‖iteratedFDeriv ℝ 2 (u a) x‖)) ∧
      (∀ σ, ‖frameLaplace (fun i => τ a x (e i)) (jetFamily e 2 (u a) σ) x‖ ≤ R*(1+‖iteratedFDeriv ℝ 2 (u a) x‖^2+‖iteratedFDeriv ℝ 3 (u a) x‖)))
    (hhigh : ∀ m, 3 ≤ m → ∀ K, IsCompact K → K ⊆ U →
      (∀ j, 1 ≤ j → j < m → EnergyBound (fun j a x => jetEnergy e j (u a) x) j K) →
      ∃ R : ℝ, 0 ≤ R ∧ ∀ a x, x ∈ K → ∀ σ,
        ‖frameLaplace (fun i => τ a x (e i)) (jetFamily e m (u a) σ) x‖ ≤
          R*(1+‖iteratedFDeriv ℝ m (u a) x‖+‖iteratedFDeriv ℝ (m+1) (u a) x‖)) :
    ∀ m, 3 ≤ m → ∀ K, IsCompact K → K ⊆ U →
      (∀ j, 1 ≤ j → j < m → EnergyBound (fun j a x => jetEnergy e j (u a) x) j K) → ∃ R : ℝ, 0 ≤ R ∧ ∀ a x, x ∈ K →
        familyDissipation (fun i => τ a x (e i)) (jetFamily e m (u a)) x-R*(1+jetEnergy e m (u a) x) ≤ frameLaplace (fun i => τ a x (e i)) (jetEnergy e m (u a)) x := by
  intro m hm K hK hKU hlo
  obtain ⟨B,hB,hτ⟩ := hframes K hK hKU
  obtain ⟨A,hA,hc⟩ := uniform_jet_controls (F := F) e m hB
  obtain ⟨R,hR,hr⟩ := hhigh m hm K hK hKU hlo
  refine ⟨4*((Fintype.card (Fin m → ι)+1)*R*A)+((Fintype.card (Fin m → ι)+1)*R*A)^2,by positivity,fun a x hx => ?_⟩
  have hc' := hc U hU (u a) (hu a) x (hKU hx) (τ a x) (hτ a x hx).1 (hτ a x hx).2
  exact energy_high_of_residual hU (hu a) e m (hKU hx) (fun i => τ a x (e i)) hA hR hc'.1 hc'.2.1 (hr a x hx)

lemma residual_family_bootstrap {U : Set E} (hU : IsOpen U)
    (e : OrthonormalBasis ι ℝ E) (u : α → E → F) (τ : α → E → E ≃L[ℝ] E)
    (hu : ∀ a, ContDiffOn ℝ ∞ (u a) U)
    (hframes : ∀ K, IsCompact K → K ⊆ U → ∃ B : ℝ, 0 ≤ B ∧ ∀ a x, x ∈ K →
      ‖(τ a x).toContinuousLinearMap‖ ≤ B ∧ ‖(τ a x).symm.toContinuousLinearMap‖ ≤ B)
    (hfirst : ∀ K, IsCompact K → K ⊆ U → ∃ R : ℝ, 0 ≤ R ∧ ∀ a x, x ∈ K → ‖iteratedFDeriv ℝ 1 (u a) x‖ ≤ R)
    (hlow : ∀ K, IsCompact K → K ⊆ U → ∃ R : ℝ, 0 ≤ R ∧ ∀ a x, x ∈ K →
      (∀ σ, ‖frameLaplace (fun i => τ a x (e i)) (jetFamily e 1 (u a) σ) x‖ ≤ R*(1+‖iteratedFDeriv ℝ 2 (u a) x‖)) ∧
      (∀ σ, ‖frameLaplace (fun i => τ a x (e i)) (jetFamily e 2 (u a) σ) x‖ ≤ R*(1+‖iteratedFDeriv ℝ 2 (u a) x‖^2+‖iteratedFDeriv ℝ 3 (u a) x‖)))
    (hhigh : ∀ m, 3 ≤ m → ∀ K, IsCompact K → K ⊆ U →
      (∀ j, 1 ≤ j → j < m → EnergyBound (fun j a x => jetEnergy e j (u a) x) j K) →
      ∃ R : ℝ, 0 ≤ R ∧ ∀ a x, x ∈ K → ∀ σ,
        ‖frameLaplace (fun i => τ a x (e i)) (jetFamily e m (u a) σ) x‖ ≤
          R*(1+‖iteratedFDeriv ℝ m (u a) x‖+‖iteratedFDeriv ℝ (m+1) (u a) x‖)) :
    ∀ m, 1 ≤ m → ∀ K, IsCompact K → K ⊆ U →
      ∃ R : ℝ, 0 ≤ R ∧ ∀ a x, x ∈ K → ‖iteratedFDeriv ℝ m (u a) x‖ ≤ R := by
  let S := fun m a x => jetEnergy e m (u a) x
  let D := fun m a x => familyDissipation (fun i => τ a x (e i)) (jetFamily e m (u a)) x
  have hf : ∀ K, IsCompact K → K ⊆ U → EnergyBound S 1 K := by
    intro K hK hKU
    obtain ⟨R,hR,hr⟩ := hfirst K hK hKU
    refine ⟨(Fintype.card (Fin 1 → ι) : ℝ)*R^2,by positivity,fun a x hx => ?_⟩
    exact (jetEnergy_le_norm hU (hu a) e 1 (hKU hx)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hr a x hx) 2) (by positivity))
  have hlowE := residual_family_low_energy hU e u τ hu hframes hfirst hlow
  have hhighE := residual_family_high_energy hU e u τ hu hframes hfirst hlow hhigh
  have hb : ∀ m, 1 ≤ m → ∀ K, IsCompact K → K ⊆ U → EnergyBound S m K := by
    apply family_bernstein_bootstrap hU S D (fun a x i => τ a x (e i))
    · exact fun m a => jetEnergy_smoothOn hU (hu a) e m
    · exact fun m a x _ => ⟨jetEnergy_nonneg _ _ _ _,familyDissipation_nonneg _ _ _⟩
    · exact fun m a x hx => jetEnergy_gradient_bound hU (hu a) e m hx _
    · intro K hK hKU
      obtain ⟨B,hB,hτ⟩ := hframes K hK hKU
      refine ⟨B,hB,fun a x hx i => ?_⟩
      exact ((τ a x).toContinuousLinearMap.le_opNorm (e i)).trans (by simpa only [e.norm_eq_one,mul_one] using (hτ a x hx).1)
    · intro m _ K hK hKU
      obtain ⟨B,hB,hτ⟩ := hframes K hK hKU
      obtain ⟨A,hA,hc⟩ := uniform_jet_controls (F := F) e m hB
      exact ⟨A,hA,fun a x hx => (hc U hU (u a) (hu a) x (hKU hx) (τ a x) (hτ a x hx).1 (hτ a x hx).2).2.2⟩
    · exact hf
    · intro m hm K hK hKU hlo
      by_cases h1 : m=1
      · subst m
        obtain ⟨R,hR,hr⟩ := hlowE K hK hKU
        exact ⟨R,hR,fun a x hx => (hr a x hx).1⟩
      · by_cases h2 : m=2
        · subst m
          obtain ⟨R,hR,hr⟩ := hlowE K hK hKU
          obtain ⟨C,hC,hc⟩ := hlo 2 (by decide) le_rfl
          refine ⟨R*(1+C*Real.sqrt C),by positivity,fun a x hx => ?_⟩
          have ht := mul_le_mul_of_nonneg_left (add_le_add_left
            (mul_le_mul (hc a x hx) (Real.sqrt_le_sqrt (hc a x hx)) (Real.sqrt_nonneg _) hC) 1) hR
          linarith only [ht,(hr a x hx).2]
        · obtain ⟨R,hR,hr⟩ := hhighE m (by omega) K hK hKU (fun j hj hjm => hlo j hj (by omega))
          obtain ⟨C,hC,hc⟩ := hlo m hm le_rfl
          refine ⟨R*(1+C),by positivity,fun a x hx => ?_⟩
          have ht := mul_le_mul_of_nonneg_left (add_le_add_left (hc a x hx) 1) hR
          linarith only [ht,hr a x hx]
    · intro K hK hKU
      obtain ⟨R,hR,hr⟩ := hlowE K hK hKU
      exact ⟨R,hR,fun a x hx => (by have hd := familyDissipation_nonneg (fun i => τ a x (e i)) (jetFamily e 2 (u a)) x; linarith only [hd,(hr a x hx).2])⟩
    · exact hhighE
  intro m hm K hK hKU
  obtain ⟨R,hR,hr⟩ := hb m hm K hK hKU
  obtain ⟨C,hC,hc⟩ := norm_iteratedFDeriv_le_jetEnergy (F := F) e.toBasis m
  exact ⟨C*Real.sqrt R,by positivity,fun a x hx => (hc U hU (u a) (hu a) x (hKU hx)).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hr a x hx)) hC.le)⟩
end HigherJet

end
end

end OAI
