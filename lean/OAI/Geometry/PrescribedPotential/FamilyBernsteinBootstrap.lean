import Mathlib
import OAI.Geometry.PrescribedPotential.BernsteinEnergyInterior
import OAI.Geometry.PrescribedPotential.CompactSmoothCutoff

namespace OAI

/-! Family Bernstein Bootstrap. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace HigherJet
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι α : Type*} [Fintype ι]

def EnergyBound (S : ℕ → α → E → ℝ) (m : ℕ) (K : Set E) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, x ∈ K → S m a x ≤ C

lemma family_bernstein_bootstrap {U : Set E} (hU : IsOpen U)
    (S D : ℕ → α → E → ℝ) (v : α → E → ι → E)
    (hsmooth : ∀ m a, ContDiffOn ℝ ∞ (S m a) U)
    (hpos : ∀ m a x, x ∈ U → 0 ≤ S m a x ∧ 0 ≤ D m a x)
    (hgrad : ∀ m a x, x ∈ U → ‖frameGradient (v a x) (S m a) x‖^2 ≤ 4*S m a x*D m a x)
    (hframes : ∀ K, IsCompact K → K ⊆ U → ∃ B : ℝ, 0 ≤ B ∧ ∀ a x, x ∈ K → ∀ i, ‖v a x i‖ ≤ B)
    (hcoerce : ∀ m, 1 ≤ m → ∀ K, IsCompact K → K ⊆ U → ∃ A : ℝ, 1 ≤ A ∧
      ∀ a x, x ∈ K → S (m+1) a x ≤ A*D m a x ∧ D m a x ≤ A*S (m+1) a x)
    (hfirst : ∀ K, IsCompact K → K ⊆ U → EnergyBound S 1 K)
    (hbounded : ∀ m, 1 ≤ m → ∀ K, IsCompact K → K ⊆ U →
      (∀ j, 1 ≤ j → j ≤ m → EnergyBound S j K) →
      ∃ R : ℝ, 0 ≤ R ∧ ∀ a x, x ∈ K → D m a x-R ≤ frameLaplace (v a x) (S m a) x)
    (hcubic : ∀ K, IsCompact K → K ⊆ U → ∃ R : ℝ, 0 ≤ R ∧ ∀ a x, x ∈ K →
      -R*(1+S 2 a x*Real.sqrt (S 2 a x)) ≤ frameLaplace (v a x) (S 2 a) x)
    (hlinear : ∀ m, 3 ≤ m → ∀ K, IsCompact K → K ⊆ U →
      (∀ j, 1 ≤ j → j < m → EnergyBound S j K) →
      ∃ R : ℝ, 0 ≤ R ∧ ∀ a x, x ∈ K →
        D m a x-R*(1+S m a x) ≤ frameLaplace (v a x) (S m a) x) :
    ∀ m, 1 ≤ m → ∀ K, IsCompact K → K ⊆ U → EnergyBound S m K := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm K hK hKU
    by_cases hm1 : m=1
    · subst m
      exact hfirst K hK hKU
    obtain ⟨L,χ,hL,hLU,hKL,hχ,hχval,hχone,hχint⟩ := compact_smooth_cutoff hK hU hKU
    obtain ⟨B,hB,hv⟩ := hframes L hL hLU
    have hχvals : ∀ x ∈ L, 0 ≤ χ x ∧ χ x ≤ 1 := fun x _ => hχval x
    by_cases hm2 : m=2
    · subst m
      obtain ⟨A,hA,hctrl⟩ := hcoerce 1 le_rfl L hL hLU
      obtain ⟨R0,hR0,hSb⟩ := hfirst L hL hLU
      obtain ⟨R1,hR1,hLS⟩ := hbounded 1 le_rfl L hL hLU (fun j hj hj1 => by
        have he : j=1 := by omega
        subst j
        exact hfirst L hL hLU)
      obtain ⟨R2,hR2,hLT⟩ := hcubic L hL hLU
      let R := 1+R0+R1+R2
      have hR : 1 ≤ R := by dsimp [R]; linarith
      have hr0 : R0 ≤ R := by dsimp [R]; linarith
      have hr1 : R1 ≤ R := by dsimp [R]; linarith
      have hr2 : R2 ≤ R := by dsimp [R]; linarith
      obtain ⟨C,hC,hbound⟩ := quartic_energy_interior (ι := ι) hL hU hLU hχ hχvals hχint hA hR hB
      refine ⟨C,hC,fun a z hz => hbound (S 1 a) (S 2 a) (hsmooth 1 a) (hsmooth 2 a) (v a)
        (fun x hx => hv a x hx) ?_ ?_ z (hKL hz) (hχone z hz)⟩
      · intro x hx
        exact ⟨(hpos 1 a x (hLU hx)).1,(hSb a x hx).trans hr0,(hpos 2 a x (hLU hx)).1⟩
      · intro x hx
        have hc := hctrl a x hx
        refine ⟨D 1 a x,(hpos 1 a x (hLU hx)).2,hc.1,hc.2,?_,?_,hgrad 1 a x (hLU hx)⟩
        · linarith only [hLS a x hx,hr1]
        · have hq := mul_le_mul_of_nonneg_right hr2
            (show 0 ≤ 1+S 2 a x*Real.sqrt (S 2 a x) by have := (hpos 2 a x (hLU hx)).1; positivity)
          nlinarith only [hq,hLT a x hx]
    · have hm3 : 3 ≤ m := by omega
      have hiL : ∀ j, 1 ≤ j → j < m → EnergyBound S j L := fun j hj hjm => ih j hjm hj L hL hLU
      have hpred : 1 ≤ m-1 := by omega
      have he : m-1+1=m := by omega
      obtain ⟨A,hA,hctrl⟩ := hcoerce (m-1) hpred L hL hLU
      obtain ⟨R0,hR0,hSb⟩ := hiL (m-1) hpred (by omega)
      obtain ⟨R1,hR1,hLS⟩ := hbounded (m-1) hpred L hL hLU
        (fun j hj hjm => hiL j hj (by omega))
      obtain ⟨R2,hR2,hLT⟩ := hlinear m hm3 L hL hLU hiL
      let R := 1+R0+R1+R2
      have hR : 1 ≤ R := by dsimp [R]; linarith
      have hr0 : R0 ≤ R := by dsimp [R]; linarith
      have hr1 : R1 ≤ R := by dsimp [R]; linarith
      have hr2 : R2 ≤ R := by dsimp [R]; linarith
      obtain ⟨C,hC,hbound⟩ := linear_energy_interior (ι := ι) hL hU hLU hχ hχvals hχint hA hR hB
      refine ⟨C,hC,fun a z hz => hbound (S (m-1) a) (S m a) (hsmooth (m-1) a) (hsmooth m a) (v a)
        (fun x hx => hv a x hx) ?_ ?_ z (hKL hz) (hχone z hz)⟩
      · intro x hx
        exact ⟨(hpos (m-1) a x (hLU hx)).1,(hSb a x hx).trans hr0,(hpos m a x (hLU hx)).1⟩
      · intro x hx
        have hc := (hctrl a x hx).1
        rw [he] at hc
        refine ⟨D (m-1) a x,D m a x,(hpos (m-1) a x (hLU hx)).2,(hpos m a x (hLU hx)).2,hc,?_,?_,hgrad m a x (hLU hx)⟩
        · linarith only [hLS a x hx,hr1]
        · have hq := mul_le_mul_of_nonneg_right hr2 (show 0 ≤ 1+S m a x by linarith [(hpos m a x (hLU hx)).1])
          linarith only [hq,hLT a x hx]
end HigherJet

end
end

end OAI
