import OAI.Analysis.AncientFlat.Regularity.CoreErrorHolder
import OAI.Analysis.AncientFlat.Profile.SphereScaling

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace CompactCore
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
theorem compact_mismatch_holder :
    ∃ K : ℝ, 0<K ∧ ∀ (α : ℝ), 0<α → α<1 → ∀ Ω : Set (V × ℝ),
      (∀ p∈Ω, ‖p.1‖≤1) → ∀ f : ℝ → V → ℂ,
      (∀ p∈Ω, ContDiff ℝ ∞ (f p.2)) →
      ∀ q : ℝ, 0≤q → q≤1 → ∀ M : ℝ, 0≤M →
      (∀ j : ℕ, j≤4 → HolderBound α Ω
        (fun p => iteratedFDeriv ℝ j (fun y => f p.2 (q • y)) p.1) M) →
      HolderBound α Ω
        (fun p => (q:ℂ)^4*compactOp (f p.2) (q • p.1)-
          flatOp (fun y => f p.2 (q • y)) p.1) (K*q^2*M) := by
  refine ⟨1000*(Module.finrank ℝ V:ℝ)+119568,by positivity,?_⟩
  intro α hα hα1 Ω hx f hf q hq hq1 M hM hb
  have hs (p : V × ℝ) (hp : p∈Ω) : ContDiff ℝ ∞ (fun y => f p.2 (q • y)) := (hf p hp).comp (by fun_prop)
  obtain ⟨h2,h4⟩ := error_holder_bounds hα hα1 hx (fun t y => f t (q • y)) hM hs hb
  have hh := (h2.const_smul (q^2/16)).add (h4.const_smul (q^4/16))
  have hq2 : q^2≤1 := by nlinarith
  have hq4 : q^4≤q^2 := by nlinarith [sq_nonneg q]
  have hk : |q^2/16| *(1000*(Module.finrank ℝ V:ℝ)*M)+|q^4/16| *(119568*M)≤
      (1000*(Module.finrank ℝ V:ℝ)+119568)*q^2*M := by
    rw [abs_of_nonneg (by positivity : 0≤q^2/16),abs_of_nonneg (by positivity : 0≤q^4/16)]
    calc
      _ ≤ q^2*(1000*(Module.finrank ℝ V:ℝ)*M)+q^2*(119568*M) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg q]) (by positivity)
        · exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg q]) (by positivity)
      _ = _ := by ring
  have hm := hh.mono hk
  have he p (hp : p∈Ω) : (q:ℂ)^4*compactOp (f p.2) (q • p.1)-
      flatOp (fun y => f p.2 (q • y)) p.1=
      (q^2/16:ℝ) • errorTwo (fun y => f p.2 (q • y)) p.1+
        (q^4/16:ℝ) • errorFour (fun y => f p.2 (q • y)) p.1 := by
    rw [compact_scaled _ (hf p hp)]
    simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_ofNat]
  constructor
  · intro p hp
    change ‖(q:ℂ)^4*compactOp (f p.2) (q • p.1)-flatOp (fun y => f p.2 (q • y)) p.1‖≤_
    rw [he p hp]
    exact hm.1 p hp
  · intro p hp r hr
    change ‖((q:ℂ)^4*compactOp (f p.2) (q • p.1)-flatOp (fun y => f p.2 (q • y)) p.1)-
      ((q:ℂ)^4*compactOp (f r.2) (q • r.1)-flatOp (fun y => f r.2 (q • y)) r.1)‖≤_
    rw [he p hp,he r hr]
    exact hm.2 p hp r hr
end CompactCore

end

end OAI
