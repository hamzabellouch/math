import OAI.Analysis.AncientFlat.Evolution.FiniteCoreCalculus
import OAI.Analysis.AncientFlat.Regularity.FiniteCoreCorrection
import OAI.Analysis.AncientFlat.Kernel.BilapNorm

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace CompactCoreFinite
open CompactCore
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
lemma laplacian_translate (f : V → ℂ) (a : V) :
    Δ (fun x => f (x+a))=fun x => Δ f (x+a) := by
  funext x
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    iteratedFDeriv_comp_add_right]
lemma jet_laplacian_holder {α M : ℝ} {Ω : Set (V × ℝ)} (f : ℝ → V → ℂ)
    (j : ℕ) (hf : ∀ p∈Ω, ContDiff ℝ (j+2 : ℕ) (f p.2))
    (hb : HolderBound α Ω (fun p => iteratedFDeriv ℝ (j+2) (f p.2) p.1) M) :
    HolderBound α Ω (fun p => iteratedFDeriv ℝ j (Δ (f p.2)) p.1)
      ((Module.finrank ℝ V:ℝ)*M) := by
  let : MeasurableSpace V := borel V
  let : BorelSpace V := ⟨rfl⟩
  constructor
  · intro p hp
    exact (FlatDuality.norm_iterated_laplacian_le j (f p.2)
      (hf p hp) p.1).trans
      (mul_le_mul_of_nonneg_left (hb.1 p hp) (Nat.cast_nonneg _))
  · intro p hp q hq
    let f₁ : V → ℂ := fun z => f p.2 (z+p.1)
    let f₂ : V → ℂ := fun z => f q.2 (z+q.1)
    have hf₁ : ContDiff ℝ (j+2 : ℕ) f₁ := (hf p hp).comp (contDiff_id.add contDiff_const)
    have hf₂ : ContDiff ℝ (j+2 : ℕ) f₂ := (hf q hq).comp (contDiff_id.add contDiff_const)
    have hl₁ : ContDiff ℝ j (Δ f₁) := laplacian_smooth _ hf₁
    have hl₂ : ContDiff ℝ j (Δ f₂) := laplacian_smooth _ hf₂
    have he : Δ (f₁-f₂)=Δ f₁-Δ f₂ := by
      funext x
      exact ((hf₁.of_le (by exact_mod_cast (show 2≤j+2 by omega))).contDiffAt).laplacian_sub
        ((hf₂.of_le (by exact_mod_cast (show 2≤j+2 by omega))).contDiffAt)
    have hh := FlatDuality.norm_iterated_laplacian_le j (f₁-f₂)
      (hf₁.sub hf₂) (0:V)
    rw [he,iteratedFDeriv_sub hl₁
      hl₂,Pi.sub_apply,
      iteratedFDeriv_sub hf₁
      hf₂,Pi.sub_apply] at hh
    simp only [f₁,f₂,laplacian_translate,iteratedFDeriv_comp_add_right,zero_add] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (hb.2 p hp q hq) (Nat.cast_nonneg _)).trans_eq (by ring))
end CompactCoreFinite

end

end OAI
