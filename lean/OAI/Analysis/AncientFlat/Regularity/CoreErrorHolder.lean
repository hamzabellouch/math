import OAI.Analysis.AncientFlat.Regularity.CoreLaplacianHolder

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace CompactCore
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
lemma error_holder_bounds {α M : ℝ} {Ω : Set (V × ℝ)} (hα : 0<α) (hα1 : α<1)
    (hx : ∀ p∈Ω, ‖p.1‖≤1) (f : ℝ → V → ℂ) (hM : 0≤M)
    (hf : ∀ p∈Ω, ContDiff ℝ ∞ (f p.2))
    (hb : ∀ j : ℕ, j≤4 → HolderBound α Ω (fun p => iteratedFDeriv ℝ j (f p.2) p.1) M) :
    HolderBound α Ω (fun p => errorTwo (f p.2) p.1) (1000*(Module.finrank ℝ V:ℝ)*M) ∧
    HolderBound α Ω (fun p => errorFour (f p.2) p.1) (119568*M) := by
  have hc := correction_jet_holder hα hα1 hx f hM hf hb
  have hl : ∀ j : ℕ, j≤2 → HolderBound α Ω (fun p => iteratedFDeriv ℝ j (Δ (f p.2)) p.1)
      ((Module.finrank ℝ V:ℝ)*M) := fun j hj => jet_laplacian_holder f hf j (hb (j+2) (by omega))
  have hcl := correction_holder hα hα1 hx (fun t => Δ (f t)) (by positivity) hl
  have hcc := correction_holder hα hα1 hx (fun t => correction (f t)) (by positivity) hc
  have hdc := holder_of_zero_jet (fun t => Δ (correction (f t)))
    (jet_laplacian_holder (fun t => correction (f t)) (fun p hp => correction_smooth _ (hf p hp))
      0 (hc 2 (by norm_num)))
  have hls := holder_of_zero_jet (fun t => Δ (f t)) (hl 0 (by norm_num))
  have hcs := correction_holder hα hα1 hx f hM (fun j hj => hb j (by omega))
  have hfs := holder_of_zero_jet f (hb 0 (by norm_num))
  constructor
  · have hh := ((hdc.neg).add hcl.neg).add ((hls.const_smul 148).neg)
    convert hh using 1
    · funext p
      simp only [errorTwo,Complex.real_smul]
      norm_num
      ring
    · norm_num
      ring
  · have hh := (hcc.add (hcs.const_smul 148)).add (hfs.const_smul 4992)
    convert hh using 1
    · funext p
      simp only [errorFour,Complex.real_smul]
      norm_num
    · norm_num
      ring
end CompactCore

end

end OAI
