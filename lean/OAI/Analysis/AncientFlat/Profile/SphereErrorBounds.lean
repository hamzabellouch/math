import OAI.Analysis.AncientFlat.Profile.SphereJetBounds

namespace OAI
noncomputable section
open scoped ContDiff Laplacian
namespace CompactCore
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
omit [FiniteDimensional ℝ V] in
lemma radialJet_norm_le (j : ℕ) (f : V → ℂ) (x : V) (hx : ‖x‖≤1) :
    ‖radialJet j f x‖≤‖iteratedFDeriv ℝ j f x‖ := by
  unfold radialJet
  calc
    _ ≤ ‖iteratedFDeriv ℝ j f x‖*∏ _i : Fin j, ‖x‖ := (iteratedFDeriv ℝ j f x).le_opNorm _
    _ ≤ ‖iteratedFDeriv ℝ j f x‖*1 := mul_le_mul_of_nonneg_left
      (Finset.prod_le_one₀ (fun _ _ => norm_nonneg x) (fun _ _ => hx)) (norm_nonneg _)
    _ = _ := mul_one _
omit [FiniteDimensional ℝ V] in
lemma correction_norm_le (f : V → ℂ) (x : V) (hx : ‖x‖≤1) :
    ‖correction f x‖≤‖iteratedFDeriv ℝ 2 f x‖+29*‖iteratedFDeriv ℝ 1 f x‖ := by
  unfold correction
  refine (norm_add_le _ _).trans (add_le_add (radialJet_norm_le _ f x hx) ?_)
  calc
    _ = 29*‖radialJet 1 f x‖ := by norm_num [norm_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (radialJet_norm_le _ f x hx) (by norm_num : (0:ℝ)≤29)
omit [FiniteDimensional ℝ V] in
lemma correction_bound (f : V → ℂ) (x : V) (hx : ‖x‖≤1) (M : ℝ)
    (hb : ∀ j : ℕ, j≤2 → ‖iteratedFDeriv ℝ j f x‖≤M) :
    ‖correction f x‖≤30*M := by
  have he := correction_norm_le f x hx
  linarith [hb 1 (by norm_num),hb 2 (by norm_num)]
lemma jet_laplacian_bound (f : V → ℂ) (hf : ContDiff ℝ ∞ f)
    (x : V) (M : ℝ) (hb : ∀ j : ℕ, j≤4 → ‖iteratedFDeriv ℝ j f x‖≤M) :
    ∀ j : ℕ, j≤2 → ‖iteratedFDeriv ℝ j (Δ f) x‖≤(Module.finrank ℝ V:ℝ)*M := by
  let : MeasurableSpace V := borel V
  let : BorelSpace V := ⟨rfl⟩
  intro j hj
  exact (FlatDuality.norm_iterated_laplacian_le j f
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl (j+2))) x).trans
      (mul_le_mul_of_nonneg_left (hb (j+2) (by omega)) (Nat.cast_nonneg _))
lemma error_norm_bounds (f : V → ℂ) (hf : ContDiff ℝ ∞ f)
    (x : V) (hx : ‖x‖≤1) (M : ℝ) (hM : 0≤M)
    (hb : ∀ j : ℕ, j≤4 → ‖iteratedFDeriv ℝ j f x‖≤M) :
    ‖errorTwo f x‖≤310*(Module.finrank ℝ V:ℝ)*M ∧
    ‖errorFour f x‖≤13392*M := by
  let : MeasurableSpace V := borel V
  let : BorelSpace V := ⟨rfl⟩
  have hc := correction_jet_bound f hf x hx M hM hb
  have hl := jet_laplacian_bound f hf x M hb
  have hcl := correction_bound (Δ f) x hx _ hl
  have hcc := correction_bound (correction f) x hx _ hc
  have hc0 := correction_bound f x hx M (fun j hj => hb j (by omega))
  have hl0 := hl 0 (by norm_num)
  simp only [norm_iteratedFDeriv_zero] at hl0
  have hf0 := hb 0 (by norm_num)
  simp only [norm_iteratedFDeriv_zero] at hf0
  have hdc := FlatDuality.norm_iterated_laplacian_le 0 (correction f)
    ((correction_smooth f hf).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) x
  simp only [norm_iteratedFDeriv_zero] at hdc
  have hdc' : ‖Δ (correction f) x‖≤(Module.finrank ℝ V:ℝ)*(132*M) :=
    hdc.trans (mul_le_mul_of_nonneg_left (hc 2 (by norm_num)) (Nat.cast_nonneg _))
  constructor
  · unfold errorTwo
    calc
      _ ≤ ‖Δ (correction f) x‖+‖correction (Δ f) x‖+148*‖Δ f x‖ := by
        have h1 := norm_sub_le (-Δ (correction f) x-correction (Δ f) x) (148*Δ f x)
        have h2 := norm_sub_le (-Δ (correction f) x) (correction (Δ f) x)
        norm_num [norm_neg,norm_mul] at h1 h2
        linarith
      _ ≤ _ := by linarith
  · unfold errorFour
    calc
      _ ≤ ‖correction (correction f) x‖+148*‖correction f x‖+4992*‖f x‖ := by
        have h1 := norm_add_le (correction (correction f) x+148*correction f x) (4992*f x)
        have h2 := norm_add_le (correction (correction f) x) (148*correction f x)
        norm_num [norm_mul] at h1 h2
        linarith
      _ ≤ _ := by linarith
end CompactCore

end

end OAI
