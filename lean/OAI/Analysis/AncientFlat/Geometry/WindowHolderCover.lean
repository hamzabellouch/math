import OAI.Analysis.AncientFlat.Geometry.WindowGeometry
import OAI.Analysis.AncientFlat.Geometry.WindowJets

namespace OAI
noncomputable section
open Set Filter
namespace ParabolicLocalization
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
omit [FiniteDimensional ℝ V] in
lemma unscale_holder {α q B : ℝ} (hq : 0<q) (p0 : V × ℝ) (S : Set (V × ℝ))
    (n : ℕ) (f : V × ℝ → E)
    (h : HolderBound α S (fun p => q^n • f (window p0 q p)) (q^n*q^α*B)) :
    (∀ p∈S, ‖f (window p0 q p)‖≤B*q^α) ∧
    (∀ p∈S, ∀ z∈S, ‖f (window p0 q p)-f (window p0 q z)‖≤B*pdist (window p0 q p) (window p0 q z)^α) := by
  have hqn : 0<q^n := pow_pos hq _
  constructor
  · intro p hp
    have hh := h.1 p hp
    simp only [norm_smul,Real.norm_of_nonneg hqn.le] at hh
    apply (mul_le_mul_iff_right₀ hqn).mp
    nlinarith
  · intro p hp z hz
    have hh := h.2 p hp z hz
    dsimp only at hh
    rw [←smul_sub,norm_smul,Real.norm_of_nonneg hqn.le] at hh
    rw [pdist_window p0 hq.le,Real.mul_rpow hq.le (pdist_nonneg p z)]
    apply (mul_le_mul_iff_right₀ hqn).mp
    nlinarith

omit [FiniteDimensional ℝ V] in
lemma holder_of_windows {α q C r : ℝ} (hα : 0≤α) (hq : 0<q) (hq1 : q≤1) (hC : 0≤C)
    (n : ℕ) (hn : n≤4) (f : V × ℝ → E)
    (h : ∀ p0∈cylinder r, HolderBound α (cylinder 1) (fun p => q^n • f (window p0 q p)) C) :
    HolderBound α (cylinder r) f (2*C/(q^4*q^α)) := by
  let B := C/(q^4*q^α)
  have hqa : 0<q^α := Real.rpow_pos_of_pos hq _
  have hB : 0≤B := by dsimp [B]; positivity
  have hq4 : q^4≤q^n := pow_le_pow_of_le_one hq.le hq1 hn
  have hqa1 : q^α≤1 := Real.rpow_le_one hq.le hq1 hα
  have heq : q^4*q^α*B=C := by dsimp [B]; field_simp
  have hCB : C≤q^n*q^α*B := by rw [←heq]; gcongr
  have Hw (p0 : V × ℝ) (hp0 : p0∈cylinder r) :=
    unscale_holder hq p0 (cylinder 1) n f ((h p0 hp0).mono hCB)
  have Hsup (p : V × ℝ) (hp : p∈cylinder r) : ‖f p‖≤B*q^α := by
    have hz : ((0:V),(0:ℝ))∈cylinder 1 := by norm_num [cylinder]
    simpa only [window_zero] using (Hw p hp).1 (0,0) hz
  have HB : 2*B=2*C/(q^4*q^α) := by dsimp [B]; ring
  rw [←HB]
  constructor
  · intro p hp
    exact (Hsup p hp).trans (by nlinarith)
  · intro p hp z hz
    by_cases hnear : pdist p z<q
    · obtain ⟨hctr,hip,hiz⟩ := close_pair_window hq p z hp hz hnear
      have hc := (Hw (p.1,max p.2 z.2) hctr).2 (windowInv (p.1,max p.2 z.2) q p) hip
        (windowInv (p.1,max p.2 z.2) q z) hiz
      simp only [window_windowInv _ hq.ne'] at hc
      exact hc.trans (mul_le_mul_of_nonneg_right (by linarith : B≤2*B) (Real.rpow_nonneg (pdist_nonneg p z) _))
    · have hdq : q≤pdist p z := le_of_not_gt hnear
      calc
        _≤‖f p‖+‖f z‖ := norm_sub_le _ _
        _≤B*q^α+B*q^α := add_le_add (Hsup p hp) (Hsup z hz)
        _=(2*B)*q^α := by ring
        _≤(2*B)*pdist p z^α := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hq.le hdq hα) (by positivity)
end ParabolicLocalization

end

end OAI
