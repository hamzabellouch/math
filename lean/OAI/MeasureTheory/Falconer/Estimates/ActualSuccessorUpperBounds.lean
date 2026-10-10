import OAI.MeasureTheory.Falconer.Recursion.BranchAnalyticSuccessors

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem finiteEnergyMaximum_le {ι : Type*} (S : Finset ι) (E : ι → ℝ≥0∞)
    {B : ℝ} (hB : 0 ≤ B) (h : ∀ i ∈ S, (E i).toReal ≤ B) :
    finiteEnergyMaximum S E ≤ B := by
  change ((S.sup (fun i => (E i).toNNReal) : ℝ≥0) : ℝ) ≤ B
  lift B to ℝ≥0 using hB
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro i hi
  exact NNReal.coe_le_coe.mp (h i hi)

namespace PositiveDistanceData

theorem prefixLowMaximum_le (d : PositiveDistanceData) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ v ∈ d.prefixLowDepths,
      ({d with t := v,i := d.i+1} : PositiveDistanceData).coincidence.toReal ≤ B) :
    d.prefixLowMaximum ≤ B := finiteEnergyMaximum_le _ _ hB h

theorem prefixSuccessorSupremum_le (d : PositiveDistanceData) (K p : ℕ) (Ψ : ℝ → ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ v ∈ Finset.Ioc d.a d.t, (d.t:ℝ)-d.sig*d.N < (v:ℝ) →
      ∀ row ∈ sourceProductVertices d.Q d.Q d.ρ d.ρ d.X d.Y (p-d.a),
      ∀ k : Fin 2 → PolicyDescriptor → ℕ,
        (∀ l, ∑ e ∈ d.prefixRemainingList p, k l e ≤ K) →
      ∀ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) →
        (∀ l x, ‖h l x‖ ≤ 1) →
        ((d.angularSuccessor p v row).energy k h Ψ).toReal ≤ B) :
    d.prefixSuccessorSupremum K p Ψ ≤ B := by
  apply csSup_le (show (d.prefixSuccessorEnergies K p Ψ).Nonempty from ⟨0,Or.inl rfl⟩)
  intro E hE
  rcases hE with rfl | ⟨v,hv,hg,row,hr,k,hk,h',hh,hhb,rfl⟩
  · exact hB
  · exact h v hv hg row hr k hk h' hh hhb

theorem prefixSuccessorEnergies_mono (d : PositiveDistanceData) {K L : ℕ}
    (hKL : K ≤ L) (p : ℕ) (Ψ : ℝ → ℝ) :
    d.prefixSuccessorEnergies K p Ψ ⊆ d.prefixSuccessorEnergies L p Ψ := by
  intro E hE
  rcases hE with rfl | ⟨v,hv,hg,row,hr,k,hk,h,hh,hhb,hE⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨v,hv,hg,row,hr,k,fun l => (hk l).trans hKL,h,hh,hhb,hE⟩

theorem separatedMaximum_le_ofReal (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (C : Finset (CellPath × CellPath)) (b : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ row ∈ C, ∀ col ∈ C, angularSeparated d.Q e.Q b row col →
      (d.atCells row.1 col.1).coincidence.toReal ≤ B ∧
      (e.atCells row.2 col.2).coincidence.toReal ≤ B) :
    d.separatedMaximum e C b ≤ ENNReal.ofReal B := by
  classical
  apply Finset.sup_le
  intro z hz
  obtain ⟨hm,hs⟩ := Finset.mem_filter.mp hz
  obtain ⟨hr,hc⟩ := Finset.mem_product.mp hm
  have hh := h z.1 hr z.2 hc hs
  apply max_le
  · exact (ENNReal.toReal_le_toReal (coincidence_ne_top _) ENNReal.ofReal_ne_top).mp
      (by simpa only [ENNReal.toReal_ofReal hB] using hh.1)
  · exact (ENNReal.toReal_le_toReal (coincidence_ne_top _) ENNReal.ofReal_ne_top).mp
      (by simpa only [ENNReal.toReal_ofReal hB] using hh.2)

theorem separatedMaximum_toReal_le (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (C : Finset (CellPath × CellPath)) (b : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ row ∈ C, ∀ col ∈ C, angularSeparated d.Q e.Q b row col →
      (d.atCells row.1 col.1).coincidence.toReal ≤ B ∧
      (e.atCells row.2 col.2).coincidence.toReal ≤ B) :
    (d.separatedMaximum e C b).toReal ≤ B := by
  simpa only [ENNReal.toReal_ofReal hB] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top (d.separatedMaximum_le_ofReal e C b hB h)

end PositiveDistanceData

namespace AngularStateData

theorem childMaximum_le (d : AngularStateData)
    (k : Fin 2 → PolicyDescriptor → ℕ) (h : Fin 2 → Plane → ℂ)
    (p : ℕ) (Ψ : ℝ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ row ∈ d.children p, ((d.successor p row).energy k h Ψ).toReal ≤ B) :
    d.childMaximum k h p Ψ ≤ B := finiteEnergyMaximum_le _ _ hB hb

theorem farDistanceMaximum_le (d : AngularStateData) [IsFiniteMeasure d.ρ]
    (b : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ row ∈ d.children b, ∀ col ∈ d.children b,
      angularSeparated d.Q d.Q b row col →
      ((d.distanceSuccessor b).atCells row.1 col.1).coincidence.toReal ≤ B ∧
      ((d.distanceSuccessor b).atCells row.2 col.2).coincidence.toReal ≤ B) :
    (d.farDistanceMaximum b).toReal ≤ B := by
  let : IsFiniteMeasure (d.distanceSuccessor b).ρ := inferInstanceAs (IsFiniteMeasure d.ρ)
  exact (d.distanceSuccessor b).separatedMaximum_toReal_le _ _ _ hB h

theorem farSum_le_card (d : AngularStateData) (p : ℕ) {B : ℝ}
    (h : ∀ b ∈ Finset.Icc (d.a+9) (p+5),
      ((2:ℝ)^d.N)^(-2*(d.profile b-d.profile d.a)+4000*(d.lam+d.sig)) *
        (d.farDistanceMaximum b).toReal ≤ B) :
    d.farSum p ≤ ((Finset.Icc (d.a+9) (p+5)).card:ℝ)*B := by
  exact (Finset.sum_le_sum h).trans_eq (by simp)

theorem farSum_le_depth_factor (d : AngularStateData) (p : ℕ) {B : ℝ}
    (hp : p+5 < d.v) (hv : d.v ≤ d.N) (hB : 0 ≤ B)
    (h : ∀ b ∈ Finset.Icc (d.a+9) (p+5),
      ((2:ℝ)^d.N)^(-2*(d.profile b-d.profile d.a)+4000*(d.lam+d.sig)) *
        (d.farDistanceMaximum b).toReal ≤ B) :
    d.farSum p ≤ (d.N:ℝ)*B := by
  apply (d.farSum_le_card p h).trans
  apply mul_le_mul_of_nonneg_right _ hB
  exact_mod_cast (show (Finset.Icc (d.a+9) (p+5)).card ≤ d.N by
    rw [Nat.card_Icc]; omega)

end AngularStateData

end PlanarFalconer

end OAI
