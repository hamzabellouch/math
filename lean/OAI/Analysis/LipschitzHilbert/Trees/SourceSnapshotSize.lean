import OAI.Analysis.LipschitzHilbert.Trees.SourceAmplitudeAssembly
import OAI.Analysis.LipschitzHilbert.Trees.SourceMaskMotion
import OAI.Analysis.LipschitzHilbert.Trees.HierarchyNormalization

namespace OAI

/-! Snapshot sizes for the source prediction. The node bound retains
the original coefficient family; normalization costs only the parent mass
raised to the small phase exponent. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem SlopeBox.weight_le_two_pow (T : SlopeBox) {K D : ℝ}
    (hK : 0 < K) (hD : 0 ≤ D) (z : ℝ × ℝ) : T.weight K D z ≤ (2:ℝ)^D := by
  unfold SlopeBox.weight
  have hb : 1 ≤ 1+T.radius z/K :=
    le_add_of_nonneg_right (div_nonneg (T.radius_nonnegative z) hK.le)
  have hp := Real.rpow_le_one_of_one_le_of_nonpos hb (neg_nonpos.mpr hD)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp
    (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) D)

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem restrictCoefficient_full (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) :
    P.restrictCoefficient coeff 0 N = coeff := by
  funext j l u
  simp only [restrictCoefficient, Nat.zero_le, j.isLt, and_self, ite_true]

theorem rawBand_coeff_real_smul (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (q : ℝ) (jet : Fin 3) (j : Fin N) (x y : ℝ) :
    P.rawBand (fun j l u => q • coeff j l u) jet j x y = q • P.rawBand coeff jet j x y := by
  exact vectorPacketSynthesis_coeff_smul
    (fun p : Σ l : P.labels j, Item j l => coeff j p.1 p.2)
    (fun p k => P.raw jet j p.1 p.2 k y) q x

end SourceLabeledLattice

namespace AngularGrid
attribute [local instance] Classical.propDecidable

/-- Full length range, with the actual endpoint masks placed in the
original coefficients. No bound on the number of tops is used. -/
theorem source_snapshot_masked_node_bound {ι X : Type*}
    (grid : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t z, 0 < weight t z)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (M : ι → ℕ) (hM : ∀ t ∈ tops, grid.eligible cutoff (precision t) (M t))
    (hMmax : ∀ t ∈ tops, ∀ k, grid.eligible cutoff (precision t) k → k ≤ M t)
    (a Z : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hZ : 0 ≤ Z)
    (hz0 : ∀ t ∈ tops, ∀ j < M t, 0 ≤ (phase j).re)
    (hz : ∀ t ∈ tops, ∀ j < M t, ‖phase j‖ ≤ Z)
    {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
    [Fintype κ] [∀ j l, Fintype (Item j l)]
    (P : ι → SourceLabeledLattice N κ Label Item)
    (coeff : ∀ t j (l : (P t).labels j), Item j l → EuclideanSpace ℂ κ)
    (jet : Fin 3) (stop : ι → Fin N → ℕ) (hstop : ∀ t ∈ tops, Antitone (stop t))
    (hmax : ∀ t ∈ tops, ∀ j, stop t j ≤ M t) (x y : ι → ℝ)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 1 ≤ C) (z : X)
    (hweight : ∀ t ∈ tops, weight t z ≤ C)
    (hinterval : ∀ t ∈ tops, ∀ l u, l ≤ u → u ≤ N →
      ‖(P t).rawInterval (coeff t) jet l u (x t) (y t)‖ ≤ A*(weight t z)^8)
    (q : ι → ℝ) (level : ℕ) (cell : ℤ)
    (hq : ∀ t ∈ tops, |q t| ≤ 1) :
    ‖grid.sourcePacketAmplitude tops slope precision cutoff weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      (fun p => (P p.1).rawBand (fun j l u => q p.1 • coeff p.1 j l u)
        jet p.2 (x p.1) (y p.1)) phase a z level cell‖ ≤
      (C^8*A*(1+(a+Z*K)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1))*C^3)*
        grid.mass tops slope precision cutoff weight level cell z := by
  have hmasked (t : ι) (ht : t ∈ tops) (l u : ℕ) (hlu : l ≤ u) (hu : u ≤ N) :
      ‖(P t).rawInterval (fun j k v => q t • coeff t j k v) jet l u (x t) (y t)‖ ≤
        A*(weight t z)^8 := by
    rw [(P t).rawInterval_coeff_smul, norm_smul, Real.norm_eq_abs]
    have hb := mul_le_mul (hq t ht) (hinterval t ht l u hlu hu) (norm_nonneg _) zero_le_one
    simpa only [one_mul] using hb
  have hb := grid.sourcePacketAmplitude_node_envelope tops slope precision cutoff weight hp hw
    hK gap phase M hM hMmax a Z ha0 ha1 hZ hz0 hz P
    (fun t j l u => q t • coeff t j l u) jet stop hstop hmax x y A C 1
    hA hC zero_le_one z hweight hmasked 0 N (fun _ => (1:ℂ)) level cell
    (fun _ _ => by simp)
  simpa only [SourceLabeledLattice.restrictCoefficient_full, mul_one, one_smul] using hb

end AngularGrid

section Normalization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem source_snapshot_normalized_size {n c μ C : ℝ}
    (_hn : 0 < n) (hc : 0 < c) (hcn : c ≤ n) (hμ : 0 ≤ μ) (hC : 0 ≤ C)
    (A : E) (hA : ‖A‖ ≤ C*c) :
    ‖((c^(μ-1):ℝ):ℂ) • A‖ ≤ C*n^μ := by
  have heq : c^(μ-1)*c = c^μ := by
    calc
      _ = c^(μ-1)*c^(1:ℝ) := by rw [Real.rpow_one]
      _ = c^((μ-1)+1) := (Real.rpow_add hc _ _).symm
      _ = _ := by congr 1; ring
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hc.le _)]
  calc
    _ ≤ c^(μ-1)*(C*c) := mul_le_mul_of_nonneg_left hA (Real.rpow_nonneg hc.le _)
    _ = C*c^μ := by rw [← heq]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hc.le hcn hμ) hC

/-- The off-path coefficient budget contains the sum of its actual
child fractions, so it vanishes with the relative path drop. -/
theorem source_snapshot_coefficient_mass {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (A : ι → E) (lam : ι → ℂ) (n μ C u : ℝ)
    (hn : 0 < n) (hc : ∀ i, 0 < c i) (hC : 0 ≤ C)
    (hA : ∀ i, ‖A i‖ ≤ C*c i) (hlam : ∀ i, ‖lam i‖ ≤ 1)
    (hmass : ∑ i, c i/n ≤ u) :
    (∑ i, ‖((((c i/n)^(1-μ):ℝ):ℂ)*lam i) •
      (((c i^(μ-1):ℝ):ℂ) • A i)‖) ≤ (C*n^μ)*u := by
  have hnμ : 0 ≤ n^μ := Real.rpow_nonneg hn.le _
  calc
    _ ≤ ∑ i, (C*n^μ)*(c i/n) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,norm_smul,norm_mul,Complex.norm_real,Complex.norm_real,
        Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (div_pos (hc i) hn).le _),
        abs_of_nonneg (Real.rpow_nonneg (hc i).le _)]
      have hb := mul_le_mul_of_nonneg_left (hA i) (Real.rpow_nonneg (hc i).le (μ-1))
      have hl := mul_le_mul (hlam i) hb
        (mul_nonneg (Real.rpow_nonneg (hc i).le _) (norm_nonneg _))
        zero_le_one
      calc
        _ = (c i/n)^(1-μ)*(‖lam i‖*(c i^(μ-1)*‖A i‖)) := by ring
        _ ≤ (c i/n)^(1-μ)*(1*(c i^(μ-1)*(C*c i))) :=
          mul_le_mul_of_nonneg_left hl (Real.rpow_nonneg (div_pos (hc i) hn).le (1-μ))
        _ = C*(((c i/n)^(1-μ)*c i^(μ-1))*c i) := by ring
        _ = C*(n^(μ-1)*c i) := by rw [child_normalization_coefficient hn (hc i)]
        _ = (C*n^μ)*(c i/n) := by rw [Real.rpow_sub hn, Real.rpow_one]; ring
    _ = (C*n^μ)*(∑ i, c i/n) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (mul_nonneg hC hnμ)

end Normalization
end LipschitzHilbert

end

end OAI
