import Mathlib
import OAI.MathematicalPhysics.BFSS.NormExhaustion
import OAI.MathematicalPhysics.BFSS.WeightedCompactness

namespace OAI

/-! Normal coordinate profiles and strong core extraction. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open MeasureTheory Set
variable {N : ℕ} (M : AlgebraData N)
attribute [local irreducible] normalSlice gaugeAction coreToL2 normalMeasuredField normalCoordinateField normalCoreField

lemma normalCoordinateField_compactSupport (q : Boson N) (h : ℝ) (f : SmoothCore N) :
    HasCompactSupport (M.normalCoordinateField q h f) := by
  unfold normalCoordinateField
  exact (M.normalCoreField_compactSupport q h f).comp_homeomorph
    (M.normalCoordinateIsometry q).toHomeomorph

def normalCoordinateWeight (q : Boson N) (J : M.normalSlice q → ℝ) (φ : Boson N → ℝ) :
    M.NormalCoordinates q → ℝ := fun x =>
  Real.sqrt (J (M.normalCoordinateIsometry q x) * φ (q+(M.normalCoordinateIsometry q x : Boson N)))

lemma normalCoordinateWeight_continuous (q : Boson N) (J : M.normalSlice q → ℝ)
    (φ : Boson N → ℝ) (hJ : Continuous J) (hφ : Continuous φ) :
    Continuous (M.normalCoordinateWeight q J φ) :=
  ((hJ.comp (M.normalCoordinateIsometry q).continuous).mul
    (hφ.comp (continuous_const.add (continuous_subtype_val.comp
      (M.normalCoordinateIsometry q).continuous)))).sqrt

def normalMeasuredCoordinates (q : Boson N) (h : ℝ) (J : M.normalSlice q → ℝ)
    (φ : Boson N → ℝ) (f : SmoothCore N) : M.NormalCoordinates q → Fermion N :=
  fun x => M.normalCoordinateWeight q J φ (h • x) • M.normalCoordinateField q h f x

lemma normalMeasuredCoordinates_eq (q : Boson N) (h : ℝ) (J : M.normalSlice q → ℝ)
    (φ : Boson N → ℝ) (f : SmoothCore N) (x : M.NormalCoordinates q) :
    M.normalMeasuredCoordinates q h J φ f x =
      M.normalMeasuredField q h J φ f (M.normalCoordinateIsometry q x) := by
  simp only [normalMeasuredCoordinates,normalCoordinateWeight,normalCoordinateField,
    normalMeasuredField,Function.comp_apply,map_smul,Submodule.coe_smul]

lemma normalMeasuredCoordinates_continuous (q : Boson N) (h : ℝ) (J : M.normalSlice q → ℝ)
    (φ : Boson N → ℝ) (f : SmoothCore N) (hJ : Continuous J) (hφ : Continuous φ) :
    Continuous (M.normalMeasuredCoordinates q h J φ f) := by
  change Continuous (fun x => M.normalCoordinateWeight q J φ (h • x) • M.normalCoordinateField q h f x)
  exact ((M.normalCoordinateWeight_continuous q J φ hJ hφ).comp
    ((continuous_const : Continuous (fun _ : M.NormalCoordinates q => h)).smul continuous_id)).smul (M.normalCoordinateField_contDiff q h f).continuous

lemma normalMeasuredCoordinates_compactSupport (q : Boson N) (h : ℝ)
    (J : M.normalSlice q → ℝ) (φ : Boson N → ℝ) (f : SmoothCore N) :
    HasCompactSupport (M.normalMeasuredCoordinates q h J φ f) := by
  change HasCompactSupport ((fun x => M.normalCoordinateWeight q J φ (h • x)) • M.normalCoordinateField q h f)
  exact (M.normalCoordinateField_compactSupport q h f).smul_left

lemma normalMeasuredCoordinates_norm_integral (q : Boson N) (h : ℝ)
    (J : M.normalSlice q → ℝ) (φ : Boson N → ℝ) (f : SmoothCore N) :
    (∫ x, ‖M.normalMeasuredCoordinates q h J φ f x‖^2) =
      ∫ z, ‖M.normalMeasuredField q h J φ f z‖^2 := by
  simp_rw [M.normalMeasuredCoordinates_eq]
  exact (M.normalCoordinateIsometry q).measurePreserving.integral_comp
    (M.normalCoordinateIsometry q).toHomeomorph.measurableEmbedding
    (fun z : M.normalSlice q => ‖M.normalMeasuredField q h J φ f z‖^2)

lemma normalMeasuredCoordinates_moment_integral (q : Boson N) (h : ℝ)
    (J : M.normalSlice q → ℝ) (φ : Boson N → ℝ) (f : SmoothCore N) :
    (∫ x : M.NormalCoordinates q, ‖x‖^2*‖M.normalMeasuredCoordinates q h J φ f x‖^2) =
      ∫ z : M.normalSlice q, ‖z‖^2*‖M.normalMeasuredField q h J φ f z‖^2 := by
  simp_rw [M.normalMeasuredCoordinates_eq]
  have he := (M.normalCoordinateIsometry q).measurePreserving.integral_comp
    (M.normalCoordinateIsometry q).toHomeomorph.measurableEmbedding
    (fun z : M.normalSlice q => ‖z‖^2*‖M.normalMeasuredField q h J φ f z‖^2)
  simpa only [LinearIsometryEquiv.norm_map] using he
end
end BFSSQuantum.AlgebraData

namespace BFSSQuantum.AlgebraData.GaugeData.MeasuredNormalPatch
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal
variable {N : ℕ} {M : AlgebraData N} {G : M.GaugeData} {q : Boson N}
  (P : G.MeasuredNormalPatch q)
attribute [local irreducible] AlgebraData.normalSlice AlgebraData.gaugeAction coreToL2

def profile (h : ℝ) (f : G.invariantCore) :
    Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)) :=
  BFSSRellich.compactLp (M.normalMeasuredCoordinates q h P.density P.cutoff f.val)
    (M.normalMeasuredCoordinates_continuous q h P.density P.cutoff f.val P.density_continuous P.cutoff_continuous)
    (M.normalMeasuredCoordinates_compactSupport q h P.density P.cutoff f.val)

lemma profile_norm_square (h : ℝ) (f : G.invariantCore) :
    ‖P.profile h f‖^2 = ∫ z, ‖M.normalMeasuredField q h P.density P.cutoff f.val z‖^2 := by
  rw [profile,BFSSRellich.compactLp_norm_square,M.normalMeasuredCoordinates_norm_integral]

lemma profile_norm_eq {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) (f : G.invariantCore) :
    ‖P.profile h f‖^2 = ∫ x, P.cutoff (h • x)*‖f.val x‖^2 := by
  rw [P.profile_norm_square,P.norm_eq h hh h1 f]

theorem profile_totallyBounded (hN : 2 ≤ N)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n ∧ h n ≤ 1) (hzero : Tendsto h atTop (nhds 0))
    (f : ℕ → G.invariantCore) (E : ℝ≥0)
    (hnorm : ∀ n, ‖coreToL2 (f n).val‖^2 ≤ E)
    (henergy : ∀ n, M.deformedCoreEnergy (h n) 1 (f n).val ≤ E) :
    TotallyBounded (range (fun n => P.profile (h n) (f n))) := by
  let C : ℝ≥0 := ⟨Real.sqrt (2*((E : ℝ)+P.K*E)/P.c),Real.sqrt_nonneg _⟩
  have hC0 : 0 ≤ 2*((E : ℝ)+P.K*E)/P.c :=
    div_nonneg (mul_nonneg (by norm_num) (add_nonneg E.coe_nonneg (mul_nonneg P.K_nonneg E.coe_nonneg))) P.c_pos.le
  change TotallyBounded (range (fun n => BFSSRellich.compactLp
    (M.normalMeasuredCoordinates q (h n) P.density P.cutoff (f n).val) _ _))
  apply BFSSRellich.weighted_tight_compactness
    (fun n => M.normalCoordinateField q (h n) (f n).val)
    (fun n => (M.normalCoordinateField_contDiff q (h n) (f n).val).continuous)
    (fun n => M.normalCoordinateField_compactSupport q (h n) (f n).val)
    (M.normalCoordinateWeight q P.density P.cutoff)
    (M.normalCoordinateWeight_continuous q P.density P.cutoff P.density_continuous P.cutoff_continuous)
    h hzero C
  · intro n
    change (∫ x : M.NormalCoordinates q, ‖x‖^2*‖M.normalMeasuredCoordinates q (h n) P.density P.cutoff (f n).val x‖^2) ≤ _
    rw [M.normalMeasuredCoordinates_moment_integral]
    have hb := P.moment_bound (h n) (hh n).1 (hh n).2 (f n)
    have hk := mul_le_mul_of_nonneg_left (hnorm n) P.K_nonneg
    change _ ≤ (Real.sqrt _)^2
    rw [Real.sq_sqrt hC0]
    apply (le_div_iff₀ P.c_pos).mpr
    nlinarith [henergy n]
  · intro R hR
    obtain ⟨η,hη,hcompact⟩ := G.normalCore_locallyCompact hN q
    let φ : ContDiffBump (0 : M.NormalCoordinates q) := ⟨R,2*R,hR,by linarith⟩
    have hev : ∀ᶠ n in atTop, h n * φ.rOut < η :=
      (hzero.mul_const φ.rOut).eventually (gt_mem_nhds (by simpa using hη))
    obtain ⟨k,hk⟩ := eventually_atTop.mp hev
    apply BFSSRellich.totallyBounded_of_tail _ k
    exact hcompact φ E (fun n => h (n+k)) (fun n => f (n+k))
      (fun n => ⟨(hh _).1,(hh _).2,hk _ (Nat.le_add_left _ _)⟩)
      (fun _ => hnorm _) (fun _ => henergy _)
end
end BFSSQuantum.AlgebraData.GaugeData.MeasuredNormalPatch
namespace BFSSQuantum.AlgebraData.GaugeData
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal
variable {N : ℕ} {M : AlgebraData N} (G : M.GaugeData)
attribute [local irreducible] AlgebraData.normalSlice AlgebraData.gaugeAction coreToL2

theorem normalCore_extraction (hN : 2 ≤ N)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n ∧ h n ≤ 1) (hzero : Tendsto h atTop (nhds 0))
    (f : ℕ → G.invariantCore) (E : ℝ≥0)
    (hnorm : ∀ n, ‖coreToL2 (f n).val‖^2 ≤ E)
    (henergy : ∀ n, M.deformedCoreEnergy (h n) 1 (f n).val ≤ E) :
    ∃ S : Finset (Boson N),
      (∀ q ∈ S, q ∈ M.massiveZeros) ∧
      M.massiveZeros = ⋃ q ∈ S, M.gaugeOrbit q ∧
      Pairwise (fun i j : S => Disjoint (M.gaugeOrbit i.val) (M.gaugeOrbit j.val)) ∧
      ∃ P : (q : S) → G.MeasuredNormalPatch q.val,
        ∃ v : (q : S) → Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q.val)),
          ∃ σ : ℕ → ℕ, StrictMono σ ∧
            (∀ q, Tendsto (fun n => (P q).profile (h (σ n)) (f (σ n))) atTop (nhds (v q))) ∧
            Tendsto (fun n => ‖coreToL2 (f (σ n)).val‖^2) atTop (nhds (∑ q : S, ‖v q‖^2)) := by
  classical
  obtain ⟨S,hS,hcov,hdis,P,hPd,δ,c,K,hδ,hc,hK,hbound⟩ := G.normalPatch_norm_exhaustion hN
  let C : ℝ := ((E : ℝ)+K*E)/(c/2*δ^2)
  have hden : 0 < c/2*δ^2 := mul_pos (half_pos hc) (sq_pos_of_pos hδ)
  let r : ℕ → ℝ := fun n => ‖coreToL2 (f n).val‖^2 - ∑ q : S, ‖(P q).profile (h n) (f n)‖^2
  have hr (n : ℕ) : 0 ≤ r n ∧ r n ≤ (h n)^2*C := by
    have hb := hbound (h n) (hh n).1 (hh n).2 (f n)
    simp_rw [←MeasuredNormalPatch.profile_norm_square] at hb
    refine ⟨hb.1,?_⟩
    change r n ≤ (h n)^2 * (((E : ℝ)+K*E)/(c/2*δ^2))
    rw [←mul_div_assoc]
    apply (le_div_iff₀ hden).2
    have he : M.deformedCoreEnergy (h n) 1 (f n).val + K*‖coreToL2 (f n).val‖^2 ≤ (E : ℝ)+K*E :=
      add_le_add (henergy n) (mul_le_mul_of_nonneg_left (hnorm n) hK)
    have hs := hb.2.trans (mul_le_mul_of_nonneg_left he (sq_nonneg _))
    change r n * (c/2*δ^2) ≤ _
    rw [mul_comm (r n)]
    exact hs
  have hrzero : Tendsto r atTop (nhds 0) :=
    squeeze_zero (fun n => (hr n).1) (fun n => (hr n).2)
      (by simpa using (hzero.pow 2).mul_const C)
  let X (q : S) := Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q.val))
  let a : ℕ → ((q : S) → X q) := fun n q => (P q).profile (h n) (f n)
  have hcompact (q : S) : IsCompact (closure (range (fun n => a n q))) :=
    ((P q).profile_totallyBounded hN h hh hzero f E hnorm henergy).closure.isCompact_of_isClosed isClosed_closure
  have hprod := isCompact_pi_infinite hcompact
  obtain ⟨v,hv,σ,hσ,ht⟩ := hprod.tendsto_subseq (fun n _ => subset_closure (mem_range_self n))
  have hcoord (q : S) : Tendsto (fun n => (P q).profile (h (σ n)) (f (σ n))) atTop (nhds (v q)) :=
    (tendsto_pi_nhds.mp ht) q
  have hsum : Tendsto (fun n => ∑ q : S, ‖(P q).profile (h (σ n)) (f (σ n))‖^2) atTop
      (nhds (∑ q : S, ‖v q‖^2)) := tendsto_finsetSum _ (fun q _ => (hcoord q).norm.pow 2)
  refine ⟨S,hS,hcov,hdis,P,v,σ,hσ,hcoord,?_⟩
  have ht' := (hrzero.comp hσ.tendsto_atTop).add hsum
  simpa only [Function.comp_apply,r,zero_add,sub_add_cancel] using ht'
end
end BFSSQuantum.AlgebraData.GaugeData

end OAI
