import OAI.Geometry.PeriodicTiling.TileDilation
import OAI.Geometry.PeriodicTiling.PlaneLattices
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

universe uι

noncomputable section

namespace PeriodicTilingThree

open Set Filter
open scoped BigOperators Topology

def directionalAverage (a : Plane → ℝ) (q : ℕ) (v : Plane) (N : ℕ) (x : Plane) : ℝ :=
  (∑ k ∈ Finset.range (N + 1), a (x - (1 + q * (k + 1)) • v)) / (N + 1 : ℕ)

theorem directionalAverage_nonneg {a : Plane → ℝ} (ha : ∀ x, 0 ≤ a x)
    (q : ℕ) (v : Plane) (N : ℕ) (x : Plane) :
    0 ≤ directionalAverage a q v N x := by
  unfold directionalAverage
  exact div_nonneg (Finset.sum_nonneg fun k _ => ha _) (by positivity)

theorem directionalAverage_le_one {a : Plane → ℝ} (ha : ∀ x, a x ≤ 1)
    (q : ℕ) (v : Plane) (N : ℕ) (x : Plane) :
    directionalAverage a q v N x ≤ 1 := by
  have hN : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  apply (div_le_iff₀ hN).2
  calc
    _ ≤ ∑ _k ∈ Finset.range (N + 1), (1 : ℝ) :=
      Finset.sum_le_sum fun k _ => ha _
    _ = _ := by simp

theorem directionalAverage_translate_sub (a : Plane → ℝ) (q : ℕ)
    (v : Plane) (N : ℕ) (x : Plane) :
    directionalAverage a q v N (x + q • v) - directionalAverage a q v N x =
      (a (x - v) - a (x - (1 + q * (N + 1)) • v)) / (N + 1 : ℕ) := by
  have hshift (k : ℕ) :
      x + q • v - (1 + q * (k + 1)) • v = x - (1 + q * k) • v := by
    have hk : 1 + q * (k + 1) = (1 + q * k) + q := by ring
    rw [hk, add_nsmul]
    abel
  unfold directionalAverage
  simp_rw [hshift]
  rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  simpa only [Nat.mul_zero, Nat.add_zero, one_nsmul] using
    Finset.sum_range_sub' (fun k => a (x - (1 + q * k) • v)) (N + 1)

theorem directionalAverage_translate_error {a : Plane → ℝ}
    (ha0 : ∀ x, 0 ≤ a x) (ha1 : ∀ x, a x ≤ 1)
    (q : ℕ) (v : Plane) (N : ℕ) (x : Plane) :
    |directionalAverage a q v N (x + q • v) - directionalAverage a q v N x| ≤
      1 / (N + 1 : ℕ) := by
  rw [directionalAverage_translate_sub, abs_div,
    abs_of_pos (show (0 : ℝ) < (N + 1 : ℕ) by positivity)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply abs_le.mpr
  constructor <;> linarith [ha0 (x - v), ha1 (x - v),
    ha0 (x - (1 + q * (N + 1)) • v), ha1 (x - (1 + q * (N + 1)) • v)]

theorem sum_directionalAverage {F : Finset Plane} (h0 : (0 : Plane) ∈ F)
    {a : Plane → ℝ} {q : ℕ}
    (hD : ∀ (k : ℕ) (x : Plane), ∑ f ∈ F, a (x - (1 + q * k) • f) = 1)
    (N : ℕ) (x : Plane) :
    (∑ f ∈ F.erase 0, directionalAverage a q f N x) = 1 - a x := by
  classical
  have hs (k : ℕ) :
      (∑ f ∈ F.erase 0, a (x - (1 + q * (k + 1)) • f)) = 1 - a x := by
    have he := Finset.sum_erase_add F
      (fun f => a (x - (1 + q * (k + 1)) • f)) h0
    rw [hD (k + 1) x] at he
    simpa only [smul_zero, sub_zero] using (eq_sub_iff_add_eq.mpr he)
  unfold directionalAverage
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [hs]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact mul_div_cancel_left₀ (1 - a x) (by positivity)

theorem exists_common_directional_subsequence {ι : Type uι} [Countable ι]
    (u : ℕ → ι → Plane → ℝ)
    (hu0 : ∀ N i x, 0 ≤ u N i x) (hu1 : ∀ N i x, u N i x ≤ 1) :
    ∃ (φ : ι → Plane → ℝ) (σ : ℕ → ℕ), StrictMono σ ∧
      (∀ i x, 0 ≤ φ i x ∧ φ i x ≤ 1) ∧
      ∀ i x, Tendsto (fun N => u (σ N) i x) atTop (𝓝 (φ i x)) := by
  let u' : ℕ → ((ι × Plane) → Set.Icc (0 : ℝ) 1) :=
    fun N ix => ⟨u N ix.1 ix.2, hu0 N ix.1 ix.2, hu1 N ix.1 ix.2⟩
  obtain ⟨l, σ, hσ, hl⟩ := CompactSpace.tendsto_subseq u'
  refine ⟨fun i x => (l (i, x) : ℝ), σ, hσ, ?_, ?_⟩
  · intro i x
    exact (l (i, x)).property
  · intro i x
    exact ((continuous_subtype_val.comp (continuous_apply (i, x))).tendsto l).comp hl

theorem exists_ungrouped_directional_limits {F : Finset Plane} (h0 : (0 : Plane) ∈ F)
    {a : Plane → ℝ} (ha0 : ∀ x, 0 ≤ a x) (ha1 : ∀ x, a x ≤ 1)
    {q : ℕ}
    (hD : ∀ (k : ℕ) (x : Plane), ∑ f ∈ F, a (x - (1 + q * k) • f) = 1) :
    ∃ φ : ↥(F.erase 0) → Plane → ℝ,
      (∀ f x, 0 ≤ φ f x ∧ φ f x ≤ 1) ∧
      (∀ x, a x + ∑ f, φ f x = 1) ∧
      ∀ f, Function.Periodic (φ f) (q • (f : Plane)) := by
  classical
  obtain ⟨φ, σ, hσ, hφ, hlim⟩ := exists_common_directional_subsequence
    (fun N (f : ↥(F.erase 0)) x => directionalAverage a q f N x)
    (fun N f x => directionalAverage_nonneg ha0 q f N x)
    (fun N f x => directionalAverage_le_one ha1 q f N x)
  refine ⟨φ, hφ, ?_, ?_⟩
  · intro x
    have hsum := tendsto_finsetSum Finset.univ (fun (f : ↥(F.erase 0)) _ => hlim f x)
    have havg (N : ℕ) :
        (∑ f : ↥(F.erase 0), directionalAverage a q f (σ N) x) = 1 - a x := by
      exact (Finset.sum_coe_sort (F.erase 0)
        (fun f : Plane => directionalAverage a q f (σ N) x)).trans
          (sum_directionalAverage h0 hD (σ N) x)
    have heq : (∑ f, φ f x) = 1 - a x :=
      tendsto_nhds_unique hsum (by simpa only [havg] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => 1 - a x) atTop (𝓝 (1 - a x))))
    linarith
  · intro f x
    have herr := (hlim f (x + q • (f : Plane))).sub (hlim f x)
    have hbound : Tendsto (fun N : ℕ => (1 : ℝ) / (σ N + 1 : ℕ)) atTop (𝓝 0) :=
      (tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).comp
        hσ.tendsto_atTop
    have hz := squeeze_zero (fun N => abs_nonneg
      (directionalAverage a q f (σ N) (x + q • (f : Plane)) -
        directionalAverage a q f (σ N) x))
      (fun N => directionalAverage_translate_error ha0 ha1 q f (σ N) x) hbound
    have heq : |φ f (x + q • (f : Plane)) - φ f x| = 0 :=
      tendsto_nhds_unique herr.abs hz
    exact sub_eq_zero.mp (abs_eq_zero.mp heq)

theorem Tiles.exists_ungrouped_directional_limits {F : Finset Plane} {A : Set Plane}
    (h : Tiles F A) (h0 : (0 : Plane) ∈ F) :
    ∃ φ : ↥(F.erase 0) → Plane → ℝ,
      (∀ f x, 0 ≤ φ f x ∧ φ f x ≤ 1) ∧
      (∀ x, tileIndicator ℝ A x + ∑ f, φ f x = 1) ∧
      ∀ f, Function.Periodic (φ f) (F.card.factorial • (f : Plane)) := by
  exact PeriodicTilingThree.exists_ungrouped_directional_limits h0
    (fun x => tileIndicator_nonneg A x) (fun x => tileIndicator_le_one A x)
    (fun k x => h.sum_tileIndicator_dilate_factorial k x)

theorem exists_grouped_directional_functions {ι : Type uι} [Fintype ι]
    (v : ι → Plane) (hv : ∀ i, v i ≠ 0) (φ : ι → Plane → ℝ)
    (hφ : ∀ i x, 0 ≤ φ i x) (hp : ∀ i, Function.Periodic (φ i) (v i))
    {a : Plane → ℝ} (ha : ∀ x, 0 ≤ a x)
    (hsum : ∀ x, a x + ∑ i, φ i x = 1) :
    ∃ (m : ℕ) (w : Fin m → Plane) (ψ : Fin m → Plane → ℝ),
      (∀ j, w j ≠ 0) ∧
      (∀ i j, i ≠ j → planeDet (w i) (w j) ≠ 0) ∧
      (∀ j x, 0 ≤ ψ j x ∧ ψ j x ≤ 1) ∧
      (∀ x, a x + ∑ j, ψ j x = 1) ∧
      ∀ j, Function.Periodic (ψ j) (w j) := by
  classical
  let r : Setoid ι :=
    { r := fun i j => planeDet (v i) (v j) = 0
      iseqv := ⟨fun i => planeDet_self (v i),
        fun {i j} hij => by rw [planeDet_swap, hij, neg_zero],
        fun {i j k} hij hjk => planeDet_zero_trans (hv j) hij hjk⟩ }
  let Q := Quotient r
  let : Fintype Q := Fintype.ofFinite Q
  let cls : ι → Q := Quotient.mk r
  let fiber (j : Q) : Finset ι := Finset.univ.filter (fun i => cls i = j)
  have mem_fiber (i : ι) (j : Q) : i ∈ fiber j ↔ cls i = j := by
    simp [fiber]
  have out_mem (j : Q) : j.out ∈ fiber j :=
    (mem_fiber _ _).2 (Quotient.out_eq j)
  have hex (j : Q) : ∃ w : Plane, w ≠ 0 ∧ ∀ i ∈ fiber j, ∃ n : ℤ, w = n • v i := by
    have himage : ((fiber j).image v).Nonempty :=
      ⟨v j.out, Finset.mem_image_of_mem v (out_mem j)⟩
    obtain ⟨w, hw, hm⟩ := exists_common_collinear_multiple ((fiber j).image v) himage
      (by
        intro z hz
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
        exact hv i)
      (by
        intro z hz z' hz'
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hz'
        exact Quotient.exact (((mem_fiber i j).1 hi).trans ((mem_fiber i' j).1 hi').symm))
    exact ⟨w, hw, fun i hi => hm (v i) (Finset.mem_image_of_mem v hi)⟩
  choose w hw hm using hex
  let ψ : Q → Plane → ℝ := fun j x => ∑ i ∈ fiber j, φ i x
  have hψ (j : Q) (x : Plane) : 0 ≤ ψ j x :=
    Finset.sum_nonneg (fun i _ => hφ i x)
  have htotal (x : Plane) : (∑ j, ψ j x) = ∑ i, φ i x := by
    simp only [ψ, fiber, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single (cls i)]
    · simp only [ite_true]
    · intro j _ hji
      exact ite_eq_right (Ne.symm hji)
    · intro hi
      exact False.elim (hi (Finset.mem_univ _))
  have hψone (j : Q) (x : Plane) : ψ j x ≤ 1 := by
    have hj : ψ j x ≤ ∑ j', ψ j' x :=
      Finset.single_le_sum (fun j' _ => hψ j' x) (Finset.mem_univ j)
    rw [htotal] at hj
    linarith [hsum x, ha x]
  have hper (j : Q) : Function.Periodic (ψ j) (w j) := by
    intro x
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨n, hn⟩ := hm j i hi
    rw [hn]
    exact (hp i).zsmul n x
  have hpair (j k : Q) (hjk : j ≠ k) : planeDet (w j) (w k) ≠ 0 := by
    intro hdet
    obtain ⟨n, hn⟩ := hm j j.out (out_mem j)
    obtain ⟨m, hmk⟩ := hm k k.out (out_mem k)
    have hn0 : n ≠ 0 := by
      intro hn0
      exact hw j (by simpa [hn0] using hn)
    have hm0 : m ≠ 0 := by
      intro hm0
      exact hw k (by simpa [hm0] using hmk)
    rw [hn, hmk, planeDet_zsmul_left, planeDet_zsmul_right] at hdet
    have hz : planeDet (v j.out) (v k.out) = 0 :=
      (mul_eq_zero.mp ((mul_eq_zero.mp hdet).resolve_left hn0)).resolve_left hm0
    apply hjk
    calc
      j = cls j.out := (Quotient.out_eq j).symm
      _ = cls k.out := Quotient.sound hz
      _ = k := Quotient.out_eq k
  let e : Fin (Fintype.card Q) ≃ Q := (Fintype.equivFin Q).symm
  refine ⟨Fintype.card Q, fun j => w (e j), fun j => ψ (e j),
    fun j => hw (e j), ?_, ?_, ?_, fun j => hper (e j)⟩
  · intro i j hij
    exact hpair (e i) (e j) (fun he => hij (e.injective he))
  · intro j x
    exact ⟨hψ (e j) x, hψone (e j) x⟩
  · intro x
    rw [e.sum_comp (fun j => ψ j x), htotal]
    exact hsum x

theorem Tiles.exists_directional_decomposition {F : Finset Plane} {A : Set Plane}
    (h : Tiles F A) (h0 : (0 : Plane) ∈ F) :
    ∃ (m : ℕ) (v : Fin m → Plane) (φ : Fin m → Plane → ℝ),
      (∀ j, v j ≠ 0) ∧
      (∀ i j, i ≠ j → planeDet (v i) (v j) ≠ 0) ∧
      (∀ j x, 0 ≤ φ j x ∧ φ j x ≤ 1) ∧
      (∀ x, tileIndicator ℝ A x + ∑ j, φ j x = 1) ∧
      ∀ j, Function.Periodic (φ j) (v j) := by
  classical
  obtain ⟨φ, hφ, hsum, hp⟩ := h.exists_ungrouped_directional_limits h0
  apply exists_grouped_directional_functions
    (fun f : ↥(F.erase 0) => F.card.factorial • (f : Plane)) _ φ
    (fun f x => (hφ f x).1) hp (fun x => tileIndicator_nonneg A x) hsum
  intro f
  have hq : (F.card.factorial : ℤ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero F.card
  simpa only [natCast_zsmul] using
    zsmul_plane_ne_zero hq (Finset.mem_erase.mp f.property).1

end PeriodicTilingThree

end

end OAI
