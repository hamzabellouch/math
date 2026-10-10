import OAI.NumberTheory.DirichletL.Hecke.BoundaryIntegration
import OAI.NumberTheory.DirichletL.Detector
import Mathlib.Analysis.Analytic.Order

namespace OAI

noncomputable section
open Set Filter
open scoped Classical Topology
namespace SevenEighths.HeckeDetectorZeros
open HeckeFamily

def rectangle (T : ℝ) : Set ℂ :=
  {s | (51/100 : ℝ) ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T}

theorem rectangle_compact (T : ℝ) : IsCompact (rectangle T) := by
  have heq : rectangle T = Set.Icc (51/100 : ℝ) 1 ×ℂ Set.Icc (-T) T := by
    ext z
    simp only [rectangle, Set.mem_ofPred_eq, Complex.mem_reProdIm, Set.mem_Icc, abs_le]
    tauto
  rw [heq]
  exact isCompact_Icc.reProdIm isCompact_Icc

def zeros (χ : Character) (T : ℝ) : Set ℂ := {s ∈ rectangle T | LFunction χ s = 0}

theorem zeros_finite (χ : Character) (hχ : χ.residue ≠ 1) (T : ℝ) :
    (zeros χ T).Finite := by
  have ha : AnalyticOnNhd ℂ (LFunction χ) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (LFunction_entire_nonprincipal χ hχ)
  have hcod := ha.preimage_zero_mem_codiscreteWithin
    (LFunction_ne_zero_of_one_lt_re χ (by norm_num : 1 < (2 : ℂ).re))
    (Set.mem_univ (2 : ℂ)) isConnected_univ
  have hfin := (rectangle_compact T).finite_sdiff_of_mem_codiscreteWithin
    (codiscreteWithin_mono (Set.subset_univ (rectangle T)) hcod)
  convert hfin using 1
  ext s
  simp [zeros]

def zeroFinset (χ : Character) (hχ : χ.residue ≠ 1) (T : ℝ) : Finset ℂ :=
  (zeros_finite χ hχ T).toFinset

@[simp] theorem mem_zeroFinset (χ : Character) (hχ : χ.residue ≠ 1) (T : ℝ) (s : ℂ) :
    s ∈ zeroFinset χ hχ T ↔
      (51/100 : ℝ) ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T ∧ LFunction χ s = 0 := by
  simp only [zeroFinset, Set.Finite.mem_toFinset, zeros, rectangle, Set.mem_ofPred_eq]
  tauto

variable {ι : Type*} [Fintype ι]

def familyZeros (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) :
    Finset (ι × ℂ) :=
  Finset.univ.biUnion (fun i => (zeroFinset (χ i) (hχ i) T).image (fun s => (i,s)))

@[simp] theorem mem_familyZeros (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1)
    (T : ℝ) (i : ι) (s : ℂ) :
    (i,s) ∈ familyZeros χ hχ T ↔
      (51/100 : ℝ) ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T ∧ LFunction (χ i) s = 0 := by
  simp [familyZeros]

def realParts (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) : Finset ℝ :=
  insert (51/100) ((familyZeros χ hχ T).image (fun p => p.2.re))

theorem realParts_nonempty (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) :
    (realParts χ hχ T).Nonempty := Finset.insert_nonempty _ _

def zeroMaximum (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) : ℝ :=
  (realParts χ hχ T).max' (realParts_nonempty χ hχ T)

theorem zeroMaximum_mem (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) :
    zeroMaximum χ hχ T ∈ realParts χ hχ T := Finset.max'_mem _ _

theorem zeroMaximum_bounds (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) :
    (51/100 : ℝ) ≤ zeroMaximum χ hχ T ∧ zeroMaximum χ hχ T ≤ 1 := by
  constructor
  · exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  · apply Finset.max'_le
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · norm_num
    · obtain ⟨⟨i,s⟩, hs, rfl⟩ := Finset.mem_image.mp hx
      exact (mem_familyZeros χ hχ T i s |>.mp hs).2.1

theorem zero_re_le_maximum (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1)
    (T : ℝ) (i : ι) {s : ℂ} (hs : (51/100 : ℝ) ≤ s.re)
    (ht : |s.im| ≤ T) (hz : LFunction (χ i) s = 0) : s.re ≤ zeroMaximum χ hχ T := by
  have hle : s.re ≤ 1 := by
    by_contra hn
    exact LFunction_ne_zero_of_one_lt_re (χ i) (lt_of_not_ge hn) hz
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨(i,s), (mem_familyZeros χ hχ T i s).mpr ⟨hs, hle, ht, hz⟩, rfl⟩)

theorem maximum_attained (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ)
    (hmax : (51/100 : ℝ) < zeroMaximum χ hχ T) :
    ∃ i s, LFunction (χ i) s = 0 ∧ |s.im| ≤ T ∧ s.re = zeroMaximum χ hχ T := by
  have hm := zeroMaximum_mem χ hχ T
  rcases Finset.mem_insert.mp hm with hm | hm
  · exact False.elim ((ne_of_gt hmax) hm)
  · obtain ⟨⟨i,s⟩, hs, heq⟩ := Finset.mem_image.mp hm
    have hz := (mem_familyZeros χ hχ T i s).mp hs
    exact ⟨i,s,hz.2.2.2,hz.2.2.1,heq⟩

theorem zeroMaximum_mono (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1)
    {T T' : ℝ} (hT : T ≤ T') : zeroMaximum χ hχ T ≤ zeroMaximum χ hχ T' := by
  rcases lt_or_ge (51/100 : ℝ) (zeroMaximum χ hχ T) with hm | hm
  · obtain ⟨i,s,hz,ht,heq⟩ := maximum_attained χ hχ T hm
    rw [← heq]
    apply zero_re_le_maximum χ hχ T' i _ (ht.trans hT) hz
    rw [heq]
    exact hm.le
  · exact hm.trans (zeroMaximum_bounds χ hχ T').1

theorem nonzero_on_buffered_disk (χ : ι → Character) (hχ : ∀ j, (χ j).residue ≠ 1)
    (T a e : ℝ) (i : ℕ) (hT : 2 < T) (ha : (51/100 : ℝ) ≤ a) (he : 0 < e)
    (hmax : zeroMaximum χ hχ (3*(i+1 : ℕ)*T) < a+2*e)
    (j : ι) (t : ℝ) (ht : |t| ≤ (3*i+2 : ℕ)*T)
    {s : ℂ} (hs : s ∈ Metric.closedBall ((2 : ℂ)+t*Complex.I) (2-a-2*e)) :
    LFunction (χ j) s ≠ 0 := by
  have hn : ‖s-((2 : ℂ)+t*Complex.I)‖ ≤ 2-a-2*e := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hs
  have hr := Complex.abs_re_le_norm (s-((2 : ℂ)+t*Complex.I))
  have hi := Complex.abs_im_le_norm (s-((2 : ℂ)+t*Complex.I))
  norm_num at hr hi
  have hre : a+2*e ≤ s.re := by linarith [(abs_le.mp (hr.trans hn)).1]
  have him : |s.im| ≤ 3*(i+1 : ℕ)*T := by
    have ht' := abs_add_le (s.im-t) t
    rw [sub_add_cancel] at ht'
    push_cast at ht ⊢
    nlinarith [hi.trans hn]
  intro hz
  have hle := zero_re_le_maximum χ hχ (3*(i+1 : ℕ)*T) j (by linarith) him hz
  linarith

theorem exists_actual_buffered_bin (χ : ι → Character)
    (hχ : ∀ j, (χ j).residue ≠ 1) (T e : ℝ) (hT : 2 < T) (he : 0 < e)
    (n : ℕ) (hn : 0 < n) (hwidth : (49/100 : ℝ) ≤ n*e) :
    ∃ i k : ℕ, 1 ≤ i ∧ i ≤ n ∧
      let a : ℝ := 51/100+e*k
      a ≤ 1 ∧ a ≤ zeroMaximum χ hχ (3*i*T) ∧
      zeroMaximum χ hχ (3*i*T) < a+e ∧
      zeroMaximum χ hχ (3*(i+1 : ℕ)*T) < a+2*e ∧
      (51/100 < a → ∃ j s, LFunction (χ j) s = 0 ∧ a ≤ s.re ∧
        s.re < a+e ∧ |s.im| ≤ 3*i*T) ∧
      (∀ j t, |t| ≤ (3*i+2 : ℕ)*T → ∀ s ∈
        Metric.closedBall ((2 : ℂ)+t*Complex.I) (2-a-2*e), LFunction (χ j) s ≠ 0) := by
  let M : ℕ → ℝ := fun j => zeroMaximum χ hχ (3*(j+1 : ℕ)*T)
  obtain ⟨i,hk,k,hone,hlo,hhi,hnext⟩ := Detector.exists_buffered_bin M hn he
    (fun j _ => zeroMaximum_bounds χ hχ _) hwidth
  refine ⟨i+1,k,by omega,by omega,hone,hlo,hhi,?_,?_,?_⟩
  · exact hnext
  · intro ha
    obtain ⟨j,s,hz,ht,hs⟩ := maximum_attained χ hχ (3*(i+1 : ℕ)*T) (lt_of_lt_of_le ha hlo)
    exact ⟨j,s,hz,by rw [hs]; exact hlo,by rw [hs]; exact hhi,ht⟩
  · intro j t ht s hs
    apply nonzero_on_buffered_disk χ hχ T (51/100+e*k) e (i+1) hT
      (by nlinarith [Nat.cast_nonneg (α := ℝ) k]) he hnext j t ht hs

end SevenEighths.HeckeDetectorZeros

end

end OAI
