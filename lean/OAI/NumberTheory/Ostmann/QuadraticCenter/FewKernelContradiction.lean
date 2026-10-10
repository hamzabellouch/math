import OAI.NumberTheory.Ostmann.Quadratic.KernelPopulationRetention
import OAI.NumberTheory.Ostmann.ZeroDensity.PagePairCapacity
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticPopulationContradiction

namespace OAI

/-! # Few squarefree kernels cannot support two large prime-difference sets

The kernel-count hypotheses are geometric intermediate data. The contradiction
uses only the previously identified published analytic inputs.
-/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem few_kernel_populations_impossible (P : PublishedProgressionInput)
    (H : PublishedRealZeroInput P) (hSiegel : PublishedSiegelBound)
    (C : ℝ) (hM : MertensLowerBound C) (a : ℝ) (ha : 0 < a) :
    ∃ η L₀ : ℝ, 0 < η ∧ η ≤ 1 / 1000 ∧ 0 < L₀ ∧
      ∀ L : ℝ, L₀ ≤ L → ∀ (S T : Finset ℤ) (f g : ℤ → ℤ)
        (r s : ℤ → ℕ) (m : ℕ) (h : ℤ),
        0 < m → (m : ℝ) ≤ Real.exp (η * L) → h.natAbs.Coprime m →
        ((S.image f).card : ℝ) ≤ Real.exp (3 * (η / 100) * L) →
        ((T.image g).card : ℝ) ≤ Real.exp (3 * (η / 100) * L) →
        (∀ x ∈ S, f x ≠ 0 ∧ Squarefree (f x).natAbs ∧
          f x * (r x : ℤ) ^ 2 = (m : ℤ) * x - h) →
        (∀ y ∈ T, g y ≠ 0 ∧ Squarefree (g y).natAbs ∧
          g y * (s y : ℤ) ^ 2 = (m : ℤ) * y - h) →
        (∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
        (∀ x ∈ T, ∀ y ∈ T, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
        (∀ x ∈ S, ∀ y ∈ T, (x - y).natAbs.Prime ∧
          kernelSplitCutoff η L < (x - y).natAbs) →
        a * Real.exp (L / 2) / L ^ 6 ≤ S.card →
        a * Real.exp (L / 2) / L ^ 6 ≤ T.card → False := by
  obtain ⟨η, L₁, hη, hηU, hL₁, hno⟩ :=
    no_large_nonexceptional_quadratic_populations P H hSiegel C hM
  obtain ⟨E, L₂, hE, hL₂, hpage⟩ := exists_page_population_decay
  have hret := eventual_populated_kernel_retention η (η / 100) a hη hηU
    (by positivity) le_rfl ha
  have hcap := eventual_page_pair_capacity (a / 2) E (by positivity)
  obtain ⟨L₃, hL₃⟩ := eventually_atTop.mp (hret.and hcap)
  let L₀ := max L₁ (max L₂ (max L₃ 1000))
  refine ⟨η, L₀, hη, hηU, lt_of_lt_of_le hL₁ (le_max_left _ _), ?_⟩
  intro L hL S T f g r s m h hm hmU hred hcountS hcountT hf hg hspanS hspanT hcross hsizeS hsizeT
  have hLbase : L₁ ≤ L := (le_max_left _ _).trans hL
  have hLpage : L₂ ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLret : L₃ ≤ L := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have hL1000 : 1000 ≤ L := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have hLpos : 0 < L := by linarith
  let U := populatedKernelPoints S f (fun u => |(u : ℝ)| ≤ Real.exp (η * L))
    (kernelSplitCutoff η L)
  let V := populatedKernelPoints T g (fun v => |(v : ℝ)| ≤ Real.exp (η * L))
    (kernelSplitCutoff η L)
  have hUS : U ⊆ S := populatedKernelPoints_subset _ _ _ _
  have hVT : V ⊆ T := populatedKernelPoints_subset _ _ _ _
  have hsmallS (x : ℤ) (hx : x ∈ U) : ((f x).natAbs : ℝ) ≤ Real.exp (η * L) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using (Finset.mem_filter.mp hx).2.1
  have hsmallT (y : ℤ) (hy : y ∈ V) : ((g y).natAbs : ℝ) ≤ Real.exp (η * L) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using (Finset.mem_filter.mp hy).2.1
  have hcop (x : ℤ) (hx : x ∈ U) (y : ℤ) (hy : y ∈ V) :
      (f x).natAbs.Coprime (g y).natAbs := by
    apply quadratic_kernels_coprime m h x y (f x) (g y) (r x) (s y)
      (hf x (hUS hx)).1 hred (hf x (hUS hx)).2.2 (hg y (hVT hy)).2.2
      (hcross x (hUS hx) y (hVT hy)).1
    exact (small_kernel_le_split_cutoff η L (f x) hηU hLpos.le (hsmallS x hx)).trans_lt
      (hcross x (hUS hx) y (hVT hy)).2
  have hbad := hpage P (kernelConductorCutoff η L) L η hLpage hηU U V f g r s m h hm hmU
    (fun x hx => (hf x (hUS hx)).1) (fun y hy => (hg y (hVT hy)).1) hred
    (fun x hx => (hf x (hUS hx)).2.2) (fun y hy => (hg y (hVT hy)).2.2)
    (fun x hx y hy => hspanS x (hUS hx) y (hUS hy))
    (fun x hx y hy => hspanT x (hVT hx) y (hVT hy)) hcop
  have hretain := (hL₃ L hLret).1
  have hU : (a / 2) * Real.exp (L / 2) / L ^ 6 ≤ U.card :=
    hretain S f r m h hm hmU hred hcountS (fun x hx => (hf x hx).2.2) hspanS hsizeS
  have hV : (a / 2) * Real.exp (L / 2) / L ^ 6 ≤ V.card :=
    hretain T g s m h hm hmU hred hcountT (fun y hy => (hg y hy).2.2) hspanT hsizeT
  have hlarge : E * (Real.exp L / L ^ 40) < (U.card : ℝ) * V.card := by
    apply (hL₃ L hLret).2.trans_le
    rw [pow_two]
    exact mul_le_mul hU hV (by positivity) (by positivity)
  obtain ⟨x, hx, y, hy, hout⟩ := exists_nonexceptional_endpoint_pair U V f g
    (fun d => d ∈ pageKernelExclusion P (kernelConductorCutoff η L) (L ^ 100))
    (E * (Real.exp L / L ^ 40)) hbad hlarge
  have hqx := (populatedKernelPoints_fiber S f
    (fun u => |(u : ℝ)| ≤ Real.exp (η * L)) (kernelSplitCutoff η L)
    (Finset.mem_image_of_mem f hx)).2.1
  have hqy := (populatedKernelPoints_fiber T g
    (fun v => |(v : ℝ)| ≤ Real.exp (η * L)) (kernelSplitCutoff η L)
    (Finset.mem_image_of_mem g hy)).2.1
  apply hno L hLbase (S.filter fun z => f z = f x) (T.filter fun z => g z = g y)
    r s m h (f x) (g y) hm hred (hf x (hUS hx)).1 (hg y (hVT hy)).1
    (hf x (hUS hx)).2.1 (hg y (hVT hy)).2.1 hmU (hsmallS x hx) (hsmallT y hy)
    _ _ _ _ _ hout hqx hqy
  · intro z hz
    obtain ⟨hz, heq⟩ := Finset.mem_filter.mp hz
    simpa only [heq] using (hf z hz).2.2
  · intro z hz
    obtain ⟨hz, heq⟩ := Finset.mem_filter.mp hz
    simpa only [heq] using (hg z hz).2.2
  · intro z hz w hw
    exact hspanS z (Finset.mem_filter.mp hz).1 w (Finset.mem_filter.mp hw).1
  · intro z hz w hw
    exact hspanT z (Finset.mem_filter.mp hz).1 w (Finset.mem_filter.mp hw).1
  · intro z hz w hw
    exact hcross z (Finset.mem_filter.mp hz).1 w (Finset.mem_filter.mp hw).1

end Ostmann

end OAI
