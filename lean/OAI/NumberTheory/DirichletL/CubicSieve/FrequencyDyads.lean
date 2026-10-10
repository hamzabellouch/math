import OAI.NumberTheory.DirichletL.CubicSieve.DualShell

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def frequencyDyad (j : ℕ) : Finset O :=
  (elementRange ((2 : ℝ)^j)).filter (fun h => Nat.clog 2 (Ideal.absNorm (Ideal.span {h})) = j)

lemma mem_frequencyDyad (h : O) (j : ℕ) :
    h ∈ frequencyDyad j ↔ h ≠ 0 ∧ Nat.clog 2 (Ideal.absNorm (Ideal.span {h})) = j := by
  simp only [frequencyDyad, Finset.mem_filter, mem_elementRange]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · rintro ⟨hh, hj⟩
    refine ⟨⟨hh, ?_⟩, hj⟩
    have hu := Nat.le_pow_clog (by norm_num : 1 < 2) (Ideal.absNorm (Ideal.span {h}))
    rw [hj] at hu
    exact_mod_cast hu

lemma frequencyDyad_bounds (j : ℕ) (h : O) (hh : h ∈ frequencyDyad j) :
    h ≠ 0 ∧ (2 : ℝ)^j / 2 ≤ (Ideal.absNorm (Ideal.span {h}) : ℝ) ∧
      (Ideal.absNorm (Ideal.span {h}) : ℝ) ≤ (2 : ℝ)^j := by
  obtain ⟨hn, hj⟩ := (mem_frequencyDyad h j).mp hh
  have hnorm : Ideal.absNorm (Ideal.span {h}) ≠ 0 := by
    exact Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hn)
  have hu := Nat.le_pow_clog (by norm_num : 1 < 2) (Ideal.absNorm (Ideal.span {h}))
  have hl := two_pow_clog_le_double _ (Nat.one_le_iff_ne_zero.mpr hnorm)
  rw [hj] at hu hl
  refine ⟨hn, ?_, by exact_mod_cast hu⟩
  have hr : (2 : ℝ)^j ≤ 2 * (Ideal.absNorm (Ideal.span {h}) : ℝ) := by exact_mod_cast hl
  linarith

def frequencyDyadicEquiv : {h : O // h ≠ 0} ≃ Σ j : ℕ, frequencyDyad j where
  toFun h := ⟨Nat.clog 2 (Ideal.absNorm (Ideal.span {h.val})),
    ⟨h.val, (mem_frequencyDyad _ _).mpr ⟨h.property, rfl⟩⟩⟩
  invFun h := ⟨h.2.val, ((mem_frequencyDyad _ _).mp h.2.property).1⟩
  left_inv h := by cases h; rfl
  right_inv h := by
    rcases h with ⟨j, h, hh⟩
    have hj := ((mem_frequencyDyad h j).mp hh).2
    dsimp only
    subst j
    rfl

theorem tsum_frequencyDyads (f : O → ℂ) (hf : Summable f) (hzero : f 0 = 0) :
    (∑' h : O, f h) = ∑' j : ℕ, ∑ h : frequencyDyad j, f h.val := by
  have he : (∑' h : O, f h) = ∑' h : {h : O // h ≠ 0}, f h.val := by
    symm
    exact tsum_subtype_eq_of_support_subset (fun h hh => by
      change h ≠ 0
      intro hz
      exact hh (hz ▸ hzero))
  rw [he]
  let g := (fun h : {h : O // h ≠ 0} => f h.val) ∘ frequencyDyadicEquiv.symm
  have hg : Summable g := frequencyDyadicEquiv.symm.summable_iff.mpr (hf.subtype _)
  calc
    _ = ∑' h, g h := (frequencyDyadicEquiv.symm.tsum_eq _).symm
    _ = ∑' j, ∑' h, g ⟨j,h⟩ := Summable.tsum_sigma' (fun _ => (hasSum_fintype _).summable) hg
    _ = _ := by
      apply tsum_congr
      intro j
      rw [tsum_fintype]
      rfl

theorem tsum_frequencyDyads_with_zero (f : O → ℂ) (hf : Summable f) :
    (∑' h : O, f h) = f 0 + ∑' j : ℕ, ∑ h : frequencyDyad j, f h.val := by
  have he : (∑' h : O, f h) = f 0 + ∑' h : {h : O // h ≠ 0}, f h.val := by
    have hs := (hf.sum_add_tsum_compl (s := {0})).symm
    have hset : ((↑({0} : Finset O) : Set O)ᶜ) = {h : O | h ≠ 0} := by
      ext h
      simp
    rw [hset] at hs
    simpa only [Finset.sum_singleton, Set.coe_ofPred] using hs
  rw [he]
  congr 1
  let g := (fun h : {h : O // h ≠ 0} => f h.val) ∘ frequencyDyadicEquiv.symm
  have hg : Summable g := frequencyDyadicEquiv.symm.summable_iff.mpr (hf.subtype _)
  calc
    _ = ∑' h, g h := (frequencyDyadicEquiv.symm.tsum_eq _).symm
    _ = ∑' j, ∑' h, g ⟨j,h⟩ := Summable.tsum_sigma' (fun _ => (hasSum_fintype _).summable) hg
    _ = _ := by
      apply tsum_congr
      intro j
      rw [tsum_fintype]
      rfl

end
end SevenEighths.CubicSieve

end OAI
