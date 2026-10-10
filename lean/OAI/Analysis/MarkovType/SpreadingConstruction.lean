import OAI.Analysis.MarkovType.SelectedRows
import OAI.Analysis.MarkovType.SpreadingLimitReal
import OAI.Analysis.MarkovType.SpreadingModel
import OAI.Analysis.MarkovType.SpreadingCoordinateEmbedding
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology

namespace MarkovSuperreflexivity

private theorem nat_tendsto_atTop_of_id_le (f : ℕ → ℕ) (hf : ∀ n, n ≤ f n) :
    Tendsto f atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  exact Filter.eventually_atTop.2 ⟨b, fun n hn => hn.trans (hf n)⟩

private theorem seminorm_spreading_of_cube (p : Seminorm ℝ C00)
    (hcube : ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
      ∀ a : Fin m → ℝ, (∀ i, |a i| ≤ 1) →
        p (C00.place ι a) = p (C00.ofArray a)) :
    ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
      ∀ a : Fin m → ℝ, p (C00.place ι a) = p (C00.ofArray a) := by
  intro m ι hι a
  let c : ℝ := (∑ i, |a i|) + 1
  have hc : 0 < c := by
    have hsum := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) =>
      abs_nonneg (a i))
    dsimp only [c]
    linarith
  let b : Fin m → ℝ := c⁻¹ • a
  have hab : c • b = a := by simp only [b, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have hb : ∀ i, |b i| ≤ 1 := by
    intro i
    have hi : |a i| ≤ c := by
      have hs := Finset.single_le_sum
        (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => abs_nonneg (a j))
        (Finset.mem_univ i)
      dsimp only [c]
      linarith
    change |c⁻¹ * a i| ≤ 1
    rw [abs_mul, abs_of_pos (inv_pos.mpr hc)]
    calc
      c⁻¹ * |a i| ≤ c⁻¹ * c :=
        mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hc.le)
      _ = 1 := inv_mul_cancel₀ hc.ne'
  have hplace : C00.place ι a = c • C00.place ι b := by
    simpa only [C00.placeLinear_apply, hab] using map_smul (C00.placeLinear ι) c b
  have harray : C00.ofArray a = c • C00.ofArray b := by
    simpa only [C00.arrayLinear_apply, hab] using map_smul (C00.arrayLinear m) c b
  rw [hplace, harray, map_smul_eq_mul p, map_smul_eq_mul p, hcube ι hι b hb]

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem exists_spreadingModel_of_triangular_arrays (d : ℝ) (hd : 0 < d)
    (hrows : ∀ M : ℕ, 0 < M → Nonempty (TriangularArray Y d (M : ℝ)⁻¹ M)) :
    Nonempty (SpreadingModel Y) := by
  classical
  let R : (n : ℕ) → SelectedRow Y d (n + 1) := fun n =>
    Classical.choice (exists_selectedRow d hrows (n + 1) (Nat.succ_pos n))
  let raw : ℕ → C00 →ₗ[ℝ] Y := fun n => (R n).synthesis
  have hraw : ∀ n i, ‖raw n (C00.basis i)‖ ≤ 1 :=
    fun n i => (R n).norm_synthesis_basis_le i
  obtain ⟨σ, hσ, hCauchy⟩ := exists_cauchy_subsequence raw hraw
  let L : ℕ → C00 →ₗ[ℝ] Y := fun n => raw (σ n)
  let p : Seminorm ℝ C00 := SpreadingLimit.limitSeminorm L hCauchy
  have hunit : ∀ n i, ‖L n (C00.basis i)‖ ≤ 1 := fun n i => hraw (σ n) i
  have hσle : ∀ n, n ≤ σ n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => exact Nat.succ_le_of_lt (ih.trans_lt (hσ (Nat.lt_succ_self n)))
  have hkTop : Tendsto (fun n => σ n + 1) atTop atTop :=
    nat_tendsto_atTop_of_id_le _ (fun n => (hσle n).trans (Nat.le_succ _))
  have hMTop : Tendsto (fun n => (R (σ n)).M) atTop atTop :=
    nat_tendsto_atTop_of_id_le _
      (fun n => (hσle n).trans ((Nat.le_succ _).trans (R (σ n)).le_M))
  have hprefix : ∀ x r, d * |prefixCut x r| ≤ p x := by
    intro x r
    obtain ⟨m, a, rfl⟩ := C00.exists_ofArray x
    let error : ℕ → ℝ := fun n => ((R (σ n)).M : ℝ)⁻¹ * coefficientL1 a
    have herror : Tendsto error atTop (𝓝 0) := by
      simpa only [error, Function.comp_apply, mul_zero, zero_mul] using
        ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hMTop).mul tendsto_const_nhds
    apply SpreadingLimit.le_limitSeminorm_of_error L hCauchy
      (C00.ofArray a) (d * |prefixCut (C00.ofArray a) r|) error herror
    apply Filter.eventually_atTop.2
    refine ⟨m, ?_⟩
    intro n hn
    have hm : m ≤ σ n + 1 := hn.trans ((hσle n).trans (Nat.le_succ _))
    exact (R (σ n)).synthesis_prefix_lower hd.le hm a r
  have hupper : ∀ {m : ℕ} (a : Fin m → ℝ), p (C00.ofArray a) ≤ ∑ i, |a i| := by
    intro m a
    exact SpreadingLimit.limitSeminorm_le L hCauchy (C00.ofArray a) (∑ i, |a i|)
      (Filter.Eventually.of_forall (fun n =>
        C00.norm_linearMap_ofArray_le (L n) (hunit n) a))
  have hspreadCube : ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
      ∀ a : Fin m → ℝ, (∀ i, |a i| ≤ 1) →
        p (C00.place ι a) = p (C00.ofArray a) := by
    intro m ι hι a ha
    let K : ℕ := max m ((Finset.univ.sup ι) + 1)
    let error : ℕ → ℝ := fun n => 3 / ((σ n + 1 : ℕ) : ℝ)
    have herror : Tendsto error atTop (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat 3).comp hkTop
    apply SpreadingLimit.limitSeminorm_eq_of_error L hCauchy
      (C00.place ι a) (C00.ofArray a) error herror
    apply Filter.eventually_atTop.2
    refine ⟨K, ?_⟩
    intro n hn
    have hK : K ≤ σ n + 1 := hn.trans ((hσle n).trans (Nat.le_succ _))
    have hm : m ≤ σ n + 1 := (le_max_left _ _).trans hK
    have hιk : ∀ i, ι i < σ n + 1 := by
      intro i
      exact (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))).trans_le
        ((le_max_right _ _).trans hK)
    exact (R (σ n)).synthesis_oscillation hm ι Fin.val hι
      (fun _ _ h => h) hιk (fun i => i.isLt.trans_le hm) a ha
  have hspread : ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
      ∀ a : Fin m → ℝ, p (C00.place ι a) = p (C00.ofArray a) := by
    intro m ι hι a
    exact seminorm_spreading_of_cube p hspreadCube ι hι a
  have hembed : ∀ (m : ℕ) (η : ℝ), 0 < η →
      ∃ T : (Fin m → ℝ) →ₗ[ℝ] Y, ∀ a,
        p (C00.ofArray a) ≤ ‖T a‖ ∧ ‖T a‖ ≤ (1 + η) * p (C00.ofArray a) := by
    intro m η hη
    let q : Seminorm ℝ (Fin m → ℝ) := p.comp (C00.arrayLinear m)
    let S : ℕ → (Fin m → ℝ) →ₗ[ℝ] Y := fun n => (L n).comp (C00.arrayLinear m)
    have hcoord : ∀ a i, (d / 2) * |a i| ≤ q a := by
      intro a i
      simpa only [q, Seminorm.comp_apply, C00.arrayLinear_apply, C00.ofArray_apply] using
        SpreadingLimit.coordinate_lower_of_prefix p d hd.le hprefix (C00.ofArray a) i.val
    have hlip : ∀ n a b, |‖S n a‖ - ‖S n b‖| ≤ ∑ i, |a i - b i| :=
      fun n a b => C00.abs_norm_linearMap_ofArray_sub_le (L n) (hunit n) a b
    have hlim : ∀ a, Tendsto (fun n => ‖S n a‖) atTop (𝓝 (q a)) :=
      fun a => SpreadingLimit.tendsto_limitSeminorm L hCauchy (C00.ofArray a)
    exact exists_coordinate_embedding_of_convergence q d hd hcoord S hlip hlim η hη
  exact ⟨⟨p, d, hd, hprefix, hupper, hspread, hembed⟩⟩

theorem exists_spreadingModel_of_nonreflexive [CompleteSpace Y]
    (hNR : ¬ Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ Y)) :
    Nonempty (SpreadingModel Y) := by
  obtain ⟨d, hd, hrows⟩ := exists_uniform_triangular_arrays hNR
  exact exists_spreadingModel_of_triangular_arrays d hd hrows

end MarkovSuperreflexivity

end

end OAI
