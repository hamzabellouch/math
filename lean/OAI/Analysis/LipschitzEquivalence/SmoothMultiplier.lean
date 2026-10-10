import OAI.Analysis.LipschitzEquivalence.BlockSelection

namespace OAI

universe uH uIndex

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem abs_prod_le_one {ι : Type uIndex} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1) : |∏ i ∈ s, a i| ≤ 1 := by
  rw [Finset.abs_prod]
  exact (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) ha).trans_eq (by simp)

theorem abs_prod_sub_prod_le {ι : Type uIndex} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1) (hb : ∀ i ∈ s, |b i| ≤ 1) :
    |(∏ i ∈ s, a i)-(∏ i ∈ s, b i)| ≤ ∑ i ∈ s, |a i-b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have ha' : ∀ j ∈ s, |a j| ≤ 1 := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hb' : ∀ j ∈ s, |b j| ≤ 1 := fun j hj => hb j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi,Finset.prod_insert hi,Finset.sum_insert hi]
    have he : a i*(∏ j ∈ s, a j)-b i*(∏ j ∈ s, b j) =
        a i*((∏ j ∈ s, a j)-(∏ j ∈ s, b j))+(a i-b i)*(∏ j ∈ s, b j) := by ring
    rw [he]
    calc
      _ ≤ |a i| * |(∏ j ∈ s, a j)-(∏ j ∈ s, b j)|+|a i-b i| * |∏ j ∈ s, b j| := by
        simpa only [abs_mul] using abs_add_le (a i*((∏ j ∈ s, a j)-(∏ j ∈ s, b j)))
          ((a i-b i)*(∏ j ∈ s, b j))
      _ ≤ (∑ j ∈ s, |a j-b j|)+|a i-b i| := by
        apply add_le_add
        · exact (mul_le_mul_of_nonneg_right (ha i (Finset.mem_insert_self _ _)) (abs_nonneg _)).trans
            (by simpa using ih ha' hb')
        · simpa using mul_le_mul_of_nonneg_left (abs_prod_le_one s b hb') (abs_nonneg (a i-b i))
      _ = _ := add_comm _ _

def damping {ι : Type uIndex} (s : Finset ι) (z : ι → Smooth H) (x : H) : ℝ :=
  ∏ i ∈ s, (1-‖Smooth.grad x (z i)‖)

theorem damping_nonneg {ι : Type uIndex} (s : Finset ι) (z : ι → Smooth H)
    (hz : ∀ i ∈ s, LipschitzWith 1 (z i).val) (x : H) : 0 ≤ damping s z x := by
  apply Finset.prod_nonneg
  intro i hi
  have h := (z i).grad_norm_le (hz i hi) x
  norm_num only [NNReal.coe_one] at h
  linarith

theorem damping_le_one {ι : Type uIndex} (s : Finset ι) (z : ι → Smooth H)
    (hz : ∀ i ∈ s, LipschitzWith 1 (z i).val) (x : H) : damping s z x ≤ 1 := by
  have hn (i : ι) (hi : i ∈ s) : 0 ≤ 1-‖Smooth.grad x (z i)‖ := by
    have h := (z i).grad_norm_le (hz i hi) x
    norm_num only [NNReal.coe_one] at h
    linarith
  have hp : (∏ i ∈ s, (1-‖Smooth.grad x (z i)‖)) ≤ ∏ _i ∈ s, (1:ℝ) :=
    Finset.prod_le_prod₀ hn (fun i _ => sub_le_self _ (norm_nonneg _))
  simpa only [damping,Finset.prod_const_one] using hp

theorem one_sub_damping_le {ι : Type uIndex} (s : Finset ι) (z : ι → Smooth H)
    (hz : ∀ i ∈ s, LipschitzWith 1 (z i).val) (x : H) :
    1-damping s z x ≤ ∑ i ∈ s, ‖Smooth.grad x (z i)‖ := by
  have h := abs_prod_sub_prod_le s (fun _ => (1:ℝ)) (fun i => 1-‖Smooth.grad x (z i)‖)
    (fun _ _ => by norm_num) (fun i hi => by
      have h := (z i).grad_norm_le (hz i hi) x
      norm_num only [NNReal.coe_one] at h
      rw [abs_le]; constructor <;> linarith [norm_nonneg (Smooth.grad x (z i))])
  simp only [Finset.prod_const_one,sub_sub_cancel,abs_norm] at h
  exact (le_abs_self _).trans h

theorem exists_smooth_multiplier {ι : Type uIndex} [Fintype ι] (z : ι → Smooth H)
    (hz : ∀ i, LipschitzWith 1 (z i).val) (Q : Set H) (hQ : IsCompact Q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : Smooth H, ∃ D : ℝ, 0 < D ∧
      (∀ x, |φ.val x-damping Finset.univ z x| ≤ ε) ∧
      ∀ x ∈ Q, ‖Smooth.grad x φ‖ ≤ D := by
  classical
  let δ : ℝ := min (1/2) (ε/((Fintype.card ι : ℝ)+1))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hδe : (Fintype.card ι : ℝ)*δ ≤ ε := by
    have h := min_le_right (1/2:ℝ) (ε/((Fintype.card ι : ℝ)+1))
    have hd : 0 < (Fintype.card ι : ℝ)+1 := by positivity
    have hmul := (le_div_iff₀ hd).mp h
    change δ*((Fintype.card ι : ℝ)+1) ≤ ε at hmul
    nlinarith
  let φ : Smooth H := ⟨fun x => ∏ i, (1-regularNorm δ (Smooth.grad x (z i))), by
    change ContDiff ℝ ∞ (fun x => ∏ i, (1-regularNorm δ (Smooth.grad x (z i))))
    apply contDiff_prod
    intro i _
    exact contDiff_const.sub ((regularNorm_contDiff hδ.ne').comp (z i).grad_contDiff)⟩
  have happ (x : H) : |φ.val x-damping Finset.univ z x| ≤ ε := by
    have ha (i : ι) : |1-regularNorm δ (Smooth.grad x (z i))| ≤ 1 := by
      have hn := (z i).grad_norm_le (hz i) x
      norm_num only [NNReal.coe_one] at hn
      have hr := regularNorm_le δ hδ.le (Smooth.grad x (z i))
      have hr0 := regularNorm_nonneg δ (Smooth.grad x (z i))
      rw [abs_le]; constructor <;> linarith
    have hb (i : ι) : |1-‖Smooth.grad x (z i)‖| ≤ 1 := by
      have hn := (z i).grad_norm_le (hz i) x
      norm_num only [NNReal.coe_one] at hn
      rw [abs_le]; constructor <;> linarith [norm_nonneg (Smooth.grad x (z i))]
    have hd (i : ι) : |(1-regularNorm δ (Smooth.grad x (z i)))-(1-‖Smooth.grad x (z i)‖)| ≤ δ := by
      have h₁ := norm_le_regularNorm δ (Smooth.grad x (z i))
      have h₂ := regularNorm_le δ hδ.le (Smooth.grad x (z i))
      rw [abs_le]; constructor <;> linarith
    exact (abs_prod_sub_prod_le Finset.univ _ _ (fun i _ => ha i) (fun i _ => hb i)).trans
      ((Finset.sum_le_sum (fun i _ => hd i)).trans (by simpa using hδe))
  obtain ⟨D,hD⟩ := hQ.exists_bound_of_continuousOn φ.grad_continuous.continuousOn
  exact ⟨φ,max D 1,by positivity,happ,fun x hx => (hD x hx).trans (le_max_left _ _)⟩

theorem product_gradient_error {ι : Type uIndex} (s : Finset ι) (z : ι → Smooth H)
    (φ f : Smooth H) {x : H} {D ε : ℝ}
    (hf : ‖Smooth.grad x f‖ ≤ 1) (hφ : ‖Smooth.grad x φ‖ ≤ D)
    (happrox : |φ.val x-damping s z x| ≤ ε/2)
    (hsmall : |f.val x| * D ≤ ε/2) :
    ‖Smooth.grad x (φ.mul f)-damping s z x • Smooth.grad x f‖ ≤ ε := by
  rw [Smooth.grad_mul]
  have he : φ.val x • Smooth.grad x f+f.val x • Smooth.grad x φ-
      damping s z x • Smooth.grad x f =
      (φ.val x-damping s z x) • Smooth.grad x f+f.val x • Smooth.grad x φ := by module
  rw [he]
  calc
    _ ≤ ‖(φ.val x-damping s z x) • Smooth.grad x f‖+‖f.val x • Smooth.grad x φ‖ := norm_add_le _ _
    _ = |φ.val x-damping s z x| * ‖Smooth.grad x f‖+|f.val x| * ‖Smooth.grad x φ‖ := by simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ |φ.val x-damping s z x|+|f.val x| * D := by
      apply add_le_add
      · simpa using mul_le_mul_of_nonneg_left hf (abs_nonneg _)
      · exact mul_le_mul_of_nonneg_left hφ (abs_nonneg _)
    _ ≤ ε := by linarith

end LipschitzCounterexample.CompactWSC
end

end OAI
