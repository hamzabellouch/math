import Mathlib
import OAI.Probability.SKGap.Localization.GramRobust

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius

theorem compact_gram_path_robust {α κ : Type*} [TopologicalSpace α] [CompactSpace α]
    [Fintype κ] [DecidableEq κ] {a : ℝ} (ha : 0 < a)
    (H : α → Matrix κ κ ℝ) (C₀ : α → ℝ → Matrix κ κ ℝ)
    (hH : Continuous H) (hc₀ : Continuous (Function.uncurry C₀))
    (hherm : ∀ x r, r ∈ Icc 0 a → (C₀ x r).IsHermitian)
    (hzero : ∀ x, C₀ x 0=0)
    (hdet : ∀ x r, r ∈ Icc 0 a → (1-H x*C₀ x r).det ≠ 0) :
    ∃ δ ρ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < ρ ∧
      ∀ x (ι : Type) [Fintype ι] [DecidableEq ι] (Q : Matrix ι κ ℝ)
        (C : Matrix κ κ ℝ), C.IsHermitian → ‖Qᵀ*Q-H x‖ < ρ →
        ‖C-C₀ x a‖ < ρ → ((1-δ) • (1 : Matrix ι ι ℝ)-Q*C*Qᵀ).PosDef := by
  let F := fun (p : ℝ × (Matrix κ κ ℝ × Matrix κ κ ℝ)) (z : α × ℝ) =>
    (1-((1-p.1)⁻¹ • (H z.1+p.2.1)) * (C₀ z.1 z.2+(z.2/a) • p.2.2)).det
  have hnear : ∀ᶠ p in 𝓝 (0,(0,0)), ∀ z ∈ (univ : Set α) ×ˢ Icc 0 a, F p z ≠ 0 := by
    apply (isCompact_univ.prod isCompact_Icc).eventually_forall_of_forall_eventually
    intro z hz
    have hbase : F (0,(0,0)) z ≠ 0 := by
      simpa only [F,sub_zero,inv_one,one_smul,smul_zero,add_zero] using hdet z.1 z.2 hz.2
    have hc : ContinuousAt (fun z => F z.1 z.2) ((0,(0,0)),z) := by
      unfold F
      have hc' : Continuous (fun z : (ℝ × (Matrix κ κ ℝ × Matrix κ κ ℝ)) × (α × ℝ) =>
          C₀ z.2.1 z.2.2) := hc₀.comp continuous_snd
      fun_prop (disch := norm_num)
    exact hc.eventually (eventually_ne_nhds hbase)
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let δ := min (ε/2) (1/2)
  have hδ : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hδε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  refine ⟨δ,ε,hδ,hδ1,hε,?_⟩
  intro x ι _ _ Q C hC hQ hCC
  have hin : dist (δ,(Qᵀ*Q-H x,C-C₀ x a)) (0,(0,0)) < ε := by
    simp only [Prod.dist_eq,dist_zero_right,Real.norm_eq_abs,abs_of_pos hδ,max_lt_iff]
    exact ⟨hδε,hQ,hCC⟩
  have hh := hball hin
  let D := fun r => C₀ x r+(r/a) • (C-C₀ x a)
  have hc : Continuous D := by
    have hx : Continuous (fun r => C₀ x r) := hc₀.comp (continuous_const.prodMk continuous_id)
    unfold D
    fun_prop
  have hhD : ∀ r ∈ Icc 0 a, (D r).IsHermitian := by
    intro r hr
    exact (hherm x r hr).add
      ((hC.sub (hherm x a ⟨ha.le,le_rfl⟩)).smul (R := ℝ) (isSelfAdjoint_iff.mpr (star_trivial (r/a))))
  have hz : D 0=0 := by simp [D,hzero]
  have heq : D a=C := by simp [D,div_self ha.ne']
  rw [← heq]
  apply positive_from_gram_path ha.le (sub_pos.mpr hδ1) Q D hc hhD hz
  intro r hr
  simpa only [F,add_sub_cancel] using hh (x,r) ⟨mem_univ _,hr⟩
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius

variable {κ ν : Type*} [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]

def augmentedGram (H : Matrix κ κ ℝ) : Matrix (κ ⊕ ν) (κ ⊕ ν) ℝ :=
  fromBlocks H 0 0 1

def augmentedCoefficient (C : Matrix κ κ ℝ) (V : Matrix κ ν ℝ) :
    Matrix (κ ⊕ ν) (κ ⊕ ν) ℝ := fromBlocks (C-V*Vᵀ) V Vᵀ 0

lemma augmented_determinant (H C : Matrix κ κ ℝ) (V : Matrix κ ν ℝ) :
    (1-augmentedGram (ν := ν) H*augmentedCoefficient C V).det=(1-H*C).det := by
  have he : (1 : Matrix (κ ⊕ ν) (κ ⊕ ν) ℝ)-augmentedGram H*augmentedCoefficient C V =
      fromBlocks (1-H*(C-V*Vᵀ)) (-H*V) (-Vᵀ) 1 := by
    simp only [augmentedGram,augmentedCoefficient,Matrix.fromBlocks_multiply]
    ext i k
    cases i <;> cases k <;> simp [Matrix.one_apply]
  rw [he,Matrix.det_fromBlocks_one₂₂]
  congr 1
  simp only [Matrix.mul_sub,Matrix.neg_mul,Matrix.mul_neg,neg_neg,Matrix.mul_assoc]
  abel

omit [Fintype κ] [DecidableEq κ] [DecidableEq ν] in
lemma augmentedCoefficient_hermitian {C : Matrix κ κ ℝ} (hC : C.IsHermitian)
    (V : Matrix κ ν ℝ) : (augmentedCoefficient C V).IsHermitian := by
  apply Matrix.IsHermitian.fromBlocks
  · apply hC.sub
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.isHermitian_mul_conjTranspose_self V
  · simp only [Matrix.conjTranspose_eq_transpose_of_trivial]
  · exact Matrix.isHermitian_zero

omit [Fintype κ] [DecidableEq κ] [DecidableEq ν] in
lemma continuous_augmentedCoefficient {α : Type*} [TopologicalSpace α]
    {C : α → Matrix κ κ ℝ} {V : α → Matrix κ ν ℝ} (hC : Continuous C) (hV : Continuous V) :
    Continuous (fun x => augmentedCoefficient (C x) (V x)) := by
  unfold augmentedCoefficient
  fun_prop

omit [Fintype κ] [DecidableEq κ] [DecidableEq ν] in
lemma augmentedCoefficient_zero : augmentedCoefficient (0 : Matrix κ κ ℝ) (0 : Matrix κ ν ℝ)=0 := by
  ext i k
  cases i <;> cases k <;> simp [augmentedCoefficient]

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius

theorem compact_limiting_augmented_gram_robust {α ν : Type*}
    [TopologicalSpace α] [CompactSpace α] [Fintype ν] [DecidableEq ν]
    {j : ℝ} (hj : 0 < j) (hj1 : j < 1) (b e s : α → ℝ)
    (V : α → Matrix (Fin 3) ν ℝ) (hb : Continuous b) (he : Continuous e)
    (hs : Continuous s) (hV : Continuous V)
    (hb1 : ∀ x, b x ≤ 1) (he0 : ∀ x, 0 ≤ e x) (hs0 : ∀ x, s x ≠ 0) :
    ∃ δ ρ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < ρ ∧
      ∀ x (ι : Type) [Fintype ι] [DecidableEq ι] (Q : Matrix ι ((Fin 3) ⊕ ν) ℝ)
        (C : Matrix ((Fin 3) ⊕ ν) ((Fin 3) ⊕ ν) ℝ), C.IsHermitian →
        ‖Qᵀ*Q-augmentedGram (limitingGram (b x) (e x) (s x))‖ < ρ →
        ‖C-augmentedCoefficient (rankCoefficient j (b x) (s x)) (V x)‖ < ρ →
        ((1-δ) • (1 : Matrix ι ι ℝ)-Q*C*Qᵀ).PosDef := by
  let H := fun x => augmentedGram (ν := ν) (limitingGram (b x) (e x) (s x))
  let C₀ := fun x r => augmentedCoefficient (rankCoefficient r (b x) (s x)) ((r/j) • V x)
  have hH : Continuous H := by
    unfold H augmentedGram limitingGram
    fun_prop (disch := aesop)
  have hC : Continuous (Function.uncurry C₀) := by
    apply continuous_augmentedCoefficient
    · unfold rankCoefficient
      fun_prop (disch := aesop)
    · fun_prop
  have hherm : ∀ x r, r ∈ Icc 0 j → (C₀ x r).IsHermitian := by
    intro x r _
    exact augmentedCoefficient_hermitian (rankCoefficient_hermitian r (b x) (s x)) _
  have hz : ∀ x, C₀ x 0=0 := by
    intro x
    have hc : rankCoefficient 0 (b x) (s x)=0 := by
      ext i k; fin_cases i <;> fin_cases k <;> simp [rankCoefficient]
    simp only [C₀,hc,zero_div,zero_smul,augmentedCoefficient_zero]
  have hd : ∀ x r, r ∈ Icc 0 j → (1-H x*C₀ x r).det ≠ 0 := by
    intro x r hr
    change (1-augmentedGram (limitingGram (b x) (e x) (s x))*
      augmentedCoefficient (rankCoefficient r (b x) (s x)) ((r/j) • V x)).det ≠ 0
    rw [augmented_determinant,limiting_rank_determinant]
    have hrb : r*b x < 1 := lt_of_le_of_lt (mul_le_of_le_one_right hr.1 (hb1 x)) (hr.2.trans_lt hj1)
    have hre : 0 ≤ r*e x := mul_nonneg hr.1 (he0 x)
    exact ne_of_gt (mul_pos (by nlinarith) (sq_pos_of_pos (by linarith)))
  obtain ⟨δ,ρ,hδ,hδ1,hρ,hfinal⟩ := compact_gram_path_robust hj H C₀ hH hC hherm hz hd
  refine ⟨δ,ρ,hδ,hδ1,hρ,?_⟩
  intro x ι _ _ Q C hc hq hcc
  apply hfinal x ι Q C hc hq
  simpa only [C₀,div_self hj.ne',one_smul] using hcc
end SKGap
end
end

end OAI
