import Mathlib

namespace OAI

section
open Filter Set
open scoped Topology
namespace SKValue
structure BoundedUniformLimit {A:Type*} (F:ℕ → A → ℝ) (f:A → ℝ) : Prop where
  tendsto : TendstoUniformly F f atTop
  bound : ∃ C:ℝ,0 ≤ C ∧ (∀ n x,|F n x| ≤ C) ∧ ∀ x,|f x| ≤ C
lemma BoundedUniformLimit.const {A:Type*} (c:ℝ) :
    BoundedUniformLimit (fun (_:ℕ) (_:A) ↦ c) (fun _ ↦ c) :=
  ⟨by
    rw [Metric.tendstoUniformly_iff]
    exact fun ε hε ↦ Eventually.of_forall (fun _ _ ↦ by simpa using hε),|c|,abs_nonneg c,fun _ _ ↦ le_rfl,fun _ ↦ le_rfl⟩
lemma BoundedUniformLimit.seq {A:Type*} {c:ℕ → ℝ} {d:ℝ}
    (hl:Tendsto c atTop (𝓝 d)) (hb:∃ C:ℝ,0 ≤ C ∧ ∀ n,|c n| ≤ C) :
    BoundedUniformLimit (fun n (_:A) ↦ c n) (fun _ ↦ d) := by
  obtain ⟨C,hC,hb⟩:=hb
  refine ⟨?_,C,hC,fun n _ ↦ hb n,fun _ ↦ le_of_tendsto hl.abs (Eventually.of_forall hb)⟩
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  exact (Metric.tendsto_nhds.mp hl ε hε).mono (fun n hn _ ↦ by simpa only [dist_comm] using hn)
lemma BoundedUniformLimit.add {A:Type*} {F G:ℕ → A → ℝ} {f g:A → ℝ}
    (hF:BoundedUniformLimit F f) (hG:BoundedUniformLimit G g) :
    BoundedUniformLimit (fun n x ↦ F n x+G n x) (fun x ↦ f x+g x) := by
  obtain ⟨C,hC,hb,hf⟩:=hF.bound
  obtain ⟨D,hD,hd,hg⟩:=hG.bound
  exact ⟨hF.tendsto.add hG.tendsto,C+D,add_nonneg hC hD,
    fun n x ↦ (abs_add_le _ _).trans (add_le_add (hb n x) (hd n x)),
    fun x ↦ (abs_add_le _ _).trans (add_le_add (hf x) (hg x))⟩
lemma BoundedUniformLimit.mul {A:Type*} {F G:ℕ → A → ℝ} {f g:A → ℝ}
    (hF:BoundedUniformLimit F f) (hG:BoundedUniformLimit G g) :
    BoundedUniformLimit (fun n x ↦ F n x*G n x) (fun x ↦ f x*g x) := by
  obtain ⟨C,hC,hb,hf⟩:=hF.bound
  obtain ⟨D,hD,hd,hg⟩:=hG.bound
  refine ⟨?_,C*D,mul_nonneg hC hD,?_,?_⟩
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    let δ:=ε/(C+D+1)
    have hden:0<C+D+1 := by linarith
    have hδ:0<δ := div_pos hε hden
    have heq:δ*(C+D+1)=ε := div_mul_cancel₀ ε hden.ne'
    filter_upwards [(Metric.tendstoUniformly_iff.mp hF.tendsto) δ hδ,
      (Metric.tendstoUniformly_iff.mp hG.tendsto) δ hδ] with n hn hm x
    have hn':|F n x-f x|<δ := by simpa only [Real.dist_eq,abs_sub_comm] using hn x
    have hm':|G n x-g x|<δ := by simpa only [Real.dist_eq,abs_sub_comm] using hm x
    rw [Real.dist_eq,abs_sub_comm]
    have he:F n x*G n x-f x*g x=F n x*(G n x-g x)+(F n x-f x)*g x := by ring
    rw [he]
    apply (abs_add_le _ _).trans_lt
    rw [abs_mul,abs_mul]
    have h1:=mul_le_mul (hb n x) hm'.le (abs_nonneg _) hC
    have h2:=mul_le_mul hn'.le (hg x) (abs_nonneg _) hδ.le
    nlinarith
  · intro n x;rw [abs_mul];exact mul_le_mul (hb n x) (hd n x) (abs_nonneg _) hC
  · intro x;rw [abs_mul];exact mul_le_mul (hf x) (hg x) (abs_nonneg _) hC
lemma BoundedUniformLimit.neg {A:Type*} {F:ℕ → A → ℝ} {f:A → ℝ}
    (hF:BoundedUniformLimit F f) : BoundedUniformLimit (fun n x ↦ -F n x) (fun x ↦ -f x) := by
  simpa only [neg_one_mul] using (BoundedUniformLimit.const (-1)).mul hF
lemma BoundedUniformLimit.sub {A:Type*} {F G:ℕ → A → ℝ} {f g:A → ℝ}
    (hF:BoundedUniformLimit F f) (hG:BoundedUniformLimit G g) :
    BoundedUniformLimit (fun n x ↦ F n x-G n x) (fun x ↦ f x-g x) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg
lemma BoundedUniformLimit.pow {A:Type*} {F:ℕ → A → ℝ} {f:A → ℝ}
    (hF:BoundedUniformLimit F f) (k:ℕ) :
    BoundedUniformLimit (fun n x ↦ F n x^k) (fun x ↦ f x^k) := by
  induction k with
  | zero => exact BoundedUniformLimit.const 1
  | succ k ih => simpa only [pow_succ] using ih.mul hF
end SKValue

end

end OAI
